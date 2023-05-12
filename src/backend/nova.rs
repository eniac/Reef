#![allow(missing_docs)]
type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
use ::bellperson::{
    gadgets::num::AllocatedNum, ConstraintSystem, LinearCombination, Namespace, SynthesisError,
    Variable,
};
use circ::{ir::term::Value, target::r1cs::*};
use ff::{Field, PrimeField};
use generic_array::typenum;
use gmp_mpfr_sys::gmp::limb_t;
use neptune::{
    circuit2::Elt,
    poseidon::PoseidonConstants,
    sponge::api::{IOPattern, SpongeAPI, SpongeOp},
    sponge::circuit::SpongeCircuit,
    sponge::vanilla::{Mode, SpongeTrait},
};
use nova_snark::{
    traits::{circuit::StepCircuit, Group},
    StepCounterType,
};
use rug::integer::{IsPrime, Order};
use rug::Integer;
use std::collections::HashMap;

/// Convert a (rug) integer to a prime field element.
pub fn int_to_ff<F: PrimeField>(i: Integer) -> F {
    let mut accumulator = F::from(0);
    let limb_bits = (std::mem::size_of::<limb_t>() as u64) << 3;
    let limb_base = F::from(2).pow_vartime([limb_bits]);
    // as_ref yeilds a least-significant-first array.
    for digit in i.as_ref().iter().rev() {
        accumulator *= limb_base;
        accumulator += F::from(*digit);
    }
    accumulator
}

/// Convert one our our linear combinations to a bellman linear combination.
/// Takes a zero linear combination. We could build it locally, but bellman provides one, so...
fn lc_to_bellman<F: PrimeField, CS: ConstraintSystem<F>>(
    vars: &HashMap<Var, Variable>,
    lc: &Lc,
    zero_lc: LinearCombination<F>,
) -> LinearCombination<F> {
    let mut lc_bellman = zero_lc;
    // This zero test is needed until https://github.com/zkcrypto/bellman/pull/78 is resolved
    if !lc.constant.is_zero() {
        lc_bellman = lc_bellman + (int_to_ff((&lc.constant).into()), CS::one());
    }
    for (v, c) in &lc.monomials {
        // ditto
        if !c.is_zero() {
            lc_bellman = lc_bellman + (int_to_ff(c.into()), *vars.get(v).unwrap());
        }
    }
    lc_bellman
}

// hmmm... this should work essentially all the time, I think
fn get_modulus<F: Field + PrimeField>() -> Integer {
    let neg_1_f = -F::one();
    let p_lsf: Integer = Integer::from_digits(neg_1_f.to_repr().as_ref(), Order::Lsf) + 1;
    let p_msf: Integer = Integer::from_digits(neg_1_f.to_repr().as_ref(), Order::Msf) + 1;
    if p_lsf.is_probably_prime(30) != IsPrime::No {
        p_lsf
    } else if p_msf.is_probably_prime(30) != IsPrime::No {
        p_msf
    } else {
        panic!("could not determine ff::Field byte order")
    }
}

#[derive(Clone, Debug)]
pub enum GlueOpts<F: PrimeField> {
    PolyHash((F, F)),             // i, hash
    NlHash((F, F, Vec<F>, F)),    // i, hash, q, v
    PolyNL((Vec<F>, F)),          // doc_q, doc_v
    NlNl((Vec<F>, F, Vec<F>, F)), // q, v, doc_q, doc_v
}

#[derive(Clone, Debug)]
pub struct NFAStepCircuit<F: PrimeField> {
    r1cs: R1csFinal, // TODO later ref
    values: Option<Vec<Value>>,
    //prover_data: &'a ProverData,
    //wits: Option<'a FxHashMap<String, Value>>,
    batch_size: usize,
    states: Vec<F>,
    glue: Vec<GlueOpts<F>>,
    commit_blind: F,
    first: bool,
    epsilon_num: F,
    start_of_ep: isize,
    accepting: Vec<F>,
    pc: PoseidonConstants<F, typenum::U4>,
}

// note that this will generate a single round, and no witnesses, unlike nova example code
// witness and loops will happen at higher level as to put as little as possible deep in circ
impl<F: PrimeField> NFAStepCircuit<F> {
    pub fn new(
        //        prover_data: &'a ProverData,
        //        wits: Option<FxHashMap<String, Value>>, //Option<&'a FxHashMap<String, Value>>,
        r1cs: R1csFinal,
        values: Option<Vec<Value>>,
        states: Vec<F>,
        glue: Vec<GlueOpts<F>>,
        commit_blind: F,
        first: bool,
        epsilon_num: F,
        start_of_ep: isize,
        accepting: Vec<F>,
        batch_size: usize,
        pcs: PoseidonConstants<F, typenum::U4>,
    ) -> Self {
        // todo check wits line up with the non det advice

        assert_eq!(states.len(), 2);
        assert_eq!(glue.len(), 2);
        assert_eq!(accepting.len(), 2);

        match (&glue[0], &glue[1]) {
            (GlueOpts::PolyHash(_), GlueOpts::PolyHash(_)) => {}
            (GlueOpts::NlHash(_), GlueOpts::NlHash(_)) => {}
            (GlueOpts::PolyNL(_), GlueOpts::PolyNL(_)) => {}
            (GlueOpts::NlNl(_), GlueOpts::NlNl(_)) => {}
            (_, _) => {
                panic!("glue I/O does not match");
            }
        }
        // todo blind, first checking here

        NFAStepCircuit {
            r1cs: r1cs, //&prover_data.r1cs, // def get rid of this crap
            values: values,
            batch_size: batch_size,
            states: states,
            glue: glue,
            commit_blind: commit_blind,
            first: first,
            epsilon_num: epsilon_num,
            start_of_ep: start_of_ep,
            accepting: accepting,
            pc: pcs,
        }
    }

    fn generate_variable_info(&self, var: Var) -> (String, String) {
        assert!(
            !matches!(var.ty(), VarType::CWit),
            "Nova doesn't support committed witnesses"
        );
        assert!(
            !matches!(var.ty(), VarType::RoundWit | VarType::Chall),
            "Nova doesn't support rounds"
        );
        //let public = matches!(var.ty(), VarType::Inst); // but we really dont care
        let name_f = format!("{var:?}");

        let s = self.r1cs.names[&var].clone();

        (name_f, s)
    }

    fn input_variable_parsing(
        &self,
        vars: &mut HashMap<Var, Variable>,
        s: &String,
        var: Var,
        state_0: AllocatedNum<F>,
    ) -> Result<bool, SynthesisError> {
        if s.starts_with("state_0") {
            vars.insert(var, state_0.get_variable());

            return Ok(true);
        }
        return Ok(false);
    }

    fn input_variable_hash_parsing(
        &self,
        vars: &mut HashMap<Var, Variable>,
        s: &String,
        var: Var,
        i_0: AllocatedNum<F>,
    ) -> Result<bool, SynthesisError> {
        if s.starts_with("i_0") {
            vars.insert(var, i_0.get_variable());

            return Ok(true);
        }
        return Ok(false);
    }

    fn input_variable_qv_parsing(
        &self,
        vars: &mut HashMap<Var, Variable>,
        s: &String,
        var: Var,
        tag: &str,
        sc_l: usize,
        prev_q: &Vec<AllocatedNum<F>>,
        prev_v: &AllocatedNum<F>,
        alloc_prev_rc: &mut Vec<Option<AllocatedNum<F>>>,
    ) -> Result<bool, SynthesisError> {
        if s.starts_with(&format!("{}_prev_running_claim", tag)) {
            vars.insert(var, prev_v.get_variable());

            alloc_prev_rc[sc_l] = Some(prev_v.clone());

            return Ok(true);
        } else if s.starts_with(&format!("{}_eq_{}_q", tag, self.batch_size)) {
            // q
            let s_sub: Vec<&str> = s.split("_").collect();
            let q: usize = s_sub[4].parse().unwrap();

            vars.insert(var, prev_q[q].get_variable());
            alloc_prev_rc[q] = Some(prev_q[q].clone());

            return Ok(true);
        }

        return Ok(false);
    }

    fn default_parsing(
        &self,
        s: &String,
        alloc_v: &AllocatedNum<F>,
        last_state: &mut Option<AllocatedNum<F>>,
        accepting: &mut Option<AllocatedNum<F>>,
    ) -> Result<(), SynthesisError>
where {
        if s.starts_with(&format!("state_{}", self.batch_size)) {
            *last_state = Some(alloc_v.clone()); //.get_variable();
        } else if s.starts_with(&format!("accepting")) {
            *accepting = Some(alloc_v.clone());
        }
        Ok(())
    }

    fn hash_parsing(
        &self,
        s: &String,
        alloc_v: &AllocatedNum<F>,
        alloc_chars: &mut Vec<Option<AllocatedNum<F>>>,
        alloc_idxs: &mut Vec<Option<AllocatedNum<F>>>,
        last_i: &mut Option<AllocatedNum<F>>,
    ) -> Result<bool, SynthesisError> {
        // intermediate (in circ) wits
        if s.starts_with("char_") {
            let char_j = Some(alloc_v.clone()); //.get_variable();

            let s_sub: Vec<&str> = s.split("_").collect();
            let j: usize = s_sub[1].parse().unwrap();

            if j < self.batch_size {
                alloc_chars[j] = char_j;
            } // don't add the last one

            return Ok(true);
        } else if s.starts_with(&format!("i_{}", self.batch_size)) {
            *last_i = Some(alloc_v.clone());
            alloc_idxs[self.batch_size] = last_i.clone();

            return Ok(true);
        } else if s.starts_with("i_") {
            let i_j = Some(alloc_v.clone()); //.get_variable();

            let s_sub: Vec<&str> = s.split("_").collect();
            let j: usize = s_sub[1].parse().unwrap();

            alloc_idxs[j] = i_j;

            return Ok(true);
        }

        return Ok(false);
    }

    // todo find and set random Has res, z hash input
    fn hash_circuit<CS>(
        &self,
        cs: &mut CS,
        first: bool,
        epsilon_num: F,
        start_of_ep: isize,
        z_input_hash: AllocatedNum<F>,
        i_0: AllocatedNum<F>,
        blind: F,
        alloc_chars: Vec<Option<AllocatedNum<F>>>,
        doc_idxs: Vec<Option<AllocatedNum<F>>>,
    ) -> Result<AllocatedNum<F>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        // println!("adding hash chain hashes in nova");
        // allocate blind
        let alloc_blind = AllocatedNum::alloc(cs.namespace(|| "blind"), || Ok(blind))?;

        let mut ns = cs.namespace(|| format!("poseidon hash start"));
        let random_hash = {
            let acc = &mut ns;
            // "random_hash_result"
            let mut sponge = SpongeCircuit::new_with_constants(&self.pc, Mode::Simplex);

            sponge.start(
                IOPattern(vec![SpongeOp::Absorb(2), SpongeOp::Squeeze(1)]),
                None,
                acc,
            );

            SpongeAPI::absorb(
                &mut sponge,
                2,
                &[
                    Elt::Allocated(alloc_blind),
                    Elt::num_from_fr::<CS>(F::from(0)),
                ],
                acc,
            );

            let output = SpongeAPI::squeeze(&mut sponge, 1, acc);

            sponge.finish(acc).unwrap();

            Elt::ensure_allocated(&output[0], &mut ns.namespace(|| "ensure allocated"), true)?
        };

        let start_hash;
        let i_0_inv;
        let first_sel;

        match first {
            true => {
                start_hash = AllocatedNum::alloc(ns.namespace(|| "start_hash"), || {
                    Ok(random_hash.get_value().unwrap())
                })?;
                i_0_inv = AllocatedNum::alloc(ns.namespace(|| "i0 inv"), || Ok(F::from(1)))?;
                first_sel = AllocatedNum::alloc(ns.namespace(|| "first_sel"), || Ok(F::from(0)))?;
            }
            false => {
                start_hash = AllocatedNum::alloc(ns.namespace(|| "start_hash"), || {
                    Ok(z_input_hash.get_value().unwrap())
                })?;

                //type_of(&i_0.get_value().unwrap());
                let inv_opt = i_0.get_value().unwrap().invert();
                let inv = inv_opt.expect("couldn't invert i_0 for wit");
                i_0_inv = AllocatedNum::alloc(ns.namespace(|| "io inv"), || Ok(inv))?;
                first_sel = AllocatedNum::alloc(ns.namespace(|| "first_sel"), || Ok(F::from(1)))?;
            }
        };

        // regular hashing
        let mut prev_hash = start_hash.clone();
        let mut next_hash = start_hash.clone(); // dummy
        for i in 0..(self.batch_size) {
            let unwrap_alloc_char = alloc_chars[i].clone().unwrap();
            let mut hash_ns = ns.namespace(|| format!("poseidon hash batch {}", i));
            let hashed = {
                let acc = &mut hash_ns;
                let mut sponge = SpongeCircuit::new_with_constants(&self.pc, Mode::Simplex);

                sponge.start(
                    IOPattern(vec![SpongeOp::Absorb(3), SpongeOp::Squeeze(1)]),
                    None,
                    acc,
                );
                /*
                                if i_0.get_value().is_some() {
                                    println!(
                                        "ELTS FOR HASH: {:#?}, {:#?}, {:#?}",
                                        prev_hash.get_value().unwrap(),
                                        unwrap_alloc_char.get_value().unwrap(),
                                        doc_idxs[i].clone().unwrap().get_value().unwrap()
                                    );
                                }
                */

                SpongeAPI::absorb(
                    &mut sponge,
                    3,
                    &[
                        Elt::Allocated(prev_hash.clone()),
                        Elt::Allocated(unwrap_alloc_char.clone()),
                        Elt::Allocated(doc_idxs[i].clone().unwrap()),
                    ],
                    // TODO "connected"? get rid clones
                    acc,
                );

                let output = SpongeAPI::squeeze(&mut sponge, 1, acc);

                sponge.finish(acc).unwrap();

                Elt::ensure_allocated(
                    &output[0],
                    &mut hash_ns.namespace(|| "ensure allocated"),
                    true,
                )?
            };

            // wrap each in ite for epsilon in batching (first not necessary)
            // if EP_SEL then NEXT_HASH = PREV_HASH else NEXT_HASH = HASHED(PREV_HASH)
            // EP_SEL = (alloc_chars[i] == EPSILON_NUM)
            // -> r1cs:
            // NEXT_HASH = PREV_HASH + EP_SEL(HASHED - PREV_HASH)
            // (epsilon_num - char) * WIT = EP_SEL
            // (1 - EP_SEL) * (epsilon_num - char) = 0

            let comp_inv;
            let ep_sel;

            let ep_num = AllocatedNum::alloc(hash_ns.namespace(|| "epsilon"), || Ok(epsilon_num))?;

            if (i as isize) >= start_of_ep && start_of_ep != -1 {
                next_hash = AllocatedNum::alloc(hash_ns.namespace(|| "next_hash"), || {
                    Ok(prev_hash.get_value().unwrap())
                })?;

                comp_inv =
                    AllocatedNum::alloc(hash_ns.namespace(|| "comp inv"), || Ok(F::from(1)))?;
                ep_sel = AllocatedNum::alloc(hash_ns.namespace(|| "ep_sel"), || Ok(F::from(0)))?;
            } else {
                next_hash = AllocatedNum::alloc(hash_ns.namespace(|| "next_hash"), || {
                    Ok(hashed.get_value().unwrap())
                })?;

                let comp_inv_pre = (ep_num.get_value().unwrap()
                    - unwrap_alloc_char.get_value().unwrap())
                .invert()
                .expect("couldn't invert comp for wit");
                comp_inv =
                    AllocatedNum::alloc(hash_ns.namespace(|| "comp inv"), || Ok(comp_inv_pre))?;
                assert_eq!(
                    comp_inv_pre
                        * (ep_num.get_value().unwrap() - unwrap_alloc_char.get_value().unwrap()),
                    F::from(1)
                );

                ep_sel = AllocatedNum::alloc(hash_ns.namespace(|| "ep_sel"), || Ok(F::from(1)))?;
            }

            // sanity - get rid of
            if i_0.get_value().is_some() {
                assert_eq!(
                    ep_sel.get_value().unwrap()
                        * (hashed.get_value().unwrap() - prev_hash.get_value().unwrap()),
                    next_hash.get_value().unwrap() - prev_hash.get_value().unwrap()
                );
                assert_eq!(
                    (ep_num.get_value().unwrap() - unwrap_alloc_char.get_value().unwrap())
                        * comp_inv.get_value().unwrap(),
                    ep_sel.get_value().unwrap()
                );
                assert_eq!(
                    (F::from(1) - ep_sel.get_value().unwrap())
                        * (ep_num.get_value().unwrap() - unwrap_alloc_char.get_value().unwrap()),
                    F::from(1) - F::from(1)
                );
            } else {
                //println!("NO SANITY CHECK");
            }

            hash_ns.enforce(
                || format!("epsilon ite {}", i),
                |z| z + ep_sel.get_variable(),
                |z| z + hashed.get_variable() - prev_hash.get_variable(),
                |z| z + next_hash.get_variable() - prev_hash.get_variable(),
            );

            hash_ns.enforce(
                || format!("epsilon sel {}", i),
                |z| z + ep_num.get_variable() - unwrap_alloc_char.get_variable(),
                |z| z + comp_inv.get_variable(),
                |z| z + ep_sel.get_variable(),
            );

            hash_ns.enforce(
                || format!("epsilon sel2 {}", i),
                |z| z + CS::one() - ep_sel.get_variable(),
                |z| z + ep_num.get_variable() - unwrap_alloc_char.get_variable(),
                |z| z + CS::one() - CS::one(),
            );

            prev_hash = next_hash.clone();
        }

        // random start ite
        // if FIRST_SEL==0 then START_HASH = RANDOM_HASH else START_HASH = Z_INPUT_HASH
        // FIRST_SEL = !(i_0 == 0)
        // -> r1cs:
        // START_HASH = RANDOM_HASH + FIRST_SEL(Z_INPUT_HASH - RANDOM_HASH) <- ite
        // i_0 * WIT = FIRST_SEL <- wit here is inv(i_0)
        // (1 - FIRST_SEL) * i_0 = 0

        // sanity - get rid of
        if i_0.get_value().is_some() {
            assert_eq!(
                first_sel.get_value().unwrap()
                    * (z_input_hash.get_value().unwrap() - random_hash.get_value().unwrap()),
                start_hash.get_value().unwrap() - random_hash.get_value().unwrap()
            );
            assert_eq!(
                i_0.get_value().unwrap() * i_0_inv.get_value().unwrap(),
                first_sel.get_value().unwrap()
            );
            assert_eq!(
                (F::from(1) - first_sel.get_value().unwrap()) * i_0.get_value().unwrap(),
                F::from(1) - F::from(1)
            );
        }

        ns.enforce(
            || format!("ite"),
            |z| z + first_sel.get_variable(),
            |z| z + z_input_hash.get_variable() - random_hash.get_variable(),
            |z| z + start_hash.get_variable() - random_hash.get_variable(),
        );

        ns.enforce(
            || format!("sel"),
            |z| z + i_0.get_variable(),
            |z| z + i_0_inv.get_variable(),
            |z| z + first_sel.get_variable(),
        );

        ns.enforce(
            || format!("sel 2"),
            |z| z + CS::one() - first_sel.get_variable(),
            |z| z + i_0.get_variable(),
            |z| z + CS::one() - CS::one(),
        );

        return Ok(next_hash); //last hash
    }

    fn intm_fs_parsing(
        &self,
        alloc_v: &AllocatedNum<F>,
        //vars: &mut HashMap<Var, Variable>,
        s: &String,
        //var: Var,
        is_doc_nl: bool,
        alloc_qv: &mut Vec<Option<AllocatedNum<F>>>,
        alloc_claim_r: &mut Option<AllocatedNum<F>>,
        alloc_gs: &mut Vec<Vec<Option<AllocatedNum<F>>>>,
        //prev_q: &Vec<AllocatedNum<F>>,
        //prev_v: &AllocatedNum<F>,
    ) -> Result<bool, SynthesisError> {
        // intermediate (in circ) wits
        if (!is_doc_nl && s.starts_with("nl_combined_q"))
            || (is_doc_nl && s.starts_with("nldoc_combined_q"))
        {
            alloc_qv[0] = Some(alloc_v.clone());

            return Ok(true);
        } else if !is_doc_nl && s.starts_with("v_") {
            let v_j = Some(alloc_v.clone()); //.get_variable();

            let s_sub: Vec<&str> = s.split("_").collect();
            let j: usize = s_sub[1].parse().unwrap();
            alloc_qv[j] = v_j; // TODO check

            return Ok(true);
        } else if is_doc_nl && s.starts_with("char_") {
            let v_j = Some(alloc_v.clone()); //.get_variable();

            //let j = s.chars().nth(5).unwrap().to_digit(10).unwrap() as usize;
            let s_sub: Vec<&str> = s.split("_").collect();
            let j: usize = s_sub[1].parse().unwrap();

            if j < self.batch_size {
                alloc_qv[j + 1] = v_j;
            } // don't add the last one

            return Ok(true);
        } else if (!is_doc_nl && s.starts_with("nl_claim_r"))
            || (is_doc_nl && s.starts_with("nldoc_claim_r"))
        {
            *alloc_claim_r = Some(alloc_v.clone());
        } else if (!is_doc_nl && s.starts_with("nl_sc_g"))
            || (is_doc_nl && s.starts_with("nldoc_sc_g"))
        {
            let gij = Some(alloc_v.clone());

            let s_sub: Vec<&str> = s.split("_").collect();
            let j: usize = s_sub[3].parse().unwrap();

            match s_sub[4] {
                "const" => {
                    alloc_gs[j - 1][0] = gij;
                }
                "x" => {
                    alloc_gs[j - 1][1] = gij;
                }
                "xsq" => {
                    alloc_gs[j - 1][2] = gij;
                }
                _ => {
                    panic!("weird variable name for sumcheck polys");
                }
            }
        }
        return Ok(false);
    }

    fn fiatshamir_circuit<'b, CS>(
        &self,
        //cs: &mut CS,
        //alloc_v: &AllocatedNum<F>,
        //namespace: String,
        query: &[Elt<F>],
        sponge: &mut SpongeCircuit<'b, F, typenum::U4, CS>,
        sponge_ns: &mut Namespace<'b, F, CS>,
        input_eq: AllocatedNum<F>,
        tag: &str,
    ) -> Result<(), SynthesisError>
    where
        //A: Arity<F>,
        CS: ConstraintSystem<F>,
    {
        // original var alloc'd before

        let new_pos = {
            SpongeAPI::absorb(sponge, query.len() as u32, query, sponge_ns);

            let output = SpongeAPI::squeeze(sponge, 1, sponge_ns);

            Elt::ensure_allocated(
                &output[0],
                &mut sponge_ns.namespace(|| format!("ensure allocated {}", tag)), // name must be the same
                // (??)
                true,
            )?
        };

        assert_eq!(new_pos.clone().get_value(), input_eq.clone().get_value());

        sponge_ns.enforce(
            || format!("eq {}", tag),
            |z| z + new_pos.get_variable(),
            |z| z + CS::one(),
            |z| z + input_eq.get_variable(),
        );

        Ok(())
    }

    fn nl_eval_fiatshamir<'b, CS>(
        &self,
        cs: &mut CS,
        //sponge: &mut SpongeCircuit<'b, F, typenum::U2, CS>,
        //sponge_ns: &mut Namespace<'b, F, CS>,
        tag: &str,
        sc_l: usize,
        alloc_qv: &Vec<Option<AllocatedNum<F>>>,
        alloc_prev_rc: &Vec<Option<AllocatedNum<F>>>,
        alloc_rc: &Vec<Option<AllocatedNum<F>>>,
        alloc_claim_r: &Option<AllocatedNum<F>>,
        //alloc_sc_r: &Vec<Option<AllocatedNum<F>>>,
        alloc_gs: &Vec<Vec<Option<AllocatedNum<F>>>>,
        vesta_hash: F,
    ) -> Result<(), SynthesisError>
    where
        //A: Arity<F>,
        CS: ConstraintSystem<F>,
    {
        let mut sponge = SpongeCircuit::new_with_constants(&self.pc, Mode::Simplex);
        let mut sponge_ns = cs.namespace(|| format!("{} sponge", tag));

        let mut pattern = match tag {
            "eval" => vec![
                SpongeOp::Absorb((self.batch_size + sc_l + 2) as u32), // vs,
                // combined_q,
                // running q,v
                SpongeOp::Squeeze(1),
            ],
            "doc" => vec![
                SpongeOp::Absorb((self.batch_size + sc_l + 3) as u32), // vs,
                SpongeOp::Squeeze(1),
            ],
            _ => panic!("weird tag"),
        };
        for _i in 0..sc_l {
            // sum check rounds
            pattern.append(&mut vec![SpongeOp::Absorb(3), SpongeOp::Squeeze(1)]);
        }

        sponge.start(IOPattern(pattern), None, &mut sponge_ns);

        // (combined_q, vs, running_q, running_v)
        let mut elts = vec![];
        // if DOC
        if matches!(tag, "doc") {
            let e = AllocatedNum::alloc(sponge_ns.namespace(|| "doc commit hash start"), || {
                Ok(vesta_hash)
            })?;
            elts.push(Elt::Allocated(e));
        }
        for e in alloc_qv {
            elts.push(Elt::Allocated(e.clone().unwrap()));
        }
        for e in alloc_prev_rc {
            elts.push(Elt::Allocated(e.clone().unwrap()));
        }

        self.fiatshamir_circuit(
            &elts,
            &mut sponge,
            &mut sponge_ns,
            alloc_claim_r.clone().unwrap(),
            "claim_r",
        )?; // TODO

        for j in 0..sc_l {
            let mut elts = vec![];
            for coeffs in &alloc_gs[j] {
                for e in coeffs {
                    elts.push(Elt::Allocated(e.clone()));
                }
            }

            self.fiatshamir_circuit(
                &elts,
                &mut sponge,
                &mut sponge_ns,
                alloc_rc[j].clone().unwrap(),
                &format!("sc_r_{}", j),
            )?;
        }

        sponge.finish(&mut sponge_ns).unwrap();
        return Ok(());
    }

    fn nl_eval_parsing(
        &self,
        alloc_v: &AllocatedNum<F>,
        s: &String,
        sc_l: usize,
        alloc_rc: &mut Vec<Option<AllocatedNum<F>>>,
        tag: &str,
        //alloc_prev_rc: &mut Vec<Option<AllocatedNum<F>>>,
    ) -> Result<bool, SynthesisError> {
        if s.starts_with(&format!("{}_next_running_claim", tag)) {
            // v

            alloc_rc[sc_l] = Some(alloc_v.clone());

            return Ok(true);
        } else if s.starts_with(&format!("{}_sc_r_", tag)) {
            // TODO move, do this in order
            // q
            let s_sub: Vec<&str> = s.split("_").collect();
            let q: usize = s_sub[3].parse().unwrap();

            alloc_rc[q - 1] = Some(alloc_v.clone());
            //println!("ALLOC_RC: {:#?}", alloc_v.get_value());

            return Ok(true);
        }
        return Ok(false);
    }
}

impl<F> StepCircuit<F> for NFAStepCircuit<F>
where
    F: PrimeField,
{
    fn arity(&self) -> usize {
        // [state, opt<i>, opt<hash>, opt<v,q for eval claim>, opt<v,q for doc claim>, accepting?]

        let mut arity = 2;
        match &self.glue[0] {
            GlueOpts::PolyHash(_) => {
                arity += 2;
            }
            GlueOpts::NlHash((_, _, q, _)) => arity += q.len() + 1 + 2, // q, v, hashes
            GlueOpts::PolyNL((dq, _)) => arity += dq.len() + 1,         // doc_q, doc_v
            GlueOpts::NlNl((q, _, dq, _)) => {
                arity += q.len() + 1 + dq.len() + 1;
            }
        }

        arity
    }

    fn output(&self, z: &[F]) -> Vec<F> {
        // sanity check
        assert_eq!(z.len(), self.arity());

        assert_eq!(z[0], self.states[0]); // "current state"
                                          //assert_eq!(z[1], self.chars[0]);

        let mut i = 1;
        match &self.glue[0] {
            GlueOpts::PolyHash((idx, h)) => {
                assert_eq!(z[i], *idx);
                i += 1;
                assert_eq!(z[i], *h);
                i += 1;
            }
            GlueOpts::NlHash((idx, h, q, v)) => {
                assert_eq!(z[i], *idx);
                i += 1;
                assert_eq!(z[i], *h);
                i += 1;
                for qi in q {
                    assert_eq!(z[i], *qi);
                    i += 1;
                }
                assert_eq!(z[i], *v);
                i += 1;
            }
            GlueOpts::PolyNL((dq, dv)) => {
                for qi in dq {
                    assert_eq!(z[i], *qi);
                    i += 1;
                }
                assert_eq!(z[i], *dv);
                i += 1;
            }
            GlueOpts::NlNl((q, v, dq, dv)) => {
                for qi in q {
                    assert_eq!(z[i], *qi);
                    i += 1;
                }
                assert_eq!(z[i], *v);
                i += 1;
                for qi in dq {
                    assert_eq!(z[i], *qi);
                    i += 1;
                }
                assert_eq!(z[i], *dv);
                i += 1;
            }
        }
        assert_eq!(z[i], self.accepting[0]);

        let mut out = vec![
            self.states[1], // "next state"
        ];
        match &self.glue[1] {
            GlueOpts::PolyHash((i, h)) => {
                out.push(*i);
                out.push(*h);
            }
            GlueOpts::NlHash((i, h, q, v)) => {
                out.push(*i);
                out.push(*h);
                out.extend(q);
                out.push(*v);
            }
            GlueOpts::PolyNL((dq, dv)) => {
                out.extend(dq);
                out.push(*dv);
            }
            GlueOpts::NlNl((q, v, dq, dv)) => {
                out.extend(q);
                out.push(*v);
                out.extend(dq);
                out.push(*dv);
            }
        }
        out.push(self.accepting[1]);
        out
    }

    fn get_counter_type(&self) -> StepCounterType {
        StepCounterType::External
    }

    // nova wants this to return the "output" of each step
    fn synthesize<CS>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
        G1: Group<Base = <G2 as Group>::Scalar>,
        G2: Group<Base = <G1 as Group>::Scalar>,
    {
        // inputs
        let state_0 = z[0].clone();

        // ouputs
        let mut last_state = None;
        let mut last_i = None;
        let mut accepting = None;
        let mut out = vec![];

        // intms
        let mut alloc_chars = vec![None; self.batch_size];
        //alloc_chars[0] = Some(char_0.clone());
        let mut alloc_qv = vec![None; self.batch_size + 1];
        let mut alloc_doc_qv = vec![None; self.batch_size + 1];
        //alloc_doc_qv[1] = Some(char_0.clone());
        let mut alloc_idxs = vec![None; self.batch_size + 1];

        let mut alloc_claim_r = None;
        let mut alloc_doc_claim_r = None;

        // convert
        let f_mod = get_modulus::<F>(); // TODO

        assert_eq!(
            self.r1cs.field.modulus(),
            &f_mod,
            "\nR1CS has modulus \n{},\n but Nova CS expects \n{}",
            self.r1cs.field,
            f_mod
        );

        let mut vars = HashMap::with_capacity(self.r1cs.vars.len());

        match &self.glue[0] {
            GlueOpts::PolyHash(_) => {
                let i_0 = z[1].clone();
                alloc_idxs[0] = Some(i_0.clone());
                let hash_0 = z[2].clone();

                for (i, var) in self.r1cs.vars.iter().copied().enumerate() {
                    let (name_f, s) = self.generate_variable_info(var);
                    let val_f = || {
                        Ok({
                            let i_val = &self.values.as_ref().expect("missing values")[i];
                            let ff_val = int_to_ff(i_val.as_pf().into());
                            //debug!("value : {var:?} -> {ff_val:?} ({i_val})");
                            ff_val
                        })
                    };

                    let mut matched = self
                        .input_variable_parsing(
                            &mut vars,
                            &s,
                            var,
                            state_0.clone(),
                            //    char_0.clone(),
                        )
                        .unwrap();
                    if !matched {
                        matched = self
                            .input_variable_hash_parsing(&mut vars, &s, var, i_0.clone())
                            .unwrap();
                    }
                    if !matched {
                        let alloc_v = AllocatedNum::alloc(cs.namespace(|| name_f), val_f)?;
                        vars.insert(var, alloc_v.get_variable());
                        matched = self
                            .hash_parsing(
                                &s,
                                &alloc_v,
                                &mut alloc_chars,
                                &mut alloc_idxs,
                                &mut last_i,
                            )
                            .unwrap();

                        if !matched {
                            self.default_parsing(&s, &alloc_v, &mut last_state, &mut accepting)
                                .unwrap();
                        }
                    }
                }
                out.push(last_state.unwrap());
                out.push(last_i.unwrap());
                let last_hash = self.hash_circuit(
                    cs,
                    self.first,
                    self.epsilon_num,
                    self.start_of_ep,
                    hash_0,
                    i_0,
                    self.commit_blind,
                    alloc_chars,
                    alloc_idxs,
                );
                out.push(last_hash.unwrap());
                out.push(accepting.unwrap());
            }
            GlueOpts::NlHash((_i, _h, q, _v)) => {
                let i_0 = z[1].clone();
                alloc_idxs[0] = Some(i_0.clone());
                let hash_0 = z[2].clone();

                let sc_l = q.len();
                let prev_q = z[3..(3 + sc_l)].to_vec(); //.clone();
                let prev_v = z[3 + sc_l].clone();

                let mut alloc_rc = vec![None; sc_l + 1];
                let mut alloc_prev_rc = vec![None; sc_l + 1];
                let mut alloc_gs = vec![vec![None; 3]; sc_l];

                for (i, var) in self.r1cs.vars.iter().copied().enumerate() {
                    let (name_f, s) = self.generate_variable_info(var);
                    let val_f = || {
                        Ok({
                            let i_val = &self.values.as_ref().expect("missing values")[i];
                            let ff_val = int_to_ff(i_val.as_pf().into());
                            //debug!("value : {var:?} -> {ff_val:?} ({i_val})");
                            ff_val
                        })
                    };
                    //println!("Var (name?) {:#?}", self.r1cs.names[&var]);

                    let mut matched = self
                        .input_variable_parsing(
                            &mut vars,
                            &s,
                            var,
                            state_0.clone(),
                            //   char_0.clone(),
                        )
                        .unwrap();
                    if !matched {
                        matched = self
                            .input_variable_hash_parsing(&mut vars, &s, var, i_0.clone())
                            .unwrap();
                    }
                    if !matched {
                        matched = self
                            .input_variable_qv_parsing(
                                &mut vars,
                                &s,
                                var,
                                "nl",
                                sc_l,
                                &prev_q,
                                &prev_v,
                                &mut alloc_prev_rc,
                            )
                            .unwrap();
                    }
                    if !matched {
                        let alloc_v = AllocatedNum::alloc(cs.namespace(|| name_f), val_f)?;
                        vars.insert(var, alloc_v.get_variable());
                        matched = self
                            .hash_parsing(
                                &s,
                                &alloc_v,
                                &mut alloc_chars,
                                &mut alloc_idxs,
                                &mut last_i,
                            )
                            .unwrap();

                        if !matched {
                            matched = self
                                .intm_fs_parsing(
                                    &alloc_v,
                                    //    &mut vars,
                                    &s,
                                    //    var,
                                    false,
                                    &mut alloc_qv,
                                    &mut alloc_claim_r,
                                    &mut alloc_gs,
                                    //    &prev_q,
                                    //    &prev_v,
                                )
                                .unwrap();

                            if !matched {
                                matched = self
                                    .nl_eval_parsing(
                                        &alloc_v,
                                        &s,
                                        sc_l,
                                        &mut alloc_rc,
                                        "nl",
                                        //    &mut alloc_prev_rc,
                                    )
                                    .unwrap();
                                if !matched {
                                    self.default_parsing(
                                        &s,
                                        &alloc_v,
                                        &mut last_state,
                                        &mut accepting,
                                    )
                                    .unwrap();
                                }
                            }
                        }
                    }
                }
                self.nl_eval_fiatshamir(
                    cs,
                    "eval",
                    //&mut sponge,
                    //    &mut fs_eval_ns,
                    sc_l,
                    &alloc_qv,
                    &alloc_prev_rc,
                    &alloc_rc,
                    &alloc_claim_r,
                    &alloc_gs,
                    self.commit_blind,
                )?;

                out.push(last_state.unwrap());
                out.push(last_i.unwrap());
                let last_hash = self.hash_circuit(
                    cs,
                    self.first,
                    self.epsilon_num,
                    self.start_of_ep,
                    hash_0,
                    i_0,
                    self.commit_blind,
                    alloc_chars,
                    alloc_idxs,
                );
                out.push(last_hash.unwrap());
                for qv in alloc_rc {
                    out.push(qv.unwrap()); // better way to do this?
                }
                out.push(accepting.unwrap());
            }
            GlueOpts::PolyNL((dq, _dv)) => {
                let doc_l = dq.len();

                let mut alloc_doc_rc = vec![None; doc_l + 1];
                let mut alloc_doc_prev_rc = vec![None; doc_l + 1];
                let mut alloc_doc_gs = vec![vec![None; 3]; doc_l];

                let prev_dq = z[1..(doc_l + 1)].to_vec(); //.clone();
                let prev_dv = z[1 + doc_l].clone();

                for (i, var) in self.r1cs.vars.iter().copied().enumerate() {
                    let (name_f, s) = self.generate_variable_info(var);

                    let val_f = || {
                        Ok({
                            let i_val = &self.values.as_ref().expect("missing values")[i];
                            let ff_val = int_to_ff(i_val.as_pf().into());
                            //debug!("value : {var:?} -> {ff_val:?} ({i_val})");
                            ff_val
                        })
                    };

                    //println!("Var (name?) {:#?}", self.r1cs.names[&var]);

                    let mut matched = self
                        .input_variable_parsing(
                            &mut vars,
                            &s,
                            var,
                            state_0.clone(),
                            //   char_0.clone(),
                        )
                        .unwrap();
                    if !matched {
                        matched = self
                            .input_variable_qv_parsing(
                                &mut vars,
                                &s,
                                var,
                                "nldoc",
                                doc_l,
                                &prev_dq,
                                &prev_dv,
                                &mut alloc_doc_prev_rc,
                            )
                            .unwrap();
                    }
                    if !matched {
                        let alloc_v = AllocatedNum::alloc(cs.namespace(|| name_f), val_f)?;
                        vars.insert(var, alloc_v.get_variable());
                        matched = self
                            .intm_fs_parsing(
                                &alloc_v,
                                //   &mut vars,
                                &s,
                                //   var,
                                true,
                                &mut alloc_doc_qv,
                                &mut alloc_doc_claim_r,
                                &mut alloc_doc_gs,
                                //   &prev_dq,
                                //   &prev_dv,
                            )
                            .unwrap();

                        // todo get rn of _ in nl_doc
                        if !matched {
                            matched = self
                                .nl_eval_parsing(
                                    &alloc_v,
                                    &s,
                                    doc_l,
                                    &mut alloc_doc_rc,
                                    "nldoc",
                                    //&mut alloc_doc_prev_rc,
                                )
                                .unwrap();
                            if !matched {
                                self.default_parsing(&s, &alloc_v, &mut last_state, &mut accepting)
                                    .unwrap();
                            }
                        }
                    }
                }
                self.nl_eval_fiatshamir(
                    cs,
                    "doc",
                    //       &mut doc_sponge,
                    //        &mut fs_doc_ns,
                    doc_l,
                    &alloc_doc_qv,
                    &alloc_doc_prev_rc,
                    &alloc_doc_rc,
                    &alloc_doc_claim_r,
                    &alloc_doc_gs,
                    self.commit_blind,
                )?;

                out.push(last_state.unwrap());
                for qv in alloc_doc_rc {
                    out.push(qv.unwrap()); // better way to do this?
                }
                out.push(accepting.unwrap());
            }
            GlueOpts::NlNl((q, _v, dq, _dv)) => {
                let sc_l = q.len();
                let doc_l = dq.len();

                let mut alloc_rc = vec![None; sc_l + 1];
                let mut alloc_prev_rc = vec![None; sc_l + 1];
                let mut alloc_gs = vec![vec![None; 3]; sc_l];

                let mut alloc_doc_rc = vec![None; doc_l + 1];
                let mut alloc_doc_prev_rc = vec![None; doc_l + 1];
                let mut alloc_doc_gs = vec![vec![None; 3]; doc_l];

                let prev_q = z[1..(1 + sc_l)].to_vec(); //.clone();
                let prev_v = z[1 + sc_l].clone();
                let prev_dq = z[(sc_l + 2)..(sc_l + doc_l + 2)].to_vec(); //.clone();
                let prev_dv = z[sc_l + doc_l + 2].clone();

                for (i, var) in self.r1cs.vars.iter().copied().enumerate() {
                    let (name_f, s) = self.generate_variable_info(var);

                    let val_f = || {
                        Ok({
                            let i_val = &self.values.as_ref().expect("missing values")[i];
                            let ff_val = int_to_ff(i_val.as_pf().into());
                            //debug!("value : {var:?} -> {ff_val:?} ({i_val})");
                            ff_val
                        })
                    };
                    // println!("Var (name?) {:#?}", self.r1cs.names[&var]);
                    let mut matched = self
                        .input_variable_parsing(
                            &mut vars,
                            &s,
                            var,
                            state_0.clone(),
                            //   char_0.clone(),
                        )
                        .unwrap();
                    if !matched {
                        matched = self
                            .input_variable_qv_parsing(
                                &mut vars,
                                &s,
                                var,
                                "nl",
                                sc_l,
                                &prev_q,
                                &prev_v,
                                &mut alloc_prev_rc,
                            )
                            .unwrap();
                    }
                    if !matched {
                        matched = self
                            .input_variable_qv_parsing(
                                &mut vars,
                                &s,
                                var,
                                "nldoc",
                                doc_l,
                                &prev_dq,
                                &prev_dv,
                                &mut alloc_doc_prev_rc,
                            )
                            .unwrap();
                    }
                    if !matched {
                        let alloc_v = AllocatedNum::alloc(cs.namespace(|| name_f), val_f)?;
                        vars.insert(var, alloc_v.get_variable());
                        matched = self
                            .intm_fs_parsing(
                                &alloc_v,
                                //   &mut vars,
                                &s,
                                //   var,
                                false,
                                &mut alloc_qv,
                                &mut alloc_claim_r,
                                &mut alloc_gs,
                                //   &prev_q,
                                //   &prev_v,
                            )
                            .unwrap();

                        if !matched {
                            matched = self
                                .intm_fs_parsing(
                                    &alloc_v,
                                    //     &mut vars,
                                    &s,
                                    //    var,
                                    true,
                                    &mut alloc_doc_qv,
                                    &mut alloc_doc_claim_r,
                                    &mut alloc_doc_gs,
                                    //  &prev_dq,
                                    //&prev_dv,
                                )
                                .unwrap();
                            if !matched {
                                matched = self
                                    .nl_eval_parsing(
                                        &alloc_v,
                                        &s,
                                        sc_l,
                                        &mut alloc_rc,
                                        "nl",
                                        //   &mut alloc_prev_rc,
                                    )
                                    .unwrap();
                                if !matched {
                                    matched = self
                                        .nl_eval_parsing(
                                            &alloc_v,
                                            &s,
                                            doc_l,
                                            &mut alloc_doc_rc,
                                            "nldoc",
                                            //&mut alloc_doc_prev_rc,
                                        )
                                        .unwrap();
                                    if !matched {
                                        self.default_parsing(
                                            &s,
                                            &alloc_v,
                                            &mut last_state,
                                            &mut accepting,
                                        )
                                        .unwrap();
                                    }
                                }
                            }
                        }
                    }
                }

                self.nl_eval_fiatshamir(
                    cs,
                    "eval",
                    //    &mut sponge,
                    //    &mut fs_eval_ns,
                    sc_l,
                    &alloc_qv,
                    &alloc_prev_rc,
                    &alloc_rc,
                    &alloc_claim_r,
                    &alloc_gs,
                    self.commit_blind,
                )?;
                self.nl_eval_fiatshamir(
                    cs,
                    "doc",
                    //    &mut doc_sponge,
                    //    &mut fs_doc_ns,
                    doc_l,
                    &alloc_doc_qv,
                    &alloc_doc_prev_rc,
                    &alloc_doc_rc,
                    &alloc_doc_claim_r,
                    &alloc_doc_gs,
                    self.commit_blind,
                )?;

                out.push(last_state.unwrap());

                for qv in alloc_rc {
                    out.push(qv.unwrap()); // better way to do this?
                }
                for qv in alloc_doc_rc {
                    out.push(qv.unwrap()); // better way to do this?
                }
                out.push(accepting.unwrap());
            }
        }

        for (i, (a, b, c)) in self.r1cs.constraints.iter().enumerate() {
            cs.enforce(
                || format!("con{}", i),
                |z| lc_to_bellman::<F, CS>(&vars, a, z),
                |z| lc_to_bellman::<F, CS>(&vars, b, z),
                |z| lc_to_bellman::<F, CS>(&vars, c, z),
            );
        }

        /*println!(
            "done with synth: {} vars {} cs",
            vars.len(),
            self.r1cs.constraints.len()
        );*/

        Ok(out)
    }
}
