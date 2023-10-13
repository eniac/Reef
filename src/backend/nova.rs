#![allow(missing_docs)]
type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
use crate::backend::merkle_tree::MerkleWit;
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
pub fn lc_to_bellman<F: PrimeField, CS: ConstraintSystem<F>>(
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
    Split((Vec<F>, F, Vec<F>, F, F, Vec<F>)), // q, v, doc q, doc v, stack ptr, stack
    Hybrid((Vec<F>, F, F, Vec<F>)),           // hybrid q, hybrid v, stack ptr, stack
    Merkle((Vec<F>, F, F, Vec<F>)),           // q, v, stack ptr, stack
}

#[derive(Clone, Debug)]
pub struct NFAStepCircuit<F: PrimeField> {
    r1cs: R1csFinal, // TODO later ref
    values: Option<Vec<Value>>,
    pub pc: PoseidonConstants<F, typenum::U4>,
    states: Vec<F>,
    cursors: Vec<F>,
    glue: Vec<GlueOpts<F>>,
    batch_size: usize,
    max_branches: usize,
    pub commit_blind: F,
    pub claim_blind: F,
    merkle_commit: F,
    merkle_tree_wits: Option<Vec<Vec<MerkleWit<F>>>>,
}

// note that this will generate a single round, and no witnesses, unlike nova example code
// witness and loops will happen at higher level bc its my code and i can do what i want
impl<F: PrimeField> NFAStepCircuit<F> {
    pub fn new(
        r1cs: R1csFinal,
        values: Option<Vec<Value>>,
        pc: PoseidonConstants<F, typenum::U4>,
        states: Vec<F>,
        cursors: Vec<F>,
        glue: Vec<GlueOpts<F>>,
        batch_size: usize,
        max_branches: usize,
        commit_blind: F,
        claim_blind: F,
        merkle_commit: F,
        merkle_tree_wits: Option<Vec<Vec<MerkleWit<F>>>>,
    ) -> Self {
        assert_eq!(states.len(), 2);
        assert_eq!(cursors.len(), 2);
        assert_eq!(glue.len(), 2);

        // todo blind, first checking here
        match (&glue[0], &glue[1]) {
            (GlueOpts::Split(_), GlueOpts::Split(_)) => {}
            (GlueOpts::Hybrid(_), GlueOpts::Hybrid(_)) => {}
            (GlueOpts::Merkle(_), GlueOpts::Merkle(_)) => {
                assert!(merkle_tree_wits.is_some());
            }
            (_, _) => {
                panic!("glue I/O does not match");
            }
        }

        // println!("wits {:#?}", values);

        NFAStepCircuit {
            r1cs,
            values,
            pc,
            states,
            cursors,
            glue,
            batch_size,
            max_branches,
            commit_blind,
            claim_blind,
            merkle_commit,
            merkle_tree_wits,
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
        num_lookups: usize,
    ) -> Result<bool, SynthesisError> {
        if s.starts_with(&format!("nl_prev_running_claim")) {
            // not for doc v or hybrid
            vars.insert(var, prev_v.get_variable());

            alloc_prev_rc[sc_l] = Some(prev_v.clone());
            return Ok(true);
        } else if s.starts_with(&format!("{}_eq_{}_q", tag, num_lookups)) {
            //self.batch_size)) {
            // q
            let s_sub: Vec<&str> = s.split("_").collect();
            let q: usize = s_sub[4].parse().unwrap();

            vars.insert(var, prev_q[q].get_variable());
            alloc_prev_rc[q] = Some(prev_q[q].clone());

            return Ok(true);
        }

        return Ok(false);
    }

    fn input_stack_parsing(
        &self,
        vars: &mut HashMap<Var, Variable>,
        s: &String,
        var: Var,
        stack_in: &Vec<AllocatedNum<F>>,
        stack_ptr_0: &AllocatedNum<F>,
        cursor_0: &AllocatedNum<F>,
        max_stack: usize,
    ) -> Result<bool, SynthesisError> {
        if s.starts_with(&format!("stack_ptr_{}_{}", 0, max_stack - 1)) {
            vars.insert(var, stack_ptr_0.get_variable());

            return Ok(true);
        } else if s.starts_with(&format!("stack_{}_", 0)) {
            let s_sub: Vec<&str> = s.split("_").collect();
            let j: usize = s_sub[2].parse().unwrap();

            vars.insert(var, stack_in[j].get_variable());

            return Ok(true);
        } else if s.starts_with(&format!("cursor_in")) {
            vars.insert(var, cursor_0.get_variable());

            return Ok(true);
        }
        return Ok(false);
    }

    fn stack_parsing(
        &self,
        s: &String,
        alloc_v: &AllocatedNum<F>,
        alloc_stack_ptr_popped: &mut Option<AllocatedNum<F>>,
        alloc_stack_out: &mut Vec<Option<AllocatedNum<F>>>,
        last_cursor: &mut Option<AllocatedNum<F>>,
    ) -> Result<bool, SynthesisError>
where {
        if s.starts_with(&format!("stack_ptr_popped")) {
            *alloc_stack_ptr_popped = Some(alloc_v.clone()); //.get_variable();
            return Ok(true);
        } else if s.starts_with(&format!("stack_{}_", self.max_branches)) {
            let s_sub: Vec<&str> = s.split("_").collect();
            let j: usize = s_sub[2].parse().unwrap();
            alloc_stack_out[j] = Some(alloc_v.clone());

            return Ok(true);
        } else if s.starts_with(&format!("cursor_{}", self.batch_size)) {
            //, self.batch_size)) {
            *last_cursor = Some(alloc_v.clone());
            return Ok(true);
        }
        Ok(false)
    }

    fn default_parsing(
        &self,
        s: &String,
        alloc_v: &AllocatedNum<F>,
        last_state: &mut Option<AllocatedNum<F>>,
    ) -> Result<(), SynthesisError>
where {
        if s.starts_with(&format!("state_{}", self.batch_size)) {
            *last_state = Some(alloc_v.clone()); //.get_variable();
        }
        Ok(())
    }

    fn merkle_parsing(
        &self,
        alloc_v: &AllocatedNum<F>,
        s: &String,
        alloc_cursors: &mut Vec<Option<AllocatedNum<F>>>,
        alloc_chars: &mut Vec<Option<AllocatedNum<F>>>,
    ) -> Result<bool, SynthesisError> {
        if s.starts_with("char_") {
            let v_j = Some(alloc_v.clone()); //.get_variable();

            let s_sub: Vec<&str> = s.split("_").collect();
            let j: usize = s_sub[1].parse().unwrap();

            if j < self.batch_size {
                alloc_chars[j] = v_j; // j+1 -> j
            }

            return Ok(true);
        } else if s.starts_with("merkle_lookup_") {
            let v_j = Some(alloc_v.clone()); //.get_variable();

            let s_sub: Vec<&str> = s.split("_").collect();
            let j: usize = s_sub[2].parse().unwrap();

            if j < self.batch_size {
                alloc_cursors[j] = v_j; // j+1 -> j
            }

            return Ok(true);
        }

        return Ok(false);
    }

    fn intm_fs_parsing(
        &self,
        alloc_v: &AllocatedNum<F>,
        s: &String,
        tag: &str,
        alloc_qs: &mut Vec<Option<AllocatedNum<F>>>,
        alloc_vs: &mut Vec<Option<AllocatedNum<F>>>,
        alloc_claim_r: &mut Option<AllocatedNum<F>>,
        alloc_gs: &mut Vec<Vec<Option<AllocatedNum<F>>>>,
    ) -> Result<bool, SynthesisError> {
        // intermediate (in circ) wits
        if s.starts_with(&format!("{}_combined_q", tag)) {
            let s_sub: Vec<&str> = s.split("_").collect();
            let j: usize = s_sub[3].parse().unwrap();
            alloc_qs[j] = Some(alloc_v.clone());

            return Ok(true);
        } else if (tag == "nl") && s.starts_with("v_") {
            let v_j = Some(alloc_v.clone()); //.get_variable();

            let s_sub: Vec<&str> = s.split("_").collect();
            let j: usize = s_sub[1].parse().unwrap();
            alloc_vs[j] = v_j; // TODO check

            return Ok(true);
        } else if (tag == "nldoc") && s.starts_with("char_") {
            let v_j = Some(alloc_v.clone()); //.get_variable();

            //let j = s.chars().nth(5).unwrap().to_digit(10).unwrap() as usize;
            let s_sub: Vec<&str> = s.split("_").collect();
            let j: usize = s_sub[1].parse().unwrap();

            if j < self.batch_size {
                alloc_vs[j] = v_j; // j+1 -> j
            } // don't add the last one

            return Ok(true);
        } else if (tag == "nlhybrid") && s.starts_with("v_") {
            let v_j = Some(alloc_v.clone()); //.get_variable();

            let s_sub: Vec<&str> = s.split("_").collect();
            let j: usize = s_sub[1].parse().unwrap();
            alloc_vs[j] = v_j;

            return Ok(true);
        } else if (tag == "nlhybrid") && s.starts_with("char_") {
            let v_j = Some(alloc_v.clone()); //.get_variable();

            //let j = s.chars().nth(5).unwrap().to_digit(10).unwrap() as usize;
            let s_sub: Vec<&str> = s.split("_").collect();
            let j: usize = s_sub[1].parse().unwrap();

            if j < self.batch_size {
                // CORRECT?
                alloc_vs[self.batch_size + j] = v_j; // j+1 -> j
            } // don't add the last one

            return Ok(true);
        } else if s.starts_with(&format!("{}_claim_r", tag)) {
            *alloc_claim_r = Some(alloc_v.clone());
        } else if s.starts_with(&format!("{}_sc_g", tag)) {
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

    fn eval_merkle<CS>(
        &self,
        cs: &mut CS,
        alloc_cursors: &Vec<Option<AllocatedNum<F>>>, // already ordered
        alloc_chars: &Vec<Option<AllocatedNum<F>>>,   // already ordered
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        // self.height, self.root
        let alloc_root = AllocatedNum::alloc(cs.namespace(|| "root"), || Ok(self.merkle_commit))?;
        let tree_wits = self.merkle_tree_wits.clone().unwrap();

        for i in 0..alloc_cursors.len() {
            // num lookups

            // leafs
            let w0 = AllocatedNum::alloc(
                cs.namespace(|| format!("filler witness idx batch {}", i)),
                || Ok(tree_wits[i][0].opposite_idx.unwrap()),
            )?;
            let w1 = AllocatedNum::alloc(
                cs.namespace(|| format!("filler witness val batch {}", i)),
                || Ok(tree_wits[i][0].opposite),
            )?;

            let lr_var = if tree_wits[i][0].l_or_r {
                F::one()
            } else {
                F::zero()
            };
            let lr =
                AllocatedNum::alloc(cs.namespace(|| format!("l or r leaf batch {}", i)), || {
                    Ok(lr_var)
                })?;

            let mut query = vec![];
            let e0 = select(
                cs,
                lr.clone(),
                alloc_cursors[i].clone().unwrap().clone(),
                w0.clone(),
                &format!("leaf 0 batch {}", i),
            )?;
            query.push(Elt::Allocated(e0));

            let e1 = select(
                cs,
                lr.clone(),
                alloc_chars[i].clone().unwrap().clone(),
                w1.clone(),
                &format!("leaf 1 batch {}", i),
            )?;
            query.push(Elt::Allocated(e1));

            let e2 = select(
                cs,
                lr.clone(),
                w0,
                alloc_cursors[i].clone().unwrap(),
                &format!("leaf 2 batch {}", i),
            )?;
            query.push(Elt::Allocated(e2));

            let e3 = select(
                cs,
                lr,
                w1,
                alloc_chars[i].clone().unwrap(),
                &format!("leaf 3 batch {}", i),
            )?;
            query.push(Elt::Allocated(e3));

            let mut hash = self.merkle_circuit(cs, &query, &format!("leaf hash batch {}", i))?;

            // non leaf
            for h in 1..tree_wits[i].len() {
                let w = AllocatedNum::alloc(
                    cs.namespace(|| format!("filler witness batch {} lvl {}", i, h)),
                    || Ok(tree_wits[i][h].opposite),
                )?;

                let lr_var = if tree_wits[i][h].l_or_r {
                    F::one()
                } else {
                    F::zero()
                };
                let lr = AllocatedNum::alloc(
                    cs.namespace(|| format!("l or r batch {} lvl {}", i, h)),
                    || Ok(lr_var),
                )?;

                let mut query = vec![];

                let e0 = select(
                    cs,
                    lr.clone(),
                    hash.clone(),
                    w.clone(),
                    &format!("left batch {} lvl {}", i, h),
                )?;
                query.push(Elt::Allocated(e0));
                let e1 = select(cs, lr, w, hash, &format!("right batch {} lvl {}", i, h))?;
                query.push(Elt::Allocated(e1));

                hash = self.merkle_circuit(cs, &query, &format!("hash batch {} lvl {}", i, h))?;
            }

            //sanity
            if hash.get_value().is_some() {
                assert_eq!(hash.get_value().unwrap(), self.merkle_commit);
            }

            cs.enforce(
                || format!("eq merkle lookup {}", i),
                |z| z + hash.get_variable(),
                |z| z + CS::one(),
                |z| z + alloc_root.get_variable(),
            );
        }
        Ok(())
    }

    fn merkle_circuit<CS>(
        &self,
        cs: &mut CS,
        query: &[Elt<F>],
        tag: &str,
    ) -> Result<AllocatedNum<F>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let inputs = query.len() as u32;
        assert!(inputs == 2 || inputs == 4);

        let mut sponge = SpongeCircuit::new_with_constants(&self.pc, Mode::Simplex);
        let mut sponge_ns = cs.namespace(|| format!("{} sponge", tag));

        let pattern = vec![SpongeOp::Absorb(inputs), SpongeOp::Squeeze(1)];

        sponge.start(IOPattern(pattern), None, &mut sponge_ns);

        let new_pos = {
            SpongeAPI::absorb(&mut sponge, inputs, query, &mut sponge_ns);

            let output = SpongeAPI::squeeze(&mut sponge, 1, &mut sponge_ns);

            Elt::ensure_allocated(
                &output[0],
                &mut sponge_ns.namespace(|| format!("ensure allocated {}", tag)), // name must be the same
                // (??)
                true,
            )?
        };

        sponge.finish(&mut sponge_ns).unwrap();

        Ok(new_pos)
    }

    fn fiatshamir_circuit<'b, CS>(
        &self,
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
        tag: &str,
        sc_l: usize,
        num_cqs: usize,
        alloc_qs: &Vec<Option<AllocatedNum<F>>>,
        alloc_vs: &Vec<Option<AllocatedNum<F>>>,
        alloc_prev_rc: &Vec<Option<AllocatedNum<F>>>,
        alloc_rc: &Vec<Option<AllocatedNum<F>>>,
        alloc_claim_r: &Option<AllocatedNum<F>>,
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
            "nl" => {
                vec![
                    SpongeOp::Absorb((self.batch_size + sc_l + 1 + num_cqs) as u32), // vs,
                    // combined_q,
                    // running q,v
                    SpongeOp::Squeeze(1),
                ]
            }
            "nldoc" => {
                vec![
                    SpongeOp::Absorb((self.batch_size + sc_l + 2 + num_cqs) as u32), // vs,
                    SpongeOp::Squeeze(1),
                ]
            }
            "nlhybrid" => {
                vec![
                    SpongeOp::Absorb((self.batch_size * 2 + sc_l + 2 + num_cqs) as u32), // vs,
                    SpongeOp::Squeeze(1),
                ]
            }
            _ => panic!("weird tag"),
        };
        for _i in 0..sc_l {
            // sum check rounds
            pattern.append(&mut vec![SpongeOp::Absorb(3), SpongeOp::Squeeze(1)]);
        }

        sponge.start(IOPattern(pattern), None, &mut sponge_ns);

        // (combined_q, vs, running_q, running_v)
        let mut elts = vec![];
        //println!("FIAT SHAMIR ELTS {}", tag);

        // if DOC
        if matches!(tag, "nldoc") || matches!(tag, "nlhybrid") {
            let e = AllocatedNum::alloc(sponge_ns.namespace(|| "doc commit hash start"), || {
                Ok(vesta_hash)
            })?;

            //println!("e: {:#?}", e.clone().get_value());
            elts.push(Elt::Allocated(e));
        }
        for e in alloc_qs {
            elts.push(Elt::Allocated(e.clone().unwrap()));
            //println!("e: {:#?}", e.clone().unwrap().get_value());
        }
        for e in alloc_vs {
            elts.push(Elt::Allocated(e.clone().unwrap()));
            //println!("e: {:#?}", e.clone().unwrap().get_value());
        }
        for e in alloc_prev_rc {
            elts.push(Elt::Allocated(e.clone().unwrap()));
            //println!("e: {:#?}", e.clone().unwrap().get_value());
        }

        self.fiatshamir_circuit(
            &elts,
            &mut sponge,
            &mut sponge_ns,
            alloc_claim_r.clone().unwrap(),
            "claim_r",
        )?;

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
        alloc_prev_rc: &mut Vec<Option<AllocatedNum<F>>>,
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

            return Ok(true);
        } else if s.starts_with(&format!("nldoc_prev_running_claim")) && tag.starts_with("nldoc")
            || s.starts_with(&format!("nlhybrid_prev_running_claim")) && tag.starts_with("nlhybrid")
        {
            alloc_prev_rc[sc_l] = Some(alloc_v.clone());
        }
        return Ok(false);
    }

    fn hiding_running_claim<CS>(
        &self,
        cs: &mut CS,
        v: &AllocatedNum<F>,
    ) -> Result<AllocatedNum<F>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let alloc_s = AllocatedNum::alloc(cs.namespace(|| "s_rc"), || Ok(self.claim_blind))?;

        //poseidon(v,s) == d
        let d_calc = {
            let acc = &mut cs.namespace(|| "d hash circuit");
            let mut sponge = SpongeCircuit::new_with_constants(&self.pc, Mode::Simplex);

            sponge.start(
                IOPattern(vec![SpongeOp::Absorb(2), SpongeOp::Squeeze(1)]),
                None,
                acc,
            );

            SpongeAPI::absorb(
                &mut sponge,
                2,
                &[Elt::Allocated(v.clone()), Elt::Allocated(alloc_s)],
                acc,
            );

            let output = SpongeAPI::squeeze(&mut sponge, 1, acc);
            sponge.finish(acc).unwrap();
            let out =
                Elt::ensure_allocated(&output[0], &mut acc.namespace(|| "ensure allocated"), true)?;
            out
        };

        Ok(d_calc)
    }
}

impl<F> StepCircuit<F> for NFAStepCircuit<F>
where
    F: PrimeField,
{
    fn arity(&self) -> usize {
        // [state, optional<q,v for eval claim>, optional<q,"v"(hash), for doc claim>,
        // optional<q, "v"(hash) for hybrid claim>, stack_ptr, <stack>]

        let mut arity = 2;
        match &self.glue[0] {
            GlueOpts::Split((q, _, dq, _, _, stack)) => {
                arity += q.len() + 1 + dq.len() + 1;
                arity += stack.len() + 1;
            }
            GlueOpts::Hybrid((hq, _, _, stack)) => {
                arity += hq.len() + 1;
                arity += stack.len() + 1;
            }
            GlueOpts::Merkle((q, _, _, stack)) => {
                arity += q.len() + 1;
                arity += stack.len() + 1;
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
            GlueOpts::Split((q, v, dq, dv, sp, stack)) => {
                for qi in q.clone() {
                    assert_eq!(z[i], qi);
                    i += 1;
                }
                assert_eq!(z[i], *v);
                i += 1;
                for qi in dq.clone() {
                    assert_eq!(z[i], qi);
                    i += 1;
                }
                assert_eq!(z[i], *dv);
                i += 1;

                assert_eq!(z[i], *sp);
                i += 1;
                for si in stack.clone() {
                    assert_eq!(z[i], si);
                    i += 1;
                }
            }
            GlueOpts::Hybrid((hq, hv, sp, stack)) => {
                for qi in hq.clone() {
                    assert_eq!(z[i], qi);
                    i += 1;
                }
                assert_eq!(z[i], *hv);
                i += 1;
                assert_eq!(z[i], *sp);
                i += 1;
                for si in stack.clone() {
                    assert_eq!(z[i], si);
                    i += 1;
                }
            }
            GlueOpts::Merkle((q, v, sp, stack)) => {
                for qi in q.clone() {
                    assert_eq!(z[i], qi);
                    i += 1;
                }
                assert_eq!(z[i], *v);
                i += 1;
                assert_eq!(z[i], *sp);
                i += 1;
                for si in stack.clone() {
                    assert_eq!(z[i], si);
                    i += 1;
                }
            }
        }
        assert_eq!(z[i], self.cursors[0]);

        let mut out = vec![
            self.states[1], // "next state"
        ];
        match &self.glue[1] {
            GlueOpts::Split((q, v, dq, dv, sp, stack)) => {
                out.extend(q.clone());
                out.push(*v);
                out.extend(dq.clone());
                out.push(*dv);
                out.push(*sp);
                out.extend(stack.clone());
            }
            GlueOpts::Hybrid((hq, hv, sp, stack)) => {
                out.extend(hq.clone());
                out.push(*hv);
                out.push(*sp);
                out.extend(stack.clone());
            }
            GlueOpts::Merkle((q, v, sp, stack)) => {
                out.extend(q.clone());
                out.push(*v);
                out.push(*sp);
                out.extend(stack.clone());
            }
        }
        out.push(self.cursors[1]);
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
        let mut last_cursor = None;
        let mut out = vec![];

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
        let glue = &self.glue[0];

        match glue {
            GlueOpts::Split((q, _, dq, _, _, stack)) => {
                let sc_l = q.len();
                let doc_l = dq.len();
                let stack_len = stack.len();

                let mut alloc_claim_r = None;
                let mut alloc_doc_claim_r = None;

                let mut alloc_rc = vec![None; sc_l + 1];
                let mut alloc_prev_rc = vec![None; sc_l + 1];
                let mut alloc_gs = vec![vec![None; 3]; sc_l];

                let mut alloc_doc_rc = vec![None; doc_l + 1];
                let mut alloc_doc_prev_rc = vec![None; doc_l + 1];
                let mut alloc_doc_gs = vec![vec![None; 3]; doc_l];

                let mut alloc_stack_ptr_popped = None;
                let mut alloc_stack_out = vec![None; stack_len];

                let prev_q = z[1..(1 + sc_l)].to_vec(); //.clone();
                let prev_v = z[1 + sc_l].clone();
                let prev_dq = z[(sc_l + 2)..(sc_l + doc_l + 2)].to_vec(); //.clone();
                let prev_dv = z[sc_l + doc_l + 2].clone();

                let stack_ptr_0 = z[sc_l + doc_l + 3].clone();
                let stack_in = z[(sc_l + doc_l + 4)..(sc_l + doc_l + 4 + stack_len)].to_vec();
                let cursor_0 = z[sc_l + doc_l + 4 + stack_len].clone();

                let num_cqs = ((self.batch_size * sc_l) as f64 / 254.0).ceil() as usize;
                let mut alloc_qs = vec![None; num_cqs];
                let mut alloc_vs = vec![None; self.batch_size];

                let num_doc_cqs = ((self.batch_size * doc_l) as f64 / 254.0).ceil() as usize;
                let mut alloc_doc_q = vec![None; num_doc_cqs];
                let mut alloc_doc_v = vec![None; self.batch_size];

                for (i, var) in self.r1cs.vars.iter().copied().enumerate() {
                    let (name_f, s) = self.generate_variable_info(var);
                    //println!("S {:#?}", s);

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
                                self.batch_size,
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
                                self.batch_size,
                            )
                            .unwrap();
                    }
                    if !matched {
                        matched = self
                            .input_stack_parsing(
                                &mut vars,
                                &s,
                                var,
                                &stack_in,
                                &stack_ptr_0,
                                &cursor_0,
                                stack_len,
                            )
                            .unwrap();
                    }

                    if !matched {
                        let alloc_v = AllocatedNum::alloc(cs.namespace(|| name_f), val_f)?;
                        vars.insert(var, alloc_v.get_variable());

                        matched = self
                            .stack_parsing(
                                &s,
                                &alloc_v,
                                &mut alloc_stack_ptr_popped,
                                &mut alloc_stack_out,
                                &mut last_cursor,
                            )
                            .unwrap();
                        if !matched {
                            matched = self
                                .intm_fs_parsing(
                                    &alloc_v,
                                    &s,
                                    "nl",
                                    &mut alloc_qs,
                                    &mut alloc_vs,
                                    &mut alloc_claim_r,
                                    &mut alloc_gs,
                                )
                                .unwrap();
                        }
                        if !matched {
                            matched = self
                                .intm_fs_parsing(
                                    &alloc_v,
                                    &s,
                                    "nldoc",
                                    &mut alloc_doc_q,
                                    &mut alloc_doc_v,
                                    &mut alloc_doc_claim_r,
                                    &mut alloc_doc_gs,
                                )
                                .unwrap();
                        }
                        if !matched {
                            matched = self
                                .nl_eval_parsing(
                                    &alloc_v,
                                    &s,
                                    sc_l,
                                    &mut alloc_rc,
                                    "nl",
                                    &mut alloc_prev_rc,
                                )
                                .unwrap();
                        }
                        if !matched {
                            matched = self
                                .nl_eval_parsing(
                                    &alloc_v,
                                    &s,
                                    doc_l,
                                    &mut alloc_doc_rc,
                                    "nldoc",
                                    &mut alloc_doc_prev_rc,
                                )
                                .unwrap();
                        }
                        if !matched {
                            self.default_parsing(&s, &alloc_v, &mut last_state).unwrap();
                        }
                    }
                }

                self.nl_eval_fiatshamir(
                    cs,
                    "nl",
                    sc_l,
                    num_cqs,
                    &alloc_qs,
                    &alloc_vs,
                    &alloc_prev_rc,
                    &alloc_rc,
                    &alloc_claim_r,
                    &alloc_gs,
                    self.commit_blind,
                )?;
                self.nl_eval_fiatshamir(
                    cs,
                    "nldoc",
                    doc_l,
                    num_doc_cqs,
                    &alloc_doc_q,
                    &alloc_doc_v,
                    &alloc_doc_prev_rc,
                    &alloc_doc_rc,
                    &alloc_doc_claim_r,
                    &alloc_doc_gs,
                    self.commit_blind,
                )?;

                let hidden_rc =
                    self.hiding_running_claim(cs, &alloc_doc_rc[doc_l].clone().unwrap())?;
                alloc_doc_rc[doc_l] = Some(hidden_rc);

                out.push(last_state.unwrap());
                for qv in alloc_rc {
                    out.push(qv.unwrap());
                }
                for qv in alloc_doc_rc {
                    out.push(qv.unwrap());
                }
                out.push(alloc_stack_ptr_popped.unwrap());
                for si in alloc_stack_out {
                    out.push(si.unwrap());
                }
                out.push(last_cursor.unwrap());
            }
            GlueOpts::Hybrid((hq, _, _, stack)) => {
                let hyb_l = hq.len();
                let stack_len = stack.len();

                let mut alloc_claim_r = None;

                let mut alloc_rc = vec![None; hyb_l + 1];
                let mut alloc_prev_rc = vec![None; hyb_l + 1];
                let mut alloc_gs = vec![vec![None; 3]; hyb_l];

                let mut alloc_stack_ptr_popped = None;
                let mut alloc_stack_out = vec![None; stack_len];

                let prev_q = z[1..(1 + hyb_l)].to_vec(); //.clone();
                let prev_v = z[1 + hyb_l].clone();

                let stack_ptr_0 = z[hyb_l + 2].clone();
                let stack_in = z[(hyb_l + 3)..(hyb_l + 3 + stack_len)].to_vec();
                let cursor_0 = z[hyb_l + 3 + stack_len].clone();

                let num_cqs = ((self.batch_size * 2 * hyb_l) as f64 / 254.0).ceil() as usize;
                let mut alloc_qs = vec![None; num_cqs];
                let mut alloc_vs = vec![None; self.batch_size * 2];

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
                                "nlhybrid",
                                hyb_l,
                                &prev_q,
                                &prev_v,
                                &mut alloc_prev_rc,
                                self.batch_size * 2,
                            )
                            .unwrap();
                    }
                    if !matched {
                        matched = self
                            .input_stack_parsing(
                                &mut vars,
                                &s,
                                var,
                                &stack_in,
                                &stack_ptr_0,
                                &cursor_0,
                                stack_len,
                            )
                            .unwrap();
                    }

                    if !matched {
                        let alloc_v = AllocatedNum::alloc(cs.namespace(|| name_f), val_f)?;
                        vars.insert(var, alloc_v.get_variable());

                        matched = self
                            .stack_parsing(
                                &s,
                                &alloc_v,
                                &mut alloc_stack_ptr_popped,
                                &mut alloc_stack_out,
                                &mut last_cursor,
                            )
                            .unwrap();
                        if !matched {
                            matched = self
                                .intm_fs_parsing(
                                    &alloc_v,
                                    &s,
                                    "nlhybrid",
                                    &mut alloc_qs,
                                    &mut alloc_vs,
                                    &mut alloc_claim_r,
                                    &mut alloc_gs,
                                )
                                .unwrap();
                        }
                        if !matched {
                            matched = self
                                .nl_eval_parsing(
                                    &alloc_v,
                                    &s,
                                    hyb_l,
                                    &mut alloc_rc,
                                    "nlhybrid",
                                    &mut alloc_prev_rc,
                                )
                                .unwrap();
                        }
                        if !matched {
                            self.default_parsing(&s, &alloc_v, &mut last_state).unwrap();
                        }
                    }
                }

                self.nl_eval_fiatshamir(
                    cs,
                    "nlhybrid",
                    hyb_l,
                    num_cqs,
                    &alloc_qs,
                    &alloc_vs,
                    &alloc_prev_rc,
                    &alloc_rc,
                    &alloc_claim_r,
                    &alloc_gs,
                    self.commit_blind,
                )?;

                let hidden_rc = self.hiding_running_claim(cs, &alloc_rc[hyb_l].clone().unwrap())?;
                alloc_rc[hyb_l] = Some(hidden_rc);

                out.push(last_state.unwrap());
                for qv in alloc_rc {
                    out.push(qv.unwrap());
                }
                out.push(alloc_stack_ptr_popped.unwrap());
                for si in alloc_stack_out {
                    out.push(si.unwrap());
                }
                out.push(last_cursor.unwrap());
            }
            GlueOpts::Merkle((q, _, _, stack)) => {
                let sc_l = q.len();
                let stack_len = stack.len();

                let mut alloc_claim_r = None;

                let mut alloc_rc = vec![None; sc_l + 1];
                let mut alloc_prev_rc = vec![None; sc_l + 1];
                let mut alloc_gs = vec![vec![None; 3]; sc_l];

                let mut alloc_stack_ptr_popped = None;
                let mut alloc_stack_out = vec![None; stack_len];

                let prev_q = z[1..(1 + sc_l)].to_vec(); //.clone();
                let prev_v = z[1 + sc_l].clone();

                let stack_ptr_0 = z[sc_l + 2].clone();
                let stack_in = z[(sc_l + 3)..(sc_l + 3 + stack_len)].to_vec();
                let cursor_0 = z[sc_l + 3 + stack_len].clone();

                let num_cqs = ((self.batch_size * sc_l) as f64 / 254.0).ceil() as usize;
                let mut alloc_qs = vec![None; num_cqs];
                let mut alloc_vs = vec![None; self.batch_size];

                let mut alloc_cursors = vec![None; self.batch_size]; // TODO here
                let mut alloc_chars = vec![None; self.batch_size];

                for (i, var) in self.r1cs.vars.iter().copied().enumerate() {
                    let (name_f, s) = self.generate_variable_info(var);
                    //println!("S {:#?}", s);

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
                                self.batch_size,
                            )
                            .unwrap();
                    }
                    if !matched {
                        matched = self
                            .input_stack_parsing(
                                &mut vars,
                                &s,
                                var,
                                &stack_in,
                                &stack_ptr_0,
                                &cursor_0,
                                stack_len,
                            )
                            .unwrap();
                    }

                    if !matched {
                        let alloc_v = AllocatedNum::alloc(cs.namespace(|| name_f), val_f)?;
                        vars.insert(var, alloc_v.get_variable());

                        matched = self
                            .stack_parsing(
                                &s,
                                &alloc_v,
                                &mut alloc_stack_ptr_popped,
                                &mut alloc_stack_out,
                                &mut last_cursor,
                            )
                            .unwrap();
                        if !matched {
                            matched = self
                                .intm_fs_parsing(
                                    &alloc_v,
                                    &s,
                                    "nl",
                                    &mut alloc_qs,
                                    &mut alloc_vs,
                                    &mut alloc_claim_r,
                                    &mut alloc_gs,
                                )
                                .unwrap();
                        }
                        if !matched {
                            matched = self
                                .merkle_parsing(&alloc_v, &s, &mut alloc_cursors, &mut alloc_chars)
                                .unwrap();
                        }
                        if !matched {
                            matched = self
                                .nl_eval_parsing(
                                    &alloc_v,
                                    &s,
                                    sc_l,
                                    &mut alloc_rc,
                                    "nl",
                                    &mut alloc_prev_rc,
                                )
                                .unwrap();
                        }
                        if !matched {
                            self.default_parsing(&s, &alloc_v, &mut last_state).unwrap();
                        }
                    }
                }

                self.nl_eval_fiatshamir(
                    cs,
                    "nl",
                    sc_l,
                    num_cqs,
                    &alloc_qs,
                    &alloc_vs,
                    &alloc_prev_rc,
                    &alloc_rc,
                    &alloc_claim_r,
                    &alloc_gs,
                    self.commit_blind,
                )?;
                self.eval_merkle(cs, &alloc_cursors, &alloc_chars)?;

                out.push(last_state.unwrap());
                for qv in alloc_rc {
                    out.push(qv.unwrap());
                }
                out.push(alloc_stack_ptr_popped.unwrap());
                for si in alloc_stack_out {
                    out.push(si.unwrap());
                }
                out.push(last_cursor.unwrap());
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

// HELPER

// ret = if condition, a, else b
// condition already asserted to be 0 or 1
fn select<F, CS>(
    cs: &mut CS,
    cond: AllocatedNum<F>,
    a: AllocatedNum<F>,
    b: AllocatedNum<F>,
    tag: &String,
) -> Result<AllocatedNum<F>, SynthesisError>
where
    F: PrimeField,
    CS: ConstraintSystem<F>,
{
    let ret = AllocatedNum::alloc(cs.namespace(|| format!("ret {}", tag)), || {
        Ok(b.get_value().unwrap()
            + cond.get_value().unwrap() * (a.get_value().unwrap() - b.get_value().unwrap()))
    })?;

    // RET = B + COND * (A - B) <- ite
    cs.enforce(
        || format!("ite {}", tag),
        |lc| lc + a.get_variable() - b.get_variable(),
        |lc| lc + cond.get_variable(),
        |lc| lc + ret.get_variable() - b.get_variable(),
    );

    return Ok(ret);
}
