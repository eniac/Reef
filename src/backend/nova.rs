#![allow(missing_docs)]
type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
use super::*;
use ::bellperson::{
    gadgets::num::AllocatedNum, ConstraintSystem, LinearCombination, SynthesisError, Variable,
};
use circ::target::r1cs::wit_comp::StagedWitCompEvaluator;
use circ::{ir::term::Value, target::r1cs::*};
use ff::{Field, PrimeField};
use fxhash::FxHashMap;
use fxhash::FxHasher;
use generic_array::typenum;
use gmp_mpfr_sys::gmp::limb_t;
use neptune::{
    circuit2::Elt,
    poseidon::{Arity, HashMode, Poseidon, PoseidonConstants},
    sponge::api::{IOPattern, SpongeAPI, SpongeOp},
    sponge::circuit::SpongeCircuit,
    sponge::vanilla::{Mode, Sponge, SpongeTrait},
    Strength,
};
use nova_snark::{
    traits::{circuit::StepCircuit, Group},
    StepCounterType,
};
use rug::integer::{IsPrime, Order};
use rug::Integer;
use std::collections::HashMap;
use std::hash::BuildHasherDefault;

fn type_of<T>(_: &T) {
    println!("{}", std::any::type_name::<T>())
}
/*
fn string_lc(pd: &ProverData, lc: &Lc) -> String {
    let mut s = vec![];
    if !lc.is_zero() {
        s.push(format!("{:#?}", lc.constant.i()));
        for (idx, coef) in &lc.monomials {
            s.push(format!(
                "({:#?} * {:#?})",
                coef.i(),
                pd.r1cs.idxs_signals.get(&idx).unwrap()
            ));
        }
    }
    s.join(" + ")
}

pub fn print_r1cs(pd: &ProverData) {
    for (a, b, c) in pd.r1cs.constraints() {
        println!(
            "[ {:#?} * {:#?} = {:#?} ]",
            string_lc(pd, a),
            string_lc(pd, b),
            string_lc(pd, c)
        );
    }
}
*/

/// Convert a (rug) integer to a prime field element.
fn int_to_ff<F: PrimeField>(i: Integer) -> F {
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
pub struct NFAStepCircuit<'a, F: PrimeField> {
    r1cs: &'a R1csFinal, // TODO later ref
    values: Option<Vec<Value>>,
    //prover_data: &'a ProverData,
    //wits: Option<'a FxHashMap<String, Value>>,
    batch_size: usize,
    states: Vec<F>,
    chars: Vec<F>,
    hashes: Vec<F>,
    pc: PoseidonConstants<F, typenum::U2>,
    nlookup: bool,
}

// note that this will generate a single round, and no witnesses, unlike nova example code
// witness and loops will happen at higher level as to put as little as possible deep in circ
impl<'a, F: PrimeField> NFAStepCircuit<'a, F> {
    pub fn new(
        prover_data: &'a ProverData,
        wits: Option<FxHashMap<String, Value>>, //Option<&'a FxHashMap<String, Value>>,
        states: Vec<F>,
        chars: Vec<F>,
        hashes: Vec<F>,
        batch_size: usize,
        pcs: PoseidonConstants<F, typenum::U2>,
        nlookup: bool,
    ) -> Self {
        // todo check wits line up with the non det advice

        if wits.is_some() {
            assert_eq!(chars.len(), 2); // only need in/out for all of these
            assert_eq!(states.len(), 2);
            assert_eq!(hashes.len(), 2);
            //assert!(hashes.is_some() || nlookup); // no hashes -> nlookup
            // we only use nlookup commit w/nlookup
        }

        let values: Option<Vec<_>> = wits.map(|values| {
            let mut evaluator = StagedWitCompEvaluator::new(&prover_data.precompute);
            let mut ffs = Vec::new();
            ffs.extend(evaluator.eval_stage(values.clone()).into_iter().cloned());
            ffs.extend(
                evaluator
                    .eval_stage(Default::default())
                    .into_iter()
                    .cloned(),
            );
            ffs
        });

        NFAStepCircuit {
            r1cs: &prover_data.r1cs, // def get rid of this crap
            values: values,
            batch_size: batch_size,
            states: states,
            chars: chars,
            hashes: hashes,
            pc: pcs,
            nlookup: nlookup,
        }
    }
}

impl<'a, F> StepCircuit<F> for NFAStepCircuit<'a, F>
where
    F: PrimeField,
{
    fn arity(&self) -> usize {
        3
    }

    // z = [state, char, hash, round_num, bool_out]
    fn output(&self, z: &[F]) -> Vec<F> {
        // sanity check
        assert_eq!(z[0], self.states[0]); // "current state"
        assert_eq!(z[1], self.chars[0]);

        //let mut next_hash = F::from(0);
        //if self.hashes.is_some() {
        assert_eq!(z[2], self.hashes[0]);
        //    next_hash = self.hashes.as_ref().unwrap()[self.batch_size];
        //}

        vec![
            self.states[1], // "next state"
            self.chars[1],
            self.hashes[1], //next_hash,
        ]
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
        let char_0 = z[1].clone();
        let hash_0 = z[2].clone();

        //println!("current_state: {:#?}", current_state.get_value());
        //println!("current_char: {:#?}", current_char.get_value());
        //println!("prev_hash: {:#?}", prev_hash.get_value());

        // ouputs
        let mut last_state = None;
        //let mut next_hash = None;

        // for nova passing (new inputs from prover, not provided by circ prover, so to speak)
        let last_char = AllocatedNum::alloc(cs.namespace(|| "last_char"), || Ok(self.chars[1]))?;

        //println!("BATCH SIZE IN NOVA {:#?}", self.batch_size);
        // intms
        let mut char_vars = vec![None; self.batch_size];

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

        for (i, var) in self.r1cs.vars.iter().copied().enumerate() {
            assert!(
                !matches!(var.ty(), VarType::CWit),
                "Bellman doesn't support committed witnesses"
            );
            assert!(
                !matches!(var.ty(), VarType::RoundWit | VarType::Chall),
                "Bellman doesn't support rounds"
            );
            let public = matches!(var.ty(), VarType::Inst); // but we really dont care
            let name_f = || format!("{var:?}");

            let val_f = || {
                Ok({
                    let i_val = &self.values.as_ref().expect("missing values")[i];
                    let ff_val = int_to_ff(i_val.as_pf().into());
                    //debug!("value : {var:?} -> {ff_val:?} ({i_val})");
                    ff_val
                })
            };
            //println!("Var (name?) {:#?}", self.r1cs.names[&var]);
            let s = self.r1cs.names[&var].clone();
            /*let v = cs.alloc(name_f, val_f)?
                vars.insert(var, v);
            */

            if s.starts_with("char_0") {
                let alloc_v = char_0.clone(); //AllocatedNum::alloc(cs.namespace(name_f), val_f)?;
                                              //assert_eq!(ff_val, current_char.get_value().unwrap()); //current_char = Some(alloc_v); //.get_variable();
                vars.insert(var, alloc_v.get_variable());
                char_vars[0] = Some(alloc_v);
            } else if s.starts_with("state_0") {
                let alloc_v = state_0.clone(); //AllocatedNum::alloc(cs.namespace(name_f), val_f)?;
                                               //assert_eq!(val_f, current_state); //current_state = alloc_v.get_variable();
                vars.insert(var, alloc_v.get_variable());

            // outputs
            } else if s.starts_with(&format!("state_{}", self.batch_size)) {
                let alloc_v = AllocatedNum::alloc(cs.namespace(name_f), val_f)?;
                last_state = Some(alloc_v); //.get_variable();
                vars.insert(var, last_state.clone().unwrap().get_variable());

            // sumcheck hashes
            } else if s.starts_with("nl_claim_r") {
                //println!("NL CLAIM R hook");
                //let mut ns = cs.namespace(name_f);
                // original var
                let alloc_v = AllocatedNum::alloc(cs.namespace(name_f), val_f)?; //Ok(new_pos.get_value().unwrap()))?;
                                                                                 //let alloc_v = new_pos; // maybe equality constraint here instead?
                vars.insert(var, alloc_v.get_variable());

                // isn't hit if no claim var
                // add hash circuit
                let mut ns = cs.namespace(|| "sumcheck hash ns"); // maybe we can just
                                                                  // change this??
                let new_pos = {
                    let mut sponge = SpongeCircuit::new_with_constants(&self.pc, Mode::Simplex);
                    let acc = &mut ns;

                    sponge.start(
                        IOPattern(vec![SpongeOp::Absorb(1), SpongeOp::Squeeze(1)]),
                        None,
                        acc,
                    );

                    //let temp_input = AllocatedNum::alloc(acc, || Ok(F::from(5 as u64)))?; // TODO!!

                    //SpongeAPI::absorb(&mut sponge, 1, &[Elt::Allocated(temp_input)], acc);
                    SpongeAPI::absorb(
                        &mut sponge,
                        1,
                        &[Elt::num_from_fr::<CS>(F::from(5 as u64))], // this is some shit
                        acc,
                    );

                    let output = SpongeAPI::squeeze(&mut sponge, 1, acc);

                    sponge.finish(acc).unwrap();

                    Elt::ensure_allocated(
                        &output[0],
                        &mut ns.namespace(|| "ensure allocated"), // name must be the same
                        // (??)
                        true,
                    )?
                };

                //println!("sc hash {:#?}", new_pos);
                //let alloc_v = AllocatedNum::alloc(ns, || Ok(new_pos.get_value().unwrap()))?;

                //println!("new pos: {:#?}", new_pos.clone().get_value());
                //println!("alloc v: {:#?}", alloc_v.clone().get_value());

                ns.enforce(
                    || format!("eq con for claim_r"),
                    |z| z + alloc_v.get_variable(),
                    |z| z + CS::one(),
                    |z| z + new_pos.get_variable(),
                );
            } else if s.starts_with("nl_sc_r_") {
                // original var
                let alloc_v = AllocatedNum::alloc(cs.namespace(name_f), val_f)?; //Ok(new_pos.get_value().unwrap()))?;
                vars.insert(var, alloc_v.get_variable());

                // isn't hit if no sc round var
                let s_sub: Vec<&str> = s.split("_").collect();
                let r: u64 = s_sub[3].parse().unwrap();
                //let r = s.chars().nth(8).unwrap().to_digit(10).unwrap() as u64; // BS!
                let mut ns = cs.namespace(|| format!("sumcheck round ns {}", r));

                let new_pos = {
                    let mut sponge = SpongeCircuit::new_with_constants(&self.pc, Mode::Simplex);
                    let acc = &mut ns;

                    sponge.start(
                        IOPattern(vec![SpongeOp::Absorb(1), SpongeOp::Squeeze(1)]),
                        None,
                        acc,
                    );

                    //let temp_input = AllocatedNum::alloc(acc, || Ok(F::from(5 as u64)))?; // TODO!!

                    //SpongeAPI::absorb(&mut sponge, 1, &[Elt::Allocated(temp_input)], acc);
                    SpongeAPI::absorb(
                        &mut sponge,
                        1,
                        &[Elt::num_from_fr::<CS>(F::from(r))], // this is some shit
                        acc,
                    );

                    let output = SpongeAPI::squeeze(&mut sponge, 1, acc);

                    sponge.finish(acc).unwrap();

                    Elt::ensure_allocated(
                        &output[0],
                        &mut ns.namespace(|| "ensure allocated"), // name must be the same
                        // (??)
                        true,
                    )?
                };
                ns.enforce(
                    || format!("eq con for sc_r {}", r),
                    |z| z + alloc_v.get_variable(),
                    |z| z + CS::one(),
                    |z| z + new_pos.get_variable(),
                );
            } else if s.starts_with("nl_doc_claim_r") {
                //println!("NL CLAIM R hook");
                //let mut ns = cs.namespace(name_f);x
                // original var
                let alloc_v = AllocatedNum::alloc(cs.namespace(name_f), val_f)?; //Ok(new_pos.get_value().unwrap()))?;
                                                                                 //let alloc_v = new_pos; // maybe equality constraint here instead?
                vars.insert(var, alloc_v.get_variable());

                // isn't hit if no claim var
                // add hash circuit
                let mut ns = cs.namespace(|| "sumcheck hash ns"); // maybe we can just
                                                                  // change this??
                let new_pos = {
                    let mut sponge = SpongeCircuit::new_with_constants(&self.pc, Mode::Simplex);
                    let acc = &mut ns;

                    sponge.start(
                        IOPattern(vec![SpongeOp::Absorb(1), SpongeOp::Squeeze(1)]),
                        None,
                        acc,
                    );

                    //let temp_input = AllocatedNum::alloc(acc, || Ok(F::from(5 as u64)))?; // TODO!!

                    //SpongeAPI::absorb(&mut sponge, 1, &[Elt::Allocated(temp_input)], acc);
                    SpongeAPI::absorb(
                        &mut sponge,
                        1,
                        &[Elt::num_from_fr::<CS>(F::from(5 as u64))], // this is some shit
                        acc,
                    );

                    let output = SpongeAPI::squeeze(&mut sponge, 1, acc);

                    sponge.finish(acc).unwrap();

                    Elt::ensure_allocated(
                        &output[0],
                        &mut ns.namespace(|| "ensure allocated"), // name must be the same
                        // (??)
                        true,
                    )?
                };
                //println!("sc hash {:#?}", new_pos);
                //let alloc_v = AllocatedNum::alloc(ns, || Ok(new_pos.get_value().unwrap()))?;

                //println!("new pos: {:#?}", new_pos.clone().get_value());

                ns.enforce(
                    || format!("eq con for doc_claim_r"),
                    |z| z + alloc_v.get_variable(),
                    |z| z + CS::one(),
                    |z| z + new_pos.get_variable(),
                );
            } else if s.starts_with("nl_doc_sc_r_") {
                // original var
                let alloc_v = AllocatedNum::alloc(cs.namespace(name_f), val_f)?; //Ok(new_pos.get_value().unwrap()))?;
                vars.insert(var, alloc_v.get_variable());

                // isn't hit if no sc round var
                // add hash circuit
                //let r = s.chars().nth(8).unwrap().to_digit(10).unwrap() as u64; // BS!
                let s_sub: Vec<&str> = s.split("_").collect();
                let r: u64 = s_sub[4].parse().unwrap();
                let mut ns = cs.namespace(|| format!("doc sumcheck round ns {}", r));
                let new_pos = {
                    let mut sponge = SpongeCircuit::new_with_constants(&self.pc, Mode::Simplex);
                    let acc = &mut ns;

                    sponge.start(
                        IOPattern(vec![SpongeOp::Absorb(1), SpongeOp::Squeeze(1)]),
                        None,
                        acc,
                    );

                    //let temp_input = AllocatedNum::alloc(acc, || Ok(F::from(5 as u64)))?; // TODO!!

                    //SpongeAPI::absorb(&mut sponge, 1, &[Elt::Allocated(temp_input)], acc);
                    SpongeAPI::absorb(
                        &mut sponge,
                        1,
                        &[Elt::num_from_fr::<CS>(F::from(r))], // this is some shit
                        acc,
                    );

                    let output = SpongeAPI::squeeze(&mut sponge, 1, acc);

                    sponge.finish(acc).unwrap();

                    Elt::ensure_allocated(
                        &output[0],
                        &mut ns.namespace(|| "ensure allocated"), // name must be the same
                        // (??)
                        true,
                    )?
                };

                ns.enforce(
                    || format!("eq con for doc_sc_r {}", r),
                    |z| z + alloc_v.get_variable(),
                    |z| z + CS::one(),
                    |z| z + new_pos.get_variable(),
                );

            // intermediate (in circ) wits
            } else if s.starts_with("char_") {
                // for hash commits
                // hash commit wits (TODO if)
                let alloc_v = AllocatedNum::alloc(cs.namespace(name_f), val_f)?;
                let char_j = Some(alloc_v); //.get_variable();
                vars.insert(var, char_j.clone().unwrap().get_variable()); // messy TODO

                //let j = s.chars().nth(5).unwrap().to_digit(10).unwrap() as usize;
                let s_sub: Vec<&str> = s.split("_").collect();
                let j: usize = s_sub[1].parse().unwrap();

                if j < self.batch_size {
                    char_vars[j] = char_j;
                } // don't add the last one
            } else {
                let alloc_v = AllocatedNum::alloc(cs.namespace(name_f), val_f)?;
                let v = alloc_v.get_variable();
                //vars.insert(i, v);

                //let v = cs.alloc(name_f, val_f)?
                vars.insert(var, v);
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
        /*
                    //        let z = LinearCombination::zero();
                    println!(
                        "i= {:#?}, a= {:#?}, b= {:#?}, c= {:#?}",
                        i,
                        a,
                        //            lc_to_bellman::<F, CS>(&vars, a, z.clone()),
                        b,
                        //             lc_to_bellman::<F, CS>(&vars, b, z.clone()),
                        c,
                        //              lc_to_bellman::<F, CS>(&vars, c, z.clone()),
                    );
                }
        */
        // https://github.com/zkcrypto/bellman/blob/2759d930622a7f18b83a905c9f054d52a0bbe748/src/gadgets/num.rs,
        // line 31 ish

        // hash commit
        let mut next_hash = hash_0.clone(); // TODO get rid
                                            //if self.hashes.is_some() {
                                            // we want a hash commit, and not nlookup doc commit
                                            // circuit poseidon

        for i in 0..(self.batch_size) {
            let mut ns = cs.namespace(|| format!("poseidon hash ns batch {}", i));
            //println!("i {:#?}", i);
            next_hash = {
                let mut sponge = SpongeCircuit::new_with_constants(&self.pc, Mode::Simplex);
                let acc = &mut ns;

                sponge.start(
                    IOPattern(vec![SpongeOp::Absorb(2), SpongeOp::Squeeze(1)]),
                    None,
                    acc,
                );

                /*println!(
                    "Hashing {:#?} {:#?}",
                    next_hash.clone().get_value(),
                    char_vars[i].clone().unwrap().get_value()
                );*/
                SpongeAPI::absorb(
                    &mut sponge,
                    2,
                    &[
                        Elt::Allocated(next_hash.clone()),
                        Elt::Allocated(char_vars[i].clone().unwrap()),
                    ], // TODO is
                    // this
                    // "connected"? get rid clones
                    acc,
                );

                let output = SpongeAPI::squeeze(&mut sponge, 1, acc);

                sponge.finish(acc).unwrap();

                Elt::ensure_allocated(&output[0], &mut ns.namespace(|| "ensure allocated"), true)?
            };
        }

        // this line for TESTING ONLY; evil peice of code that could fuck things up
        /*let next_hash = AllocatedNum::alloc(cs.namespace(|| "next_hash"), || {
            Ok(self.hashes.as_ref().unwrap()[self.batch_size])
        })?;*/

        //println!("hash out: {:#?}", next_hash.clone().get_value());

        //assert_eq!(expected, out.get_value().unwrap()); //get_value().unwrap());

        println!(
            "done with synth: {} vars {} cs",
            vars.len(),
            self.r1cs.constraints.len()
        );

        Ok(vec![last_state.unwrap(), last_char, next_hash])
    }
}
