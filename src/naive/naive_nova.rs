#![allow(missing_docs)]
type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
type EE = nova_snark::provider::ipa_pc::EvaluationEngine<G1>;
type Fg1 = <G1 as Group>::Scalar;

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
    sponge::vanilla::{Mode, SpongeTrait,Sponge},
    Strength,
};
use nova_snark::{
    traits::{circuit::StepCircuit, Group, evaluation::EvaluationEngineTrait},
    CompressedSNARK, PublicParams, RecursiveSNARK, StepCounterType, FINAL_EXTERNAL_COUNTER,
    spartan::direct::*,
};
use pasta_curves::{Fq, Ep};
use rug::integer::{IsPrime, Order};
use rand::rngs::OsRng;
use rug::Integer;
use serde::__private::doc;
use std::{collections::HashMap, default};
use crate::backend::{nova, commitment::HashCommitmentStruct, r1cs_helper::new_wit};
use core::marker::PhantomData;
use fxhash::{FxHashMap,FxHasher};
use std::hash::BuildHasherDefault;
use circ::target::r1cs::wit_comp::StagedWitCompEvaluator;
use crate::naive::dfa::*; 
use memory_stats::memory_stats;

#[derive(Clone, Debug)]
pub struct NaiveCircuit<F: PrimeField> {
    r1cs: R1csFinal, // TODO later ref
    values: Option<Vec<Value>>,
    doc_length: usize,
    pc: PoseidonConstants<F, typenum::U4>,
    blind: F,
    commitment: F,
    is_match: F,
    //prover_data: &'a ProverData,
    //wits: Option<'a FxHashMap<String, Value>>,
}

// note that this will generate a single round, and no witnesses, unlike nova example code
// witness and loops will happen at higher level as to put as little as possible deep in circ
impl<F: PrimeField> NaiveCircuit<F> {
    pub fn new(
        //        prover_data: &'a ProverData,
        //        wits: Option<FxHashMap<String, Value>>, //Option<&'a FxHashMap<String, Value>>,
        r1cs: R1csFinal,
        values: Option<Vec<Value>>,
        doc_length: usize,
        pc: PoseidonConstants<F, typenum::U4>,
        blind: F,
        commitment: F,
        is_match: F,
    ) -> Self {
        NaiveCircuit {
            r1cs: r1cs, //&prover_data.r1cs, // def get rid of this crap
            values: values,
            doc_length: doc_length,
            pc: pc, 
            blind: blind,
            is_match: is_match,
            commitment:commitment
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
}

impl<F> StepCircuit<F> for NaiveCircuit<F>
where
    F: PrimeField,
{
    fn arity(&self) -> usize {
        1
      }
  
    fn get_counter_type(&self) -> StepCounterType {
        StepCounterType::Incremental
    }

    fn output(&self, z: &[F]) -> Vec<F> {
        vec![z[0]]
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
        println!("start synth");
        if let Some(usage) = memory_stats() {
    println!("Current physical memory usage: {}", usage.physical_mem);
    println!("Current virtual memory usage: {}", usage.virtual_mem);
} else {
    println!("Couldn't get the current memory usage :(");
}
        let mut vars = HashMap::with_capacity(self.r1cs.vars.len());

         // find chars
        let mut alloc_chars = vec![None;self.doc_length];
        
        for (i, var) in self.r1cs.vars.iter().copied().enumerate() {
            let (name_f, s) = self.generate_variable_info(var);
            let val_f = || {
                Ok({
                    let i_val = &self.values.as_ref().expect("missing values")[i];
                    let ff_val = nova::int_to_ff(i_val.as_pf().into());
                    //debug!("value : {var:?} -> {ff_val:?} ({i_val})");
                    ff_val
                })
            };

            let alloc_v = AllocatedNum::alloc(cs.namespace(|| name_f), val_f)?;
            vars.insert(var, alloc_v.get_variable());
            if s.starts_with("document.") { // doc.0_n587
                let char_j = Some(alloc_v.clone()); //.get_variable();
        
                let s_sub: Vec<&str> = s.split(['.','_']).collect(); // name = char_i
                let j: usize = s_sub[1].parse().unwrap();
        
                if j < self.doc_length {
                    alloc_chars[j] = char_j;
                }
        
            } 
        }

        for (i, (a, b, c)) in self.r1cs.constraints.iter().enumerate() {
            cs.enforce(
                || format!("con{}", i),
                |z| nova::lc_to_bellman::<F, CS>(&vars, a, z),
                |z| nova::lc_to_bellman::<F, CS>(&vars, b, z),
                |z| nova::lc_to_bellman::<F, CS>(&vars, c, z),
            );
        }

        // make hash
        let mut hash_ns = cs.namespace(|| format!("poseidon hash"));

        let alloc_blind = AllocatedNum::alloc(hash_ns.namespace(|| "blind"), || Ok(self.blind))?;

        let mut elts = vec![Elt::Allocated(alloc_blind)];
        
        for x in alloc_chars {
            elts.push(Elt::Allocated(x.clone().unwrap()));
        }
        
        let hashed = {
            let acc = &mut hash_ns;
            let mut sponge = SpongeCircuit::new_with_constants(&self.pc, Mode::Simplex);
            
            sponge.start(
                IOPattern(vec![SpongeOp::Absorb(self.doc_length as u32 + 1), SpongeOp::Squeeze(1)]),
                None,
                acc,
            );

            SpongeAPI::absorb(
                &mut sponge,
                self.doc_length as u32 + 1,
                &elts,
                acc
            );

            let output = SpongeAPI::squeeze(&mut sponge, 1, acc);

            sponge.finish(acc).unwrap();

            Elt::ensure_allocated(
                &output[0],
                &mut hash_ns.namespace(|| "ensure allocated"),
                true,
            )?
        };

        hash_ns.enforce(
            || format!("commit eq"),
            |lc| lc + hashed.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc+ z[0].get_variable(),
        );

        let out = vec![hashed];
        println!("end synth");
        if let Some(usage) = memory_stats() {
    println!("Current physical memory usage: {}", usage.physical_mem);
    println!("Current virtual memory usage: {}", usage.virtual_mem);
} else {
    println!("Couldn't get the current memory usage :(");
}
        Ok(out)

    }
}

pub fn gen_commitment(doc: Vec<u32>, pc: &PoseidonConstants<Fq, typenum::U4>)->HashCommitmentStruct<pasta_curves::Fq>{
    let mut hash: Vec<Fq>;

    let mut sponge = Sponge::new_with_constants(pc, Mode::Simplex);
    let acc = &mut ();

    sponge.start(
        IOPattern(vec![SpongeOp::Absorb(doc.len() as u32 + 1), SpongeOp::Squeeze(1)]),
        None,
        acc,
    );

    let blind = <G1 as Group>::Scalar::random(&mut OsRng);
     
    let mut doc_clone: Vec<Fq> = doc.into_iter().map(|x| <G1 as Group>::Scalar::from(x as u64)).collect();
    doc_clone.insert(0, blind);

    SpongeAPI::absorb(
        &mut sponge,
        doc_clone.len() as u32,
        &doc_clone,
        acc,
    );

    hash = SpongeAPI::squeeze(&mut sponge, 1, acc);
    sponge.finish(acc).unwrap();
    return HashCommitmentStruct{
        commit: hash[0],
        blind: blind
    }


} 

pub fn gen_wits<'a>(doc_vec: Vec<u32>, is_match: bool, doc_len: usize, solution: Vec<(u32,u32,u32)>, dfa: &DFA<'_>, n_char: usize, P:&'a ProverData)->Option<Vec<Value>> {
    let mut wits: HashMap<String, Value, BuildHasherDefault<FxHasher>> = FxHashMap::default();
    //Document
    for i in 0..doc_len {
        wits.insert(format!("document.{}",i), new_wit(doc_vec[i]));
    }

    //Prover Solution
    for i in 0..solution.len() {
        wits.insert(format!("prover_states.{}",i), new_wit(solution[i].0));
    }
    //Final state in solution
    wits.insert(format!("prover_states.{}",solution.len()), new_wit(solution[solution.len()-1].2));

    //Return Value
    wits.insert(format!("return"), new_wit(is_match as u32));

    P.check_all(&wits);

    let values: Option<Vec<_>> = Some(wits).map(|values| {
        let mut evaluator = StagedWitCompEvaluator::new(&P.precompute);
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

    values
}

pub fn naive_spartan_snark_setup(circuit: NaiveCircuit<Fq>)-> (SpartanProverKey<G1, EE>, SpartanVerifierKey<G1, EE>) {
    // // produce keys
    let (pk, vk) =
      SpartanSNARK::<G1, EE, NaiveCircuit<<G1 as Group>::Scalar>>::setup(circuit.clone()).unwrap();

    (pk,vk)
  }
