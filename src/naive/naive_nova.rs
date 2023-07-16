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
use crate::backend::{nova, commitment::HashCommitmentStruct};
use core::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct NaiveCircuit<F: PrimeField> {
    r1cs: R1csFinal, // TODO later ref
    values: Option<Vec<Value>>,
    _p: PhantomData<F>,
    doc_length: usize,
    pc: PoseidonConstants<F, typenum::U4>,
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
    ) -> Self {
        NaiveCircuit {
            r1cs: r1cs, //&prover_data.r1cs, // def get rid of this crap
            values: values,
            _p: Default::default(),
            doc_length: doc_length,
            pc: pc
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

                let mut elts = vec![];
        
                for x in alloc_chars {
                    elts.push(Elt::Allocated(x.clone().unwrap()));
                }
        
                let hashed = {
                    let acc = &mut hash_ns;
                    let mut sponge = SpongeCircuit::new_with_constants(&self.pc, Mode::Simplex);
                    
                    sponge.start(
                        IOPattern(vec![SpongeOp::Absorb(self.doc_length as u32), SpongeOp::Squeeze(1)]),
                        None,
                        acc,
                    );
        
                    SpongeAPI::absorb(
                        &mut sponge,
                        self.doc_length as u32,
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

        let out = vec![hashed,z[0].clone()];
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
        doc_clone.len() as u32 + 1,
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

pub fn gen_circuit(r1cs: R1csFinal, wits: Option<Vec<Value>>, pc: PoseidonConstants<Fq, typenum::U4>) -> NaiveCircuit<Fq> {
    let circuit = NaiveCircuit::new(r1cs, wits,2,pc); 
    circuit
}

pub fn naive_spartan_snark_setup(circuit: NaiveCircuit<Fq>)-> (SpartanProverKey<G1, EE>, SpartanVerifierKey<G1, EE>) {
    // // produce keys
    let (pk, vk) =
      SpartanSNARK::<G1, EE, NaiveCircuit<<G1 as Group>::Scalar>>::setup(circuit.clone()).unwrap();

    (pk,vk)
    // // setup inputs
    // let input = vec![<G1 as Group>::Scalar::one()];

    // // produce a SNARK
    // let res = SpartanSNARK::prove(&pk, circuit.clone(), &input);
    // assert!(res.is_ok());

    // let output = circuit.output(&input);

    // let snark = res.unwrap();

    // // verify the SNARK
    // let io = input
    //   .into_iter()
    //   .chain(output.clone().into_iter())
    //   .collect::<Vec<_>>();
    // let res = snark.verify(&vk, &io);
    // assert!(res.is_ok());

    // // sanity: check the claimed output with a direct computation of the same
    // assert_eq!(output, vec![<G1 as Group>::Scalar::one()]);
  }