#![allow(missing_docs)]
type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
type EE = nova_snark::provider::ipa_pc::EvaluationEngine<G1>;

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
    CompressedSNARK, PublicParams, RecursiveSNARK, StepCounterType, FINAL_EXTERNAL_COUNTER,
    spartan::direct::*,
};
use rug::integer::{IsPrime, Order};
use rug::Integer;
use std::{collections::HashMap, default};
use crate::backend::nova;
use core::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct NaiveCircuit<F: PrimeField> {
    r1cs: R1csFinal, // TODO later ref
    values: Option<Vec<Value>>,
    _p: PhantomData<F>,
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
    ) -> Self {
        NaiveCircuit {
            r1cs: r1cs, //&prover_data.r1cs, // def get rid of this crap
            values: values,
            _p: Default::default(),
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
        }

        for (i, (a, b, c)) in self.r1cs.constraints.iter().enumerate() {
            cs.enforce(
                || format!("con{}", i),
                |z| nova::lc_to_bellman::<F, CS>(&vars, a, z),
                |z| nova::lc_to_bellman::<F, CS>(&vars, b, z),
                |z| nova::lc_to_bellman::<F, CS>(&vars, c, z),
            );
        }
        Ok(z.to_vec())

    }
}

pub fn naive_spartan_snark(r1cs: R1csFinal, wits: Vec<Value>) {
    let circuit = NaiveCircuit::new(r1cs, Some(wits));

    // produce keys
    let (pk, vk) =
      SpartanSNARK::<G1, EE, NaiveCircuit<<G1 as Group>::Scalar>>::setup(circuit.clone()).unwrap();

    // setup inputs
    let input = vec![<G1 as Group>::Scalar::one()];

    // produce a SNARK
    let res = SpartanSNARK::prove(&pk, circuit.clone(), &input);
    assert!(res.is_ok());

    let output = circuit.output(&input);

    let snark = res.unwrap();

    // verify the SNARK
    let io = input
      .into_iter()
      .chain(output.clone().into_iter())
      .collect::<Vec<_>>();
    let res = snark.verify(&vk, &io);
    assert!(res.is_ok());

    // sanity: check the claimed output with a direct computation of the same
    assert_eq!(output, vec![<G1 as Group>::Scalar::one()]);
  }