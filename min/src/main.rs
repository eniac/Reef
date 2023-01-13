#![allow(missing_docs)]
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::{fp::FpVar, FieldVar};
use ark_relations::ns;

use ark_r1cs_std::poly::domain::Radix2DomainVar;
use ark_r1cs_std::poly::evaluations::univariate::EvaluationsVar;
use ark_r1cs_std::R1CSVar;

use ark_ff::FftField;
use ark_pallas::Fr;
use ark_relations::r1cs::{ConstraintSystem, OptimizationGoal};

pub fn nth(d: &Radix2DomainVar<Fr>, n: u64) -> Fr {
    let mut cur = d.offset.value().unwrap();
    if n == 0 {
        cur
    } else {
        for _ in 0..n {
            cur *= d.gen;
        }
        cur
    }
}

pub fn get_domain(num_bits: u64) -> Radix2DomainVar<Fr> {

    // Generator 2^n
    let gen = Fr::get_root_of_unity(1 << num_bits).unwrap();
        let domain = Radix2DomainVar {
            gen,
            offset: FpVar::constant(Fr::multiplicative_generator()),
            dim: num_bits, // 2^4 = 16
        };

    return domain;
}


fn main() {

    // make eval poly
    let domain = get_domain(2); // 2 bits for 4 points
    let init = nth(&domain, 0);

    let mut pairs = vec![&(0, 'a', 0), &(1, 'a', 1), &(2, 'a', 2), &(3, 'a', 3)]; 
    pairs.sort_by(|(a, _, _), (b, _, _)| a.cmp(b));

    println!("PAIRS {:#?}", pairs);

    let evals = pairs
        .iter()
        .map(|(_, _, to)| FpVar::constant(nth(&domain, *to)))
        .collect::<Vec<_>>();

    println!("EVALS {:#?}", evals);

    let poly = EvaluationsVar::from_vec_and_domain(evals, domain.clone(), true);

    // make constraints
    let cs = ConstraintSystem::new_ref();
    let curr_state = FpVar::new_witness(ns!(cs, "state i"), || Ok(init)).unwrap();
   
    let next_state = poly.interpolate_and_evaluate(&curr_state);
 
    assert!(cs.is_satisfied().unwrap());

    println!("in state {:#?}", curr_state.value().unwrap());
    println!("out state {:#?}", next_state.unwrap().value());

}
