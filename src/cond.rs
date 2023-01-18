use ark_std::Zero;use ark_ff::FftField;
use ark_pallas::Fr;
use ark_r1cs_std::bits::ToBitsGadget;
use ark_r1cs_std::fields::{fp::FpVar, FieldVar};
use ark_r1cs_std::poly::{domain::Radix2DomainVar};
use ark_r1cs_std::select::CondSelectGadget;
use ark_r1cs_std::R1CSVar;
use std::collections::HashMap;
use std::collections::HashSet;
use std::vec::Vec;
use ark_std::Zero;
use ark_std::One;

use crate::deriv::{mk_dfa, DFA};
use crate::parser::re::Regex;



/// This creates the big switch across polynomials used in the outer loop
/// across the document
/// Arguments
///
/// c: A private witness, the *index* of the current character in the alphabet,
///    so if alphabet is ASCII, character = 'D' then c = '68'
/// state: A private witness to the current state
pub fn dfa_to_cs(self, c: FpVar<Fr>, state: FpVar<Fr>) -> FpVar<Fr> {

    CondSelectGadget::conditionally_select_power_of_two_vector(&index, &ps).unwrap()

    let temp = &self.poly[&'a'];
    let index = c.to_bits_le().unwrap();

    let ps = self
        .poly.clone()
        .into_iter()
        .map(|(_, p)| p.interpolate_and_evaluate(&state).unwrap())
        .collect::<Vec<_>>();


    //println!("{:#?}", ps);
    //println!("{:#?}", self.poly.len());
    ps[0].clone()
}

      // For testing
pub fn is_match(&self, doc: &String) -> bool {
          let mut s = self.init;
          // For "abb" compute [P_b(P_b(P_a(init)))]
          for c in doc.chars() {
              let ss = self.poly[&c].interpolate_and_evaluate(&FpVar::constant(s));
              println!("{:?} -> {:?}", s, ss);
              s = ss.unwrap().value().unwrap();
          }
          // If it is in the final states, then success
          self.fin.contains(&s)
  }

pub fn frth(n: u64) -> Fr {
    let mut curr = Fr::zero();
    for _ in 0..n {
        curr += Fr::one();
    }
    curr
}

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

/// Ceil[log2(n)]
fn num_bits(n: u64) -> u64 {
    let mut a = 0;
    let mut e = n;
    while e > 0 {
        e = e >> 1;
        a += 1;
    }
    return a;
}

pub fn get_domain(size: u64) -> Radix2DomainVar<Fr> {
    let n = num_bits(size - 1);

    // Generator 2^n
    let gen = Fr::get_root_of_unity(1 << n).unwrap();
    let domain = Radix2DomainVar {
        gen,
        offset: FpVar::constant(Fr::multiplicative_generator()),
        dim: n, // 2^4 = 16
    };

    return domain;
}

/// End-to-end: From Regex -> DFA -> PolyDFA
pub fn mk_poly(q0: &Regex, ab: &String) -> PolyDFA {
    // Construct DFA
    let mut dfa = DFA::new();
    mk_dfa(q0, ab, &mut dfa);
    println!("dfa: {:#?}, {:#?}", dfa.states, dfa.trans);

    // Upper bound number of states n = ceil[log2(dfa.n)]
    let n = num_bits(dfa.n - 1);
    let domain = get_domain(dfa.n);

    // Get G^q0 is the initial state
    let init = nth(&domain, 0); //dfa.get_state_num(q0));
    println!("when init state created: {:#?}", init);
    let fin = dfa
        .get_final_states()
        .into_iter()
        .map(|i| nth(&domain, i))
        .collect::<HashSet<_>>();

    for i in 0..6 {
        println!("{:#?} is {:#?}", i, nth(&domain, i));
    }
    println!("init {:#?}, fin {:#?}", init, fin);
    let mut pdfa = PolyDFA::new(init, &fin);

    for c in ab.chars() {
        let ds = dfa.deltas();

        let mut pairs = ds // For all transitions....
            .iter()
            .filter(|(_, x, _)| *x == c)
            .collect::<Vec<_>>();

         pairs = vec![&(0, 'a', 0), &(1, 'a', 1), &(2, 'a', 2), &(3, 'a', 3)]; // [&(3, 'a', 0)];

        // Pad to 2^n
        // println!("dfa n is {:#?}", n);
        let dummy = (0, c, 0);
        while pairs.len() < (1 << n) {
            pairs.push(&dummy);
        }

        // Sort by x
        pairs.sort_by(|(a, _, _), (b, _, _)| a.cmp(b));

        //println!("PAIRS {:#?}", pairs);

        // Take ys
        let evals = pairs
            .iter()
            .map(|(_, _, to)| FpVar::constant(nth(&domain, *to))) //nth(&domain, *to)))
            .collect::<Vec<_>>();

        //println!("EVALS {:#?}", evals);

        let poly = EvaluationsVar::from_vec_and_domain(evals, domain.clone(), true);

        // Lagrange interpolation; P_c(x) intersects (xs, ys)
        pdfa.add(c, &poly);
    }
    pdfa
}

#[test]
pub fn test_num_bits() {
    assert_eq!(num_bits(0), 0);
    assert_eq!(num_bits(1), 1);
    assert_eq!(num_bits(3), 2);
    assert_eq!(num_bits(4), 3);
}

