use std::collections::HashMap;
use std::collections::HashSet;
use ark_r1cs_std::poly::{
    domain::Radix2DomainVar,
    evaluations::univariate::*
    };
use ark_r1cs_std::fields::{fp::FpVar, FieldVar};
use ark_r1cs_std::R1CSVar;
use ark_ff::FftField;
use ark_bls12_381::Fr;

use std::vec::Vec;

use crate::deriv::{DFA, mk_dfa};
use crate::parser::re::Regex;

/// DFA encoding using Lagrange polynomials
pub struct PolyDFA {
    /// For each [char], a characteristic polynomial P(state_id) = state_id'
    /// Another encoding of the DFA's delta function
    poly: HashMap<char, EvaluationsVar<Fr>>,
    /// Initial state
    init: Fr,
    /// Final state
    fin: HashSet<Fr>
}

impl PolyDFA {
    pub fn new(init: Fr, fin: &HashSet<Fr>) -> Self {
       Self { poly: HashMap::new(), init, fin: fin.clone() }
    }

    pub fn add(&mut self, c: char, p: &EvaluationsVar<Fr>) {
       self.poly.insert(c, p.clone());
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
}

fn nth(d: &Radix2DomainVar<Fr>, n: u64) -> Fr {
    let mut cur = d.gen;
    if n == 0 {
        cur
    } else {
        for _ in 0..(n-1) {
           cur = cur * cur;
        }
        cur
    }
}

/// End-to-end: From Regex -> DFA -> PolyDFA
pub fn mk_poly(q0: &Regex, ab: &String) -> PolyDFA {
    let mut dfa = DFA::new();
    mk_dfa(q0, ab, &mut dfa);
    let gen = Fr::get_root_of_unity(1 << dfa.n).unwrap();
    let domain = Radix2DomainVar {
        gen,
        offset: FpVar::one(),
        dim: dfa.n // 2^n
    };

    // Get G^q0 is the initial state
    let init = nth(&domain, dfa.get_state_num(q0));
    let mut fin = Vec::new();
    for i in dfa.get_final_states() {
        fin.push(nth(&domain, i).clone());
    }

    let mut pdfa = PolyDFA::new(init, &HashSet::from_iter(fin));

    for c in ab.chars() {
        let deltas = dfa.deltas();           // For all transitions....
        let mut garbage = deltas       // For all transitions....
                .iter()
                .filter(|(_, x, _)|*x == c)
                .collect::<Vec<_>>();

        garbage
                .sort_by(|(a,_,_),(b,_,_)| a.cmp(b));

        let yys =
                garbage.iter()
                .map(|(from,_,to)|
                        (
                        FpVar::constant(nth(&domain, *from)),
                        FpVar::constant(nth(&domain, *to))
                     ))
                .unzip::<_, _, Vec<_>, Vec<_>>()
                .1;

        // Make lagrange
        let poly = EvaluationsVar::from_vec_and_domain(yys, domain.clone(), true);

        // Lagrange interpolation; P_c(x) intersects (xs, ys)
        pdfa.add(c, &poly);
    }
    // println!("DFA: {:?}, PolyDFA: {:?}", dfa, pdfa);
    pdfa
}

