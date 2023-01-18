use itertools::Itertools;
use std::collections::HashMap;
use std::collections::HashSet;
use std::io::{Error, ErrorKind, Result};

use ark_pallas::Fr;
use ark_r1cs_std::bits::{boolean::Boolean, ToBitsGadget};
use ark_r1cs_std::fields::{fp::FpVar, FieldVar};
use ark_r1cs_std::select::CondSelectGadget;
use ark_r1cs_std::R1CSVar;
use ark_relations::ns;
use ark_std::One;
use ark_std::Zero;

use crate::deriv::nullable;
use crate::domain::{frth, num_bits, DomainRadix2};
use crate::parser::re::Regex;

#[derive(Debug)]
pub struct DFA<'a> {
    /// Alphabet
    pub ab: &'a str,
    /// Set of states (and their index)
    pub states: HashMap<Regex, u64>,
    /// Transition relation from [state -> state], given [char]
    pub trans: HashSet<(Regex, char, Regex)>,
}

impl<'a> DFA<'a> {
    pub fn new(ab: &'a str) -> Self {
        Self {
            ab,
            states: HashMap::new(),
            trans: HashSet::new(),
        }
    }

    pub fn nstates(&self) -> usize {
        self.states.len()
    }

    pub fn add_transition(&mut self, from: &Regex, c: char, to: &Regex) {
        self.trans.insert((from.clone(), c, to.clone()));
    }

    pub fn add_state(&mut self, new_state: &Regex) {
        self.states.insert(new_state.clone(), self.nstates() as u64);
    }

    pub fn contains_state(&self, state: &Regex) -> bool {
        self.states.contains_key(state)
    }

    pub fn get_state_num(&self, state: &Regex) -> u64 {
        self.states[state]
    }

    /// Initial state
    pub fn get_init_state(&self) -> u64 {
        0
    }

    /// Final state
    pub fn get_final_states(&self) -> HashSet<u64> {
        self.states
            .clone()
            .into_iter()
            .filter_map(|(k, v)| if nullable(&k) { Some(v) } else { None })
            .collect()
    }

    /// DFA step function [delta(s, c) = s'] function
    fn delta(&self, state: u64, ch: char) -> Result<u64> {
        let res: Vec<u64> = self
            .deltas()
            .clone()
            .into_iter()
            .filter_map(|(s, c, t)| if s == state && c == ch { Some(t) } else { None })
            .collect();

        if res.len() == 1 {
            Ok(res[0])
        } else {
            Err(Error::new(
                ErrorKind::InvalidInput,
                "Invalidated DFA invariant",
            ))
        }
    }

    fn deltas(&self) -> Vec<(u64, char, u64)> {
        self.trans
            .clone()
            .into_iter()
            .map(|(a, b, c)| (self.get_state_num(&a), b, self.get_state_num(&c)))
            .collect()
    }

    /// Make a DFA delta function into a circuit
    /// Both [c] and [state] are in index
    /// form in a [DomainRadix2] in [src/domain.rs]
    pub fn cond_delta(&self, c: FpVar<Fr>, state: FpVar<Fr>) -> FpVar<Fr> {
        println!(
            "state {:#?}, c {:#?}",
            state.value().unwrap(),
            c.value().unwrap()
        );

        let index = (state * frth(self.ab.len() as u64) + c)
            .to_bits_le()
            .unwrap();

        let mut bits = Vec::new();
        for i in 0..num_bits(self.deltas().len() as u64) {
            bits.push(index[i as usize].clone());
        }
        println!("Bits {:#?}", bits.value().unwrap());

        // Sort so indexing by (state, char) works correctly in the CondGadget
        let mut ds: Vec<FpVar<Fr>> = self
            .deltas()
            .into_iter()
            .sorted()
            .map(|(_, _, c)| FpVar::constant(frth(c)))
            .collect();

        println!("Deltas {:#?}", self.deltas());

        // pad ds
        let dummy = FpVar::constant(Fr::zero());
        while ds.len() < (1 << num_bits(self.deltas().len() as u64)) {
            ds.push(dummy.clone());
        }

        println!("ds = {:#?}", ds);

        CondSelectGadget::conditionally_select_power_of_two_vector(&bits, &ds).unwrap()
    }
}
