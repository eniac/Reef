use std::collections::HashMap;
use std::collections::HashSet;
use std::io::{Result, Error, ErrorKind};
use itertools::Itertools;

use ark_r1cs_std::bits::ToBitsGadget;
use ark_r1cs_std::fields::{fp::FpVar, FieldVar};
use ark_r1cs_std::select::CondSelectGadget;
use ark_r1cs_std::R1CSVar;
use ark_pallas::Fr;

use crate::parser::re::Regex;
use crate::deriv::nullable;
use crate::domain::DomainRadix2;

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

    pub fn nab(&self) -> usize {
        self.ab.len()
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
       let res : Vec<u64> = self.deltas()
            .clone()
            .into_iter()
            .filter_map(|(s, c, t)|
                if s == state && c == ch {
                    Some(t)
                } else { None })
            .collect();

        if res.len() == 1 {
            Ok(res[0])
        } else {
            Err(Error::new(ErrorKind::InvalidInput, "Invalidated DFA invariant"))
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
    pub fn cond_delta(&self, c: FpVar<Fr>, state: FpVar<Fr>, state_domain: &DomainRadix2) -> FpVar<Fr> {
        let ic = c.to_bits_le().unwrap();
        let istate = state.to_bits_le().unwrap();

        // Sort so indexing by (state, char) works correctly in the CondGadget
        let ds: Vec<FpVar<Fr>> = self.deltas()
            .into_iter()
            .sorted()
            .map(|(_, _ ,c)| FpVar::constant(state_domain.get(c)))
            .collect();
        // Concat the bits of [istate] and [ic], warning did not debug this yet!
        let index = [&istate[..], &ic[..]].concat();

        CondSelectGadget::conditionally_select_power_of_two_vector(&index, &ds).unwrap()
    }
}

