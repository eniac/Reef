#![allow(missing_docs, non_snake_case)]
use crate::naive::dfa::*;
use crate::naive::naive_parser::*;

// #[cfg(all(not(windows), not(target_env = "musl")))]
// #[global_allocator]
// static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

// #[cfg(feature = "metrics")]
// use reef::metrics::{log, log::Component};

pub fn make_delta(state: u64, c: u32, next: u64) -> String {
    format!("\t out = if (state=={state} && cur_char=={c}) then {next} else out fi\n")
}
pub fn make_zok(dfa: DFA<'_>) -> String {
    let mut delta_base_string = "def delta(field state, field cur_char) -> field: \n
    \t field out = -1\n"
        .to_owned();
    for delta in dfa.deltas() {
        let line = make_delta(delta.0, delta.1 as u32, delta.2).to_owned();
        delta_base_string.push_str(&line);
    }
    delta_base_string.push_str("\t return out");
    println!("{}", delta_base_string);
    delta_base_string
}

fn naive(r: &str, alpha: String) {
    let regex = regex_parser(&String::from(r), &alpha);

    let mut dfa = DFA::new(&alpha[..], regex);
    println!("{:#?}", dfa.get_init_state());
    println!("{:#?}", dfa.get_final_states());
    make_zok(dfa);
    // println!("{:#?}",dfa.deltas());

    //write to zok
    //setup circ
    //convert zok to r1cs with circ
    //use nova prover
    return;
    //println!("parse_ms {:#?}, commit_ms {:#?}, r1cs_ms {:#?}, setup_ms {:#?}, precomp_ms {:#?}, nova_ms {:#?},",parse_ms, commit_ms, r1cs_ms, setup_ms, precomp_ms, nova_ms);
}

#[test]
fn test_1() {
    let s = "ab";
    //let abvec: Vec<char> = (0..256).filter_map(std::char::from_u32).collect();
    //let ab: String = abvec.iter().collect();
    let ab = "abc".to_owned();
    naive(s, ab);
}
