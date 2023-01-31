use itertools::Itertools;

use crate::dfa::DFA;

use circ::cfg::*;
use circ::ir::opt::*;
use circ::ir::proof::Constraints;
use circ::ir::term::*;
use circ::target::r1cs::{opt::reduce_linearities, trans::to_r1cs, ProverData, VerifierData};
use fxhash::FxHashMap;
use rug::Integer;

fn new_const<I>(i: I) -> Term
// constants
where
    Integer: From<I>,
{
    leaf_term(Op::Const(Value::Field(cfg().field().new_v(i))))
}

fn new_var(name: String) -> Term {
    // empty holes
    leaf_term(Op::Var(name, Sort::Field(cfg().field().clone())))
}

fn new_wit<I>(i: I) -> Value
// wit values
where
    Integer: From<I>,
{
    Value::Field(cfg().field().new_v(i))
}

pub fn to_lookup_comp(dfa: &DFA) -> (ProverData, VerifierData) {
    let sorted_ab = dfa.ab.chars().sorted();

    let mut char_bottom = new_const(dfa.nstates()); //TODO
    let mut i = 0; // position of char
    for c in sorted_ab {
        // for each char
        let mut state_bottom = new_const(dfa.nstates()); //TODO dummy state that is returned in case of no match
                                                         // perhaps better way todo
                                                         // make each state ite
        for (s, ch, t) in dfa.deltas() {
            if ch == c {
                // if this char is transition
                state_bottom = term(
                    Op::Ite,
                    vec![
                        term(
                            Op::Eq,
                            vec![new_var("current_state".to_owned()), new_const(s)],
                        ), // if match on this state
                        new_const(t), // true (??)
                        state_bottom, // false
                    ],
                );
            }
        }

        // add to char ite (outer)
        char_bottom = term(
            Op::Ite,
            vec![
                term(Op::Eq, vec![new_var("char".to_owned()), new_const(i)]),
                state_bottom,
                char_bottom,
            ],
        );
        i += 1;
    }

    let ite = term(Op::Eq, vec![new_var("next_state".to_owned()), char_bottom]);

    //println!("ITE {:#?}", ite);

    let assertions = vec![ite];
    let pub_inputs = vec![];

    let cs = Computation::from_constraint_system_parts(assertions, pub_inputs);

    let mut css = Computations::new();
    css.comps.insert("main".to_string(), cs);

    let opt_css = opt(
        css,
        vec![
            Opt::ScalarizeVars,
            Opt::Flatten,
            Opt::Sha,
            Opt::ConstantFold(Box::new([])),
            // Tuples must be eliminated before oblivious array elim
            Opt::Tuple,
            Opt::ConstantFold(Box::new([])),
            Opt::Obliv,
            // The obliv elim pass produces more tuples, that must be eliminated
            Opt::Tuple,
            Opt::LinearScan,
            // The linear scan pass produces more tuples, that must be eliminated
            Opt::Tuple,
            Opt::Flatten,
            Opt::ConstantFold(Box::new([])),
        ],
    );

    let (mut prover_data, verifier_data) = to_r1cs(opt_css.get("main").clone(), cfg());

    println!(
        "Pre-opt R1cs size: {}",
        prover_data.r1cs.constraints().len()
    );
    prover_data.r1cs = reduce_linearities(prover_data.r1cs, cfg());

    println!("Final R1cs size: {}", prover_data.r1cs.constraints().len());
    return (prover_data, verifier_data);
}

pub fn gen_wit_i(dfa: &DFA, doc_i: char, current_state: u64) -> (FxHashMap<String, Value>, u64) {
    let next_state = dfa.delta(current_state, doc_i).unwrap();

    let values: FxHashMap<String, Value> = vec![
        ("current_state".to_owned(), new_wit(current_state)),
        ("char".to_owned(), new_wit(dfa.ab_to_num(doc_i))),
        ("next_state".to_owned(), new_wit(next_state)),
    ]
    .into_iter()
    .collect();

    return (values, next_state);
}
