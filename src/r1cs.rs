use itertools::Itertools;

use crate::dfa::DFA;

use circ::cfg::*;
use circ::ir::opt::*;
use circ::ir::proof::Constraints;
use circ::ir::term::*;
use circ::target::r1cs::{
    opt::reduce_linearities, trans::to_r1cs, Lc, ProverData, R1cs, VerifierData,
};
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

fn add(a: &Integer, b: &Integer) -> Integer {
    let (_, rem) = (a.clone() + b.clone()).div_rem_euc(cfg().field().modulus().clone());
    rem
}

fn sub(a: &Integer, b: &Integer) -> Integer {
    let (_, rem) = (a.clone() - b.clone()).div_rem_euc(cfg().field().modulus().clone());
    rem
}

fn mul(a: &Integer, b: &Integer) -> Integer {
    let (_, rem) = (a.clone() * b.clone()).div_rem_euc(cfg().field().modulus().clone());
    rem
}

//fn horner_testing(coeffs: &Vec<Integer>,

fn denom(i: usize, evals: &Vec<(Integer, Integer)>) -> Integer {
    let mut res = Integer::from(1);
    for j in (0..evals.len()).rev() {
        if i != j {
            res = mul(&res, &sub(&evals[i].0, &evals[j].0));
        }
    }

    // find inv in feild
    let inv = res.invert(cfg().field().modulus()).unwrap();

    return inv;
}

pub fn lagrange_from_dfa(dfa: &DFA) -> Vec<Integer> {
    let mut evals = vec![];
    for (si, c, so) in dfa.deltas() {
        evals.push((
            Integer::from(si * (dfa.chars.len() as u64) + dfa.ab_to_num(c)),
            Integer::from(so),
        ));
    }

    lagrange_field(evals)
}

pub fn lagrange_field(evals: Vec<(Integer, Integer)>) -> Vec<Integer> {
    let num_pts = evals.len();
    println!("evals = {:#?}", evals);

    let mut coeffs = vec![Integer::from(0); num_pts];
    for i in 0..num_pts {
        // make l_i
        let mut l_i = vec![Integer::from(0); num_pts];
        l_i[0] = denom(i, &evals);

        let mut new_l_i = vec![Integer::from(0); num_pts];
        for k in 0..num_pts {
            if k != i {
                new_l_i = vec![Integer::from(0); num_pts];
                let mut range = (0..k).rev();
                if k < i {
                    range = (0..(k + 1)).rev();
                }
                for j in range {
                    new_l_i[j + 1] = add(&new_l_i[j + 1], &l_i[j]);
                    new_l_i[j] = sub(&new_l_i[j], &mul(&evals[k].0, &l_i[j]));
                    println!("new_li j, j+1 = {:#?}, {:#?}", new_l_i[j], new_l_i[j + 1]);
                }
                l_i = new_l_i;
            }
        }

        println!("li = {:#?}", l_i);
        // mult y's
        for k in 0..num_pts {
            coeffs[k] = add(&coeffs[k], &mul(&evals[i].1, &l_i[k]));
        }
    }

    return coeffs;
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

    println!("ITE {:#?}", ite);

    let assertions = vec![ite];

    // we must make intermediate private witnesses temporarily "public" as they serve as
    // inputs/outputs to the nova F circuit. in the grand scheme of things (nova) they need to be
    // changed back to private, but as far as circ is aware, they are public.
    let pub_inputs = vec![
        //new_var("current_state".to_owned()),
        //new_var("char".to_owned()),
        new_var("next_state".to_owned()),
    ];

    let cs = Computation::from_constraint_system_parts(assertions, pub_inputs);

    let mut css = Computations::new();
    css.comps.insert("main".to_string(), cs);
    /*
        let css = opt(
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
    */
    let (mut prover_data, verifier_data) = to_r1cs(css.get("main").clone(), cfg());

    println!(
        "Pre-opt R1cs size: {}",
        prover_data.r1cs.constraints().len()
    );
    //println!("Prover data {:#?}", prover_data);
    //prover_data.r1cs = reduce_linearities(prover_data.r1cs, cfg());

    //println!("Prover data {:#?}", prover_data);

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

#[cfg(test)]
mod tests {

    use crate::dfa::DFA;
    use crate::r1cs::*;
    use circ::cfg;
    use circ::cfg::CircOpt;

    fn set_up_cfg(m: String) {
        let mut circ: CircOpt = Default::default();
        circ.field.custom_modulus = m.into();

        cfg::set(&circ);
    }

    #[test]
    fn basic_lg() {
        set_up_cfg("79".to_owned());

        let points = vec![
            (Integer::from(1), Integer::from(1)),
            (Integer::from(10), Integer::from(10)),
            (Integer::from(3), Integer::from(3)),
            (Integer::from(4), Integer::from(4)),
        ];
        let coeffs = lagrange_field(points);

        let expected = vec![
            Integer::from(0),
            Integer::from(1),
            Integer::from(0),
            Integer::from(0),
        ];

        assert_eq!(coeffs, expected);
    }

    fn lg_1() {
        set_up_cfg("1019".to_owned());

        let points = vec![
            (Integer::from(1), Integer::from(2)),
            (Integer::from(10), Integer::from(3)),
            (Integer::from(3), Integer::from(3)),
            (Integer::from(4), Integer::from(9)),
        ];
        let coeffs = lagrange_field(points);

        let expected = vec![
            Integer::from(124),
            Integer::from(277),
            Integer::from(929),
            Integer::from(774),
        ];

        assert_eq!(coeffs, expected);
    }

    /*
        fn dfa_lg() {

        }
    */
}
