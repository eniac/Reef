use crate::backend::nova::int_to_ff;
use crate::frontend::{
    quantifier::Quant,
    regex::Regex,
    safa::{Either, Skip, SAFA},
};
use crate::trace::{Trace, TraceElem};
use circ::cfg;
use circ::cfg::*;
use circ::ir::term::*;
use ff::PrimeField;
use fxhash::FxHashMap;
use generic_array::typenum;
use neptune::sponge::{api::SpongeAPI, vanilla::Sponge};
use petgraph::{
    graph::{EdgeIndex, NodeIndex},
    prelude::Dfs,
    visit::EdgeRef,
    Graph,
};
use rug::{integer::Order, ops::RemRounding, Assign, Integer};
use std::collections::HashSet;
use std::collections::LinkedList;
use std::sync::Once;

pub static INIT: Once = Once::new();

pub fn init() {
    INIT.call_once(|| {
        setup_circ();
    });
}
fn setup_circ() {
    if !cfg::is_cfg_set() {
        // set up CirC library
        let mut circ: CircOpt = Default::default();
        circ.field.custom_modulus =
            "28948022309329048855892746252171976963363056481941647379679742748393362948097".into(); // vesta
        cfg::set(&circ);
    }
}

pub(crate) fn new_const<I>(i: I) -> Term
where
    Integer: From<I>,
{
    leaf_term(Op::Const(Value::Field(cfg().field().new_v(i))))
}

pub(crate) fn new_bool_const(b: bool) -> Term {
    leaf_term(Op::Const(Value::Bool(b)))
}

pub(crate) fn new_var(name: String) -> Term {
    leaf_term(Op::Var(name, Sort::Field(cfg().field().clone())))
}

pub(crate) fn new_wit<I>(i: I) -> Value
where
    Integer: From<I>,
{
    Value::Field(cfg().field().new_v(i))
}

pub(crate) fn trace_preprocessing(trace: &Option<Trace<char>>) -> Vec<LinkedList<TraceElem<char>>> {
    // split
    let mut sols: Vec<LinkedList<TraceElem<char>>> = Vec::new();
    let mut sol = trace.clone().unwrap().0;
    let mut i = 0;
    let mut state_i = 0;
    for e in sol.clone().iter() {
        if state_i != e.from_node.index() {
            let new_sol = sol.split_off(i);
            sols.push(sol);
            sol = new_sol;
            i = 0;
        }

        state_i = e.to_node.index();
        i += 1;
    }

    sols.push(sol);

    sols
}

pub fn normal_add_table<'a, C>(
    safa: &'a SAFA<char>,
    depth_safa: &mut Graph<(&Quant<Regex>, usize, NodeIndex), &Either<C, Skip>>,
    num_ab: &mut FxHashMap<Option<char>, usize>,
    set_table: &mut HashSet<Integer>,
    num_states: usize,
    exit_state: usize,
    num_chars: u128,
    kid_padding: usize,
    max_branches: usize,
    max_offsets: u128,
    star_offset: usize,
    actual_state: NodeIndex,
    backtrace_state: usize,
    and_states: Vec<usize>,
    final_exists_pass: bool,
) -> (usize, Vec<(usize, NodeIndex)>) {
    let mut sub_max_rel = 0;
    // dupicate safa, run this path
    let mut dfs_small = Dfs::new(&safa.g, actual_state);

    let num_states_mult = num_states as u128;

    let mut sub_path_lens = vec![];
    let mut final_path_lens = vec![];

    // note: duplicate "back branches" being added, but added to set so its all cool
    // this could probably be more efficient tho
    while let Some(state) = dfs_small.next(&safa.g) {
        let in_state = state.index();

        if !final_exists_pass || !safa.g[state].is_and() {
            for edge in safa.g.edges(state) {
                if !safa.is_sink(&edge.target()) {
                    let out_state = edge.target().index();

                    match edge.weight().clone() {
                        Either(Err(openset)) => {
                            let single = openset.is_single(); // single offset/epsilon
                            if single.is_some() {
                                let lower_offset = single.unwrap();
                                let upper_offset = single.unwrap();

                                let rel = calc_rel(
                                    state.index(),
                                    out_state,
                                    &and_states,
                                    kid_padding,
                                    max_branches,
                                    safa,
                                    num_states,
                                    exit_state,
                                    false,
                                );
                                if rel > sub_max_rel {
                                    sub_max_rel = rel;
                                }

                                let c = num_ab[&None]; //EPSILON
                                set_table.insert(Integer::from(
                                    (rel as u128
                                        * num_states_mult
                                        * num_states_mult
                                        * num_chars
                                        * max_offsets
                                        * max_offsets)
                                        + (in_state as u128
                                            * num_states_mult
                                            * num_chars
                                            * max_offsets
                                            * max_offsets)
                                        + (out_state as u128
                                            * num_chars
                                            * max_offsets
                                            * max_offsets)
                                        + (c as u128 * max_offsets * max_offsets)
                                        + (lower_offset as u128 * max_offsets)
                                        + upper_offset as u128,
                                ));
                            } else if openset.is_full() {
                                // [0,*]
                                let c = num_ab[&None];
                                let lower_offset = 0;
                                let upper_offset = star_offset;

                                let rel = calc_rel(
                                    state.index(),
                                    out_state,
                                    &and_states,
                                    kid_padding,
                                    max_branches,
                                    safa,
                                    num_states,
                                    exit_state,
                                    false,
                                );
                                if rel > sub_max_rel {
                                    sub_max_rel = rel;
                                }

                                set_table.insert(Integer::from(
                                    (rel as u128
                                        * num_states_mult
                                        * num_states_mult
                                        * num_chars
                                        * max_offsets
                                        * max_offsets)
                                        + (in_state as u128
                                            * num_states_mult
                                            * num_chars
                                            * max_offsets
                                            * max_offsets)
                                        + (out_state as u128
                                            * num_chars
                                            * max_offsets
                                            * max_offsets)
                                        + (c as u128 * max_offsets * max_offsets)
                                        + (lower_offset as u128 * max_offsets)
                                        + upper_offset as u128,
                                ));
                            } else {
                                // ranges
                                let mut iter = openset.0.iter();

                                while let Some(r) = iter.next() {
                                    let lower_offset = r.start;
                                    let upper_offset = if r.end.is_some() {
                                        r.end.unwrap()
                                    } else {
                                        star_offset
                                    };

                                    let c = num_ab[&None]; //EPSILON
                                    let rel = calc_rel(
                                        state.index(),
                                        out_state,
                                        &and_states,
                                        kid_padding,
                                        max_branches,
                                        safa,
                                        num_states,
                                        exit_state,
                                        false,
                                    );
                                    if rel > sub_max_rel {
                                        sub_max_rel = rel;
                                    }

                                    set_table.insert(Integer::from(
                                        (rel as u128
                                            * num_states_mult
                                            * num_states_mult
                                            * num_chars
                                            * max_offsets
                                            * max_offsets)
                                            + (in_state as u128
                                                * num_states_mult
                                                * num_chars
                                                * max_offsets
                                                * max_offsets)
                                            + (out_state as u128
                                                * num_chars
                                                * max_offsets
                                                * max_offsets)
                                            + (c as u128 * max_offsets * max_offsets)
                                            + (lower_offset as u128 * max_offsets)
                                            + upper_offset as u128,
                                    ));
                                }
                            }
                        }
                        Either(Ok(ch)) => {
                            let c = num_ab[&Some(ch)];
                            let lower_offset = 1;
                            let upper_offset = 1;
                            let rel = calc_rel(
                                state.index(),
                                out_state,
                                &and_states,
                                kid_padding,
                                max_branches,
                                safa,
                                num_states,
                                exit_state,
                                false,
                            );
                            if rel > sub_max_rel {
                                sub_max_rel = rel;
                            }

                            set_table.insert(Integer::from(
                                (rel as u128
                                    * num_states_mult
                                    * num_states_mult
                                    * num_chars
                                    * max_offsets
                                    * max_offsets)
                                    + (in_state as u128
                                        * num_states_mult
                                        * num_chars
                                        * max_offsets
                                        * max_offsets)
                                    + (out_state as u128 * num_chars * max_offsets * max_offsets)
                                    + (c as u128 * max_offsets * max_offsets)
                                    + (lower_offset as u128 * max_offsets)
                                    + upper_offset as u128,
                            ));
                        }
                    }
                }
                let forall_depth = incr_depth(depth_safa, state, edge.target());
                if forall_depth.is_some() {
                    final_path_lens.push(forall_depth.unwrap());
                }
            }

            if safa.accepting().contains(&state) {
                let lower_offset = 0;
                let upper_offset = 0;

                let out_state = backtrace_state;

                let rel = calc_rel(
                    state.index(),
                    out_state,
                    &and_states,
                    kid_padding,
                    max_branches,
                    safa,
                    num_states,
                    exit_state,
                    true,
                );
                if rel > sub_max_rel {
                    sub_max_rel = rel;
                }
                let in_state = state.index();

                let c = num_ab[&Some(26u8 as char)]; // we can only pop after EOF

                set_table.insert(Integer::from(
                    (rel as u128
                        * num_states_mult
                        * num_states_mult
                        * num_chars
                        * max_offsets
                        * max_offsets)
                        + (in_state as u128
                            * num_states_mult
                            * num_chars
                            * max_offsets
                            * max_offsets)
                        + (out_state as u128 * num_chars * max_offsets * max_offsets)
                        + (c as u128 * max_offsets * max_offsets)
                        + (lower_offset as u128 * max_offsets)
                        + upper_offset as u128,
                ));

                // final depth
                sub_path_lens.push((depth_safa[state].1 + 1, depth_safa[state].2));
            }
        } else {
            break;
        }
    }

    let max = sub_path_lens.iter().max();
    if max.is_some() {
        final_path_lens.push(*max.unwrap());
    }

    (sub_max_rel, final_path_lens)
}

pub(crate) fn calc_rel<'a>(
    in_state: usize,
    out_state: usize,
    children: &Vec<usize>,
    kid_padding: usize,
    max_branches: usize,
    safa: &'a SAFA<char>,
    num_states: usize,
    exit_state: usize,
    trans: bool,
) -> usize {
    // 0 = normal
    // 1 = transition (in_state is accepting, out is forall or FINAL)
    // 2 = out_state is accepting
    // >3 = in_state is forall, out_state is the "first branch"
    // 3 = in_state is forall, out_state is a "pop branch"

    let mut rel = 0;

    if trans {
        assert!(out_state == exit_state || safa.g[NodeIndex::new(out_state)].is_and());
        assert!(safa.accepting().contains(&NodeIndex::new(in_state)));
        rel = 1;
    } else if safa.g[NodeIndex::new(in_state)].is_and() {
        if children[0] == out_state {
            let base: usize = num_states;
            // push only for the "first branch"
            rel = 4;
            for k in 1..children.len() {
                rel += children[children.len() - k] * base.pow(k as u32);
            }
            for k in children.len()..(max_branches + 1) {
                rel += kid_padding * base.pow(k as u32);
            }
        } else {
            // others are pops
            rel = 3;
        }
    } else if safa.accepting().contains(&NodeIndex::new(out_state)) {
        rel = 2;
    }

    rel
}

fn incr_depth<C>(
    depth_safa: &mut Graph<(&Quant<Regex>, usize, NodeIndex), &Either<C, Skip>>,
    prev_node: NodeIndex,
    target_node: NodeIndex,
) -> Option<(usize, NodeIndex)> {
    // return if forall
    if target_node != prev_node {
        if depth_safa[target_node].0.is_and() {
            return Some((depth_safa[prev_node].1 + 1, depth_safa[prev_node].2));
        } else {
            let prev = depth_safa.node_weight(prev_node).unwrap();
            let prev_depth = prev.1 + 1;
            let from_forall = prev.2;

            let node_ref = depth_safa.node_weight_mut(target_node).unwrap();
            *node_ref = (node_ref.0, prev_depth, from_forall);
            return None;
        }
    }
    return None;
}

pub(crate) fn edge_id<C>(_idx: EdgeIndex<u32>, e: &Either<C, Skip>) -> &Either<C, Skip> {
    e
}

pub(crate) fn node_depth_map(
    idx: NodeIndex<u32>,
    n: &Quant<Regex>,
) -> (&Quant<Regex>, usize, NodeIndex) {
    (n, 0, NodeIndex::new(0))
}

// starts with evals on hypercube
pub(crate) fn linear_mle_product<F: PrimeField>(
    table_t: &mut Vec<Integer>,
    table_eq: &mut Vec<Integer>,
    ell: usize,
    i: usize,
    sponge: &mut Sponge<F, typenum::U4>,
) -> (Integer, Integer, Integer, Integer) {
    let base: usize = 2;
    let pow: usize = base.pow((ell - i) as u32);
    assert_eq!(table_t.len(), base.pow(ell as u32));
    assert_eq!(table_eq.len(), base.pow(ell as u32));

    let mut xsq = Integer::from(0);
    let mut x = Integer::from(0);
    let mut con = Integer::from(0);

    for b in 0..pow {
        let ti_0 = &table_t[b];
        let ti_1 = &table_t[b + pow];
        let ei_0 = &table_eq[b];
        let ei_1 = &table_eq[b + pow];

        let t_slope = ti_1.clone() - ti_0;
        let e_slope = ei_1.clone() - ei_0;

        xsq += t_slope.clone() * &e_slope;
        x += e_slope * ti_0;
        x += t_slope * ei_0;
        con += ti_0 * ei_0;
    }

    xsq = xsq.rem_floor(cfg().field().modulus()).keep_bits(255);
    x = x.rem_floor(cfg().field().modulus()).keep_bits(255);
    con = con.rem_floor(cfg().field().modulus()).keep_bits(255);

    let query = vec![
        int_to_ff(con.clone()),
        int_to_ff(x.clone()),
        int_to_ff(xsq.clone()),
    ];

    let acc = &mut ();
    SpongeAPI::absorb(sponge, 3, &query, acc);
    let rand = SpongeAPI::squeeze(sponge, 1, acc);
    let r_i = Integer::from_digits(rand[0].to_repr().as_ref(), Order::Lsf);

    for b in 0..pow {
        table_t[b] = &table_t[b] * (Integer::from(1) - &r_i) + &table_t[b + pow] * &r_i;
        table_t[b] = table_t[b]
            .clone()
            .rem_floor(cfg().field().modulus())
            .keep_bits(255);
        table_eq[b] = &table_eq[b] * (Integer::from(1) - &r_i) + &table_eq[b + pow] * &r_i;
        table_eq[b] = table_eq[b]
            .clone()
            .rem_floor(cfg().field().modulus())
            .keep_bits(255);
    }

    (r_i, xsq, x, con)
}

pub(crate) fn gen_eq_table(
    rs: &Vec<Integer>,
    qs: &Vec<usize>,
    last_q: &Vec<Integer>,
) -> Vec<Integer> {
    let base: usize = 2;
    let ell: usize = last_q.len();

    let t_len = base.pow(ell as u32);
    assert_eq!(rs.len(), qs.len() + 1);

    let mut eq_t = vec![Integer::from(0); t_len];

    for i in 0..qs.len() {
        eq_t[qs[i]] += &rs[i];
    }

    for i in 0..eq_t.len() {
        let mut term = rs[qs.len()].clone();

        for j in (0..ell).rev() {
            let xi = (i >> j) & 1;

            term *= Integer::from(xi) * &last_q[j]
                + Integer::from(1 - xi) * (Integer::from(1) - &last_q[j]);
        }

        eq_t[i] += term;
        eq_t[i] = eq_t[i]
            .clone()
            .rem_floor(cfg().field().modulus())
            .keep_bits(255);
    }

    eq_t
}

// x = [r_0, r_1, ... -1, {0,1}, {0,1},...]
// where -1 is the "hole"
// returns (coeff (of "hole"), constant)
// if no hole, returns (crap, full result)
// x = eval_at, prods = coeffs of table/eq(), e's = e/q's
pub(crate) fn prover_mle_partial_eval(
    prods: &[Integer],
    x: &[Integer],
    es: &Vec<usize>,
    for_t: bool,
    last_q: Option<&Vec<Integer>>, // only q that isn't in {0,1}
) -> (Integer, Integer) {
    let base: usize = 2;
    let m = x.len();

    if for_t {
        assert!(base.pow(m as u32 - 1) <= prods.len());
        assert!(base.pow(m as u32) >= prods.len());
        assert_eq!(es.len(), prods.len()); //todo final q
    } else if last_q.is_some() {
        assert_eq!(es.len() + 1, prods.len());
    }

    let mut hole_coeff = Integer::from(0);
    let mut minus_coeff = Integer::from(0);
    for i in 0..es.len() + 1 {
        // ~eq(x,e)
        if i < es.len() {
            let mut prod = prods[i].clone();
            let mut next_hole_coeff = 0;
            for j in (0..m).rev() {
                let ej = (es[i] >> j) & 1;

                // for each x
                if x[m - j - 1] == -1 {
                    // if x_j is the hole
                    next_hole_coeff = ej;
                } else {
                    let mut intm = Integer::from(1);
                    if ej == 1 {
                        intm.assign(&x[m - j - 1]);
                    } else {
                        intm -= &x[m - j - 1];
                    }
                    prod *= intm;
                }
            }
            if next_hole_coeff == 1 {
                hole_coeff += &prod;
            } else {
                minus_coeff += &prod;
            }
        } else {
            // final q?
            match last_q {
                Some(q) => {
                    let mut prod = prods[i].clone();
                    let mut next_hole_coeff = Integer::from(1); // in case of no hole
                    let mut next_minus_coeff = Integer::from(1);
                    for j in 0..m {
                        let ej = q[j].clone();
                        if x[j] == -1 {
                            // if x_j is the hole
                            next_hole_coeff = ej.clone();
                            next_minus_coeff = Integer::from(1) - &ej;
                        } else {
                            let mut intm = ej.clone() * &x[j];
                            intm += (Integer::from(1) - &ej) * (Integer::from(1) - &x[j]);
                            prod *= intm;
                        }
                    }
                    hole_coeff += &prod * next_hole_coeff;
                    minus_coeff += &prod * next_minus_coeff;
                }
                None => {}
            }
        }
    }
    hole_coeff -= &minus_coeff;
    (
        hole_coeff.rem_floor(cfg().field().modulus()).keep_bits(255),
        minus_coeff
            .rem_floor(cfg().field().modulus())
            .keep_bits(255),
    )
}

// external full "partial" eval for table check
pub fn verifier_mle_eval(table: &[Integer], q: &[Integer]) -> Integer {
    let (_, con) = prover_mle_partial_eval(table, q, &(0..table.len()).collect(), true, None);

    con
}

// coeffs = [constant, x, x^2 ...]
pub(crate) fn horners_circuit_vars(coeffs: &Vec<Term>, x_lookup: Term) -> Term {
    let num_c = coeffs.len();

    let mut horners = term(
        Op::PfNaryOp(PfNaryOp::Mul),
        vec![coeffs[num_c - 1].clone(), x_lookup.clone()],
    );
    for i in (1..(num_c - 1)).rev() {
        horners = term(
            Op::PfNaryOp(PfNaryOp::Mul),
            vec![
                x_lookup.clone(),
                term(
                    Op::PfNaryOp(PfNaryOp::Add),
                    vec![horners, coeffs[i].clone()],
                ),
            ],
        );
    }

    // constant
    horners = term(
        Op::PfNaryOp(PfNaryOp::Add),
        vec![horners, coeffs[0].clone()],
    );

    horners
}
