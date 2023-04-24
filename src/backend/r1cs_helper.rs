use crate::backend::{config::*, costs::*};
use circ::cfg;
use circ::cfg::*;
use circ::ir::{opt::*, proof::Constraints, term::*};
use ff::PrimeField;
use rug::{
    integer::Order,
    ops::{RemRounding, RemRoundingAssign},
    rand::RandState,
    Assign, Integer,
};
use std::sync::Once;

static INIT: Once = Once::new();

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
            "28948022309329048855892746252171976963363056481941647379679742748393362948097".into(); // vesta (fuck???)
                                                                                                    //"28948022309329048855892746252171976963363056481941560715954676764349967630337".into(); // pallas curve (i think?)
        cfg::set(&circ);
    }
}

// circuit values
pub(crate) fn new_const<I>(i: I) -> Term
// constants
where
    Integer: From<I>,
{
    leaf_term(Op::Const(Value::Field(cfg().field().new_v(i))))
}
pub(crate) fn new_bool_const(b: bool) -> Term
// constants
{
    leaf_term(Op::Const(Value::Bool(b)))
}

pub(crate) fn new_var(name: String) -> Term {
    // empty holes
    leaf_term(Op::Var(name, Sort::Field(cfg().field().clone())))
}

pub(crate) fn new_bool_var(name: String) -> Term {
    // empty holes
    leaf_term(Op::Var(name, Sort::Bool))
}

pub(crate) fn new_wit<I>(i: I) -> Value
// wit values
where
    Integer: From<I>,
{
    Value::Field(cfg().field().new_v(i))
}

pub(crate) fn new_bool_wit(b: bool) -> Value
// wit values
{
    Value::Bool(b)
}

// feild ops
fn denom(i: usize, evals: &Vec<(Integer, Integer)>) -> Integer {
    let mut res = Integer::from(1);
    for j in (0..evals.len()).rev() {
        if i != j {
            res *= evals[i].0.clone() - &evals[j].0; //.rem_floor_assign(cfg().field().modulus().clone());
                                                     //res.rem_floor(cfg().field().modulus());
        } // TODO
    }

    // find inv in feild
    let inv = res.invert(cfg().field().modulus()).unwrap();

    return inv;
}

// TODO Q - do we need to pad out the table ??

// PROVER WORK

// x = [r_0, r_1, ... -1, {0,1}, {0,1},...]
// where -1 is the "hole"
// returns (coeff (of "hole"), constant)
// if no hole, returns (crap, full result)
// O(mn log mn) :) - or was once upon a time, i'll update this later
// x = eval_at, prods = coeffs of table/eq(), e's = e/q's
pub(crate) fn prover_mle_partial_eval(
    prods: &Vec<Integer>,
    x: &Vec<Integer>,
    es: &Vec<usize>,
    for_t: bool,
    last_q: Option<&Vec<Integer>>, // only q that isn't in {0,1}, inelegant but whatever
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
        //e in 0..table.len() {

        //println!("\ni = {:#?}", i);
        // ~eq(x,e)
        if i < es.len() {
            let mut prod = prods[i].clone();
            let mut next_hole_coeff = 0; // TODO as below ???
            let mut next_minus_coeff = 0;
            for j in (0..m).rev() {
                let ej = (es[i] >> j) & 1;

                // for each x
                if x[m - j - 1] == -1 {
                    // if x_j is the hole
                    next_hole_coeff = ej;
                    next_minus_coeff = 1 - ej;
                } else {
                    let mut intm = Integer::from(1);
                    if ej == 1 {
                        intm.assign(&x[m - j - 1]);
                    } else {
                        // ej == 0
                        intm -= &x[m - j - 1];
                    }
                    prod *= intm; //&x[j] * ej + (1 - &x[j]) * (1 - ej);
                }
            }
            if next_hole_coeff == 1 {
                hole_coeff += &prod;
            } else {
                // next minus coeff == 1
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
                        let ej = q[j].clone(); // TODO order?
                                               // for each x
                        if x[j] == -1 {
                            // if x_j is the hole
                            next_hole_coeff = ej.clone();
                            next_minus_coeff = Integer::from(1) - &ej;
                        } else {
                            let mut intm = ej.clone() * &x[j]; // ei*xi
                            intm += (Integer::from(1) - &ej) * (Integer::from(1) - &x[j]); // +(1-ei)(1-xi)
                            prod *= intm; //&x[j] * ej + (1 - &x[j]) * (1 - ej);
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
        hole_coeff.rem_floor(cfg().field().modulus()),
        minus_coeff.rem_floor(cfg().field().modulus()),
    )
}

// external full "partial" eval for table check
pub fn verifier_mle_eval(table: &Vec<Integer>, q: &Vec<Integer>) -> Integer {
    let (_, con) = prover_mle_partial_eval(table, q, &(0..table.len()).collect(), true, None);

    con
}

// for sum check, computes the sum of many mle univar slices
// takes raw table (pre mle'd), and rands = [r_0, r_1,...], leaving off the hole and x_i's
pub(crate) fn prover_mle_sum_eval(
    table: &Vec<Integer>,
    rands: &Vec<Integer>,
    qs: &Vec<usize>,
    claim_r: &Integer,
    last_q: Option<&Vec<Integer>>,
) -> (Integer, Integer, Integer) {
    let mut sum_xsq = Integer::from(0);
    let mut sum_x = Integer::from(0);
    let mut sum_con = Integer::from(0);
    let hole = rands.len();
    let total = logmn(table.len());

    assert!(hole + 1 <= total, "batch size too small for nlookup");
    let num_x = total - hole - 1;

    let base: usize = 2;

    for combo in 0..base.pow(num_x as u32) {
        let mut eval_at = rands.clone();
        eval_at.push(Integer::from(-1));

        for i in 0..num_x {
            eval_at.push(Integer::from((combo >> i) & 1));
        }

        //println!("eval at: {:#?}", eval_at.clone());
        // T(j)
        let (coeff_a, con_a) =
            prover_mle_partial_eval(table, &eval_at, &(0..table.len()).collect(), true, None); // TODO
                                                                                               //println!("T {:#?}, {:#?}", coeff_a, con_a);

        // r^i * eq(q_i,j) for all i
        // TODO - eq must be an MLE? ask

        // make rs (horner esq)
        let mut rs = vec![claim_r.clone()];
        for i in 1..(qs.len() + 1) {
            rs.push(rs[i - 1].clone() * claim_r);
        }

        let (coeff_b, con_b) = prover_mle_partial_eval(&rs, &eval_at, &qs, false, last_q);
        sum_xsq += &coeff_a * &coeff_b;
        sum_x += &coeff_b * &con_a;
        sum_x += &coeff_a * &con_b;
        sum_con += &con_a * &con_b;
    }

    (
        sum_xsq.rem_floor(cfg().field().modulus()),
        sum_x.rem_floor(cfg().field().modulus()),
        sum_con.rem_floor(cfg().field().modulus()),
    )
}

// CIRCUITS

// coeffs = [constant, x, x^2 ...]
pub(crate) fn horners_circuit_vars(coeffs: &Vec<Term>, x_lookup: Term) -> Term {
    let num_c = coeffs.len();
    //println!("coeffs = {:#?}", coeffs);

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

// eval circuit
pub(crate) fn poly_eval_circuit(points: Vec<Integer>, x_lookup: Term) -> Term {
    let mut eval = new_const(1); // dummy

    for p in points {
        // for sub
        let sub = if p == 0 {
            p
        } else {
            cfg().field().modulus() - p
        };

        eval = term(
            Op::PfNaryOp(PfNaryOp::Mul),
            vec![
                eval,
                term(
                    Op::PfNaryOp(PfNaryOp::Add),
                    vec![x_lookup.clone(), new_const(sub)], // subtraction
                                                            // - TODO for
                                                            // bit eq too
                ),
            ],
        );
    }

    eval
}
