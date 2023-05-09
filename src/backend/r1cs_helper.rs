use crate::backend::nova::int_to_ff;
use circ::cfg;
use circ::cfg::*;
use circ::ir::term::*;
use ff::PrimeField;
use generic_array::typenum;
use neptune::sponge::{api::SpongeAPI, vanilla::Sponge};
use rug::{integer::Order, ops::RemRounding, Assign, Integer};
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

pub(crate) fn new_var(name: String) -> Term {
    // empty holes
    leaf_term(Op::Var(name, Sort::Field(cfg().field().clone())))
}

pub(crate) fn new_wit<I>(i: I) -> Value
// wit values
where
    Integer: From<I>,
{
    Value::Field(cfg().field().new_v(i))
}

// PROVER WORK

// a starts with evals on hypercube
pub(crate) fn linear_mle_product<F: PrimeField>(
    table_t: &mut Vec<Integer>,
    table_eq: &mut Vec<Integer>,
    ell: usize,
    i: usize,
    sponge: &mut Sponge<F, typenum::U4>,
    //    last_q: Vec<Integer>,
) -> (Integer, Integer, Integer, Integer) {
    let base: usize = 2;
    let pow: usize = base.pow((ell - i) as u32);
    assert_eq!(table_t.len(), base.pow(ell as u32));
    assert_eq!(table_eq.len(), base.pow(ell as u32));

    //    println!("ell {:#?}, i {:#?}", ell, i);
    //    println!("pow {:#?}", pow);

    let mut xsq = Integer::from(0);
    let mut x = Integer::from(0);
    let mut con = Integer::from(0);

    for b in 0..pow {
        //for t in vec![0,1] {
        let ti_0 = &table_t[b];
        let ti_1 = &table_t[b + pow];
        let ei_0 = &table_eq[b];
        let ei_1 = &table_eq[b + pow];
        //println!("add ({:#?}, {:#?})", ai_0, ai_1);

        let t_slope = ti_1.clone() - ti_0;
        let e_slope = ei_1.clone() - ei_0;

        xsq += t_slope.clone() * &e_slope;
        x += e_slope * ti_0;
        x += t_slope * ei_0;
        con += ti_0 * ei_0;
    }

    xsq = xsq.rem_floor(cfg().field().modulus());
    x = x.rem_floor(cfg().field().modulus());
    con = con.rem_floor(cfg().field().modulus());

    // generate rands
    let query = vec![
        int_to_ff(con.clone()),
        int_to_ff(x.clone()),
        int_to_ff(xsq.clone()),
    ];

    let acc = &mut ();
    SpongeAPI::absorb(sponge, 3, &query, acc);
    let rand = SpongeAPI::squeeze(sponge, 1, acc);
    let r_i = Integer::from_digits(rand[0].to_repr().as_ref(), Order::Lsf); // TODO?

    for b in 0..pow {
        // todo opt
        table_t[b] = &table_t[b] * (Integer::from(1) - &r_i) + &table_t[b + pow] * &r_i;
        table_eq[b] = &table_eq[b] * (Integer::from(1) - &r_i) + &table_eq[b + pow] * &r_i;
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

    //let mut term = Integer::from(0);
    for i in 0..qs.len() {
        eq_t[qs[i]] += &rs[i];
        //term += evals[qs[i]].clone() * &claims[i];
        //println!("term: {:#?}", term);
    }

    for i in 0..eq_t.len() {
        println!("start");

        // eq_t
        let mut term = rs[qs.len()].clone(); //Integer::from(1);

        for j in (0..ell).rev() {
            let xi = (i >> j) & 1;

            term *= Integer::from(xi) * &last_q[j]
                + Integer::from(1 - xi) * (Integer::from(1) - &last_q[j]);

            //println!("{:#?}", term);
        }

        // println!("{:#?}", term);

        eq_t[i] += term;

        // println!("{:#?}", eq_t[i]);
    }

    eq_t
}

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
                                         //let mut next_minus_coeff;
            for j in (0..m).rev() {
                let ej = (es[i] >> j) & 1;

                // for each x
                if x[m - j - 1] == -1 {
                    // if x_j is the hole
                    next_hole_coeff = ej;
                //      next_minus_coeff = 1 - ej;
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

/*
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
*/

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
