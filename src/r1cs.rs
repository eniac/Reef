use crate::costs;
use crate::costs::{opt_cost_model_select, JBatching};
use crate::dfa::DFA;
use circ::cfg::*;
use circ::ir::{opt::*, proof::Constraints, term::*};
use circ::target::r1cs::{opt::reduce_linearities, trans::to_r1cs, ProverData, VerifierData};
use ff::PrimeField;
use fxhash::FxHashMap;
use generic_array::typenum;
use neptune::{
    poseidon::PoseidonConstants,
    sponge::api::{IOPattern, SpongeAPI, SpongeOp},
    sponge::vanilla::{Mode, Sponge, SpongeTrait},
    Strength,
};
use nova_snark::traits::Group;
use rug::{
    integer::Order,
    ops::{RemRounding, RemRoundingAssign},
    rand::RandState,
    Assign, Integer,
};
use std::time::{Duration, Instant};

// circuit values
fn new_const<I>(i: I) -> Term
// constants
where
    Integer: From<I>,
{
    leaf_term(Op::Const(Value::Field(cfg().field().new_v(i))))
}
fn new_bool_const(b: bool) -> Term
// constants
{
    leaf_term(Op::Const(Value::Bool(b)))
}

fn new_var(name: String) -> Term {
    // empty holes
    leaf_term(Op::Var(name, Sort::Field(cfg().field().clone())))
}

fn new_bool_var(name: String) -> Term {
    // empty holes
    leaf_term(Op::Var(name, Sort::Bool))
}

fn new_wit<I>(i: I) -> Value
// wit values
where
    Integer: From<I>,
{
    Value::Field(cfg().field().new_v(i))
}

fn new_bool_wit(b: bool) -> Value
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

// x = [r_0, r_1, ... -1, {0,1}, {0,1},...].rev()
// where -1 is the "hole"
// returns (coeff (of "hole"), constant)
// if no hole, returns (crap, full result)
// O(mn log mn) :) - or was once upon a time, i'll update this later
// x = eval_at, prods = coeffs of table/eq(), e's = e/q's
fn prover_mle_partial_eval(
    prods: &Vec<Integer>,
    x: &Vec<Integer>,
    es: &Vec<usize>,
    for_t: bool,
    last_q: Option<&Vec<Integer>>, // only q that isn't in {0,1}, inelegant but whatever
) -> (Integer, Integer) {
    let base: usize = 2;
    let m = x.len();
    println!("m {:#?}, prods {:#?}", m, prods.len());

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

        // ~eq(x,e)
        if i < es.len() {
            let mut prod = prods[i].clone();
            let mut next_hole_coeff = 0;
            let mut next_minus_coeff = 0;
            for j in 0..m {
                let ej = (es[i] >> j) & 1;
                // for each x
                if x[j] == -1 {
                    // if x_j is the hole
                    next_hole_coeff = ej;
                    next_minus_coeff = 1 - ej;
                } else {
                    let mut intm = Integer::from(1);
                    if ej == 1 {
                        intm.assign(&x[j]);
                    } else {
                        // ej == 0
                        intm -= &x[j];
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
                    let mut next_hole_coeff = Integer::from(0);
                    let mut next_minus_coeff = Integer::from(0);
                    for j in 0..m {
                        let ej = q[j].clone(); // TODO order?
                                               // for each x
                        if x[j] == -1 {
                            // if x_j is the hole
                            next_hole_coeff = ej.clone();
                            next_minus_coeff = Integer::from(1) - &ej;
                        } else {
                            let mut intm = Integer::from(1);
                            if ej == 1 {
                                intm.assign(&x[j]);
                            } else {
                                // ej == 0
                                intm -= &x[j];
                            }
                            prod *= intm; //&x[j] * ej + (1 - &x[j]) * (1 - ej);
                        }
                    }
                    if next_hole_coeff == Integer::from(1) {
                        hole_coeff += &prod;
                    } else {
                        // next minus coeff == 1
                        minus_coeff += &prod;
                    }
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

// for sum check, computes the sum of many mle univar slices
// takes raw table (pre mle'd), and rands = [r_0, r_1,...], leaving off the hole and x_i's
fn prover_mle_sum_eval(
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
    let total = (table.len() as f32).log2().ceil() as usize;

    println!(
        "sum eval: rands: {:#?}, table: {:#?}, table log {:#?}",
        rands, table, total
    );
    assert!(hole + 1 <= total, "batch size too small for nlookup");
    let num_x = total - hole - 1;

    let base: usize = 2;

    for combo in 0..base.pow(num_x as u32) {
        let mut eval_at = rands.clone();
        eval_at.push(Integer::from(-1));

        for i in 0..num_x {
            eval_at.push(Integer::from((combo >> i) & 1));
        }

        println!("eval at: {:#?}", eval_at.clone());
        // T(j)
        let (coeff_a, con_a) = prover_mle_partial_eval(
            table,
            &eval_at.clone().into_iter().rev().collect(), // TODO
            &(0..table.len()).collect(),
            true,
            None,
        ); // TODO
        println!("T {:#?}, {:#?}", coeff_a, con_a);

        // r^i * eq(q_i,j) for all i
        // TODO - eq must be an MLE? ask

        // make rs (horner esq)
        let mut rs = vec![claim_r.clone()];
        for i in 1..(qs.len() + 1) {
            rs.push(rs[i - 1].clone() * claim_r);
        }

        let (coeff_b, con_b) = prover_mle_partial_eval(
            &rs,
            &eval_at.into_iter().rev().collect(),
            &qs,
            false,
            last_q,
        );
        println!("eq {:#?}, {:#?}", coeff_b, con_b);
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
fn horners_circuit_vars(coeffs: &Vec<Term>, x_lookup: Term) -> Term {
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
fn poly_eval_circuit(points: Vec<Integer>, x_lookup: Term) -> Term {
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

pub struct R1CS<'a, F: PrimeField> {
    dfa: &'a DFA,
    batching: JBatching,
    assertions: Vec<Term>,
    // perhaps a misleading name, by "public inputs", we mean "circ leaves these wires exposed from
    // the black box, and will not optimize them away"
    // at the nova level, we will "reprivitize" everything, it's just important to see the hooks
    // sticking out here
    pub_inputs: Vec<Term>,
    batch_size: usize,
    doc: Vec<String>,
    is_match: bool,
    pc: PoseidonConstants<F, typenum::U2>,
    commitment: Option<F>,
}

impl<'a, F: PrimeField> R1CS<'a, F> {
    pub fn new(
        dfa: &'a DFA,
        doc: &Vec<String>,
        batch_size: usize,
        pcs: PoseidonConstants<F, typenum::U2>,
    ) -> Self {
        let is_match = dfa.is_match(doc);
        println!("Match? {:#?}", is_match);

        // run cost model (with Poseidon) to decide batching
        let batching: JBatching = costs::opt_cost_model_select(
            &dfa,
            batch_size,
            batch_size,
            dfa.is_match(&doc),
            doc.len(),
        );

        Self {
            dfa,
            batching: JBatching::NaivePolys, // TODO
            assertions: Vec::new(),
            pub_inputs: Vec::new(),
            batch_size,
            doc: doc.clone(),
            is_match,
            pc: pcs,
            commitment: None,
        }
    }

    pub fn gen_commitment(&mut self) {
        let mut hash = vec![F::from(0)];
        for c in self.doc.clone().into_iter() {
            let mut sponge = Sponge::new_with_constants(&self.pc, Mode::Simplex);
            let acc = &mut ();

            let parameter = IOPattern(vec![SpongeOp::Absorb(2), SpongeOp::Squeeze(1)]);
            sponge.start(parameter, None, acc);
            SpongeAPI::absorb(
                &mut sponge,
                2,
                &[hash[0], F::from(self.dfa.ab_to_num(&c.to_string()) as u64)],
                acc,
            );
            hash = SpongeAPI::squeeze(&mut sponge, 1, acc);
            sponge.finish(acc).unwrap();
        }
        println!("commitment = {:#?}", hash.clone());
        self.commitment = Some(hash[0]);
    }

    // seed Questions todo
    fn prover_random_from_seed(&self, s: usize) -> Integer {
        let seed = F::from(s as u64); // TODO GEN
        let mut sponge = Sponge::new_with_constants(&self.pc, Mode::Simplex);
        let acc = &mut ();
        let parameter = IOPattern(vec![SpongeOp::Absorb(1), SpongeOp::Squeeze(1)]);

        sponge.start(parameter, None, acc);
        SpongeAPI::absorb(&mut sponge, 1, &[seed], acc);
        let rand = SpongeAPI::squeeze(&mut sponge, 1, acc);
        sponge.finish(acc).unwrap();

        Integer::from_digits(rand[0].to_repr().as_ref(), Order::Lsf)
    }

    fn lookup_idxs(&mut self) -> Vec<Term> {
        let mut v = vec![];
        for i in 1..=self.batch_size {
            let v_i = term(
                Op::PfNaryOp(PfNaryOp::Add),
                vec![
                    term(
                        Op::PfNaryOp(PfNaryOp::Add),
                        vec![
                            term(
                                Op::PfNaryOp(PfNaryOp::Mul),
                                vec![
                                    new_var(format!("state_{}", i - 1)),
                                    new_const(self.dfa.nstates() * self.dfa.nchars()),
                                ],
                            ),
                            term(
                                Op::PfNaryOp(PfNaryOp::Mul),
                                vec![
                                    new_var(format!("state_{}", i)),
                                    new_const(self.dfa.nchars()),
                                ],
                            ),
                        ],
                    ),
                    new_var(format!("char_{}", i - 1)),
                ],
            );
            v.push(v_i);
            self.pub_inputs.push(new_var(format!("state_{}", i - 1)));
            self.pub_inputs.push(new_var(format!("char_{}", i - 1)));
        }
        self.pub_inputs
            .push(new_var(format!("state_{}", self.batch_size)));
        v
    }

    fn r1cs_conv(&self) -> (ProverData, VerifierData) {
        let time = Instant::now();
        let cs = Computation::from_constraint_system_parts(
            self.assertions.clone(),
            self.pub_inputs.clone(),
        );

        println!("assertions: {:#?}", self.assertions.clone());

        let mut css = Computations::new();
        css.comps.insert("main".to_string(), cs);
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
        let (mut prover_data, verifier_data) = to_r1cs(css.get("main").clone(), cfg());

        println!(
            "Pre-opt R1cs size (no hashes): {}",
            prover_data.r1cs.constraints().len()
        );
        // println!("Prover data {:#?}", prover_data);
        prover_data.r1cs = reduce_linearities(prover_data.r1cs, cfg());

        //println!("Prover data {:#?}", prover_data);
        let ms = time.elapsed().as_millis();
        println!(
            "Final R1cs size (no hashes): {}",
            prover_data.r1cs.constraints().len()
        );
        println!("r1cs conv: {:#?}", ms);

        return (prover_data, verifier_data);
    }

    pub fn to_r1cs(&mut self) -> (ProverData, VerifierData) {
        match self.batching {
            JBatching::NaivePolys => self.to_polys(),
            JBatching::Nlookup => self.to_nlookup(),
            JBatching::Plookup => todo!(), //gen_wit_i_plookup(round_num, current_state, doc, batch_size),
        }
    }

    // TODO batch size (1 currently)
    fn to_polys(&mut self) -> (ProverData, VerifierData) {
        let l_time = Instant::now();
        let lookup = self.lookup_idxs();

        let mut evals = vec![];
        for (si, c, so) in self.dfa.deltas() {
            //println!("trans: {:#?},{:#?},{:#?}", si, c, so);
            evals.push(
                Integer::from(
                    (si * self.dfa.nstates() * self.dfa.nchars())
                        + (so * self.dfa.nchars())
                        + self.dfa.ab_to_num(&c.to_string()),
                )
                .rem_floor(cfg().field().modulus()),
            );
        }
        //println!("eval form poly {:#?}", evals);

        for i in 0..self.batch_size {
            let eq = term(
                Op::Eq,
                vec![
                    new_const(0), // vanishing
                    poly_eval_circuit(evals.clone(), lookup[i].clone()), // this means repeats, but I think circ
                                                                         // takes care of; TODO also clones
                ],
            );
            self.assertions.push(eq);
        }
        let lag_ms = l_time.elapsed().as_millis();

        // final state (non) match check
        let vanishing_poly;
        let final_states = self.dfa.get_final_states();
        let non_final_states = self.dfa.get_non_final_states();
        let mut vanish_on = vec![];
        let v_time = Instant::now();
        if self.is_match {
            //println!("in states: {:#?}", final_states);
            // proof of membership
            for xi in final_states.into_iter() {
                vanish_on.push(Integer::from(xi));
            }
        } else {
            //println!("in states: {:#?}", non_final_states);
            for xi in non_final_states.into_iter() {
                vanish_on.push(Integer::from(xi));
            }
        }
        vanishing_poly =
            poly_eval_circuit(vanish_on, new_var(format!("state_{}", self.batch_size)));
        let vanish_ms = v_time.elapsed().as_millis();

        println!("lag {:#?}, vanish {:#?}", lag_ms, vanish_ms);

        let match_term = term(
            Op::Ite,
            vec![
                term(
                    Op::Eq,
                    vec![
                        new_var("round_num".to_owned()),
                        new_const(self.doc.len() - 1), // TODO make private + hashing crap
                                                       // + batching crap + element might be too
                                                       // big for feild crap
                    ],
                ), // if in final round
                term(Op::Eq, vec![vanishing_poly, new_const(0)]), // true -> check next_state (not) in final_states
                new_bool_const(true),                             // not in correct round
            ],
        );

        let round_term = term(
            Op::Eq,
            vec![
                new_var("next_round_num".to_owned()),
                term(
                    Op::PfNaryOp(PfNaryOp::Add),
                    vec![new_var("round_num".to_owned()), new_const(1)],
                ),
            ],
        );

        self.assertions.push(match_term);
        self.assertions.push(round_term);

        self.pub_inputs.push(new_var("round_num".to_owned()));
        self.pub_inputs.push(new_var("next_round_num".to_owned()));

        self.r1cs_conv()
    }

    // for use at the end of sum check
    // eq([x0,x1,x2...],[e0,e1,e2...])
    fn bit_eq_circuit(&mut self, m: usize, q_bit: usize) -> Term {
        let mut eq = new_const(1); // dummy, not used

        let q_name = format!("eq{}", q_bit);
        for i in 0..m {
            let next = term(
                Op::PfNaryOp(PfNaryOp::Add),
                vec![
                    term(
                        Op::PfNaryOp(PfNaryOp::Mul),
                        vec![
                            new_var(format!("{}_q_{}", q_name, i)),
                            new_var(format!("sc_r_{}", i + 1)), // sc_r idx's start @1
                        ],
                    ),
                    term(
                        Op::PfNaryOp(PfNaryOp::Mul),
                        vec![
                            term(
                                Op::PfNaryOp(PfNaryOp::Add),
                                vec![
                                    new_const(1),
                                    term(
                                        Op::PfUnOp(PfUnOp::Neg),
                                        vec![new_var(format!("{}_q_{}", q_name, i))],
                                    ),
                                ],
                            ),
                            term(
                                Op::PfNaryOp(PfNaryOp::Add),
                                vec![
                                    new_const(1),
                                    term(
                                        Op::PfUnOp(PfUnOp::Neg),
                                        vec![new_var(format!("sc_r_{}", i + 1))],
                                    ),
                                ],
                            ),
                        ],
                    ),
                ],
            );

            self.pub_inputs.push(new_var(format!("{}_q_{}", q_name, i)));

            /* we add elsewhere
             * if q_bit == 0 {
                self.pub_inputs.push(new_var(format!("sc_r_{}", i))); // eq_j_i = rc_r_i
            }
            */

            if i == 0 {
                eq = next;
            } else {
                eq = term(Op::PfNaryOp(PfNaryOp::Mul), vec![eq, next]);
            }
        }

        eq
    }

    // C_1 = LHS/"claim"
    fn sum_check_circuit(&mut self, C_1: Term, num_rounds: usize) {
        // first round claim
        let mut claim = C_1.clone();

        for j in 1..=num_rounds {
            // P makes a claim g_j(X_j) about a univariate slice of its large multilinear polynomial
            // g_j is degree 1 in our case (woo constant time evaluation)

            // V checks g_{j-1}(r_{j-1}) = g_j(0) + g_j(1)
            // Ax^2 + Bx + C -> A + B + C + C TODO
            let g_j = term(
                Op::PfNaryOp(PfNaryOp::Add),
                vec![
                    new_var(format!("sc_g_{}_xsq", j)),
                    term(
                        Op::PfNaryOp(PfNaryOp::Add),
                        vec![
                            new_var(format!("sc_g_{}_x", j)),
                            term(
                                Op::PfNaryOp(PfNaryOp::Add),
                                vec![
                                    new_var(format!("sc_g_{}_const", j)),
                                    new_var(format!("sc_g_{}_const", j)),
                                ],
                            ),
                        ],
                    ),
                ],
            );

            let claim_check = term(Op::Eq, vec![claim.clone(), g_j]);

            self.assertions.push(claim_check);
            self.pub_inputs.push(new_var(format!("sc_g_{}_xsq", j)));
            self.pub_inputs.push(new_var(format!("sc_g_{}_x", j)));
            self.pub_inputs.push(new_var(format!("sc_g_{}_const", j)));
            self.pub_inputs.push(new_var(format!("sc_r_{}", j)));

            // "V" chooses rand r_{j} (P chooses this with hash)
            //let r_j = new_var(format!("sc_r_{}", j));

            // update claim for the next round g_j(r_j)
            claim = term(
                Op::PfNaryOp(PfNaryOp::Add),
                vec![
                    new_var(format!("sc_g_{}_const", j)),
                    term(
                        Op::PfNaryOp(PfNaryOp::Mul),
                        vec![
                            new_var(format!("sc_r_{}", j)),
                            term(
                                Op::PfNaryOp(PfNaryOp::Add),
                                vec![
                                    new_var(format!("sc_g_{}_x", j)),
                                    term(
                                        Op::PfNaryOp(PfNaryOp::Mul),
                                        vec![
                                            new_var(format!("sc_r_{}", j)),
                                            new_var(format!("sc_g_{}_xsq", j)),
                                        ],
                                    ),
                                ],
                            ),
                        ],
                    ),
                ],
            );

            if j == num_rounds {
                // output last g_v(r_v) claim

                let last_claim = term(
                    Op::Eq,
                    vec![claim.clone(), new_var(format!("sc_last_claim"))],
                );
                self.assertions.push(last_claim);
                self.pub_inputs.push(new_var(format!("sc_last_claim")));
            }
        }
    }

    pub fn to_nlookup(&mut self) -> (ProverData, VerifierData) {
        // TODO pub inputs -> can make which priv?
        // last state_batch is final "next_state" output
        // v_{batch-1} = (state_{batch-1}, c, state_batch)
        // v_batch = T eval check (optimization)
        //                self.pub_inputs
        //                    .push(new_var(format!("state_{}", self.batch_size)));

        let mut v = vec![new_const(0)]; // dummy constant term for lhs claim
        v.append(&mut self.lookup_idxs());
        v.push(new_var(format!("prev_running_claim"))); // running claim
        self.pub_inputs.push(new_var(format!("prev_running_claim")));

        // generate claim on lhs
        let lhs = horners_circuit_vars(&v, new_var(format!("claim_r")));
        self.pub_inputs.push(new_var(format!("claim_r")));

        // size of table (T -> mle)
        let sc_l = (self.dfa.trans.len() as f64).log2().ceil() as usize;
        println!("table size: {}", self.dfa.trans.len());
        println!("sum check rounds: {}", sc_l);

        self.sum_check_circuit(lhs, sc_l);

        // last eq circ on l-element point

        //TODO check ordering correct
        let mut eq_evals = vec![new_const(0)]; // dummy for horners
        for i in 0..self.batch_size + 1 {
            eq_evals.push(self.bit_eq_circuit(sc_l, i));
        }
        let eq_eval = horners_circuit_vars(&eq_evals, new_var(format!("claim_r")));

        // last_claim = eq_eval * next_running_claim
        let sum_check_domino = term(
            Op::Eq,
            vec![
                new_var(format!("sc_last_claim")),
                term(
                    Op::PfNaryOp(PfNaryOp::Mul),
                    vec![eq_eval, new_var(format!("next_running_claim"))],
                ),
            ],
        );
        self.assertions.push(sum_check_domino);
        self.pub_inputs.push(new_var(format!("next_running_claim")));

        self.r1cs_conv()
    }

    pub fn gen_wit_i(
        &self,
        batch_num: usize,
        current_state: usize,
        prev_running_claim_q: Option<Vec<Integer>>,
        prev_running_claim_v: Option<Integer>,
    ) -> (
        FxHashMap<String, Value>,
        usize,
        Option<Vec<Integer>>,
        Option<Integer>,
    ) {
        match self.batching {
            JBatching::NaivePolys => {
                let (wits, next_state) = self.gen_wit_i_polys(batch_num, current_state);
                (wits, next_state, None, None)
            }
            JBatching::Nlookup => self.gen_wit_i_nlookup(
                batch_num,
                current_state,
                prev_running_claim_q,
                prev_running_claim_v,
            ),
            JBatching::Plookup => todo!(), //gen_wit_i_plookup(round_num, current_state, doc, batch_size),
        }
    }

    fn gen_wit_i_nlookup(
        &self,
        batch_num: usize,
        current_state: usize,
        running_q: Option<Vec<Integer>>,
        running_v: Option<Integer>,
    ) -> (
        FxHashMap<String, Value>,
        usize,
        Option<Vec<Integer>>,
        Option<Integer>,
    ) {
        // generate T
        let mut table = vec![];
        for (ins, c, out) in self.dfa.deltas() {
            table.push(
                Integer::from(
                    (ins * self.dfa.nstates() * self.dfa.nchars())
                        + (out * self.dfa.nchars())
                        + self.dfa.ab_to_num(&c.to_string()),
                )
                .rem_floor(cfg().field().modulus()),
            );
        }

        let mut wits = FxHashMap::default();

        // TODO - what needs to be public?

        let sc_l = (self.dfa.trans.len() as f64).log2().ceil() as usize; // sum check rounds

        // generate claim r
        let claim_r = self.prover_random_from_seed(5); // TODO make general
        wits.insert(format!("claim_r"), new_wit(claim_r.clone()));

        // generate claim v's (well, v isn't a real named var, generate the states/chars)
        let mut state_i = current_state;
        let mut next_state = 0;
        let mut v = vec![];
        let mut q = vec![];
        for i in 1..=self.batch_size {
            let c = self.doc[batch_num * self.batch_size + i - 1].clone();
            next_state = self.dfa.delta(&state_i, &c.to_string()).unwrap();

            wits.insert(format!("state_{}", i - 1), new_wit(state_i));
            wits.insert(
                format!("char_{}", i - 1),
                new_wit(self.dfa.ab_to_num(&c.to_string())),
            );

            // v_i = (state_i * (#states*#chars)) + (state_i+1 * #chars) + char_i

            v.push(
                Integer::from(
                    (state_i * self.dfa.nstates() * self.dfa.nchars())
                        + (next_state * self.dfa.nchars())
                        + self.dfa.ab_to_num(&c.to_string()),
                )
                .rem_floor(cfg().field().modulus()),
            );

            q.push(table.iter().position(|val| val == &v[i - 1]).unwrap());

            println!(
                "state {:#?} -> {:#?} -> state {:#?} is {:#?} in table",
                state_i,
                self.dfa.ab_to_num(&c.to_string()),
                next_state,
                &q[i - 1]
            );

            state_i = next_state;
        }
        // last state
        wits.insert(format!("state_{}", self.batch_size), new_wit(next_state));

        // running claim about T (optimization)
        // if first
        let mut prev_running_q = match running_q {
            Some(q) => q,
            None => vec![Integer::from(0); sc_l],
        };
        let mut prev_running_v = match running_v {
            Some(v) => v,
            None => table[0].clone(),
        };
        v.push(prev_running_v.clone()); // todo get rid of v?
        wits.insert(
            format!("prev_running_claim"),
            new_wit(prev_running_v.clone()),
        );
        // q.push(prev_running_q);

        println!("v: {:#?}", v.clone());

        /*let (a, b) =
            prover_mle_partial_eval(&table, &running_q, &(0..table.len()).collect(), true, None);
        println!("eval of T @ running q {:#?}", b);
        */

        /*
        // need to round out table size
        let base: usize = 2;
        while table.len() < base.pow((table.len() as f32).log2().ceil() as u32) {
            table.push(
                Integer::from(
                    (self.dfa.nstates() * self.dfa.nstates() * self.dfa.nchars())
                        + (self.dfa.nstates() * self.dfa.nchars())
                        + self.dfa.nchars(),
                )
                .rem_floor(cfg().field().modulus()),
            );
        }
        */

        println!("table: {:#?}", table);

        // generate polynomial g's for sum check
        let mut sc_rs = vec![];
        let mut g_xsq = Integer::from(0);
        let mut g_x = Integer::from(0);
        let mut g_const = Integer::from(0);
        for i in 1..=sc_l {
            (g_xsq, g_x, g_const) =
                prover_mle_sum_eval(&table, &sc_rs, &q, &claim_r, Some(&prev_running_q));

            wits.insert(format!("sc_g_{}_xsq", i), new_wit(g_xsq.clone()));
            wits.insert(format!("sc_g_{}_x", i), new_wit(g_x.clone()));
            wits.insert(format!("sc_g_{}_const", i), new_wit(g_const.clone()));

            // new sumcheck rand for the round
            // generate rands
            let rand = self.prover_random_from_seed(i); // TODO make gen
            sc_rs.push(rand.clone());
            wits.insert(format!("sc_r_{}", i), new_wit(rand.clone()));
            println!(
                "{:#?}x^2 + {:#?}x + {:#?}",
                g_xsq.clone(),
                g_x.clone(),
                g_const.clone()
            );
        }
        // last claim = g_v(r_v)
        println!("sc rs {:#?}", sc_rs.clone());
        g_xsq *= &sc_rs[sc_rs.len() - 1];
        g_xsq *= &sc_rs[sc_rs.len() - 1];
        g_x *= &sc_rs[sc_rs.len() - 1];
        g_const += &g_x;
        g_const += &g_xsq;

        let last_claim = g_const.rem_floor(cfg().field().modulus());
        wits.insert(format!("sc_last_claim"), new_wit(last_claim.clone()));

        // generate last round eqs
        for i in 0..self.batch_size {
            // regular
            let q_name = format!("eq{}", i);
            for j in 0..sc_l {
                let qj = (q[i] >> j) & 1;
                wits.insert(format!("{}_q_{}", q_name, (sc_l - 1 - j)), new_wit(qj));
            }
        }
        for j in 0..sc_l {
            // running
            let q_name = format!("eq{}", v.len() - 1);
            wits.insert(
                format!("{}_q_{}", q_name, j),
                new_wit(prev_running_q[j].clone()),
            );
        }

        // update running claim
        let (_, next_running_v) = prover_mle_partial_eval(
            &table,
            &sc_rs.clone().into_iter().rev().collect(), // must fix
            &(0..table.len()).collect(),
            true,
            None,
        );
        let next_running_q = sc_rs.clone();
        wits.insert(
            format!("next_running_claim"),
            new_wit(next_running_v.clone()),
        );

        // sanity check - TODO eliminate
        // make rs
        /*let mut rs = vec![claim_r.clone()];
        for i in 1..(q.len() + 1) {
            rs.push(rs[i - 1].clone() * claim_r.clone());
        }
        let (_, eq_term) = prover_mle_partial_eval(
            &rs,
            &sc_rs.clone().into_iter().rev().collect(),
            &q,
            false,
            Some(&prev_running_q),
        );
        assert_eq!(
            last_claim,
            (eq_term * next_running_v.clone()).rem_floor(cfg().field().modulus())
        );
        */
        // other
        // wits.insert(format!("round_num"), new_wit(batch_num)); // TODO circuit for this wit

        // return
        println!("wits: {:#?}", wits);
        (wits, next_state, Some(next_running_q), Some(next_running_v))
    }

    // TODO BATCH SIZE (rn = 1)
    fn gen_wit_i_polys(
        &self,
        batch_num: usize,
        current_state: usize,
    ) -> (FxHashMap<String, Value>, usize) {
        let mut wits = FxHashMap::default();
        let mut state_i = current_state;
        let mut next_state = 0;

        for i in 0..self.batch_size {
            let doc_i = self.doc[batch_num * self.batch_size + i].clone();
            next_state = self.dfa.delta(&state_i, &doc_i.clone()).unwrap();

            wits.insert(format!("state_{}", i), new_wit(state_i));
            wits.insert(format!("char_{}", i), new_wit(self.dfa.ab_to_num(&doc_i)));

            state_i = next_state;
        }
        wits.insert(format!("state_{}", self.batch_size), new_wit(state_i));

        wits.insert("round_num".to_owned(), new_wit(batch_num));
        wits.insert("next_round_num".to_owned(), new_wit(batch_num + 1));

        (wits, next_state)
    }
}

#[cfg(test)]
mod tests {

    use crate::dfa::DFA;
    use crate::r1cs::*;
    use crate::regex::Regex;
    use circ::cfg;
    use circ::cfg::CircOpt;
    use serial_test::serial;
    type G1 = pasta_curves::pallas::Point;

    fn set_up_cfg() {
        println!("cfg set? {:#?}", cfg::is_cfg_set());
        if !cfg::is_cfg_set() {
            let m = "28948022309329048855892746252171976963363056481941647379679742748393362948097"
                .to_owned();
            let mut circ: CircOpt = Default::default();
            circ.field.custom_modulus = m.into();

            cfg::set(&circ);
        }
    }

    #[test]
    #[serial]
    fn mle_partial() {
        set_up_cfg();

        let table = vec![
            Integer::from(1),
            Integer::from(3),
            Integer::from(8),
            Integer::from(2),
            Integer::from(9),
            Integer::from(5),
            Integer::from(13),
            Integer::from(4),
        ];

        let v: Vec<i32> = vec![0, 1, -1];
        for x_1 in v.clone() {
            for x_2 in v.clone() {
                for x_3 in v.clone() {
                    let x = vec![Integer::from(x_3), Integer::from(x_2), Integer::from(x_1)];
                    let (coeff, con) = prover_mle_partial_eval(
                        &table,
                        &x,
                        &(0..table.len()).collect(),
                        true,
                        None,
                    );
                    println!(
                        "coeff {:#?}, con {:#?} @ {:#?}{:#?}{:#?}",
                        coeff, con, x_1, x_2, x_3
                    );

                    if ((x_1 == -1) ^ (x_2 == -1) ^ (x_3 == -1)) & !(x_1 + x_2 + x_3 == -3) {
                        if x_1 == -1 {
                            assert_eq!(
                                (coeff.clone() + con.clone()).rem_floor(cfg().field().modulus()),
                                table[(4 + x_2 * 2 + x_3) as usize]
                            );
                            assert_eq!(con.clone(), table[(x_2 * 2 + x_3) as usize]);
                        } else if x_2 == -1 {
                            assert_eq!(
                                (coeff.clone() + con.clone()).rem_floor(cfg().field().modulus()),
                                table[(x_1 * 4 + 2 + x_3) as usize]
                            );
                            assert_eq!(con.clone(), table[(x_1 * 4 + x_3) as usize]);
                        } else if x_3 == -1 {
                            assert_eq!(
                                (coeff.clone() + con.clone()).rem_floor(cfg().field().modulus()),
                                table[(x_1 * 4 + x_2 * 2 + 1) as usize]
                            );
                            assert_eq!(con.clone(), table[(x_1 * 4 + x_2 * 2) as usize]);
                        }
                    } else if (x_1 != -1) & (x_2 != -1) & (x_3 != -1) {
                        let e = x_1 * 4 + x_2 * 2 + x_3;
                        assert_eq!(table[e as usize], con);
                    }
                }
            }
        }
    }

    #[test]
    #[serial]
    fn mle_sums() {
        set_up_cfg();
        let table = vec![
            Integer::from(9),
            Integer::from(4),
            Integer::from(5),
            Integer::from(7),
        ];

        // generate polynomial g's for sum check
        let mut sc_rs = vec![];
        let claim_r = Integer::from(17);

        // round 1
        let (mut g_xsq, mut g_x, mut g_const) =
            prover_mle_sum_eval(&table, &sc_rs, &vec![1, 0], &claim_r, None);
        println!("mle sums {:#?}, {:#?}, {:#?}", g_xsq, g_x, g_const);

        let mut claim = claim_r.clone() * table[1].clone()
            + claim_r.clone() * claim_r.clone() * table[0].clone();
        assert_eq!(
            claim.rem_floor(cfg().field().modulus()),
            (g_xsq.clone() + g_x.clone() + g_const.clone() + g_const.clone())
                .rem_floor(cfg().field().modulus())
        );

        sc_rs.push(Integer::from(10));
        claim = Integer::from(100) * g_xsq + Integer::from(10) * g_x + g_const;

        // round 2
        (g_xsq, g_x, g_const) = prover_mle_sum_eval(&table, &sc_rs, &vec![1, 0], &claim_r, None);
        println!("mle sums {:#?}, {:#?}, {:#?}", g_xsq, g_x, g_const);
        assert_eq!(
            claim.rem_floor(cfg().field().modulus()),
            (g_xsq.clone() + g_x.clone() + g_const.clone() + g_const.clone())
                .rem_floor(cfg().field().modulus())
        );

        sc_rs.push(Integer::from(4));
        claim = Integer::from(16) * g_xsq + Integer::from(4) * g_x + g_const;

        // last V check
        let (_, mut con_a) = prover_mle_partial_eval(
            &table,
            &sc_rs.clone().into_iter().rev().collect(),
            &(0..table.len()).collect(),
            true,
            None,
        );
        //println!("mle sums {:#?}, {:#?}", g_x, g_const);

        let (_, con_b) = prover_mle_partial_eval(
            &vec![Integer::from(17), Integer::from(289)],
            &sc_rs.into_iter().rev().collect(),
            &vec![1, 0],
            false,
            None,
        );
        con_a *= &con_b;

        assert_eq!(
            claim.rem_floor(cfg().field().modulus()),
            con_a.rem_floor(cfg().field().modulus())
        );
    }

    fn test_func_no_hash(ab: String, rstr: String, doc: String, batch_sizes: Vec<usize>) {
        let r = Regex::new(&rstr);
        let dfa = DFA::new(&ab[..], r);
        //println!("{:#?}", dfa);

        let chars: Vec<String> = doc.chars().map(|c| c.to_string()).collect();

        for s in batch_sizes {
            let num_steps = doc.len() / s;
            for b in vec![JBatching::NaivePolys, JBatching::Nlookup] {
                let sc =
                    Sponge::<<G1 as Group>::Scalar, typenum::U2>::api_constants(Strength::Standard);
                let mut r1cs_converter =
                    R1CS::new(&dfa, &doc.chars().map(|c| c.to_string()).collect(), s, sc);
                r1cs_converter.batching = b.clone(); // hacky - don't do this outside tests

                let mut running_q = None;
                let mut running_v = None;
                match b {
                    JBatching::NaivePolys => {}
                    JBatching::Nlookup => {
                        if s <= 1 {
                            break;
                        }
                        running_q = None;
                        running_v = None;
                    }
                    JBatching::Plookup => todo!(),
                }

                println!("Batching {:#?}", r1cs_converter.batching);
                let (prover_data, _) = r1cs_converter.to_r1cs();
                //println!("{:#?}", prover_data.r1cs);
                let precomp = prover_data.clone().precompute;
                let mut current_state = dfa.get_init_state();

                for i in 0..num_steps {
                    let (values, next_state, running_q, running_v) = r1cs_converter.gen_wit_i(
                        i,
                        current_state,
                        running_q.clone(),
                        running_v.clone(),
                    );
                    //println!("VALUES ROUND {:#?}: {:#?}", i, values);
                    let extd_val = precomp.eval(&values);
                    println!("EXT VALUES ROUND {:#?}: {:#?}", i, extd_val);

                    prover_data.r1cs.check_all(&extd_val);
                    // for next i+1 round
                    current_state = next_state;
                }
                /* this got screwed up during merge, not sure where it should be @ Eli
                        println!(
                            "cost model: {:#?}",
                            R1CS::<<G1 as Group>::Scalar>::naive_cost_model_nohash(&dfa, dfa.is_match(&chars))
                        );
                        println!("actual cost: {:#?}", prover_data.r1cs.constraints().len());
                        assert!(
                            prover_data.r1cs.constraints().len()
                                <= R1CS::<<G1 as Group>::Scalar>::naive_cost_model_nohash(&dfa, dfa.is_match(&chars))
                        );
                    }

                                // for next i+1 round
                                current_state = next_state;
                            }
                */
                println!(
                    "cost model: {:#?}",
                    costs::full_round_cost_model_nohash(&dfa, s, b.clone(), dfa.is_match(&chars))
                );
                println!("actual cost: {:#?}", prover_data.r1cs.constraints().len());
                /*assert!(
                    prover_data.r1cs.constraints().len() as usize
                        <= costs::full_round_cost_model_nohash(
                            &dfa,
                            s,
                            b.clone(),
                            dfa.is_match(&chars)
                        )
                );*/
            }
        }
    }

    #[test]
    #[serial]
    fn naive_test() {
        set_up_cfg();
        test_func_no_hash(
            "a".to_string(),
            "a".to_string(),
            "aaaa".to_string(),
            vec![1, 2],
        );
    }

    #[test]
    #[serial]
    fn dfa_2() {
        set_up_cfg();
        test_func_no_hash(
            "ab".to_string(),
            "ab".to_string(),
            "ab".to_string(),
            vec![1],
        );
        test_func_no_hash(
            "abc".to_string(),
            "ab".to_string(),
            "ab".to_string(),
            vec![1],
        );
        test_func_no_hash(
            "abcdef".to_string(),
            "ab.*f".to_string(),
            "abcdeffff".to_string(),
            vec![1, 3],
        );
    }

    #[test]
    #[serial]
    fn dfa_star() {
        set_up_cfg();
        test_func_no_hash(
            "ab".to_string(),
            "a*b*".to_string(),
            "ab".to_string(),
            vec![1],
        );
        test_func_no_hash(
            "ab".to_string(),
            "a*b*".to_string(),
            "aaaaaabbbbbbbbbbbbbb".to_string(),
            vec![1, 2, 4],
        );
        test_func_no_hash(
            "ab".to_string(),
            "a*b*".to_string(),
            "aaaaaaaaaaab".to_string(),
            vec![1, 2, 4],
        );
    }

    #[test]
    #[serial]
    fn dfa_non_match() {
        set_up_cfg();
        test_func_no_hash("ab".to_string(), "a".to_string(), "b".to_string(), vec![1]);
        test_func_no_hash(
            "ab".to_string(),
            "a*b*".to_string(),
            "aaabaaaaaaaabbb".to_string(),
            vec![1, 2, 4],
        );

        test_func_no_hash(
            "abcd".to_string(),
            "a*b*cccb*".to_string(),
            "aaaaaaaaaabbbbbbbbbb".to_string(),
            vec![1, 2, 5, 10],
        );
    }

    #[test]
    #[serial]
    #[should_panic]
    fn dfa_bad_1() {
        set_up_cfg();
        test_func_no_hash("ab".to_string(), "a".to_string(), "c".to_string(), vec![1]);
    }
}
