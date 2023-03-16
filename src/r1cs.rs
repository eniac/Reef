use crate::dfa::DFA;
use bitvec::prelude::*;
use circ::cfg::*;
use circ::ir::{opt::*, proof::Constraints, term::*};
use circ::target::r1cs::{opt::reduce_linearities, trans::to_r1cs, ProverData, VerifierData};
use ff::PrimeField;
use fxhash::FxHashMap;
use generic_array::typenum;
use itertools::Itertools;
use neptune::{
    poseidon::PoseidonConstants,
    sponge::api::{IOPattern, SpongeAPI, SpongeOp},
    sponge::vanilla::{Mode, Sponge, SpongeTrait},
    Strength,
};
use rug::{
    integer::Order,
    ops::{RemRounding, RemRoundingAssign},
    rand::RandState,
    Integer,
};
use std::collections::HashSet;
use std::time::{Duration, Instant};
type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
use nova_snark::traits::Group; // use F here instead TODO

static POSEIDON_NUM: usize = 238; // jess took literal measurement and 238 is the real diff

#[derive(Debug, Clone)]
pub enum JBatching {
    NaivePolys,
    Plookup,
    Nlookup,
}

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

fn vanishing(xs: HashSet<usize>) -> Vec<Integer> {
    let mut evals = vec![];
    for xi in xs.into_iter() {
        evals.push((Integer::from(xi), Integer::from(0)));
    }
    // note we don't just want y = 0
    let mut rand = RandState::new();
    evals.push((
        cfg().field().modulus().clone().random_below(&mut rand),
        cfg().field().modulus().clone().random_below(&mut rand),
    )); // todo different? - check not in domain

    lagrange_field(evals)
}

fn lagrange_field(evals: Vec<(Integer, Integer)>) -> Vec<Integer> {
    let num_pts = evals.len();
    //println!("evals = {:#?}", evals);

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
                    new_l_i[j + 1] += &l_i[j];
                    new_l_i[j] -= &evals[k].0 * &l_i[j];
                    //println!("new_li j, j+1 = {:#?}, {:#?}", new_l_i[j], new_l_i[j + 1]);
                }
                l_i = new_l_i;
            }
        }

        //println!("li = {:#?}", l_i);
        // mult y's
        for k in 0..num_pts {
            coeffs[k] += &evals[i].1 * &l_i[k];
            coeffs[k].rem_floor_assign(cfg().field().modulus());
            //.div_rem_euc(&cfg().field().modulus());
            /*let (_, rem) = coeffs[k]
                .clone()
                .div_rem_euc(cfg().field().modulus().clone());
            coeffs[k] = rem;
            */
        }
    }

    return coeffs;
}
// calculate multilinear extension from evals of univariate
fn mle_from_pts(pts: Vec<Integer>) -> Vec<Integer> {
    let num_pts = pts.len();
    if num_pts == 1 {
        return vec![pts[0].clone()];
    }

    let h = num_pts / 2;
    println!("num_pts {}, h {}", num_pts, h);

    let mut l = mle_from_pts(pts[..h].to_vec());
    let mut r = mle_from_pts(pts[h..].to_vec());

    for i in 0..r.len() {
        r[i] -= &l[i];
        l.push(r[i].clone().rem_floor(cfg().field().modulus()));
    }

    l
}

// to compute g coeffs each sum check round
// "mle" is coeffs of mle [const, ...]
// "at" should be rev([rand_0, rand_i, ...., -1, {0,1}, {0,1} ...])
// the -1 slot is the "hole" (this will only create a degree 1 univar poly)
// returns [coeff (of "hole"), constant]
// if there is no hole, this will return [0, full result]
fn mle_partial_eval(mle: &Vec<Integer>, at: &Vec<Integer>) -> (Integer, Integer) {
    let base: usize = 2;
    println!("mle len {:#?} at len {:#?}", mle.len(), at.len());
    assert!(base.pow(at.len() as u32 - 1) <= mle.len());
    assert!(base.pow(at.len() as u32) >= mle.len()); // number of combos = coeffs
                                                     // mle could potentially be computed faster w/better organization .... ugh. we could be optimizing this till we die
                                                     // it's "prover work" tho, so whatever for now

    let mut coeff = Integer::from(0);
    let mut con = Integer::from(0);
    for i in 0..(mle.len()) {
        // for each term
        let mut new_term = mle[i].clone();
        //println!("new term {:#?}", new_term);
        let mut hole_included = false;
        for j in 0..at.len() {
            // for each possible var in this term
            hole_included = hole_included || (((i / base.pow(j as u32)) % 2 == 1) && (at[j] == -1));
            //println!("hole? {:#?}", hole_included);
            if ((i / base.pow(j as u32)) % 2 == 1) && (at[j] != -1) {
                // is this var in this term? AND is this var NOT the hole?
                new_term *= &at[j];
                //println!("new term after mul {:#?}", new_term);
                // note this loop is never triggered for constant :)
            }
        }
        // does this eval belong as a hole coeff? (does this term include the hole?)
        //println!("hole @ end of term? {:#?}", hole_included);
        if hole_included {
            coeff += new_term;
        } else {
            con += new_term;
        }
    }

    (
        coeff.rem_floor(cfg().field().modulus()),
        con.rem_floor(cfg().field().modulus()),
    )
}

// for sum check, computes the sum of many mle univar slices
// takes mle coeffs, and rands = [r_0, r_1,...], leaving off the hole and x_i's
fn mle_sum_evals(mle: &Vec<Integer>, rands: &Vec<Integer>) -> (Integer, Integer) {
    let mut sum_coeff = Integer::from(0);
    let mut sum_con = Integer::from(0);
    let hole = rands.len();
    let total = (mle.len() as f32).log2().ceil() as usize; // total # mle terms

    println!("#r: {:#?}, #total: {:#?}", hole, total);

    let num_x = total - hole - 1;
    assert!(num_x >= 0, "batch size too small for nlookup");
    let mut opts = vec![];
    for i in 0..num_x {
        opts.push(Integer::from(0));
        opts.push(Integer::from(1));
    }

    for mut combo in opts.into_iter().permutations(num_x).unique() {
        println!("combo: {:#?}", combo);

        let mut eval_at = rands.clone();
        eval_at.push(Integer::from(-1));
        eval_at.append(&mut combo);
        println!("eval at: {:#?}", eval_at.clone());
        let (coeff, con) = mle_partial_eval(mle, &eval_at.into_iter().rev().collect());
        println!("mle partial {:#?}, {:#?}", coeff, con);

        sum_coeff += &coeff;
        sum_con += &con;
    }
    println!("mle sums {:#?}, {:#?}", sum_coeff, sum_con);
    (
        sum_coeff.rem_floor(cfg().field().modulus()),
        sum_con.rem_floor(cfg().field().modulus()),
    )
}

fn horners_eval(coeffs: Vec<Integer>, x_lookup: Integer) -> Integer {
    let num_c = coeffs.len();
    let mut horners = coeffs[num_c - 1].clone() * &x_lookup;
    for i in (1..(num_c - 1)).rev() {
        let temp = coeffs[i].clone() + &horners;
        horners = temp * &x_lookup;
        //horners = &x_lookup * (&horners + &coeffs[i]);
    }
    horners += &coeffs[0];
    horners.rem_floor(cfg().field().modulus())
}

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

// if your mult terms are not yet CirC Terms
fn horners_circuit_const(coeffs: Vec<Integer>, x_lookup: Term) -> Term {
    let mut vars = vec![];
    for c in coeffs {
        vars.push(new_const(c));
    }

    horners_circuit_vars(&vars, x_lookup)
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
        let batching: JBatching = Self::opt_cost_model_select(
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
        let mut seed = F::from(s as u64); // TODO GEN
        let mut sponge = Sponge::new_with_constants(&self.pc, Mode::Simplex);
        let acc = &mut ();
        let parameter = IOPattern(vec![SpongeOp::Absorb(1), SpongeOp::Squeeze(1)]);

        sponge.start(parameter, None, acc);
        SpongeAPI::absorb(&mut sponge, 1, &[seed], acc);
        let rand = SpongeAPI::squeeze(&mut sponge, 1, acc);
        sponge.finish(acc).unwrap();

        Integer::from_digits(rand[0].to_repr().as_ref(), Order::Lsf)
    }

    fn lagrange_from_dfa(&self) -> Vec<Integer> {
        let mut evals = vec![];
        for (si, c, so) in self.dfa.deltas() {
            evals.push((
                Integer::from(si * self.dfa.nchars() + self.dfa.ab_to_num(&c.to_string())),
                Integer::from(so),
            ));
        }

        lagrange_field(evals)
    }

    fn r1cs_conv(&self) -> (ProverData, VerifierData) {
        let time = Instant::now();
        let cs = Computation::from_constraint_system_parts(
            self.assertions.clone(),
            self.pub_inputs.clone(),
        );

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
        let coeffs = self.lagrange_from_dfa();
        let lag_ms = l_time.elapsed().as_millis();
        //println!("lagrange coeffs {:#?}", coeffs);

        // hash the in state and char -> Integer::from(si * (dfa.chars.len() as usize) + dfa.ab_to_num(c))
        let x_lookup = term(
            Op::PfNaryOp(PfNaryOp::Add),
            vec![
                term(
                    Op::PfNaryOp(PfNaryOp::Mul),
                    vec![
                        new_var("current_state".to_owned()),
                        new_const(self.dfa.nchars()),
                    ],
                ),
                new_var("char".to_owned()),
            ],
        );

        // next_state
        let eq = term(
            Op::Eq,
            vec![
                new_var("next_state".to_owned()),
                horners_circuit_const(coeffs, x_lookup),
            ],
        );

        // final state (non) match check
        let mut vanishing_poly;
        let mut final_states = self.dfa.get_final_states();
        let mut non_final_states = self.dfa.get_non_final_states();

        let v_time = Instant::now();
        if self.is_match {
            //println!("MEMBERSHIP");
            //println!("in states: {:#?}", final_states);
            // proof of membership
            vanishing_poly =
                horners_circuit_const(vanishing(final_states), new_var("next_state".to_owned()));
        } else {
            //println!("NONMEMBERSHIP");
            //println!("in states: {:#?}", non_final_states);
            vanishing_poly = horners_circuit_const(
                vanishing(non_final_states),
                new_var("next_state".to_owned()),
            );
        }
        let vanish_ms = v_time.elapsed().as_millis();

        println!("lag {:#?}, vanish {:#?}", lag_ms, vanish_ms);

        let match_term = term(
            Op::Ite,
            vec![
                term(
                    Op::Eq,
                    vec![
                        new_var("round_num".to_owned()),
                        new_const(self.doc.len() - 1), // TODO make private
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

        self.assertions.push(eq);
        self.assertions.push(match_term);
        self.assertions.push(round_term);

        self.pub_inputs.push(new_var("round_num".to_owned()));
        self.pub_inputs.push(new_var("next_round_num".to_owned()));
        self.pub_inputs.push(new_var("current_state".to_owned()));
        self.pub_inputs.push(new_var("char".to_owned()));
        self.pub_inputs.push(new_var("next_state".to_owned()));

        self.r1cs_conv()
    }

    // for use at the end of sum check
    // eq([x0,x1,x2...],[e0,e1,e2...])
    fn bit_eq_circuit(&mut self, m: usize, q_name: String) -> Term {
        let mut eq = new_const(1); // dummy, not used

        for i in 0..m {
            let next = term(
                Op::PfNaryOp(PfNaryOp::Add),
                vec![
                    term(
                        Op::PfNaryOp(PfNaryOp::Mul),
                        vec![
                            new_var(format!("{}_q_{}", q_name, i)),
                            new_var(format!("eq_j_{}", i)),
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
                                        vec![new_var(format!("eq_j_{}", i))],
                                    ),
                                ],
                            ),
                        ],
                    ),
                ],
            );

            self.pub_inputs.push(new_var(format!("{}_q_{}", q_name, i)));
            self.pub_inputs.push(new_var(format!("eq_j_{}", i)));

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
            let g_j = term(
                Op::PfNaryOp(PfNaryOp::Add),
                vec![
                    new_var(format!("sc_g_{}_coeff", j)),
                    term(
                        Op::PfNaryOp(PfNaryOp::Add),
                        vec![
                            new_var(format!("sc_g_{}_const", j)),
                            new_var(format!("sc_g_{}_const", j)),
                        ],
                    ),
                ],
            );

            let claim_check = term(Op::Eq, vec![claim.clone(), g_j]);

            self.assertions.push(claim_check);
            self.pub_inputs.push(new_var(format!("sc_g_{}_coeff", j)));
            self.pub_inputs.push(new_var(format!("sc_g_{}_const", j)));
            self.pub_inputs.push(new_var(format!("sc_r_{}", j)));

            // "V" chooses rand r_{j} (P chooses this with hash)
            let r_j = new_var(format!("sc_r_{}", j));

            // update claim for the next round g_j(r_j)
            claim = term(
                Op::PfNaryOp(PfNaryOp::Add),
                vec![
                    new_var(format!("sc_g_{}_const", j)),
                    term(
                        Op::PfNaryOp(PfNaryOp::Mul),
                        vec![new_var(format!("sc_g_{}_coeff", j)), r_j],
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
        // generate v's
        let mut v = vec![];

        // TODO pub inputs -> can make which priv?
        for i in 0..self.batch_size {
            self.pub_inputs.push(new_var(format!("state_{}", i)));
            self.pub_inputs.push(new_var(format!("char_{}", i)));
        }

        // last state_batch is final "next_state" output
        // v_{batch-1} = (state_{batch-1}, c, state_batch)
        // v_batch = T eval check (optimization)
        self.pub_inputs
            .push(new_var(format!("state_{}", self.batch_size)));

        for i in 1..self.batch_size {
            // v_i = (state_i * (#states*#chars)) + (state_i+1 * #chars) + char_i
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
                    new_var(format!("char_{}", i)),
                ],
            );
            v.push(v_i);
        }
        //v.push(new_var(format!("v_for_T"))); // the optimization T(j) check

        // generate claim on lhs
        let mut lhs = horners_circuit_vars(&v, new_var(format!("claim_r")));
        self.pub_inputs.push(new_var(format!("claim_r")));

        // size of table (T -> mle)
        let sc_l = (self.dfa.trans.len() as f64).log2().ceil() as usize;
        println!("table size: {}", self.dfa.trans.len());
        println!("sum check rounds: {}", sc_l);

        self.sum_check_circuit(lhs, sc_l);

        // calculate eq's
        // TODO check ordering correct
        // TODO pub wits for eq circ
        let mut eq_evals = vec![];
        for i in 0..v.len() {
            eq_evals.push(self.bit_eq_circuit(sc_l, format!("eq{}", i)));
        }
        horners_circuit_vars(&eq_evals, new_var(format!("claim_r")));

        // add last v_m+1 check (for T(j) optimization) - TODO

        self.r1cs_conv()
    }

    pub fn gen_wit_i(
        &self,
        round_num: usize,
        current_state: usize,
    ) -> (FxHashMap<String, Value>, usize) {
        match self.batching {
            JBatching::NaivePolys => self.gen_wit_i_polys(round_num, current_state),
            JBatching::Nlookup => self.gen_wit_i_nlookup(round_num, current_state),
            JBatching::Plookup => todo!(), //gen_wit_i_plookup(round_num, current_state, doc, batch_size),
        }
    }

    fn gen_wit_i_nlookup(
        &self,
        batch_num: usize,
        current_state: usize,
    ) -> (FxHashMap<String, Value>, usize) {
        let mut wits = FxHashMap::default();

        // TODO - what needs to be public?

        // generate claim r
        let claim_r = self.prover_random_from_seed(5); // TODO make general

        wits.insert(format!("claim_r"), new_wit(claim_r));

        // generate claim v's (well, v isn't a real named var, generate the states/chars)
        let mut state_i = current_state;
        let mut next_state = 0;
        let mut v = vec![];
        for i in 0..self.batch_size {
            let c = self.doc[batch_num * self.batch_size + i].clone();
            next_state = self.dfa.delta(&state_i, &c.to_string()).unwrap();

            wits.insert(format!("state_{}", i), new_wit(state_i));
            wits.insert(
                format!("char_{}", i),
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
        }
        // last state
        wits.insert(format!("state_{}", self.batch_size), new_wit(state_i));

        //v.push(Integer::from(4)); // dummy!! TODO
        //wits.insert(format!("v_for_T"), new_wit(4));

        println!("v: {:#?}", v.clone());

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

        println!("table: {:#?}", table);
        let mle_T = mle_from_pts(table.clone());

        // generate polynomial g's for sum check
        let mut sc_rs = vec![];

        println!("T mle coeffs: {:#?}", mle_T);
        let mut g_coeff = Integer::from(0);
        let mut g_const = Integer::from(0);
        for i in 1..=self.batch_size {
            // going to use thaler numbering for sum check
            // i don't like it either
            // + 1 {

            (g_coeff, g_const) = mle_sum_evals(&mle_T, &sc_rs);

            wits.insert(format!("sc_g_{}_coeff", i), new_wit(g_coeff.clone()));
            wits.insert(format!("sc_g_{}_const", i), new_wit(g_const.clone()));

            // new sumcheck rand for the round
            let rand = self.prover_random_from_seed(i); // TODO make gen
            sc_rs.push(rand.clone());
            wits.insert(format!("sc_r_{}", i), new_wit(rand));
        }
        // last claim = g_v(r_v)
        g_coeff *= &sc_rs[sc_rs.len() - 1];
        g_const += &g_coeff;
        let last_claim = g_const.rem_floor(cfg().field().modulus());
        wits.insert(format!("sc_last_claim"), new_wit(last_claim));

        // generate sum check eq vals
        // find qi list
        let mut qis = vec![];
        for i in 0..table.len() {
            //v.len() {
            // TODO clone elim
            qis.push(table.clone().into_iter().position(|t| t == v[i]).unwrap());

            // convert to bits
            let qi_bits: Vec<Integer> = (0..((table.len() as f32).log2().ceil() as usize))
                .map(|n| Integer::from((qis[i] >> n) & 1))
                .collect();
            println!("qi bits {:#?}", qi_bits);
            let temp_eval = mle_partial_eval(&mle_T, &qi_bits.into_iter().rev().collect());
            println!("T eval {:#?}", temp_eval);

            /*for b in bits {
                wits.insert(format!("eq{}_q_{}", i, b), new_wit(BIT));

            }*/
        }
        println!("qis {:#?}", qis);

        // sanity check, lhs = rhs

        // other
        // wits.insert(format!("round_num"), new_wit(batch_num)); // TODO circuit for this wit
        println!("wits: {:#?}", wits);
        (wits, next_state)
    }

    // TODO BATCH SIZE (rn = 1)
    fn gen_wit_i_polys(
        &self,
        round_num: usize,
        current_state: usize,
    ) -> (FxHashMap<String, Value>, usize) {
        let doc_i = self.doc[round_num].clone();
        let next_state = self.dfa.delta(&current_state, &doc_i.clone()).unwrap();

        let values: FxHashMap<String, Value> = vec![
            ("round_num".to_owned(), new_wit(round_num)),
            ("next_round_num".to_owned(), new_wit(round_num + 1)),
            ("current_state".to_owned(), new_wit(current_state)),
            ("char".to_owned(), new_wit(self.dfa.ab_to_num(&doc_i))),
            ("next_state".to_owned(), new_wit(next_state)),
        ]
        .into_iter()
        .collect();

        return (values, next_state);
    }

    pub fn naive_cost_model_nohash(dfa: &'a DFA, is_match: bool) -> usize {
        // horners selection - poly of degree m * n - 1, +1 for x_lookup
        let mut cost = dfa.nstates() * dfa.nchars();

        // vanishing selection for final check
        // poly of degree (# final states - 1)
        // (alt, # non final states - 1)
        // + 3 for round_num selection + 1 for next_round_num
        if is_match {
            cost += dfa.get_final_states().len() as usize + 3;
        } else {
            cost += dfa.get_non_final_states().len() as usize + 3;
        }

        cost
    }

    pub fn plookup_cost_model_nohash(dfa: &'a DFA, batch_size: usize) -> usize {
        let mut cost = 0;
        // 2 prove sequence constructions
        cost = dfa.nstates() * dfa.nchars();
        cost += batch_size;
        cost = cost * 2;

        //Batchsize creating v_i
        cost += 3 * batch_size;

        //Schwarz Zippel evals of sequence
        cost += 2 * ((dfa.nstates() * dfa.nchars()) + batch_size);

        cost
    }

    pub fn plookup_cost_model_hash(dfa: &'a DFA, batch_size: usize) -> usize {
        let mut cost: usize = Self::plookup_cost_model_nohash(dfa, batch_size);

        //Randomized difference
        cost += 2 * POSEIDON_NUM;

        //Poseidon hash in Schwarz Zippel
        cost += POSEIDON_NUM;

        cost
    }

    pub fn nlookup_cost_model_nohash(dfa: &'a DFA, batch_size: usize) -> usize {
        let mn: usize = dfa.nstates() * dfa.ab.len();
        let log_mn: usize = (mn as f32).log2().ceil() as usize;
        let mut cost: usize = 0;

        //Multiplications
        cost += batch_size + 1;

        //Sum-check additions
        cost += log_mn * 3;

        //eq calc
        cost += (batch_size + 1) * log_mn;

        //horners
        cost += batch_size * 2;

        //v_i creation
        cost += batch_size * 3;

        cost
    }

    pub fn nlookup_cost_model_hash(dfa: &'a DFA, batch_size: usize) -> usize {
        let mn: usize = dfa.nstates() * dfa.ab.len();
        let log_mn: usize = (mn as f32).log2().ceil() as usize;
        let mut cost = Self::nlookup_cost_model_nohash(dfa, batch_size);

        //R generation hashes
        cost += POSEIDON_NUM;

        //Sum check poseidon hashes
        cost += log_mn * POSEIDON_NUM;

        cost
    }

    pub fn full_round_cost_model_nohash(
        dfa: &'a DFA,
        batch_size: usize,
        lookup_type: JBatching,
        is_match: bool,
    ) -> usize {
        let mut cost = match lookup_type {
            JBatching::NaivePolys => Self::naive_cost_model_nohash(dfa, is_match) * batch_size,
            JBatching::Nlookup => Self::nlookup_cost_model_nohash(dfa, batch_size),
            JBatching::Plookup => Self::plookup_cost_model_nohash(dfa, batch_size),
        };
        cost
    }

    pub fn full_round_cost_model(
        dfa: &'a DFA,
        batch_size: usize,
        lookup_type: JBatching,
        is_match: bool,
    ) -> usize {
        let mut cost = match lookup_type {
            JBatching::NaivePolys => Self::naive_cost_model_nohash(dfa, is_match) * batch_size,
            JBatching::Nlookup => Self::nlookup_cost_model_hash(dfa, batch_size),
            JBatching::Plookup => Self::plookup_cost_model_hash(dfa, batch_size),
        };
        cost += POSEIDON_NUM * batch_size;
        cost
    }

    pub fn opt_cost_model_select_with_batch(
        dfa: &'a DFA,
        batch_size: usize,
        is_match: bool,
        doc_length: usize,
    ) -> (JBatching, usize) {
        let mut opt_batching: JBatching = JBatching::NaivePolys;
        let mut cost: usize =
            Self::full_round_cost_model(dfa, batch_size, JBatching::NaivePolys, is_match);

        if Self::full_round_cost_model(dfa, batch_size, JBatching::Nlookup, is_match) < cost {
            cost = Self::full_round_cost_model(dfa, batch_size, JBatching::Nlookup, is_match);
            opt_batching = JBatching::Nlookup;
        }

        if Self::full_round_cost_model(dfa, batch_size, JBatching::Plookup, is_match) < cost {
            cost = Self::full_round_cost_model(dfa, batch_size, JBatching::Plookup, is_match);
            opt_batching = JBatching::Plookup;
        }

        (opt_batching, cost * (doc_length / batch_size))
    }
    pub fn opt_cost_model_select(
        dfa: &'a DFA,
        batch_range_lower: usize,
        batch_range_upper: usize,
        is_match: bool,
        doc_length: usize,
    ) -> JBatching {
        let mut opt_batching: JBatching = JBatching::NaivePolys;
        let mut cost = Self::full_round_cost_model(
            dfa,
            2 << batch_range_lower,
            JBatching::NaivePolys,
            is_match,
        );

        for n in batch_range_lower..batch_range_upper + 1 {
            let mut batching_and_cost: (JBatching, usize) =
                Self::opt_cost_model_select_with_batch(dfa, 2 << n, is_match, doc_length);
            if batching_and_cost.1 < cost {
                cost = batching_and_cost.1;
                opt_batching = batching_and_cost.0;
            }
        }
        opt_batching
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

    fn set_up_cfg(m: String) {
        println!("cfg set? {:#?}", cfg::is_cfg_set());
        if !cfg::is_cfg_set() {
            let m = "1019".to_owned();
            let mut circ: CircOpt = Default::default();
            circ.field.custom_modulus = m.into();

            cfg::set(&circ);
        }
    }

    #[test]
    #[serial]
    fn basic_lg() {
        set_up_cfg("1019".to_owned());
        //set_up_cfg("79".to_owned());

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

    #[test]
    #[serial]
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
            Integer::from(742),
            Integer::from(929),
            Integer::from(245),
        ];

        assert_eq!(coeffs, expected);
    }

    fn test_func_no_hash(ab: String, rstr: String, doc: String) {
        let r = Regex::new(&rstr);
        let mut dfa = DFA::new(&ab[..], r);
        //println!("{:#?}", dfa);

        let batch_size = 2 as usize;
        let mut chars: Vec<String> = doc.chars().map(|c| c.to_string()).collect();
        let num_steps = doc.len();

        let sc = Sponge::<<G1 as Group>::Scalar, typenum::U2>::api_constants(Strength::Standard);
        let mut r1cs_converter =
            R1CS::new(&dfa, &doc.chars().map(|c| c.to_string()).collect(), 1, sc);

        for b in vec![JBatching::Nlookup] {
            r1cs_converter.batching = b.clone();
            println!("Batching {:#?}", r1cs_converter.batching);
            //println!("{:#?}", prover_data.r1cs);
            let (prover_data, _) = r1cs_converter.to_r1cs();
            let precomp = prover_data.clone().precompute;
            let mut current_state = dfa.get_init_state();

            for i in 0..num_steps {
                let (values, next_state) = r1cs_converter.gen_wit_i(i, current_state);
                //println!("VALUES ROUND {:#?}: {:#?}", i, values);
                let extd_val = precomp.eval(&values);

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
                R1CS::<<G1 as Group>::Scalar>::full_round_cost_model_nohash(
                    &dfa,
                    batch_size,
                    b.clone(),
                    dfa.is_match(&chars)
                )
            );
            println!("actual cost: {:#?}", prover_data.r1cs.constraints().len());
            assert!(
                prover_data.r1cs.constraints().len() as usize
                    <= R1CS::<<G1 as Group>::Scalar>::full_round_cost_model_nohash(
                        &dfa,
                        batch_size,
                        b.clone(),
                        dfa.is_match(&chars)
                    )
            );
        }
    }

    #[test]
    #[serial]
    fn naive_test() {
        test_func_no_hash("a".to_string(), "a".to_string(), "aaaa".to_string());
    }
    /*
        #[test]
        fn dfa_2() {
            test_func_no_hash("ab".to_string(), "ab".to_string(), "ab".to_string());
            test_func_no_hash("abc".to_string(), "ab".to_string(), "ab".to_string());
        }

        #[test]
        fn dfa_star() {
            test_func_no_hash("ab".to_string(), "a*b*".to_string(), "ab".to_string());
            test_func_no_hash(
                "ab".to_string(),
                "a*b*".to_string(),
                "aaaabbbbbbbbbbbbbb".to_string(),
            );
            test_func_no_hash(
                "ab".to_string(),
                "a*b*".to_string(),
                "aaaaaaaaaaab".to_string(),
            );
        }

        #[test]
        fn dfa_non_match() {
            test_func_no_hash("ab".to_string(), "a".to_string(), "b".to_string());
            test_func_no_hash(
                "ab".to_string(),
                "a*b*".to_string(),
                "aaabaaaaaaaab".to_string(),
            );
        }

        #[test]
        #[should_panic]
        fn dfa_bad_1() {
            test_func_no_hash("ab".to_string(), "a".to_string(), "c".to_string());
        }
    */
    #[test]
    fn mle_1() {
        let mut rand = RandState::new();

        let mut points: Vec<(Integer, Integer)> = vec![];
        for x in 0..8 {
            let mut lim = Integer::from(1019);
            lim.random_below_mut(&mut rand);
            points.push((Integer::from(x), lim));
        }
        println!("points: {:#?}", points);
        let uni = points.clone().into_iter().map(|(_, y)| y).collect();

        let coeffs = lagrange_field(points);
        println!("coeffs: {:#?}", coeffs);

        let mle = mle_from_pts(uni);
        println!("mle coeffs: {:#?}", mle);

        for x in vec![Integer::from(0), Integer::from(1)] {
            for y in vec![Integer::from(0), Integer::from(1)] {
                for z in vec![Integer::from(0), Integer::from(1)] {
                    let f: Integer = z.clone() + 2 * y.clone() + 4 * x.clone();

                    let uni_out = horners_eval(coeffs.clone(), f);

                    /*
                    let mle_out = &mle[0]
                        + (&mle[1] * &z)
                        + (&mle[2] * &y)
                        + (&mle[3] * &y * &z)
                        + (&mle[4] * &x)
                        + (mle[5] * &x * &z)
                        + (mle[6] * &x * &y)
                        + (mle[7] * &x * &y * &z);
                    */

                    let vec = vec![z.clone(), y.clone(), x.clone()];
                    let mle_eval = mle_partial_eval(&mle, &vec);

                    assert_eq!(mle_eval.1, uni_out);
                    //assert_eq!(mle_out, mle_eval.1);
                }
            }
        }
    }

    #[test]
    fn mle_sums() {
        let mle_T = vec![
            Integer::from(9),
            Integer::from(4),
            Integer::from(5),
            Integer::from(7),
        ];

        // generate polynomial g's for sum check
        let mut sc_rs = vec![];

        // round 1
        let (mut g_coeff, mut g_const) = mle_sum_evals(&mle_T, &sc_rs);
        assert_eq!(g_coeff, Integer::from(17));
        assert_eq!(g_const, Integer::from(22));

        sc_rs.push(Integer::from(10));

        // round 2
        (g_coeff, g_const) = mle_sum_evals(&mle_T, &sc_rs);
        assert_eq!(g_coeff, Integer::from(74));
        assert_eq!(g_const, Integer::from(59));

        sc_rs.push(Integer::from(4));

        // last V check
        (g_coeff, g_const) = mle_partial_eval(&mle_T, &sc_rs.into_iter().rev().collect());
        assert_eq!(g_coeff, Integer::from(0));
        assert_eq!(g_const, Integer::from(355));
    }
}
