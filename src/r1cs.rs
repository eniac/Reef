use crate::deriv::nullable;
use crate::dfa::DFA;
use circ::cfg::*;
use circ::ir::opt::*;
use circ::ir::proof::Constraints;
use circ::ir::term::*;
use circ::target::r1cs::{
    opt::reduce_linearities, trans::to_r1cs, Lc, ProverData, R1cs, VerifierData,
};
use ff::PrimeField;
use fxhash::FxHashMap;
use generic_array::typenum;
use itertools::Itertools;
use neptune::{
    poseidon::{Arity, HashMode, Poseidon, PoseidonConstants},
    Strength,
};
use nova_snark::{
    traits::{circuit::TrivialTestCircuit, Group},
    CompressedSNARK, PublicParams, RecursiveSNARK, StepCounterType, FINAL_EXTERNAL_COUNTER,
};
use rug::rand::RandState;
use rug::Integer;

type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;

static POSEIDON_NUM: usize = 237;

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

fn vanishing(xs: Vec<u64>) -> Vec<Integer> {
    let mut evals = vec![];
    for xi in xs {
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
                    new_l_i[j + 1] = add(&new_l_i[j + 1], &l_i[j]);
                    new_l_i[j] = sub(&new_l_i[j], &mul(&evals[k].0, &l_i[j]));
                    //println!("new_li j, j+1 = {:#?}, {:#?}", new_l_i[j], new_l_i[j + 1]);
                }
                l_i = new_l_i;
            }
        }

        //println!("li = {:#?}", l_i);
        // mult y's
        for k in 0..num_pts {
            coeffs[k] = add(&coeffs[k], &mul(&evals[i].1, &l_i[k]));
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
    let mut l = mle_from_pts(pts[..h].to_vec());
    let r = mle_from_pts(pts[h..].to_vec());

    for i in 0..r.len() {
        l.push(sub(&r[i], &l[i]));
    }

    l
}

fn horners_eval(coeffs: Vec<Integer>, x_lookup: Integer) -> Integer {
    let num_c = coeffs.len();
    let mut horners = mul(&coeffs[num_c - 1], &x_lookup);
    for i in (1..(num_c - 1)).rev() {
        horners = mul(&x_lookup, &add(&horners, &coeffs[i]));
    }
    horners = add(&horners, &coeffs[0]);
    horners
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
    dfa: &'a DFA<'a>,
    batching: JBatching,
    assertions: Vec<Term>,
    pub_inputs: Vec<Term>,
    batch_size: usize,
    doc: String,
    is_match: bool,
    pc: PoseidonConstants<F, typenum::U2>,
    commitment: Option<F>,
}

impl<'a, F: PrimeField> R1CS<'a, F> {
    pub fn new(
        dfa: &'a DFA<'a>,
        doc: String,
        batch_size: usize,
        pcs: PoseidonConstants<F, typenum::U2>,
    ) -> Self {
        let is_match = dfa.is_match(&doc);
        println!("Match? {:#?}", is_match);

        // run cost model (with Poseidon) to decide batching
        let batching: JBatching = Self::opt_cost_model_select(&dfa, batch_size, dfa.is_match(&doc));

        Self {
            dfa,
            batching: JBatching::NaivePolys, // TODO
            assertions: Vec::new(),
            pub_inputs: Vec::new(),
            batch_size: batch_size,
            doc: doc,
            is_match: is_match,
            pc: pcs,
            commitment: None,
        }
    }

    pub fn gen_commitment(&mut self) {
        let mut hash = F::from(0);
        for c in self.doc.chars() {
            let mut data = vec![hash, F::from(self.dfa.ab_to_num(c))];
            let mut p = Poseidon::<F, typenum::U2>::new_with_preimage(&data, &self.pc);
            hash = p.hash();
        }
        println!("commitment = {:#?}", hash.clone());
        self.commitment = Some(hash);
    }

    fn lagrange_from_dfa(&self) -> Vec<Integer> {
        let mut evals = vec![];
        for (si, c, so) in self.dfa.deltas() {
            evals.push((
                Integer::from(si * (self.dfa.chars.len() as u64) + self.dfa.ab_to_num(c)),
                Integer::from(so),
            ));
        }

        lagrange_field(evals)
    }

    fn r1cs_conv(&self) -> (ProverData, VerifierData) {
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

        println!(
            "Final R1cs size (no hashes): {}",
            prover_data.r1cs.constraints().len()
        );

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
        let coeffs = self.lagrange_from_dfa();
        //println!("lagrange coeffs {:#?}", coeffs);

        // hash the in state and char -> Integer::from(si * (dfa.chars.len() as u64) + dfa.ab_to_num(c))
        let x_lookup = term(
            Op::PfNaryOp(PfNaryOp::Add),
            vec![
                term(
                    Op::PfNaryOp(PfNaryOp::Mul),
                    vec![
                        new_var("current_state".to_owned()),
                        new_const(self.dfa.chars.len() as u64),
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
        let mut final_states = vec![];
        let mut non_final_states = vec![];
        for (k, v) in self.dfa.states.clone() {
            if nullable(&k) {
                final_states.push(v);
            } else {
                non_final_states.push(v);
            }
        }

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

        let match_term = term(
            Op::Ite,
            vec![
                term(
                    Op::Eq,
                    vec![
                        new_var("round_num".to_owned()),
                        new_const(self.doc.len() - 1),
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
    // m = dim of bool hypercube
    fn bit_eq_circuit(&self, m: u64, q_name: String) -> Term {
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
            if i == 0 {
                eq = next;
            } else {
                eq = term(Op::PfNaryOp(PfNaryOp::Mul), vec![eq, next]);
            }
        }

        eq
    }

    // C_1 = LHS/"claim"
    fn sum_check_circuit(&mut self, C_1: Term, num_rounds: u64) {
        // first round claim
        let mut claim = C_1.clone();

        for j in 0..num_rounds {
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

            if j == num_rounds - 1 {
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

        // TODO pub inputs
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
                                    new_const(self.dfa.nstates() * self.dfa.chars.len()),
                                ],
                            ),
                            term(
                                Op::PfNaryOp(PfNaryOp::Mul),
                                vec![
                                    new_var(format!("state_{}", i)),
                                    new_const(self.dfa.chars.len() as u64),
                                ],
                            ),
                        ],
                    ),
                    new_var(format!("char_{}", i)),
                ],
            );
            v.push(v_i);
        }

        // generate claim on lhs
        let mut lhs = horners_circuit_vars(&v, new_var(format!("claim_r")));
        self.pub_inputs.push(new_var(format!("claim_r")));

        // size of table (T -> mle)
        let sc_l = (self.dfa.trans.len() as f64).log2().ceil() as u64;
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
        current_state: u64,
    ) -> (FxHashMap<String, Value>, u64) {
        match self.batching {
            JBatching::NaivePolys => self.gen_wit_i_polys(round_num, current_state),
            JBatching::Nlookup => self.gen_wit_i_nlookup(round_num, current_state),
            JBatching::Plookup => todo!(), //gen_wit_i_plookup(round_num, current_state, doc, batch_size),
        }
    }

    fn gen_wit_i_nlookup(
        &self,
        batch_num: usize,
        current_state: u64,
    ) -> (FxHashMap<String, Value>, u64) {
        let mut wits = FxHashMap::default();

        // TODO - what needs to be public?

        // generate claim r
        let pc = PoseidonConstants::<<G1 as Group>::Scalar, typenum::U2>::new_with_strength(
            Strength::Standard,
        );
        let mut data = vec![<G1 as Group>::Scalar::zero(), <G1 as Group>::Scalar::zero()];

        let mut p = Poseidon::<<G1 as Group>::Scalar, typenum::U2>::new_with_preimage(&data, &pc);
        let claim_r: <G1 as Group>::Scalar = p.hash();

        // TODO GET INT wits.insert(format!("claim_r"), new_wit(claim_r));

        // generate claim v's (well, v isn't a real named var, generate the states/chars)
        let mut state_i = current_state;
        let mut next_state = 0;
        for i in 0..self.batch_size {
            let c = self
                .doc
                .chars()
                .nth(batch_num * self.batch_size + i)
                .unwrap();
            next_state = self.dfa.delta(state_i, c).unwrap();

            wits.insert(format!("state_{}", i), new_wit(state_i));
            wits.insert(format!("char_{}", i), new_wit(self.dfa.ab_to_num(c)));

            state_i = next_state;
        }
        // todo last state (?)

        // generate polynomial g's for sum check

        // generate sum check r's

        // other
        wits.insert(format!("round_num"), new_wit(batch_num)); // TODO circuit for this wit

        (wits, next_state)
    }

    // TODO BATCH SIZE (rn = 1)
    fn gen_wit_i_polys(
        &self,
        round_num: usize,
        current_state: u64,
    ) -> (FxHashMap<String, Value>, u64) {
        let doc_i = self.doc.chars().nth(round_num).unwrap();
        let next_state = self.dfa.delta(current_state, doc_i).unwrap();

        let values: FxHashMap<String, Value> = vec![
            ("round_num".to_owned(), new_wit(round_num)),
            ("next_round_num".to_owned(), new_wit(round_num + 1)),
            ("current_state".to_owned(), new_wit(current_state)),
            ("char".to_owned(), new_wit(self.dfa.ab_to_num(doc_i))),
            ("next_state".to_owned(), new_wit(next_state)),
        ]
        .into_iter()
        .collect();

        return (values, next_state);
    }

    pub fn naive_cost_model_nohash(dfa: &'a DFA<'a>, is_match: bool) -> usize {
        // horners selection - poly of degree m * n - 1, +1 for x_lookup
        let mut cost = dfa.nstates() * dfa.chars.len();

        // vanishing selection for final check
        // poly of degree (# final states - 1)
        // (alt, # non final states - 1)
        // + 3 for round_num selection + 1 for next_round_num
        if is_match {
            cost += dfa.get_final_states().len() + 3;
        } else {
            cost += (dfa.nstates() - dfa.get_final_states().len()) + 3;
        }

        cost
    }

    pub fn plookup_cost_model_nohash(dfa: &'a DFA<'a>, batch_size: usize) -> usize {
        let mut cost = 0;
        // 2 prove sequence constructions
        cost = dfa.nstates() * dfa.chars.len();
        cost += batch_size;
        cost = cost * 2;

        //Batchsize creating v_i
        cost += 3 * batch_size;

        //Schwarz Zippel evals of sequence
        cost += 2 * ((dfa.nstates() * dfa.chars.len()) + batch_size);

        cost
    }

    pub fn plookup_cost_model_hash(dfa: &'a DFA<'a>, batch_size: usize) -> usize {
        let mut cost: usize = Self::plookup_cost_model_nohash(dfa, batch_size);

        //Randomized difference
        cost += 2 * POSEIDON_NUM;

        //Poseidon hash in Schwarz Zippel
        cost += POSEIDON_NUM;

        cost
    }

    pub fn nlookup_cost_model_nohash(dfa: &'a DFA<'a>, batch_size: usize) -> usize {
        let mn: usize = dfa.nstates() * dfa.chars.len();
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

    pub fn nlookup_cost_model_hash(dfa: &'a DFA<'a>, batch_size: usize) -> usize {
        let mn: usize = dfa.nstates() * dfa.chars.len();
        let log_mn: usize = (mn as f32).log2().ceil() as usize;
        let mut cost = Self::nlookup_cost_model_nohash(dfa, batch_size);

        //R generation hashes
        cost += POSEIDON_NUM;

        //Sum check poseidon hashes
        cost += log_mn * POSEIDON_NUM;

        cost
    }

    pub fn full_round_cost_model(
        dfa: &'a DFA<'a>,
        batch_size: usize,
        lookup_type: JBatching,
        is_match: bool,
    ) -> usize {
        let mut cost: usize = match lookup_type {
            JBatching::NaivePolys => Self::naive_cost_model_nohash(dfa, is_match) * batch_size,
            JBatching::Nlookup => Self::nlookup_cost_model_hash(dfa, batch_size),
            JBatching::Plookup => Self::plookup_cost_model_hash(dfa, batch_size),
        };
        cost += POSEIDON_NUM * batch_size;
        cost
    }

    pub fn opt_cost_model_select(dfa: &'a DFA<'a>, batch_size: usize, is_match: bool) -> JBatching {
        let mut opt_batching: JBatching = JBatching::NaivePolys;
        let mut cost: usize =
            Self::full_round_cost_model(dfa, batch_size, JBatching::NaivePolys, is_match);

        if cost < 10000 {
            cost = 10000
        }

        if Self::full_round_cost_model(dfa, batch_size, JBatching::Nlookup, is_match) < cost {
            cost = Self::full_round_cost_model(dfa, batch_size, JBatching::Nlookup, is_match);
            opt_batching = JBatching::Nlookup;
        }

        if Self::full_round_cost_model(dfa, batch_size, JBatching::Plookup, is_match) < cost {
            cost = Self::full_round_cost_model(dfa, batch_size, JBatching::Plookup, is_match);
            opt_batching = JBatching::Plookup;
        }
        opt_batching
    }
}

#[cfg(test)]
mod tests {

    use crate::deriv::*;
    use crate::dfa::DFA;
    use crate::parser::regex_parser;
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
    fn lg_1() {
        //set_up_cfg("1019".to_owned());

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

    fn naive_test_func_no_hash(ab: String, regex: String, doc: String) {
        //set_up_cfg("1019".to_owned());

        let r = regex_parser(&regex, &ab);
        let mut dfa = DFA::new(&ab[..]);
        mk_dfa(&r, &ab, &mut dfa);
        //println!("{:#?}", dfa);

        let mut chars = doc.chars();
        let num_steps = doc.chars().count();

        let mut r1cs_converter = R1CS::new(&dfa, doc.clone(), 1, pc);
        let (prover_data, _) = r1cs_converter.to_r1cs();
        let precomp = prover_data.clone().precompute;
        //println!("{:#?}", prover_data);

        let mut current_state = dfa.get_init_state();

        for i in 0..num_steps {
            let (values, next_state) = r1cs_converter.gen_wit_i(i, current_state);
            //println!("VALUES ROUND {:#?}: {:#?}", i, values);
            let extd_val = precomp.eval(&values);

            prover_data.r1cs.check_all(&extd_val);

            // for next i+1 round
            current_state = next_state;
        }

        println!(
            "cost model: {:#?}",
            R1CS::naive_cost_model_nohash(&dfa, dfa.is_match(&doc))
        );
        println!("actual cost: {:#?}", prover_data.r1cs.constraints().len());
        assert!(
            prover_data.r1cs.constraints().len()
                <= R1CS::naive_cost_model_nohash(&dfa, dfa.is_match(&doc))
        );
    }

    #[test]
    fn naive_test() {
        naive_test_func_no_hash("a".to_string(), "a".to_string(), "a".to_string());
    }

    #[test]
    fn dfa_2() {
        naive_test_func_no_hash("ab".to_string(), "ab".to_string(), "ab".to_string());
        naive_test_func_no_hash("abc".to_string(), "ab".to_string(), "ab".to_string());
    }

    #[test]
    fn dfa_star() {
        naive_test_func_no_hash("ab".to_string(), "a*b*".to_string(), "ab".to_string());
        naive_test_func_no_hash(
            "ab".to_string(),
            "a*b*".to_string(),
            "aaaabbbbbbbbbbbbbb".to_string(),
        );
        naive_test_func_no_hash(
            "ab".to_string(),
            "a*b*".to_string(),
            "aaaaaaaaaaab".to_string(),
        );
    }

    #[test]
    fn dfa_non_match() {
        naive_test_func_no_hash("ab".to_string(), "a".to_string(), "b".to_string());
        naive_test_func_no_hash(
            "ab".to_string(),
            "a*b*".to_string(),
            "aaabaaaaaaaab".to_string(),
        );
    }

    #[test]
    #[should_panic]
    fn dfa_bad_1() {
        naive_test_func_no_hash("ab".to_string(), "a".to_string(), "c".to_string());
    }

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
                    let f = add(
                        &z,
                        &add(&mul(&Integer::from(2), &y), &mul(&Integer::from(4), &x)),
                    );

                    let uni_out = horners_eval(coeffs.clone(), f);

                    let mle_out = add(
                        &add(
                            &add(
                                &add(
                                    &add(
                                        &add(&add(&mle[0], &mul(&mle[1], &z)), &mul(&mle[2], &y)),
                                        &mul(&mul(&mle[3], &y), &z),
                                    ),
                                    &mul(&mle[4], &x),
                                ),
                                &mul(&mul(&mle[5], &x), &z),
                            ),
                            &mul(&mul(&mle[6], &x), &y),
                        ),
                        &mul(&mul(&mul(&mle[7], &x), &y), &z),
                    );

                    assert_eq!(mle_out, uni_out);
                }
            }
        }
    }
}
