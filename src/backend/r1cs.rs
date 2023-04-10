use crate::backend::costs::{opt_cost_model_select, JBatching, JCommit};
use crate::dfa::NFA;
use circ::cfg;
use circ::cfg::CircOpt;
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
use std::sync::Once;
use std::time::{Duration, Instant};

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

// x = [r_0, r_1, ... -1, {0,1}, {0,1},...]
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
    dfa: &'a NFA,
    batching: JBatching,
    commit_type: JCommit,
    assertions: Vec<Term>,
    // perhaps a misleading name, by "public inputs", we mean "circ leaves these wires exposed from
    // the black box, and will not optimize them away"
    // at the nova level, we will "reprivitize" everything, it's just important to see the hooks
    // sticking out here
    pub_inputs: Vec<Term>,
    pub batch_size: usize,
    doc: Vec<String>,
    is_match: bool,
    pub substring: (usize, usize), // todo getters
    pc: PoseidonConstants<F, typenum::U2>,
    commitment: Option<(F, F)>, // (start, end)
}

impl<'a, F: PrimeField> R1CS<'a, F> {
    pub fn new(
        dfa: &'a NFA,
        doc: &Vec<String>,
        batch_size: usize,
        pcs: PoseidonConstants<F, typenum::U2>,
        batch_override: Option<JBatching>,
        commit_override: Option<JCommit>,
    ) -> Self {
        let is_match = dfa.is_match(doc).is_some();

        println!("Match? {:#?}", is_match);

        // run cost model (with Poseidon) to decide batching
        let (batching, commit, opt_batch_size) = opt_cost_model_select(
            &dfa,
            batch_size,
            batch_size,
            dfa.is_match(doc),
            doc.len(),
            commit_override,
            batch_override,
        );

        let mut sel_batch_size;
        // TODO ELI: handle substring costs, select batch size correctly
        if batch_size < 1 {
            // default to selecting the optimal
            sel_batch_size = opt_batch_size;
        } else {
            // CLI batch_size override
            sel_batch_size = batch_size;
        }

        assert!(sel_batch_size >= 1);
        println!(
            "batch type: {:#?}, commit type: {:#?}, batch_size {:#?}",
            batching, commit, sel_batch_size
        );

        println!("substring pre {:#?}", dfa.is_match(doc));

        let mut substring = (0, doc.len());
        match dfa.is_match(doc) {
            Some((start, end)) => {
                match commit {
                    JCommit::HashChain => {
                        assert!(
                            end == doc.len(),
                            "for HashChain commitment, Regex must handle EOD, switch commit type or change Regex r to r$ or r.*$"
                        );
                        substring = (start, doc.len()); // ... right?
                    }
                    JCommit::Nlookup => {
                        substring = (start, end); // exact
                    }
                }
            }
            None => { // see above
            }
        }

        println!("'substring': {:#?}", substring);

        Self {
            dfa,
            batching, // TODO
            commit_type: commit,
            assertions: Vec::new(),
            pub_inputs: Vec::new(),
            batch_size: sel_batch_size,
            doc: doc.clone(),
            is_match,
            substring,
            pc: pcs,
            commitment: None,
        }
    }

    // IN THE CLEAR

    pub fn gen_commitment(&mut self) {
        match self.commit_type {
            JCommit::HashChain => {
                let mut i = 0;
                let mut start = F::from(0);
                let mut hash = vec![start.clone()];

                for c in self.doc.clone().into_iter() {
                    if i == self.substring.0 {
                        start = hash[0];
                    }
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
                self.commitment = Some((start, hash[0]));
            }
            JCommit::Nlookup => todo!(),
        }
    }

    pub fn verifier_final_checks(
        &self,
        final_hash: Option<F>,
        accepting_state: F,
        final_q: Vec<F>,
        final_v: F,
    ) {
        // TODO
        // commitment matches?
        if matches!(self.commit_type, JCommit::HashChain) {
            assert_eq!(self.commitment.unwrap().1, final_hash.unwrap());
        }

        // state matches?
        assert_eq!(accepting_state, F::from(1));

        // T claim
        // generate table TODO - actually, store the table somewhere
        /*
        let (_, running_v) =
            prover_mle_partial_eval(&table, &final_q, &(0..table.len()).collect(), true, None);
        assert_eq!(final_v, running_v);
        */
    }

    // PROVER

    // seed Questions todo
    fn prover_random_from_seed(&self, absorbs: u32, s: &[F]) -> Integer {
        assert_eq!(absorbs, s.len() as u32);

        let mut sponge = Sponge::new_with_constants(&self.pc, Mode::Simplex);
        let acc = &mut ();
        let parameter = IOPattern(vec![SpongeOp::Absorb(absorbs), SpongeOp::Squeeze(1)]);

        sponge.start(parameter, None, acc);
        SpongeAPI::absorb(&mut sponge, absorbs, s, acc);
        let rand = SpongeAPI::squeeze(&mut sponge, 1, acc);
        sponge.finish(acc).unwrap();

        Integer::from_digits(rand[0].to_repr().as_ref(), Order::Lsf)
    }

    pub fn prover_accepting_state(&self, batch_num: usize, state: usize) -> bool {
        let mut out = false;

        if self.is_match {
            // proof of membership
            for xi in self.dfa.get_final_states().into_iter() {
                out = out || (state == xi);
            }
        } else {
            for xi in self.dfa.get_non_final_states().into_iter() {
                out = out || (state == xi);
            }
        }

        println!("ACCEPTING CHECK: state: {:#?} accepting? {:#?}", state, out);

        // sanity
        if (batch_num + 1) * self.batch_size >= self.doc.len() {
            assert!(out);
        }

        out
    }

    // CIRCUIT

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

    // TODO - we don't want it to always accept state 0
    fn accepting_state_circuit(&mut self) {
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

        //println!("lag {:#?}, vanish {:#?}", lag_ms, vanish_ms);

        let match_term = term(
            Op::Eq,
            vec![
                new_bool_var("accepting".to_owned()),
                term(Op::Eq, vec![new_const(0), vanishing_poly]),
            ],
        );

        self.assertions.push(match_term);
        self.pub_inputs.push(new_bool_var(format!("accepting")));
    }

    fn r1cs_conv(&self) -> (ProverData, VerifierData) {
        let time = Instant::now();
        let mut cs = Computation::from_constraint_system_parts(
            self.assertions.clone(),
            self.pub_inputs.clone(),
        );

        //println!("assertions: {:#?}", self.assertions.clone());

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
        let final_cs = css.get("main");
        let mut circ_r1cs = to_r1cs(final_cs, cfg());

        println!(
            "Pre-opt R1cs size (no hashes): {}",
            circ_r1cs.constraints().len()
        );
        // println!("Prover data {:#?}", prover_data);
        circ_r1cs = reduce_linearities(circ_r1cs, cfg());

        //println!("Prover data {:#?}", prover_data);
        let ms = time.elapsed().as_millis();
        println!(
            "Final R1cs size (no hashes): {}",
            circ_r1cs.constraints().len()
        );
        println!("r1cs conv: {:#?}", ms);

        circ_r1cs.finalize(&final_cs)
    }

    pub fn to_circuit(&mut self) -> (ProverData, VerifierData) {
        match self.batching {
            JBatching::NaivePolys => self.to_polys(),
            JBatching::Nlookup => self.to_nlookup(),
            //JBatching::Plookup => todo!(), //gen_wit_i_plookup(round_num, current_state, doc, batch_size),
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

        //Makes big polynomial
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

        self.accepting_state_circuit();

        if matches!(self.commit_type, JCommit::Nlookup) {
            assert!(
                self.batch_size > 1,
                "don't use a doc commitment if you aren't going to batch"
            );
            self.nlookup_doc_commit();
        }

        self.r1cs_conv()
    }

    // for use at the end of sum check
    // eq([x0,x1,x2...],[e0,e1,e2...])
    fn bit_eq_circuit(&mut self, m: usize, q_bit: usize, id: &str) -> Term {
        let mut eq = new_const(1); // dummy, not used
        let q_name = format!("{}_eq{}", id, q_bit);
        for i in 0..m {
            let next = term(
                Op::PfNaryOp(PfNaryOp::Add),
                vec![
                    term(
                        Op::PfNaryOp(PfNaryOp::Mul),
                        vec![
                            new_var(format!("{}_q_{}", q_name, i)),
                            new_var(format!("{}_sc_r_{}", id, i + 1)), // sc_r idx's start @1
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
                                        vec![new_var(format!("{}_sc_r_{}", id, i + 1))],
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
    fn sum_check_circuit(&mut self, C_1: Term, num_rounds: usize, id: &str) {
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
                    new_var(format!("{}_sc_g_{}_xsq", id, j)),
                    term(
                        Op::PfNaryOp(PfNaryOp::Add),
                        vec![
                            new_var(format!("{}_sc_g_{}_x", id, j)),
                            term(
                                Op::PfNaryOp(PfNaryOp::Add),
                                vec![
                                    new_var(format!("{}_sc_g_{}_const", id, j)),
                                    new_var(format!("{}_sc_g_{}_const", id, j)),
                                ],
                            ),
                        ],
                    ),
                ],
            );

            let claim_check = term(Op::Eq, vec![claim.clone(), g_j]);

            self.assertions.push(claim_check);
            self.pub_inputs
                .push(new_var(format!("{}_sc_g_{}_xsq", id, j)));
            self.pub_inputs
                .push(new_var(format!("{}_sc_g_{}_x", id, j)));
            self.pub_inputs
                .push(new_var(format!("{}_sc_g_{}_const", id, j)));
            self.pub_inputs.push(new_var(format!("{}_sc_r_{}", id, j)));

            // "V" chooses rand r_{j} (P chooses this with hash)
            //let r_j = new_var(format!("sc_r_{}", j));

            // update claim for the next round g_j(r_j)
            claim = term(
                Op::PfNaryOp(PfNaryOp::Add),
                vec![
                    new_var(format!("{}_sc_g_{}_const", id, j)),
                    term(
                        Op::PfNaryOp(PfNaryOp::Mul),
                        vec![
                            new_var(format!("{}_sc_r_{}", id, j)),
                            term(
                                Op::PfNaryOp(PfNaryOp::Add),
                                vec![
                                    new_var(format!("{}_sc_g_{}_x", id, j)),
                                    term(
                                        Op::PfNaryOp(PfNaryOp::Mul),
                                        vec![
                                            new_var(format!("{}_sc_r_{}", id, j)),
                                            new_var(format!("{}_sc_g_{}_xsq", id, j)),
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
                    vec![claim.clone(), new_var(format!("{}_sc_last_claim", id))],
                );
                self.assertions.push(last_claim);
                self.pub_inputs
                    .push(new_var(format!("{}_sc_last_claim", id)));
            }
        }
    }

    pub fn to_nlookup(&mut self) -> (ProverData, VerifierData) {
        let lookups = self.lookup_idxs();
        self.nlookup_gadget(lookups, self.dfa.trans.len(), "nl");

        self.accepting_state_circuit(); // TODO

        if matches!(self.commit_type, JCommit::Nlookup) {
            self.nlookup_doc_commit();
        }

        self.r1cs_conv()
    }

    fn nlookup_doc_commit(&mut self) {
        // start: usize, end: usize) {
        let mut char_lookups = vec![];
        for c in 0..self.batch_size {
            // TODO details
            char_lookups.push(new_var(format!("char_{}", c)));
            //self.pub_inputs.push(new_var(format!("char_{}", c))); <- done elsewhere
        }

        self.nlookup_gadget(char_lookups, self.doc.len(), "nl_doc");
    }

    fn nlookup_gadget(&mut self, mut lookup_vals: Vec<Term>, t_size: usize, id: &str) {
        // TODO pub inputs -> can make which priv?
        // last state_batch is final "next_state" output
        // v_{batch-1} = (state_{batch-1}, c, state_batch)
        // v_batch = T eval check (optimization)
        //                self.pub_inputs
        //                    .push(new_var(format!("state_{}", self.batch_size)));

        let mut v = vec![new_const(0)]; // dummy constant term for lhs claim
        v.append(&mut lookup_vals);
        v.push(new_var(format!("{}_prev_running_claim", id))); // running claim
        self.pub_inputs
            .push(new_var(format!("{}_prev_running_claim", id)));

        // generate claim on lhs
        let lhs = horners_circuit_vars(&v, new_var(format!("{}_claim_r", id)));
        self.pub_inputs.push(new_var(format!("{}_claim_r", id)));

        // size of table (T -> mle)
        let sc_l = (t_size as f64).log2().ceil() as usize;
        //println!("table size: {}", t_size);
        //println!("sum check rounds: {}", sc_l);

        self.sum_check_circuit(lhs, sc_l, id);

        // last eq circ on l-element point

        //TODO check ordering correct
        let mut eq_evals = vec![new_const(0)]; // dummy for horners
        for i in 0..self.batch_size + 1 {
            eq_evals.push(self.bit_eq_circuit(sc_l, i, id));
        }
        let eq_eval = horners_circuit_vars(&eq_evals, new_var(format!("{}_claim_r", id)));

        // last_claim = eq_eval * next_running_claim
        let sum_check_domino = term(
            Op::Eq,
            vec![
                new_var(format!("{}_sc_last_claim", id)),
                term(
                    Op::PfNaryOp(PfNaryOp::Mul),
                    vec![eq_eval, new_var(format!("{}_next_running_claim", id))],
                ),
            ],
        );
        self.assertions.push(sum_check_domino);
        self.pub_inputs
            .push(new_var(format!("{}_next_running_claim", id)));
    }

    pub fn gen_wit_i(
        &self,
        batch_num: usize,
        current_state: usize,
        prev_running_claim_q: Option<Vec<Integer>>,
        prev_running_claim_v: Option<Integer>,
        prev_doc_running_claim_q: Option<Vec<Integer>>,
        prev_doc_running_claim_v: Option<Integer>,
    ) -> (
        FxHashMap<String, Value>,
        usize,
        Option<Vec<Integer>>,
        Option<Integer>,
        Option<Vec<Integer>>,
        Option<Integer>,
    ) {
        match self.batching {
            JBatching::NaivePolys => {
                let (wits, next_state, next_doc_running_claim_q, next_doc_running_claim_v) = self
                    .gen_wit_i_polys(
                        batch_num,
                        current_state,
                        prev_doc_running_claim_q,
                        prev_doc_running_claim_v,
                    );
                (
                    wits,
                    next_state,
                    None,
                    None,
                    next_doc_running_claim_q,
                    next_doc_running_claim_v,
                )
            }
            JBatching::Nlookup => self.gen_wit_i_nlookup(
                batch_num,
                current_state,
                prev_running_claim_q,
                prev_running_claim_v,
                prev_doc_running_claim_q,
                prev_doc_running_claim_v,
            ),
            //JBatching::Plookup => todo!(), //gen_wit_i_plookup(round_num, current_state, doc, batch_size),
        }
    }

    fn gen_wit_i_nlookup(
        &self,
        batch_num: usize,
        current_state: usize,
        running_q: Option<Vec<Integer>>,
        running_v: Option<Integer>,
        doc_running_q: Option<Vec<Integer>>,
        doc_running_v: Option<Integer>,
    ) -> (
        FxHashMap<String, Value>,
        usize,
        Option<Vec<Integer>>,
        Option<Integer>,
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

        //println!("TABLE {:#?}", table);

        let mut wits = FxHashMap::default();

        // generate claim v's (well, v isn't a real named var, generate the states/chars)
        let mut state_i = current_state;
        let mut next_state = 0;
        //      let mut v = vec![];
        let mut q = vec![];
        for i in 1..=self.batch_size {
            let c = self.doc[batch_num * self.batch_size + i - 1].clone();
            next_state = self.dfa.delta(state_i, &c.to_string()).unwrap();

            wits.insert(format!("state_{}", i - 1), new_wit(state_i));
            wits.insert(
                format!("char_{}", i - 1),
                new_wit(self.dfa.ab_to_num(&c.to_string())),
            );

            // v_i = (state_i * (#states*#chars)) + (state_i+1 * #chars) + char_i

            //v.push(
            let v_i = Integer::from(
                (state_i * self.dfa.nstates() * self.dfa.nchars())
                    + (next_state * self.dfa.nchars())
                    + self.dfa.ab_to_num(&c.to_string()),
            )
            .rem_floor(cfg().field().modulus());

            q.push(table.iter().position(|val| val == &v_i).unwrap());

            //println!("vi = {:#?}", v_i);

            /*println!(
                "state {:#?} -> {:#?} -> state {:#?} is {:#?} in table",
                state_i,
                self.dfa.ab_to_num(&c.to_string()),
                next_state,
                &q[i - 1]
            );*/

            state_i = next_state;
        }

        // last state
        wits.insert(format!("state_{}", self.batch_size), new_wit(next_state));

        //    println!("v: {:#?}", v.clone());

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

        assert!(running_q.is_some() || batch_num == 0);
        assert!(running_v.is_some() || batch_num == 0);
        let (w, next_running_q, next_running_v) =
            self.wit_nlookup_gadget(wits, table, q, running_q, running_v, "nl");
        wits = w;
        //println!("next running q out of main {:#?}", next_running_q.clone());

        wits.insert(
            format!("accepting"),
            new_bool_wit(self.prover_accepting_state(batch_num, next_state)),
        );

        if matches!(self.commit_type, JCommit::Nlookup) {
            assert!(doc_running_q.is_some() || batch_num == 0);
            assert!(doc_running_v.is_some() || batch_num == 0);
            let (w, next_doc_running_q, next_doc_running_v) =
                self.wit_nlookup_doc_commit(wits, batch_num, doc_running_q, doc_running_v);
            wits = w;
            //println!("RUNNING DOC Q {:#?}", next_doc_running_q.clone());
            (
                wits,
                next_state,
                Some(next_running_q),
                Some(next_running_v),
                Some(next_doc_running_q),
                Some(next_doc_running_v),
            )
        } else {
            (
                wits,
                next_state,
                Some(next_running_q),
                Some(next_running_v),
                None,
                None,
            )
        }
    }

    fn wit_nlookup_doc_commit(
        &self,
        mut wits: FxHashMap<String, Value>,
        batch_num: usize,
        running_q: Option<Vec<Integer>>,
        running_v: Option<Integer>,
    ) -> (FxHashMap<String, Value>, Vec<Integer>, Integer) {
        // generate T
        let mut doc = vec![];
        for c in self.doc.clone().into_iter() {
            // todo save this crap somewhere so we don't recalc
            doc.push(Integer::from(self.dfa.ab_to_num(&c.to_string())));
            // .rem_floor(cfg().field().modulus()), // thoughts?
        }

        let mut q = vec![];
        for i in 0..self.batch_size {
            // let c = self.doc[batch_num * self.batch_size + i].clone();
            // "char val" witnesses already made

            // position in doc
            q.push(batch_num * self.batch_size + i);
        }

        let (w, next_running_q, next_running_v) =
            self.wit_nlookup_gadget(wits, doc, q, running_q, running_v, "nl_doc");
        wits = w;

        (wits, next_running_q, next_running_v)
    }

    fn wit_nlookup_gadget(
        &self,
        mut wits: FxHashMap<String, Value>,
        table: Vec<Integer>,
        q: Vec<usize>,
        //v: Vec<Integer>,
        running_q: Option<Vec<Integer>>,
        running_v: Option<Integer>,
        id: &str,
    ) -> (FxHashMap<String, Value>, Vec<Integer>, Integer) {
        // TODO - what needs to be public?

        let sc_l = (table.len() as f64).log2().ceil() as usize; // sum check rounds

        // generate claim r
        let claim_r = self.prover_random_from_seed(1, &[F::from(5 as u64)]); // TODO make general
        wits.insert(format!("{}_claim_r", id), new_wit(claim_r.clone()));

        // running claim about T (optimization)
        // if first (not yet generated)
        let mut prev_running_q = match running_q {
            Some(q) => q,
            None => vec![Integer::from(0); sc_l],
        };
        let mut prev_running_v = match running_v {
            Some(v) => v,
            None => table[0].clone(),
        };
        //println!("prev running v {:#?}", prev_running_v.clone());

        //v.push(prev_running_v.clone()); // todo get rid of v?

        wits.insert(
            format!("{}_prev_running_claim", id),
            new_wit(prev_running_v.clone()),
        );
        // q.push(prev_running_q);

        // println!("v: {:#?}", v.clone());

        // generate polynomial g's for sum check
        let mut sc_rs = vec![];
        let mut g_xsq = Integer::from(0);
        let mut g_x = Integer::from(0);
        let mut g_const = Integer::from(0);
        for i in 1..=sc_l {
            (g_xsq, g_x, g_const) =
                prover_mle_sum_eval(&table, &sc_rs, &q, &claim_r, Some(&prev_running_q));

            wits.insert(format!("{}_sc_g_{}_xsq", id, i), new_wit(g_xsq.clone()));
            wits.insert(format!("{}_sc_g_{}_x", id, i), new_wit(g_x.clone()));
            wits.insert(format!("{}_sc_g_{}_const", id, i), new_wit(g_const.clone()));

            // new sumcheck rand for the round
            // generate rands
            let rand = self.prover_random_from_seed(1, &[F::from(i as u64)]); // TODO make gen
            sc_rs.push(rand.clone());
            wits.insert(format!("{}_sc_r_{}", id, i), new_wit(rand.clone()));
        }
        // last claim = g_v(r_v)
        //println!("sc rs {:#?}", sc_rs.clone());
        g_xsq *= &sc_rs[sc_rs.len() - 1];
        g_xsq *= &sc_rs[sc_rs.len() - 1];
        g_x *= &sc_rs[sc_rs.len() - 1];
        g_const += &g_x;
        g_const += &g_xsq;

        let last_claim = g_const.rem_floor(cfg().field().modulus());
        wits.insert(format!("{}_sc_last_claim", id), new_wit(last_claim.clone()));

        // generate last round eqs
        for i in 0..self.batch_size {
            // regular
            let q_name = format!("{}_eq{}", id, i);
            for j in 0..sc_l {
                let qj = (q[i] >> j) & 1;
                wits.insert(format!("{}_q_{}", q_name, (sc_l - 1 - j)), new_wit(qj));
            }
        }
        for j in 0..sc_l {
            // running
            let q_name = format!("{}_eq{}", id, q.len()); //v.len() - 1);
            wits.insert(
                format!("{}_q_{}", q_name, j),
                new_wit(prev_running_q[j].clone()),
            );
        }

        // update running claim
        let (_, next_running_v) =
            prover_mle_partial_eval(&table, &sc_rs, &(0..table.len()).collect(), true, None);
        let next_running_q = sc_rs.clone();
        wits.insert(
            format!("{}_next_running_claim", id),
            new_wit(next_running_v.clone()),
        );

        // sanity check - TODO eliminate
        // make rs
        let mut rs = vec![claim_r.clone()];
        for i in 1..(q.len() + 1) {
            rs.push(rs[i - 1].clone() * claim_r.clone());
        }
        let (_, eq_term) = prover_mle_partial_eval(&rs, &sc_rs, &q, false, Some(&prev_running_q));
        assert_eq!(
            last_claim,
            (eq_term * next_running_v.clone()).rem_floor(cfg().field().modulus())
        );

        // return
        // println!("wits: {:#?}", wits);

        (wits, next_running_q, next_running_v)
    }

    // TODO BATCH SIZE (rn = 1)
    fn gen_wit_i_polys(
        &self,
        batch_num: usize,
        current_state: usize,
        doc_running_q: Option<Vec<Integer>>,
        doc_running_v: Option<Integer>,
    ) -> (
        FxHashMap<String, Value>,
        usize,
        Option<Vec<Integer>>,
        Option<Integer>,
    ) {
        let mut wits = FxHashMap::default();
        let mut state_i = current_state;
        let mut next_state = 0;

        for i in 0..self.batch_size {
            let doc_i = self.doc[batch_num * self.batch_size + i].clone();
            next_state = self.dfa.delta(state_i, &doc_i.clone()).unwrap();

            wits.insert(format!("state_{}", i), new_wit(state_i));
            wits.insert(format!("char_{}", i), new_wit(self.dfa.ab_to_num(&doc_i)));

            state_i = next_state;
        }
        wits.insert(format!("state_{}", self.batch_size), new_wit(state_i));

        wits.insert(
            format!("accepting"),
            new_bool_wit(self.prover_accepting_state(batch_num, next_state)),
        );
        //println!("wits {:#?}", wits);

        if matches!(self.commit_type, JCommit::Nlookup) {
            assert!(doc_running_q.is_some() || batch_num == 0);
            assert!(doc_running_v.is_some() || batch_num == 0);
            let (w, next_doc_running_q, next_doc_running_v) =
                self.wit_nlookup_doc_commit(wits, batch_num, doc_running_q, doc_running_v);
            wits = w;
            //println!("RUNNING DOC Q {:#?}", next_doc_running_q.clone());
            (
                wits,
                next_state,
                Some(next_doc_running_q),
                Some(next_doc_running_v),
            )
        } else {
            (wits, next_state, None, None)
        }
    }
}

#[cfg(test)]
mod tests {

    use crate::backend::costs;
    use crate::backend::r1cs::*;
    use crate::dfa::NFA;
    use crate::regex::Regex;
    use circ::cfg;
    use circ::cfg::CircOpt;
    use serial_test::serial;
    type G1 = pasta_curves::pallas::Point;

    fn set_up_cfg() {
        println!("cfg set? {:#?}", cfg::is_cfg_set());
        if !cfg::is_cfg_set() {
            //let m = format!("1019");
            let m = format!(
                "28948022309329048855892746252171976963363056481941647379679742748393362948097"
            );
            let mut circ: CircOpt = Default::default();
            circ.field.custom_modulus = m.into();

            cfg::set(&circ);
        }
    }

    #[test]
    fn mle_partial() {
        init();

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
                    let x = vec![Integer::from(x_1), Integer::from(x_2), Integer::from(x_3)];
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
    fn mle_sums() {
        init();
        let table = vec![
            Integer::from(9),
            Integer::from(4),
            Integer::from(5),
            Integer::from(7),
        ];

        // generate polynomial g's for sum check

        // v = [4, 9, extra]
        // extra: [33, 30] -> 543
        for q in [None, Some(&vec![Integer::from(33), Integer::from(30)])] {
            let mut sc_rs = vec![];
            let claim_r = Integer::from(17);

            // round 1
            let (mut g_xsq, mut g_x, mut g_const) =
                prover_mle_sum_eval(&table, &sc_rs.clone(), &vec![1, 0], &claim_r, q);
            //println!("mle sums {:#?}, {:#?}, {:#?}", g_xsq, g_x, g_const);

            let mut claim = claim_r.clone() * table[1].clone()
                + claim_r.clone() * claim_r.clone() * table[0].clone();
            if q.is_some() {
                claim += claim_r.clone() * claim_r.clone() * claim_r.clone() * Integer::from(6657);
            }
            assert_eq!(
                claim.rem_floor(cfg().field().modulus()),
                (g_xsq.clone() + g_x.clone() + g_const.clone() + g_const.clone())
                    .rem_floor(cfg().field().modulus())
            );

            sc_rs.push(Integer::from(10));
            claim = Integer::from(100) * g_xsq + Integer::from(10) * g_x + g_const;

            // round 2
            (g_xsq, g_x, g_const) =
                prover_mle_sum_eval(&table, &sc_rs.clone(), &vec![1, 0], &claim_r, q);
            //println!("mle sums {:#?}, {:#?}, {:#?}", g_xsq, g_x, g_const);
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
                &sc_rs.clone(),
                &(0..table.len()).collect(),
                true,
                None,
            );
            //println!("mle sums {:#?}, {:#?}", g_x, g_const);

            let (_, con_b) = prover_mle_partial_eval(
                &vec![Integer::from(17), Integer::from(289), Integer::from(4913)],
                &sc_rs.clone(),
                &vec![1, 0],
                false,
                q,
            );
            con_a *= &con_b;

            assert_eq!(
                claim.rem_floor(cfg().field().modulus()),
                con_a.rem_floor(cfg().field().modulus())
            );
        }
    }

    fn test_func_no_hash(
        ab: String,
        rstr: String,
        doc: String,
        batch_sizes: Vec<usize>,
        expected_match: bool,
    ) {
        let r = Regex::new(&rstr);
        let dfa = NFA::new(&ab[..], r);
        //println!("{:#?}", dfa);

        let chars: Vec<String> = doc.chars().map(|c| c.to_string()).collect();

        for s in batch_sizes {
            for b in vec![JBatching::NaivePolys, JBatching::Nlookup] {
                for c in vec![JCommit::HashChain, JCommit::Nlookup] {
                    println!("\nNew");
                    let sc = Sponge::<<G1 as Group>::Scalar, typenum::U2>::api_constants(
                        Strength::Standard,
                    );
                    let mut r1cs_converter = R1CS::new(
                        &dfa,
                        &doc.chars().map(|c| c.to_string()).collect(),
                        s,
                        sc,
                        Some(b.clone()),
                        Some(c.clone()),
                    );

                    assert_eq!(expected_match, r1cs_converter.is_match);

                    let mut running_q = None;
                    let mut running_v = None;
                    let mut doc_running_q = None;
                    let mut doc_running_v = None;
                    match b {
                        JBatching::NaivePolys => {}
                        JBatching::Nlookup => {
                            if s <= 1 {
                                // don't use nlookup with batch of 1
                                break;
                            }
                        } //JBatching::Plookup => todo!(),
                    }
                    match c {
                        JCommit::HashChain => {}
                        JCommit::Nlookup => {
                            if s <= 1 {
                                // don't use nlookup with batch of 1
                                break;
                            }
                        } //JBatching::Plookup => todo!(),
                    } // TODO make batch size 1 work at some point, you know for nice figs

                    println!("Batching {:#?}", r1cs_converter.batching);
                    println!("Commit {:#?}", r1cs_converter.commit_type);
                    let (prover_data, _) = r1cs_converter.to_circuit();

                    let mut current_state = dfa.get_init_state();

                    let mut values;
                    let mut next_state;

                    let num_steps = (r1cs_converter.substring.1 - r1cs_converter.substring.0) / s;
                    for i in 0..num_steps {
                        (
                            values,
                            next_state,
                            running_q,
                            running_v,
                            doc_running_q,
                            doc_running_v,
                        ) = r1cs_converter.gen_wit_i(
                            i,
                            current_state,
                            running_q.clone(),
                            running_v.clone(),
                            doc_running_q.clone(),
                            doc_running_v.clone(),
                        );

                        //println!("VALUES ROUND {:#?}: {:#?}", i, values);
                        //println!("EXT VALUES ROUND {:#?}: {:#?}", i, extd_val);

                        prover_data.check_all(&values);
                        // for next i+1 round
                        current_state = next_state;
                    }
                    println!("b? {:#?}", b.clone());
                    println!(
                        "cost model: {:#?}",
                        costs::full_round_cost_model_nohash(
                            &dfa,
                            s,
                            b.clone(),
                            dfa.is_match(&chars),
                            doc.len(),
                            c,
                        )
                    );
                    println!("actual cost: {:#?}", prover_data.r1cs.constraints.len());
                    assert!(
                        prover_data.r1cs.constraints.len() as usize
                            <= costs::full_round_cost_model_nohash(
                                &dfa,
                                s,
                                b.clone(),
                                dfa.is_match(&chars),
                                doc.len(),
                                c
                            )
                    ); // deal with later TODO
                }
            }
        }
    }

    #[test]
    fn naive_test() {
        init();
        test_func_no_hash(
            "a".to_string(),
            "^a*$".to_string(),
            "aaaa".to_string(),
            vec![1, 2],
            true,
        );
    }

    #[test]
    fn dfa_2() {
        init();
        test_func_no_hash(
            "ab".to_string(),
            "^ab$".to_string(),
            "ab".to_string(),
            vec![1],
            true,
        );
        test_func_no_hash(
            "abc".to_string(),
            "^ab$".to_string(),
            "ab".to_string(),
            vec![1],
            true,
        );
        test_func_no_hash(
            "abcdef".to_string(),
            "^ab.*f$".to_string(),
            "abcdeffff".to_string(),
            vec![1, 3],
            true,
        );
    }

    #[test]
    fn dfa_star() {
        init();
        test_func_no_hash(
            "ab".to_string(),
            "^a*b*$".to_string(),
            "ab".to_string(),
            vec![1],
            true,
        );
        test_func_no_hash(
            "ab".to_string(),
            "^a*b*$".to_string(),
            "aaaaaabbbbbbbbbbbbbb".to_string(),
            vec![1, 2, 4],
            true,
        );
        test_func_no_hash(
            "ab".to_string(),
            "^a*b*$".to_string(),
            "aaaaaaaaaaab".to_string(),
            vec![1, 2, 4],
            true,
        );
    }

    #[test]
    fn dfa_non_match() {
        init();
        // TODO make sure match/non match is expected
        test_func_no_hash(
            "ab".to_string(),
            "a".to_string(),
            "b".to_string(),
            vec![1],
            false,
        );
        test_func_no_hash(
            "ab".to_string(),
            "^a*b*$".to_string(),
            "aaabaaaaaaaabbb".to_string(),
            vec![1, 2, 4],
            false,
        );

        test_func_no_hash(
            "abcd".to_string(),
            "^a*b*cccb*$".to_string(),
            "aaaaaaaaaabbbbbbbbbb".to_string(),
            vec![1, 2, 5, 10],
            false,
        );
    }

    #[test]
    #[should_panic]
    fn dfa_bad_1() {
        init();
        test_func_no_hash(
            "ab".to_string(),
            "^a$".to_string(),
            "c".to_string(),
            vec![1],
            false,
        );
    }

    #[test]
    #[should_panic]
    fn dfa_bad_substring() {
        init();
        test_func_no_hash(
            "helowrd".to_string(),
            "hello".to_string(),
            "helloworld".to_string(),
            vec![1],
            true,
        );
    }

    #[test]
    #[should_panic]
    fn dfa_bad_substring_2() {
        init();
        test_func_no_hash(
            "helowrd".to_string(),
            "^hello".to_string(),
            "helloworld".to_string(),
            vec![1],
            true,
        );
    }

    #[test]
    fn dfa_ok_substring() {
        init();
        test_func_no_hash(
            "helowrd".to_string(),
            "^hello.*$".to_string(),
            "helloworld".to_string(),
            vec![1],
            true,
        );

        test_func_no_hash(
            "helowrd".to_string(),
            "^hello$".to_string(),
            "helloworld".to_string(),
            vec![1, 5],
            false,
        );
    }
}
