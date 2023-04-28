use crate::backend::{commitment::*, costs::*, nova::int_to_ff, r1cs_helper::*};
use crate::config::*;
use crate::dfa::NFA;
use circ::cfg::cfg;
use circ::ir::{opt::*, proof::Constraints, term::*};
use circ::target::r1cs::*;
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
use std::fs;
use std::sync::Once;
use std::time::{Duration, Instant};

pub struct R1CS<'a, F: PrimeField> {
    dfa: &'a NFA,
    pub table: Vec<Integer>,
    pub batching: JBatching,
    pub commit_type: JCommit,
    pub reef_commit: Option<ReefCommitment>,
    assertions: Vec<Term>,
    // perhaps a misleading name, by "public inputs", we mean "circ leaves these wires exposed from
    // the black box, and will not optimize them away"
    // at the nova level, we will "reprivitize" everything, it's just important to see the hooks
    // sticking out here
    pub_inputs: Vec<Term>,
    pub batch_size: usize,
    pub doc: Vec<String>,
    is_match: bool,
    pub substring: (usize, usize), // todo getters
    pc: PoseidonConstants<F, typenum::U2>,
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
        let batching;
        let commit;
        let opt_batch_size;
        if batch_size > 1 {
            (batching, commit, opt_batch_size) = match (batch_override, commit_override) {
                (Some(b), Some(c)) => (b, c, batch_size),
                (Some(b), _) => {
                    opt_commit_select_with_batch(dfa, batch_size, dfa.is_match(doc), doc.len(), b)
                }
                (None, Some(c)) => opt_cost_model_select_with_commit(
                    &dfa,
                    batch_size,
                    dfa.is_match(doc),
                    doc.len(),
                    c,
                ),
                (None, None) => {
                    opt_cost_model_select_with_batch(&dfa, batch_size, dfa.is_match(doc), doc.len())
                }
            };
        } else {
            (batching, commit, opt_batch_size) = opt_cost_model_select(
                &dfa,
                0,
                logmn(doc.len()),
                dfa.is_match(doc),
                doc.len(),
                commit_override,
                batch_override,
            );
        }

        let sel_batch_size = opt_batch_size;

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

        // generate T
        let mut table = vec![];
        for (ins, c, out) in dfa.deltas() {
            table.push(
                Integer::from(
                    (ins * dfa.nstates() * dfa.nchars())
                        + (out * dfa.nchars())
                        + dfa.ab_to_num(&c.to_string()),
                )
                .rem_floor(cfg().field().modulus()),
            );
        }

        Self {
            dfa,
            table,    // TODO fix else
            batching, // TODO
            commit_type: commit,
            reef_commit: None,
            assertions: Vec::new(),
            pub_inputs: Vec::new(),
            batch_size: sel_batch_size,
            doc: doc.clone(),
            is_match,
            substring,
            pc: pcs,
        }
    }

    pub fn set_commitment(&mut self, rc: ReefCommitment) {
        println!("SETTING COMMITMENT");
        match (&rc, self.commit_type) {
            (ReefCommitment::HashChain(_), JCommit::HashChain) => {
                self.reef_commit = Some(rc);
            }
            (ReefCommitment::Nlookup(_), JCommit::Nlookup) => {
                self.reef_commit = Some(rc);
            }
            _ => {
                panic!("Commitment does not match selected type");
            }
        }
    }

    // IN THE CLEAR

    pub fn prover_calc_hash(&self, start_hash_or_blind: F, i: usize) -> F {
        let mut next_hash;

        if i == 0 {
            // H_0 = Hash(0, r, 0)
            let mut sponge = Sponge::new_with_constants(&self.pc, Mode::Simplex);
            let acc = &mut ();

            let parameter = IOPattern(vec![SpongeOp::Absorb(2), SpongeOp::Squeeze(1)]);
            sponge.start(parameter, None, acc);

            SpongeAPI::absorb(&mut sponge, 2, &[start_hash_or_blind, F::from(0)], acc);
            next_hash = SpongeAPI::squeeze(&mut sponge, 1, acc);
            sponge.finish(acc).unwrap();
        } else {
            next_hash = vec![start_hash_or_blind];
        }

        println!("PROVER START HASH ROUND {:#?}", next_hash);
        let parameter = IOPattern(vec![SpongeOp::Absorb(3), SpongeOp::Squeeze(1)]);
        for b in 0..self.batch_size {
            // expected poseidon
            let mut sponge = Sponge::new_with_constants(&self.pc, Mode::Simplex);
            let acc = &mut ();

            sponge.start(parameter.clone(), None, acc);
            SpongeAPI::absorb(
                &mut sponge,
                3,
                &[
                    next_hash[0],
                    F::from(
                        self.dfa
                            .ab_to_num(&self.doc[i * self.batch_size + b].clone())
                            as u64,
                    ),
                    F::from((i * self.batch_size + b) as u64),
                ],
                acc,
            );
            next_hash = SpongeAPI::squeeze(&mut sponge, 1, acc);
            /*println!(
                "prev, expected next hash in main {:#?} {:#?}",
                prev_hash, expected_next_hash
            );
            */
            println!("PROVER HASH ROUND {:#?}", next_hash);
            sponge.finish(acc).unwrap(); // assert expected hash finished correctly
        }

        next_hash[0]
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

        // println!("ACCEPTING CHECK: state: {:#?} accepting? {:#?}", state, out);

        // sanity
        if (batch_num + 1) * self.batch_size - 1 >= self.doc.len() {
            // todo check
            assert!(out);
        }

        out
    }

    // CIRCUIT

    // check if we need vs as vars
    fn lookup_idxs(&mut self, include_vs: bool) -> Vec<Term> {
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
            v.push(v_i.clone());
            self.pub_inputs.push(new_var(format!("state_{}", i - 1)));
            self.pub_inputs.push(new_var(format!("char_{}", i - 1)));

            if include_vs {
                let match_v = term(Op::Eq, vec![new_var(format!("v_{}", i)), v_i]);

                self.assertions.push(match_v);
                self.pub_inputs.push(new_var(format!("v_{}", i)));
            }
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

        if self.is_match {
            // proof of membership
            for xi in final_states.into_iter() {
                vanish_on.push(Integer::from(xi));
            }
        } else {
            for xi in non_final_states.into_iter() {
                vanish_on.push(Integer::from(xi));
            }
        }
        vanishing_poly =
            poly_eval_circuit(vanish_on, new_var(format!("state_{}", self.batch_size)));

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
        //println!("{:#?}", final_cs.clone());

        let mut circ_r1cs = to_r1cs(final_cs, cfg());

        println!(
            "Pre-opt R1cs size (no hashes): {}",
            circ_r1cs.constraints().len()
        );
        // println!("Prover data {:#?}", prover_data);
        circ_r1cs = reduce_linearities(circ_r1cs, cfg());

        for r in circ_r1cs.constraints().clone() {
            println!("{:#?}", circ_r1cs.format_qeq(&r));
        }

        //println!("Prover data {:#?}", circ_r1cs);
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
        }
    }

    // TODO batch size (1 currently)
    fn to_polys(&mut self) -> (ProverData, VerifierData) {
        let l_time = Instant::now();
        let lookup = self.lookup_idxs(false);

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

        self.accepting_state_circuit();

        match self.commit_type {
            JCommit::HashChain => {
                self.hashchain_commit();
            }
            JCommit::Nlookup => {
                self.nlookup_doc_commit();
            }
        }

        self.r1cs_conv()
    }

    fn hashchain_commit(&mut self) {
        self.pub_inputs.push(new_var(format!("i_0")));
        for idx in 1..=self.batch_size {
            let i_plus = term(
                Op::Eq,
                vec![
                    new_var(format!("i_{}", idx)),
                    term(
                        Op::PfNaryOp(PfNaryOp::Add),
                        vec![new_var(format!("i_{}", idx - 1)), new_const(1)],
                    ),
                ],
            );

            self.assertions.push(i_plus);
            self.pub_inputs.push(new_var(format!("i_{}", idx)));
        }
        /*
              let ite = term(
                  Op::Ite,
                  vec![
                      term(Op::Eq, vec![new_var(format!("i_0")), new_const(0)]),
                      term(
                          Op::Eq,
                          vec![
                              new_var(format!("first_hash_input")),
                              new_var(format!("random_hash_result")),
                          ],
                      ),
                      term(
                          Op::Eq,
                          vec![
                              new_var(format!("first_hash_input")),
                              new_var(format!("z_hash_input")),
                          ],
                      ),
                  ],
              );
              self.assertions.push(ite);
              self.pub_inputs.push(new_var(format!("first_hash_input")));
              self.pub_inputs.push(new_var(format!("random_hash_result")));
              self.pub_inputs.push(new_var(format!("z_hash_input")));
        */
    }

    // for use at the end of sum check
    // eq([x0,x1,x2...],[e0,e1,e2...])
    fn bit_eq_circuit(&mut self, m: usize, q_bit: usize, id: &str) -> Term {
        let mut eq = new_const(1); // dummy, not used
        let q_name = format!("{}_eq_{}", id, q_bit);
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

            if i == 0 {
                eq = next;
            } else {
                eq = term(Op::PfNaryOp(PfNaryOp::Mul), vec![eq, next]);
            }
        }

        eq
    }

    // note that the running claim q is not included
    fn combined_q_circuit(&mut self, num_eqs: usize, num_q_bits: usize, id: &str) {
        assert!(
            num_eqs * num_q_bits < 256,
            "may have field overflow when combining q bits for fiat shamir"
        );

        let mut combined_q = new_const(0); // dummy, not used
        let mut next_slot = Integer::from(1);
        for i in 0..num_eqs {
            for j in 0..num_q_bits {
                combined_q = term(
                    Op::PfNaryOp(PfNaryOp::Add),
                    vec![
                        combined_q,
                        term(
                            Op::PfNaryOp(PfNaryOp::Mul),
                            vec![
                                new_const(next_slot.clone()),
                                new_var(format!("{}_eq_{}_q_{}", id, i, j)),
                            ],
                        ),
                    ],
                );
                next_slot *= Integer::from(2);
            }
        }

        let combined_q_eq = term(
            Op::Eq,
            vec![combined_q, new_var(format!("{}_combined_q", id))],
        );

        self.assertions.push(combined_q_eq);
        self.pub_inputs.push(new_var(format!("{}_combined_q", id)));
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
        let lookups = self.lookup_idxs(true);
        self.nlookup_gadget(lookups, self.dfa.trans.len(), "nl");

        self.accepting_state_circuit(); // TODO

        match self.commit_type {
            JCommit::HashChain => {
                self.hashchain_commit();
            }
            JCommit::Nlookup => {
                self.nlookup_doc_commit();
            }
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

        self.nlookup_gadget(char_lookups, self.doc.len(), "nldoc");
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
        let sc_l = logmn(t_size);
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

        // make combined_q
        let combined_q = self.combined_q_circuit(self.batch_size, sc_l, id); // running claim q not
                                                                             // included

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

        let mut v = vec![];
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
            let v_i = Integer::from(
                (state_i * self.dfa.nstates() * self.dfa.nchars())
                    + (next_state * self.dfa.nchars())
                    + self.dfa.ab_to_num(&c.to_string()),
            )
            .rem_floor(cfg().field().modulus());
            v.push(v_i.clone());
            wits.insert(format!("v_{}", i), new_wit(v_i.clone()));

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
            self.wit_nlookup_gadget(wits, table, q, v, running_q, running_v, "nl");
        wits = w;
        //println!("next running q out of main {:#?}", next_running_q.clone());

        wits.insert(
            format!("accepting"),
            new_bool_wit(self.prover_accepting_state(batch_num, next_state)),
        );

        match self.commit_type {
            JCommit::HashChain => {
                for i in 0..=self.batch_size {
                    wits.insert(format!("i_{}", i), new_wit(batch_num * self.batch_size + i));
                }
                // values not actually checked or used
                wits.insert(format!("first_hash_input"), new_wit(0));
                wits.insert(format!("random_hash_result"), new_wit(0));
                wits.insert(format!("z_hash_input"), new_wit(0));
                (
                    wits,
                    next_state,
                    Some(next_running_q),
                    Some(next_running_v),
                    None,
                    None,
                )
            }
            JCommit::Nlookup => {
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
            }
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

        let mut v = vec![];
        let mut q = vec![];
        for i in 0..self.batch_size {
            let c = doc[batch_num * self.batch_size + i].clone();
            v.push(c); // todo check

            // position in doc
            q.push(batch_num * self.batch_size + i);
        }

        let (w, next_running_q, next_running_v) =
            self.wit_nlookup_gadget(wits, doc, q, v, running_q, running_v, "nldoc");
        wits = w;

        (wits, next_running_q, next_running_v)
    }

    fn wit_nlookup_gadget(
        &self,
        mut wits: FxHashMap<String, Value>,
        table: Vec<Integer>,
        q: Vec<usize>,
        v: Vec<Integer>,
        running_q: Option<Vec<Integer>>,
        running_v: Option<Integer>,
        id: &str,
    ) -> (FxHashMap<String, Value>, Vec<Integer>, Integer) {
        let sc_l = logmn(table.len()); // sum check rounds

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
        wits.insert(
            format!("{}_prev_running_claim", id),
            new_wit(prev_running_v.clone()),
        );
        // q.push(prev_running_q);

        // q processing
        let mut combined_q = Integer::from(0);
        let mut next_slot = Integer::from(1);
        for i in 0..self.batch_size {
            // regular
            let mut qjs = vec![];
            let q_name = format!("{}_eq_{}", id, i);
            for j in 0..sc_l {
                let qj = (q[i] >> j) & 1;
                wits.insert(format!("{}_q_{}", q_name, (sc_l - 1 - j)), new_wit(qj));
                qjs.push(qj);
            }

            for qj in qjs.into_iter().rev() {
                combined_q += (Integer::from(qj) * &next_slot);
                next_slot *= Integer::from(2);
            }
        }

        wits.insert(format!("{}_combined_q", id), new_wit(combined_q.clone()));

        for j in 0..sc_l {
            // running
            let q_name = format!("{}_eq_{}", id, q.len()); //v.len() - 1);
            wits.insert(
                format!("{}_q_{}", q_name, j),
                new_wit(prev_running_q[j].clone()),
            );
        }

        // sponge

        let mut sponge = Sponge::new_with_constants(&self.pc, Mode::Simplex);
        let acc = &mut ();

        let mut pattern = vec![
            SpongeOp::Absorb((self.batch_size + sc_l + 2) as u32), // vs, combined_q, running q,v
            SpongeOp::Squeeze(1),
        ];
        for i in 0..sc_l {
            // sum check rounds
            pattern.append(&mut vec![SpongeOp::Absorb(3), SpongeOp::Squeeze(1)]);
        }

        sponge.start(IOPattern(pattern), None, acc);

        let mut query = vec![combined_q]; // q_comb, v1,..., vm, running q, running v
        query.extend(v);
        query.append(&mut prev_running_q.clone());
        query.append(&mut vec![prev_running_v.clone()]);
        let query_f: Vec<F> = query.into_iter().map(|i| int_to_ff(i)).collect();

        //println!("R1CS sponge absorbs {:#?}", query_f);

        SpongeAPI::absorb(
            &mut sponge,
            (self.batch_size + sc_l + 2) as u32,
            &query_f,
            acc,
        );

        // TODO - what needs to be public?

        // generate claim r
        let rand = SpongeAPI::squeeze(&mut sponge, 1, acc);
        //println!("R1CS sponge squeezes {:#?}", rand);
        let claim_r = Integer::from_digits(rand[0].to_repr().as_ref(), Order::Lsf); // TODO?
        wits.insert(format!("{}_claim_r", id), new_wit(claim_r.clone()));

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
            let prev_rand = match i {
                1 => Integer::from(0),
                _ => sc_rs[i - 2].clone(),
            };
            // let query = vec![]; //vs TODO?
            let query = vec![
                int_to_ff(g_const.clone()),
                int_to_ff(g_x.clone()),
                int_to_ff(g_xsq.clone()),
            ];

            //println!("R1CS sponge absorbs {:#?}", query);
            SpongeAPI::absorb(&mut sponge, 3, &query, acc);
            let rand = SpongeAPI::squeeze(&mut sponge, 1, acc);
            //println!("R1CS sponge squeezes {:#?}", rand);
            let sc_r = Integer::from_digits(rand[0].to_repr().as_ref(), Order::Lsf); // TODO?

            sc_rs.push(sc_r.clone());
            wits.insert(format!("{}_sc_r_{}", id, i), new_wit(sc_r.clone()));
        }
        sponge.finish(acc).unwrap();

        // last claim = g_v(r_v)
        //println!("sc rs {:#?}", sc_rs.clone());
        g_xsq *= &sc_rs[sc_rs.len() - 1];
        g_xsq *= &sc_rs[sc_rs.len() - 1];
        g_x *= &sc_rs[sc_rs.len() - 1];
        g_const += &g_x;
        g_const += &g_xsq;

        let last_claim = g_const.rem_floor(cfg().field().modulus());
        wits.insert(format!("{}_sc_last_claim", id), new_wit(last_claim.clone()));

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
        current_state: usize, // pass in the real one, let's deal with all the dummy stuff under
        // the hood
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
            wits.insert(format!("char_{}", i), new_wit(self.dfa.ab_to_num(&doc_i)));
            next_state = self.dfa.delta(state_i, &doc_i.clone()).unwrap();
            wits.insert(format!("state_{}", i), new_wit(state_i));

            state_i = next_state;
        }
        wits.insert(format!("state_{}", self.batch_size), new_wit(state_i));

        wits.insert(
            format!("accepting"),
            new_bool_wit(self.prover_accepting_state(batch_num, next_state)),
        );
        //println!("wits {:#?}", wits);

        match self.commit_type {
            JCommit::HashChain => {
                for i in 0..=self.batch_size {
                    wits.insert(format!("i_{}", i), new_wit(batch_num * self.batch_size + i));
                }
                // values not actually checked or used
                wits.insert(format!("first_hash_input"), new_wit(0));
                wits.insert(format!("random_hash_result"), new_wit(0));
                wits.insert(format!("z_hash_input"), new_wit(0));
                (wits, next_state, None, None)
            }
            JCommit::Nlookup => {
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
            }
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
        println!("DFA Size: {:#?}", dfa.trans.len());

        let chars: Vec<String> = doc.chars().map(|c| c.to_string()).collect();

        // doc to usizes - can I use this elsewhere too? TODO
        let mut usize_doc = vec![];
        let mut int_doc = vec![];
        for c in chars.clone().into_iter() {
            let u = dfa.ab_to_num(&c.to_string());
            usize_doc.push(u);
            int_doc.push(<G1 as Group>::Scalar::from(u as u64));
        }

        for s in batch_sizes {
            for b in vec![JBatching::NaivePolys, JBatching::Nlookup] {
                for c in vec![JCommit::HashChain, JCommit::Nlookup] {
                    println!("\nNew");
                    let sc = Sponge::<<G1 as Group>::Scalar, typenum::U2>::api_constants(
                        Strength::Standard,
                    );
                    println!("Doc:{:#?}", doc);
                    let mut r1cs_converter = R1CS::new(
                        &dfa,
                        &doc.chars().map(|c| c.to_string()).collect(),
                        s,
                        sc.clone(),
                        Some(b.clone()),
                        Some(c.clone()),
                    );

                    let reef_commit =
                        gen_commitment(r1cs_converter.commit_type, usize_doc.clone(), &sc);
                    r1cs_converter.set_commitment(reef_commit.clone());

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
                            == costs::full_round_cost_model_nohash(
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

    // #[test]
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

    //#[test]
    fn big() {
        init();
        let ASCIIchars: Vec<char> = (0..128).filter_map(std::char::from_u32).collect();
        test_func_no_hash(
            ASCIIchars.into_iter().collect::<String>(),
            "^.*our technology.*$".to_string(),
            fs::read_to_string("gov_text.txt").unwrap(),
            vec![1],
            true,
        );
    }
}
