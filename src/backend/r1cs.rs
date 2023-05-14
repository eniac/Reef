use crate::backend::nova::int_to_ff;
use crate::backend::{commitment::*, costs::*, r1cs_helper::*};
use crate::nfa::{EPSILON, NFA};
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
};
use rug::{integer::Order, ops::RemRounding, Integer};

pub struct R1CS<'a, F: PrimeField> {
    pub nfa: &'a NFA,
    pub table: Vec<Integer>,
    pub batching: JBatching,
    pub commit_type: JCommit,
    pub reef_commit: Option<ReefCommitment<F>>,
    assertions: Vec<Term>,
    // perhaps a misleading name, by "public inputs", we mean "circ leaves these wires exposed from
    // the black box, and will not optimize them away"
    // at the nova level, we will "reprivitize" everything, it's just important to see the hooks
    // sticking out here
    pub_inputs: Vec<Term>,
    pub batch_size: usize,
    pub cdoc: Vec<String>,
    pub udoc: Vec<usize>,
    pub idoc: Vec<Integer>,
    pub doc_extend: usize,
    is_match: bool,
    pub substring: (usize, usize), // todo getters
    pub pc: PoseidonConstants<F, typenum::U4>,
}

impl<'a, F: PrimeField> R1CS<'a, F> {
    pub fn new(
        nfa: &'a NFA,
        doc: &Vec<String>,
        batch_size: usize,
        pcs: PoseidonConstants<F, typenum::U4>,
        batch_override: Option<JBatching>,
        commit_override: Option<JCommit>,
    ) -> Self {
        let nfa_match = nfa.is_match(doc);
        let is_match = nfa_match.is_some();

        let batching;
        let commit;
        let opt_batch_size;
        let cost: usize;
        if batch_size > 0 {
            (batching, commit, opt_batch_size, cost) = match (batch_override, commit_override) {
                (Some(b), Some(c)) => (
                    b,
                    c,
                    batch_size,
                    full_round_cost_model(nfa, batch_size, b, nfa_match, doc.len(), c),
                ),
                (Some(b), _) => {
                    opt_commit_select_with_batch(nfa, batch_size, nfa_match, doc.len(), b)
                }
                (None, Some(c)) => opt_cost_model_select_with_commit(
                    &nfa,
                    batch_size,
                    nfa.is_match(doc),
                    doc.len(),
                    c,
                ),
                (None, None) => {
                    opt_cost_model_select_with_batch(&nfa, batch_size, nfa_match, doc.len())
                }
            };
        } else {
            (batching, commit, opt_batch_size, cost) = opt_cost_model_select(
                &nfa,
                0,
                logmn(doc.len()) - 1,
                nfa_match,
                doc.len(),
                commit_override,
                batch_override,
            );
        }

        let sel_batch_size = opt_batch_size;

        println!(
            "batch type: {:#?}, commit type: {:#?}, batch_size {:#?}, cost {:#?}",
            batching, commit, sel_batch_size, cost
        );

        let mut batch_doc = doc.clone();

        if matches!(commit, JCommit::Nlookup) {
            batch_doc.push(EPSILON.clone()); // MUST do to make batching work w/commitments
        }

        let mut epsilon_to_add = sel_batch_size - (batch_doc.len() % sel_batch_size);

        if batch_doc.len() % sel_batch_size == 0 {
            epsilon_to_add = 0;
        }

        let mut substring = (0, batch_doc.len());

        match nfa_match {
            // todo remove this bs call
            Some((start, end)) => {
                match commit {
                    JCommit::HashChain => {
                        assert!(
                            end == batch_doc.len(),
                            "for HashChain commitment, Regex must handle EOD, switch commit type or change Regex r to r$ or r.*$"
                        );
                        substring = (start, batch_doc.len()); // ... right?
                    }
                    JCommit::Nlookup => {
                        substring = (start, end); // exact
                    }
                }
            }
            None => { // see above
            }
        }

        // generate T
        let mut table = vec![];
        for (ins, c, out) in nfa.deltas() {
            table.push(
                Integer::from(
                    (ins * nfa.nstates() * nfa.nchars())
                        + (out * nfa.nchars())
                        + nfa.ab_to_num(&c.to_string()),
                )
                .rem_floor(cfg().field().modulus()),
            );
        }

        // need to round out table size
        let base: usize = 2;
        while table.len() < base.pow(logmn(table.len()) as u32) {
            table.push(
                Integer::from(
                    (nfa.nstates() * nfa.nstates() * nfa.nchars())
                        + (nfa.nstates() * nfa.nchars())
                        + nfa.nchars(),
                )
                .rem_floor(cfg().field().modulus()),
            );
        }

        // generate usize doc
        // doc to usizes - can I use this elsewhere too? TODO
        let mut usize_doc = vec![];
        let mut int_doc = vec![];
        for c in batch_doc.clone().into_iter() {
            let u = nfa.ab_to_num(&c.to_string());
            usize_doc.push(u);
            int_doc.push(Integer::from(u));
        }

        Self {
            nfa,
            table,    // TODO fix else
            batching, // TODO
            commit_type: commit,
            reef_commit: None,
            assertions: Vec::new(),
            pub_inputs: Vec::new(),
            batch_size: sel_batch_size,
            cdoc: batch_doc, //chars
            udoc: usize_doc, //usizes
            idoc: int_doc,   // big ints
            doc_extend: epsilon_to_add,
            is_match,
            substring,
            pc: pcs,
        }
    }

    pub fn set_commitment(&mut self, rc: ReefCommitment<F>) {
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

    pub fn prover_calc_hash(
        &self,
        start_hash_or_blind: F,
        blind: bool,
        start: usize,
        num_iters: usize,
    ) -> F {
        let mut next_hash;

        if start == 0 && blind {
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

        let parameter = IOPattern(vec![SpongeOp::Absorb(3), SpongeOp::Squeeze(1)]);
        for b in 0..num_iters {
            //self.batch_size {
            let access_at = start + b;
            if access_at < self.substring.1 {
                // else nothing

                // expected poseidon
                let mut sponge = Sponge::new_with_constants(&self.pc, Mode::Simplex);
                let acc = &mut ();

                sponge.start(parameter.clone(), None, acc);
                SpongeAPI::absorb(
                    &mut sponge,
                    3,
                    &[
                        next_hash[0],
                        F::from(self.udoc[access_at].clone() as u64),
                        F::from((access_at) as u64),
                    ],
                    acc,
                );
                next_hash = SpongeAPI::squeeze(&mut sponge, 1, acc);
                sponge.finish(acc).unwrap(); // assert expected hash finished correctly
            }
        }

        next_hash[0]
    }

    // PROVER

    pub fn prover_accepting_state(&self, batch_num: usize, state: usize) -> u64 {
        let mut out = false;

        if self.is_match {
            // proof of membership
            for xi in self.nfa.accepting().into_iter() {
                out = out || (state == xi);
            }
        } else {
            for xi in self.nfa.get_non_final_states().into_iter() {
                out = out || (state == xi);
            }
        }

        //println!("ACCEPTING? {:#?}", out);

        if out {
            1
        } else {
            0
        }
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
                                    new_const(self.nfa.nstates() * self.nfa.nchars()),
                                ],
                            ),
                            term(
                                Op::PfNaryOp(PfNaryOp::Mul),
                                vec![
                                    new_var(format!("state_{}", i)),
                                    new_const(self.nfa.nchars()),
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
        let final_states = self.nfa.accepting();
        let non_final_states = self.nfa.get_non_final_states();
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
            Op::Ite,
            vec![
                term(Op::Eq, vec![new_const(0), vanishing_poly]),
                term(Op::Eq, vec![new_var(format!("accepting")), new_const(1)]),
                term(Op::Eq, vec![new_var(format!("accepting")), new_const(0)]),
            ],
        );

        self.assertions.push(match_term);
        self.pub_inputs.push(new_var(format!("accepting")));
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
        let final_cs = css.get("main");

        let mut circ_r1cs = to_r1cs(final_cs, cfg());
        circ_r1cs = reduce_linearities(circ_r1cs, cfg());

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
        //let l_time = Instant::now();
        let lookup = self.lookup_idxs(false);

        let mut evals = vec![];
        for (si, c, so) in self.nfa.deltas() {
            evals.push(
                Integer::from(
                    (si * self.nfa.nstates() * self.nfa.nchars())
                        + (so * self.nfa.nchars())
                        + self.nfa.ab_to_num(&c.to_string()),
                )
                .rem_floor(cfg().field().modulus()),
            );
        }

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
        // 254 bits to work with
        let num_cqs = ((num_eqs * num_q_bits) as f64 / 254.0).ceil() as usize;
        //println!("num cqs {:#?}", num_cqs);

        let mut cq = 0;
        let mut combined_qs = vec![];
        let mut combined_q = new_const(0); // dummy, not used
        let mut next_slot = Integer::from(1);

        while cq < num_cqs {
            //println!("start loop {:#?}", cq);
            for i in 0..num_eqs {
                for j in 0..num_q_bits {
                    //println!("{:#?} >= {:#?} ?", (i * num_q_bits) + j, 254 * (cq + 1));

                    if (i * num_q_bits) + j >= 254 * (cq + 1)
                        || (i == num_eqs - 1 && j == num_q_bits - 1)
                    {
                        cq += 1;
                        combined_qs.push(combined_q.clone());
                        combined_q = new_const(0);
                        next_slot = Integer::from(1);
                    } else {
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
            }
        }

        assert_eq!(num_cqs, combined_qs.len());

        for cq in 0..num_cqs {
            let combined_q_eq = term(
                Op::Eq,
                vec![
                    combined_qs[cq].clone(),
                    new_var(format!("{}_combined_q_{}", id, cq)),
                ],
            );

            self.assertions.push(combined_q_eq);
            self.pub_inputs
                .push(new_var(format!("{}_combined_q_{}", id, cq)));
        }
    }

    // C_1 = LHS/"claim"
    fn sum_check_circuit(&mut self, c_1: Term, num_rounds: usize, id: &str) {
        // first round claim
        let mut claim = c_1.clone();

        for j in 1..=num_rounds {
            // P makes a claim g_j(X_j) about a slice of its large multilinear polynomial
            // g_j is degree 2 in our case

            // V checks g_{j-1}(r_{j-1}) = g_j(0) + g_j(1)
            // Ax^2 + Bx + C -> A + B + C + C
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
        self.nlookup_gadget(lookups, self.nfa.nedges(), "nl");

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
            char_lookups.push(new_var(format!("char_{}", c)));
        }

        self.nlookup_gadget(char_lookups, self.udoc.len(), "nldoc");
    }

    fn nlookup_gadget(&mut self, mut lookup_vals: Vec<Term>, t_size: usize, id: &str) {
        // TODO pub inputs -> can make which priv?
        // last state_batch is final "next_state" output
        // v_{batch-1} = (state_{batch-1}, c, state_batch)
        // v_batch = T eval check (optimization)

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

        self.sum_check_circuit(lhs, sc_l, id);

        let mut eq_evals = vec![new_const(0)]; // dummy for horners
        for i in 0..self.batch_size + 1 {
            eq_evals.push(self.bit_eq_circuit(sc_l, i, id));
        }
        let eq_eval = horners_circuit_vars(&eq_evals, new_var(format!("{}_claim_r", id)));

        // make combined_q
        self.combined_q_circuit(self.batch_size, sc_l, id); // running claim q not
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
        isize,
    ) {
        match self.batching {
            JBatching::NaivePolys => {
                let (
                    wits,
                    next_state,
                    next_doc_running_claim_q,
                    next_doc_running_claim_v,
                    start_epsilons,
                ) = self.gen_wit_i_polys(
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
                    start_epsilons,
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

    fn access_doc_at(&self, batch_num: usize, i: usize) -> (usize, bool) {
        let access_at = batch_num * self.batch_size + i;

        match self.commit_type {
            JCommit::HashChain => (access_at, access_at >= self.substring.1),

            JCommit::Nlookup => {
                if access_at >= self.substring.1 {
                    //self.udoc.len() - 1 {
                    (self.udoc.len() - 1, true)
                } else {
                    (access_at, false)
                }
            }
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
        isize,
    ) {
        let mut wits = FxHashMap::default();

        // generate claim v's (well, v isn't a real named var, generate the states/chars)
        let mut state_i = current_state;
        let mut next_state = 0;

        let mut v = vec![];
        let mut q = vec![];
        let mut start_epsilons = -1;
        for i in 1..=self.batch_size {
            let (access_at, is_epsilon) = self.access_doc_at(batch_num, i - 1 + self.substring.0);

            let char_num;

            //println!("is EPSILON? {:#?}", is_epsilon);
            if is_epsilon {
                next_state = self.nfa.delta(state_i, EPSILON).unwrap();
                char_num = self.nfa.nchars();
            } else {
                next_state = self.nfa.delta(state_i, &self.cdoc[access_at]).unwrap();
                char_num = self.udoc[access_at];
            }

            //println!("Char {:#?}", char_num);
            //println!("Next State {:#?}", next_state);

            wits.insert(format!("char_{}", i - 1), new_wit(char_num));
            wits.insert(format!("state_{}", i - 1), new_wit(state_i));

            if (start_epsilons == -1) && is_epsilon {
                start_epsilons = (i - 1) as isize;
            }

            // v_i = (state_i * (#states*#chars)) + (state_i+1 * #chars) + char_i
            let v_i = Integer::from(
                (state_i * self.nfa.nstates() * self.nfa.nchars())
                    + (next_state * self.nfa.nchars())
                    + char_num,
            )
            .rem_floor(cfg().field().modulus());
            v.push(v_i.clone());
            wits.insert(format!("v_{}", i), new_wit(v_i.clone()));

            q.push(self.table.iter().position(|val| val == &v_i).unwrap());

            state_i = next_state;
        }

        // last state
        wits.insert(format!("state_{}", self.batch_size), new_wit(next_state));

        assert!(running_q.is_some() || batch_num == 0);
        assert!(running_v.is_some() || batch_num == 0);
        let (w, next_running_q, next_running_v) =
            self.wit_nlookup_gadget(wits, &self.table, q, v, running_q, running_v, "nl");
        wits = w;

        wits.insert(
            format!("accepting"),
            new_wit(self.prover_accepting_state(batch_num, next_state)),
        );

        match self.commit_type {
            JCommit::HashChain => {
                for i in 0..=self.batch_size {
                    wits.insert(
                        format!("i_{}", i),
                        new_wit(batch_num * self.batch_size + i + self.substring.0),
                    );
                }
                (
                    wits,
                    next_state,
                    Some(next_running_q),
                    Some(next_running_v),
                    None,
                    None,
                    start_epsilons,
                )
            }
            JCommit::Nlookup => {
                assert!(doc_running_q.is_some() || batch_num == 0);
                assert!(doc_running_v.is_some() || batch_num == 0);
                let (w, next_doc_running_q, next_doc_running_v) =
                    self.wit_nlookup_doc_commit(wits, batch_num, doc_running_q, doc_running_v);
                wits = w;
                (
                    wits,
                    next_state,
                    Some(next_running_q),
                    Some(next_running_v),
                    Some(next_doc_running_q),
                    Some(next_doc_running_v),
                    start_epsilons,
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
        let mut v = vec![];
        let mut q = vec![];
        for i in 0..self.batch_size {
            let (access_at, _is_epsilon) = self.access_doc_at(batch_num, i + self.substring.0);
            q.push(access_at);

            v.push(self.idoc[access_at].clone());
        }

        let (w, next_running_q, next_running_v) =
            self.wit_nlookup_gadget(wits, &self.idoc, q, v, running_q, running_v, "nldoc");
        wits = w;

        (wits, next_running_q, next_running_v)
    }

    fn wit_nlookup_gadget(
        &self,
        mut wits: FxHashMap<String, Value>,
        table: &Vec<Integer>,
        q: Vec<usize>,
        v: Vec<Integer>,
        running_q: Option<Vec<Integer>>,
        running_v: Option<Integer>,
        id: &str,
    ) -> (FxHashMap<String, Value>, Vec<Integer>, Integer) {
        let sc_l = logmn(table.len()); // sum check rounds

        // running claim about T (optimization)
        // if first (not yet generated)
        let prev_running_q = match running_q {
            Some(q) => q,
            None => vec![Integer::from(0); sc_l],
        };
        let prev_running_v = match running_v {
            Some(v) => v,
            None => table[0].clone(),
        };

        wits.insert(
            format!("{}_prev_running_claim", id),
            new_wit(prev_running_v.clone()),
        );
        // q.push(prev_running_q);

        // q processing
        let mut combined_qs = vec![];
        let num_cqs = ((self.batch_size * sc_l) as f64 / 254.0).ceil() as usize;

        println!("num cqs {:#?}", num_cqs);

        let mut cq = 0;
        while cq < num_cqs {
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

                let mut j = 0;
                for qj in qjs.into_iter().rev() {
                    if (i * sc_l) + j >= 254 * (cq + 1)
                        || (i == self.batch_size - 1 && j == sc_l - 1)
                    {
                        cq += 1;
                        // println!("PUSH CQ");
                        combined_qs.push(combined_q.clone());
                        combined_q = Integer::from(0);
                        next_slot = Integer::from(1);
                    } else {
                        combined_q += Integer::from(qj) * &next_slot;
                        next_slot *= Integer::from(2);
                    }

                    j += 1;
                }
            }
        }

        assert_eq!(num_cqs, combined_qs.len());
        for cq in 0..num_cqs {
            wits.insert(
                format!("{}_combined_q_{}", id, cq),
                new_wit(combined_qs[cq].clone()),
            );
        }

        println!("combined_qs {:#?}", combined_qs);

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

        let mut pattern = match id {
            "nl" => vec![
                SpongeOp::Absorb((self.batch_size + sc_l + 1 + num_cqs) as u32), // vs, combined_q, running q,v
                SpongeOp::Squeeze(1),
            ],
            "nldoc" => vec![
                SpongeOp::Absorb((self.batch_size + sc_l + 2 + num_cqs) as u32), // doc commit, vs, combined_q, running q,v
                SpongeOp::Squeeze(1),
            ],
            _ => panic!("weird tag"),
        };

        for _i in 0..sc_l {
            // sum check rounds
            pattern.append(&mut vec![SpongeOp::Absorb(3), SpongeOp::Squeeze(1)]);
        }

        sponge.start(IOPattern(pattern), None, acc);
        let mut query: Vec<F> = match id {
            "nl" => vec![],
            "nldoc" => match &self.reef_commit {
                Some(ReefCommitment::Nlookup(dcs)) => vec![dcs.commit_doc_hash],
                _ => panic!("commitment not found"),
            },
            _ => panic!("weird tag"),
        };
        for cq in combined_qs {
            query.push(int_to_ff(cq)); // q_comb, v1,..., vm, running q, running v
        }
        for vi in v.into_iter() {
            query.push(int_to_ff(vi));
        }
        query.append(
            &mut prev_running_q
                .clone()
                .into_iter()
                .map(|i| int_to_ff(i))
                .collect(),
        );
        query.push(int_to_ff(prev_running_v.clone()));
        //let query_f: Vec<G1::Scalar> = query.into_iter().map(|i| int_to_ff(i)).collect();

        SpongeAPI::absorb(&mut sponge, query.len() as u32, &query, acc);

        // TODO - what needs to be public?

        // generate claim r
        let rand = SpongeAPI::squeeze(&mut sponge, 1, acc);
        let claim_r = Integer::from_digits(rand[0].to_repr().as_ref(), Order::Lsf); // TODO?
        wits.insert(format!("{}_claim_r", id), new_wit(claim_r.clone()));

        let mut rs = vec![claim_r.clone()];
        for i in 1..(q.len() + 1) {
            rs.push(rs[i - 1].clone() * claim_r.clone());
        }
        // make eq table for this round
        let mut eq_table =
            gen_eq_table(&rs, &q, &prev_running_q.clone().into_iter().rev().collect());
        let mut sc_table = match id {
            "nl" => table.clone(),
            "nldoc" => {
                let base: usize = 2;
                let len = base.pow(logmn(table.len()) as u32) - table.len();

                let mut sct = table.clone();
                sct.extend(vec![Integer::from(0); len]); // ep num = self.nfa.nchars()
                sct
            }
            _ => panic!("weird tag"),
        };

        // generate polynomial g's for sum check
        let mut sc_rs = vec![];
        let mut sc_r = Integer::from(0);
        let mut g_xsq = Integer::from(0);
        let mut g_x = Integer::from(0);
        let mut g_const = Integer::from(0);

        for i in 1..=sc_l {
            (sc_r, g_xsq, g_x, g_const) =
                linear_mle_product(&mut sc_table, &mut eq_table, sc_l, i, &mut sponge);
            //prover_mle_sum_eval(table, &sc_rs, &q, &claim_r, Some(&prev_running_q));

            wits.insert(format!("{}_sc_g_{}_xsq", id, i), new_wit(g_xsq.clone()));
            wits.insert(format!("{}_sc_g_{}_x", id, i), new_wit(g_x.clone()));
            wits.insert(format!("{}_sc_g_{}_const", id, i), new_wit(g_const.clone()));

            sc_rs.push(sc_r.clone());
            wits.insert(format!("{}_sc_r_{}", id, i), new_wit(sc_r.clone()));
        }
        sponge.finish(acc).unwrap();

        // last claim = g_v(r_v)
        let mut last_claim = g_xsq * &sc_r * &sc_r + g_x * &sc_r + g_const;
        last_claim = last_claim.rem_floor(cfg().field().modulus());
        wits.insert(format!("{}_sc_last_claim", id), new_wit(last_claim.clone()));

        // update running claim
        let (_, next_running_v) = prover_mle_partial_eval(
            table,
            &sc_rs, //.clone().into_iter().rev().collect(),
            &(0..table.len()).collect(),
            true,
            None,
        );
        let next_running_q = sc_rs.clone();
        wits.insert(
            format!("{}_next_running_claim", id),
            new_wit(next_running_v.clone()),
        );

        // sanity check - TODO eliminate
        let (_, eq_term) = prover_mle_partial_eval(
            &rs,
            &sc_rs, //.into_iter().rev().collect(),
            &q,
            false,
            Some(&prev_running_q),
        );
        assert_eq!(
            last_claim,
            (eq_term * next_running_v.clone()).rem_floor(cfg().field().modulus())
        );

        // return

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
        isize,
    ) {
        let mut wits = FxHashMap::default();
        let mut state_i = current_state;
        let mut next_state = 0;

        let mut start_epsilons = -1;
        for i in 0..self.batch_size {
            let (access_at, is_epsilon) = self.access_doc_at(batch_num, i + self.substring.0);

            if is_epsilon {
                wits.insert(format!("char_{}", i), new_wit(self.nfa.nchars()));
                next_state = self.nfa.delta(state_i, EPSILON).unwrap();
            } else {
                wits.insert(format!("char_{}", i), new_wit(self.udoc[access_at]));
                next_state = self
                    .nfa
                    .delta(state_i, &self.cdoc[access_at].clone())
                    .unwrap();
            }

            wits.insert(format!("state_{}", i), new_wit(state_i));

            if (start_epsilons == -1) && is_epsilon {
                start_epsilons = i as isize;
            }

            state_i = next_state;
        }
        wits.insert(format!("state_{}", self.batch_size), new_wit(state_i));

        wits.insert(
            format!("accepting"),
            new_wit(self.prover_accepting_state(batch_num, next_state)),
        );

        match self.commit_type {
            JCommit::HashChain => {
                for i in 0..=self.batch_size {
                    wits.insert(
                        format!("i_{}", i),
                        new_wit(batch_num * self.batch_size + i + self.substring.0),
                    );
                }
                // values not actually checked or used
                (wits, next_state, None, None, start_epsilons)
            }
            JCommit::Nlookup => {
                assert!(doc_running_q.is_some() || batch_num == 0);
                assert!(doc_running_v.is_some() || batch_num == 0);
                let (w, next_doc_running_q, next_doc_running_v) =
                    self.wit_nlookup_doc_commit(wits, batch_num, doc_running_q, doc_running_v);
                wits = w;
                (
                    wits,
                    next_state,
                    Some(next_doc_running_q),
                    Some(next_doc_running_v),
                    start_epsilons,
                )
            }
        }
    }
}

pub fn ceil_div(a: usize, b: usize) -> usize {
    (a + b - 1) / b
}

#[cfg(test)]
mod tests {

    use crate::backend::costs;
    use crate::backend::r1cs::*;
    use crate::nfa::NFA;
    use crate::regex::Regex;
    use neptune::Strength;
    use nova_snark::traits::Group;
    type G1 = pasta_curves::pallas::Point;

    #[test]
    fn mle_linear_basic() {
        init();

        let mut evals = vec![
            Integer::from(2),
            Integer::from(3),
            Integer::from(5),
            Integer::from(7),
            Integer::from(9),
            Integer::from(13),
            Integer::from(17),
            Integer::from(19),
        ];

        let table = evals.clone();

        let qs = vec![2, 1, 7];
        for last_q in vec![
            vec![Integer::from(2), Integer::from(3), Integer::from(5)],
            //vec![Integer::from(0), Integer::from(1), Integer::from(0)],
        ] {
            let claims = vec![
                Integer::from(3),
                Integer::from(9),
                Integer::from(27),
                Integer::from(81),
            ];

            let mut term = Integer::from(0);
            for i in 0..qs.len() {
                term += evals[qs[i]].clone() * &claims[i];
            }

            let mut eq_a = gen_eq_table(&claims, &qs, &last_q.clone().into_iter().rev().collect());

            // claim check
            let (_, running_v) = prover_mle_partial_eval(
                &evals,
                &last_q, //.clone().into_iter().rev().collect(),
                &(0..evals.len()).collect(),
                true,
                None,
            );
            term += running_v * &claims[3];

            let mut claim: Integer = evals
                .iter()
                .zip(eq_a.iter())
                .map(|(ti, eqi)| ti * eqi)
                .sum();

            assert_eq!(
                term.rem_floor(cfg().field().modulus()),
                claim.clone().rem_floor(cfg().field().modulus())
            );

            let sc =
                Sponge::<<G1 as Group>::Scalar, typenum::U4>::api_constants(Strength::Standard);

            let mut sponge = Sponge::new_with_constants(&sc, Mode::Simplex);
            let acc = &mut ();

            let mut pattern = vec![];
            for _i in 0..3 {
                // sum check rounds
                pattern.append(&mut vec![SpongeOp::Absorb(3), SpongeOp::Squeeze(1)]);
            }

            sponge.start(IOPattern(pattern), None, acc);

            let mut sc_rs = vec![];
            for i in 1..=3 {
                let (r_i, xsq, x, con) =
                    linear_mle_product(&mut evals, &mut eq_a, 3, i, &mut sponge);

                let g0_g1 = Integer::from(2) * &con + &x + &xsq;
                assert_eq!(
                    claim.rem_floor(cfg().field().modulus()),
                    g0_g1.rem_floor(cfg().field().modulus())
                );

                claim = xsq * &r_i * &r_i + x * &r_i + con;
                claim = claim.rem_floor(cfg().field().modulus());

                sc_rs.push(r_i);
            }

            // next
            let (_, next_running_v) = prover_mle_partial_eval(
                &table,
                &sc_rs, //.clone().into_iter().rev().collect(),
                &(0..table.len()).collect(),
                true,
                None,
            );

            // sanity check - TODO eliminate
            let (_, eq_term) = prover_mle_partial_eval(
                &claims,
                &sc_rs, //.into_iter().rev().collect(),
                &qs,
                false,
                Some(&last_q), //.into_iter().rev().collect()),
            );
            assert_eq!(
                claim, // last claim
                (eq_term * next_running_v.clone()).rem_floor(cfg().field().modulus())
            );

            sponge.finish(acc).unwrap();
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

    fn test_func_no_hash(
        ab: String,
        rstr: String,
        doc: String,
        batch_sizes: Vec<usize>,
        expected_match: bool,
    ) {
        let r = Regex::new(&rstr);
        let nfa = NFA::new(&ab[..], r);

        let chars: Vec<String> = doc.chars().map(|c| c.to_string()).collect();

        for s in batch_sizes {
            for c in vec![JCommit::HashChain, JCommit::Nlookup] {
                for b in vec![JBatching::NaivePolys, JBatching::Nlookup] {
                    let sc = Sponge::<<G1 as Group>::Scalar, typenum::U4>::api_constants(
                        Strength::Standard,
                    );
                    let mut r1cs_converter = R1CS::new(
                        &nfa,
                        &chars,
                        s,
                        sc.clone(),
                        Some(b.clone()),
                        Some(c.clone()),
                    );

                    let reef_commit = gen_commitment(
                        r1cs_converter.commit_type,
                        r1cs_converter.udoc.clone(),
                        &sc,
                    );
                    r1cs_converter.set_commitment(reef_commit.clone());

                    assert_eq!(expected_match, r1cs_converter.is_match);

                    let mut running_q = None;
                    let mut running_v = None;
                    let mut doc_running_q = None;
                    let mut doc_running_v = None;

                    let (pd, _vd) = r1cs_converter.to_circuit();

                    let mut current_state = nfa.get_init_state();

                    let mut values;
                    let mut next_state;

                    let mut _start_epsilons;
                    let num_steps = ceil_div(
                        r1cs_converter.substring.1 - r1cs_converter.substring.0,
                        r1cs_converter.batch_size,
                    );
                    for i in 0..num_steps {
                        (
                            values,
                            next_state,
                            running_q,
                            running_v,
                            doc_running_q,
                            doc_running_v,
                            _start_epsilons,
                        ) = r1cs_converter.gen_wit_i(
                            i,
                            current_state,
                            running_q.clone(),
                            running_v.clone(),
                            doc_running_q.clone(),
                            doc_running_v.clone(),
                        );

                        pd.check_all(&values);
                        // for next i+1 round
                        current_state = next_state;
                    }

                    let rq = match running_q {
                        Some(x) => Some(x.into_iter().map(|i| int_to_ff(i)).collect()),
                        None => None,
                    };
                    let rv = match running_v {
                        Some(x) => Some(int_to_ff(x)),
                        None => None,
                    };
                    let drq = match doc_running_q {
                        Some(x) => Some(x.into_iter().map(|i| int_to_ff(i)).collect()),
                        None => None,
                    };
                    let drv = match doc_running_v {
                        Some(x) => Some(int_to_ff(x)),
                        None => None,
                    };
                    //dummy hash check (hashes not generated at this level)
                    let dummy_hash = match &reef_commit {
                        ReefCommitment::HashChain(hcs) => Some(hcs.commit),
                        _ => None,
                    };

                    final_clear_checks(
                        r1cs_converter.batching,
                        reef_commit,
                        <G1 as Group>::Scalar::from(1), // dummy, not checked
                        &r1cs_converter.table,
                        r1cs_converter.udoc.len(),
                        rq,
                        rv,
                        dummy_hash, // final hash not checked
                        drq,
                        drv,
                    );

                    println!(
                        "cost model: {:#?}",
                        costs::full_round_cost_model_nohash(
                            &nfa,
                            r1cs_converter.batch_size,
                            b.clone(),
                            nfa.is_match(&chars),
                            doc.len(),
                            c,
                        )
                    );
                    println!("actual cost: {:#?}", pd.r1cs.constraints.len());
                    println!("\n\n\n");

                                   assert!(
                                      pd.r1cs.constraints.len() as usize
                                          == costs::full_round_cost_model_nohash(
                                              &nfa,
                                              r1cs_converter.batch_size,
                                              b.clone(),
                                              nfa.is_match(&chars),
                                              doc.len(),
                                              c
                                          )
                                  );
                     // deal with later TODO
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
    fn nfa_2() {
        init();
        test_func_no_hash(
            "ab".to_string(),
            "^ab$".to_string(),
            "ab".to_string(),
            vec![0, 1],
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
    fn nfa_star() {
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
            vec![0, 1, 2, 4],
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
    fn nfa_non_match() {
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
    fn nfa_bad_1() {
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
    fn nfa_bad_substring() {
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
    fn nfa_bad_substring_2() {
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
    fn nfa_ok_substring() {
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

    #[test]
    fn weird_batch_size() {
        init();
        test_func_no_hash(
            "helowrd".to_string(),
            "^hello.*$".to_string(),
            "helloworld".to_string(),
            vec![3, 4, 6, 7],
            true,
        );

        test_func_no_hash(
            "helowrd".to_string(),
            "^hello$".to_string(),
            "helloworld".to_string(),
            vec![3, 4, 6, 7],
            false,
        );
    }

    #[test]
    fn r1cs_q_overflow() {
        init();
        test_func_no_hash(
            "abcdefg".to_string(),
            "gaa*bb*cc*dd*ee*f".to_string(),
            "gaaaaaabbbbbbccccccddddddeeeeeef".to_string(),
            vec![33],
            true,
        );

        test_func_no_hash(
            "abcdefg".to_string(),
            "gaaaaaabbbbbbccccccddddddeeeeeef".to_string(),
            "gaaaaaabbbbbbccccccddddddeeeeeef".to_string(),
            vec![33],
            true,
        );
    }

    fn big() {
        use std::fs;

        init();
        let ascii_chars: Vec<char> = (0..128).filter_map(std::char::from_u32).collect();
        test_func_no_hash(
            ascii_chars.into_iter().collect::<String>(),
            "^.*our technology.*$".to_string(),
            fs::read_to_string("gov_text.txt").unwrap(),
            vec![1],
            true,
        );
    }

    fn test_func_no_hash_kstride(
        ab: String,
        rstr: String,
        doc: String,
        batch_sizes: Vec<usize>,
        k: usize,
    ) {
        let r = Regex::new(&rstr);
        let mut nfa = NFA::new(&ab[..], r);
        let mut d = doc.chars().map(|c| c.to_string()).collect();
        d = nfa.k_stride(k, &d);
        let nfa_match = nfa.is_match(&d);
        // println!(
        //     "DFA Size: {:#?}, |doc| : {}, |ab| : {}, match: {:?}",
        //     nfa.nedges(),
        //     d.len(),
        //     nfa.ab.len(),
        //     nfa_match
        // );

        //let chars: Vec<String> = d.clone();
        //.chars().map(|c| c.to_string()).collect();

        for s in batch_sizes {
            for b in vec![JBatching::NaivePolys, JBatching::Nlookup] {
                for c in vec![JCommit::HashChain, JCommit::Nlookup] {
                    println!("Batching {:#?}", b.clone());
                    println!("Commit {:#?}", c);
                    println!("K {:#?}", k);
                    println!(
                        "cost model: {:#?}",
                        costs::full_round_cost_model(&nfa, s, b.clone(), nfa_match, d.len(), c,)
                    );
                }
            }
        }
    }

    #[test]
    fn k_stride2() {
        init();
        let preamble: String = "ffffabcdffffabcd".to_string();
        let ab = "abcdef".to_string();
        for i in 0..9 {
            test_func_no_hash_kstride(
                ab.clone(),
                "^hello.*$".to_string(),
                preamble.clone(),
                vec![1],
                i,
            );
        }
    }

    #[test]
    fn k_stride() {
        init();
        let preamble: String = "we the people in order to form a more perfect union, establish justic ensure domestic tranquility, provide for the common defense, promote the general welfare and procure the blessings of liberty to ourselves and our posterity do ordain and establish this ".to_string();
        let ab = " ,abcdefghijlmnopqrstuvwy".to_string();
        for i in 0..9 {
            test_func_no_hash_kstride(
                ab.clone(),
                "^.*order.to.*$".to_string(),
                preamble.clone(),
                vec![1],
                i,
            );
        }
    }
}
