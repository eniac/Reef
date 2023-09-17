use crate::backend::nova::int_to_ff;
use crate::backend::{commitment::*, costs::*, r1cs_helper::*};
use crate::openset::OpenSet;
use crate::safa::{Either, Skip, SAFA};
use crate::trace::{Trace, TraceElem};
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
};
use petgraph::{
    graph::{EdgeReference, NodeIndex},
    prelude::Dfs,
    visit::{EdgeRef, VisitMap},
    Incoming,
};
use rug::{integer::Order, ops::RemRounding, Integer};
use std::cmp::max;
use std::collections::HashSet;
use std::collections::LinkedList;

pub struct R1CS<'a, F: PrimeField, C: Clone> {
    pub safa: &'a SAFA<C>,
    foralls_w_kids: FxHashMap<usize, Vec<usize>>,
    pub num_ab: FxHashMap<Option<C>, usize>,
    pub table: Vec<Integer>,
    max_offsets: usize,
    pub reef_commit: Option<ReefCommitment<F>>,
    assertions: Vec<Term>,
    // perhaps a misleading name, by "public inputs", we mean "circ leaves these wires exposed from
    // the black box, and will not optimize them away"
    // at the nova level, we will "reprivitize" everything, it's just important to see the hooks
    // sticking out here
    pub_inputs: Vec<Term>,
    pub batch_size: usize,
    //pub cdoc: Vec<String>,
    pub udoc: Vec<usize>,
    pub idoc: Vec<Integer>,
    ep_num: usize,
    star_num: usize,
    pub doc_extend: usize,
    is_match: bool,
    // circuit crap
    stack_ptr_circ_count: usize,
    max_branches: usize,
    pub max_stack: usize,
    pub num_states: usize,
    kid_padding: usize,
    // witness crap
    pub sol_num: usize,
    pub stack: Vec<(usize, usize)>,
    pub stack_ptr: usize,
    pub pc: PoseidonConstants<F, typenum::U4>,
}

fn type_of<T>(_: &T) {
    println!("{}", std::any::type_name::<T>())
}

impl<'a, F: PrimeField> R1CS<'a, F, char> {
    pub fn new(
        safa: &'a SAFA<char>,
        doc: &Vec<char>,
        batch_size: usize,
        pcs: PoseidonConstants<F, typenum::U4>,
    ) -> Self {
        //let nfa_match = nfa.is_match(doc);
        //let is_match = nfa_match.is_some();

        //let opt_batch_size;
        let cost: usize;
        //      let sel_batch_size = opt_batch_size;

        // TODO timing here
        let sol = safa.solve(&doc);
        let is_match = sol.is_some();

        let mut sel_batch_size = 1; // TODO!!sol.unwrap().0.len();
        for s in sol.iter() {
            sel_batch_size = max(sel_batch_size, s.0.len() + 1);
        }
        /*for m in moves.clone().unwrap().0 {
            sel_batch_size = max(sel_batch_size, m.to_cur - m.from_cur);
        }*/
        println!("BATCH {:#?}", sel_batch_size);

        println!("batch_size {:#?}", sel_batch_size);

        //let mut batch_doc = doc.clone();
        let mut batch_doc_len = doc.len();

        batch_doc_len += 2; // ??? TODO????

        let mut epsilon_to_add = sel_batch_size - (batch_doc_len % sel_batch_size);

        if batch_doc_len % sel_batch_size == 0 {
            epsilon_to_add = 0;
        }

        // character conversions
        let mut num_ab: FxHashMap<Option<char>, usize> = FxHashMap::default();
        let mut i = 0;
        for c in safa.ab.clone() {
            num_ab.insert(Some(c), i);
            i += 1;
        }
        num_ab.insert(None, i); // EPSILON
        num_ab.insert(Some('*'), i + 1); // STAR
        num_ab.insert(Some('!'), i + 2); // EOF TODO

        // generate T
        let num_states = safa.g.node_count();
        let num_chars = safa.ab.len();
        let mut max_offsets = 1;
        for (_, edge, _) in safa.deltas() {
            match edge {
                Either(Err(openset)) => {
                    if openset.is_single().is_none() && !openset.is_full() {
                        // ranges
                        let mut num_offsets = 0;
                        let mut iter = openset.0.iter();
                        if let Some(r) = iter.next() {
                            num_offsets += r.end.unwrap() - r.start;
                        }
                        max_offsets = max(max_offsets, num_offsets);
                    }
                }
                _ => {}
            }
        }

        // TODO range check
        let mut set_table: HashSet<Integer> = HashSet::default();

        safa.write_pdf("safa1").unwrap();

        println!("ACCEPTING {:#?}", safa.accepting);
        //println!("DELTAS {:#?}", safa.deltas());
        //println!("SOLVE {:#?}", safa.solve(&doc));
        //        println!("DOC {:#?}", doc.clone());
        println!(
            "STATES {:#?}",
            safa.g
                .node_indices()
                .for_each(|i| println!("({}) -> {}", i.index(), safa.g[i]))
        );

        let mut dfs_alls = Dfs::new(&safa.g, safa.get_init());

        let mut forall_children: Vec<Vec<usize>> = Vec::new();
        let mut foralls_w_kids: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
        let mut current_forall_node = NodeIndex::new(0);
        let mut max_branches = 0;
        let mut max_stack = 0;
        let mut current_max_stack = 0;
        let mut current_forall_state_stack: LinkedList<usize> = LinkedList::new();

        while let Some(all_state) = dfs_alls.next(&safa.g) {
            println!("PROCESS STATE {:#?}", all_state);
            if safa.g[all_state].is_and() {
                current_forall_node = all_state;

                let mut and_edges: Vec<EdgeReference<Either<char, Skip>>> = safa
                    .g
                    .edges(all_state)
                    .filter(|e| e.source() != e.target())
                    .collect();
                and_edges.sort_by(|a, b| a.target().partial_cmp(&b.target()).unwrap());
                let mut and_states = vec![];
                for i in 0..and_edges.len() {
                    and_states.push(and_edges[i].target().index());
                }

                if and_edges.len() > max_branches {
                    max_branches = and_edges.len();
                }

                for i in 0..and_edges.len() {
                    match and_edges[i].weight().clone() {
                        Either(Err(openset)) => {
                            let single = openset.is_single(); // single offset/epsilon
                            if single.is_some() {
                                // is single
                                let offset = single.unwrap();
                                if offset == 0 {
                                    // epsilon
                                    //and_states.push(and_edges[i].target().index());

                                    // add table
                                    let in_state = all_state.index();
                                    let out_state = and_edges[i].target().index();
                                    let c = num_ab[&None]; //EPSILON
                                    let rel = calc_rel(
                                        all_state.index(),
                                        out_state,
                                        &and_states,
                                        &safa,
                                        num_states,
                                        false,
                                    );

                                    set_table.insert(
                                        Integer::from(
                                            (in_state * num_states * num_chars * max_offsets * 2)
                                                + (out_state * num_chars * max_offsets * 2)
                                                + (c * max_offsets * 2)
                                                + (offset * 2)
                                                + rel,
                                        )
                                        .rem_floor(cfg().field().modulus()),
                                    );
                                } else {
                                    panic!("Non epsilon edge from ForAll state");
                                }
                            } else {
                                panic!("Non epsilon edge from ForAll state");
                            }
                        }
                        _ => {
                            panic!("Weird edge coming from ForAll node {:#?}", all_state);
                        }
                    }
                }

                foralls_w_kids.insert(all_state.index(), and_states.clone());
                forall_children.push(and_states);
                //current_stack_level += 1;
            }

            println!("forall children {:#?}", forall_children);

            // normal processing for state
            let all_state_idx = all_state.index();

            // this is a fucked way of doing this
            for stack_lvl in 0..forall_children.len() {
                for k in 0..forall_children[stack_lvl].len() {
                    if forall_children[stack_lvl][k] == all_state_idx {
                        //current_path_state = all_state_idx;

                        normal_add_table(
                            &safa,
                            &mut num_ab,
                            &mut current_forall_state_stack,
                            &mut set_table,
                            num_states,
                            num_chars,
                            max_offsets,
                            current_forall_node,
                            forall_children[stack_lvl].clone(),
                            k == forall_children[stack_lvl].len() - 1,
                        );
                    }
                }
            }
        }

        for k in forall_children {
            max_stack += k.len(); // overestimation - make this tighter
        }

        if set_table.len() == 0 {
            // no for alls, presumably (do we ever start on not a forall when
            // we have foralls in the graph?)

            normal_add_table(
                &safa,
                &mut num_ab,
                &mut current_forall_state_stack,
                &mut set_table,
                num_states,
                num_chars,
                max_offsets,
                NodeIndex::new(0), //all_state, TODO ?
                vec![],
                true,
            );
        }

        // last "empty" transition
        // add check entries to table
        let base: i32 = 2; // an explicit type is required

        let c = 0; //path count is usually at least 2^0 = 1
        let offset = 0;
        let rel = 1;
        let in_state = 0;
        let out_state = 0;
        // TODO we have to make sure the multipliers are big enough

        let mut table: Vec<Integer> = set_table.into_iter().collect();

        println!("TABLE SET {:#?}", table.clone());
        // need to round out table size ?
        let base: usize = 2;
        while table.len() < base.pow(logmn(table.len()) as u32) {
            table.push(
                Integer::from(
                    (num_states * num_states * num_chars) + (num_states * num_chars) + num_chars,
                )
                .rem_floor(cfg().field().modulus()),
            );
        }

        // generate usize doc
        // doc to usizes - can I use this elsewhere too? TODO
        let mut usize_doc = vec![];
        let mut int_doc = vec![];
        for c in doc.clone().into_iter() {
            let u = num_ab[&Some(c)];
            usize_doc.push(u);
            int_doc.push(Integer::from(u));
        }
        println!("udoc {:#?}", usize_doc.clone());

        // EPSILON, STAR
        let ep_num = usize_doc.len();
        let u = num_ab[&None];
        usize_doc.push(u);
        int_doc.push(Integer::from(u));

        let star_num = usize_doc.len();
        let u = num_ab[&Some('*')];
        usize_doc.push(u);
        int_doc.push(Integer::from(u));

        println!("TABLE {:#?}", table);

        let kid_padding = 0; // TODO !!

        let mut stack = vec![];
        for i in 0..max_stack {
            stack.push((0, 0)); // TODO CHANGE THIS TO THE PADDING
        }

        Self {
            safa,
            foralls_w_kids,
            num_ab,
            table, // TODO fix else
            max_offsets,
            reef_commit: None,
            assertions: Vec::new(),
            pub_inputs: Vec::new(),
            batch_size: sel_batch_size,
            udoc: usize_doc, //usizes
            idoc: int_doc,   // big ints
            ep_num,
            star_num,
            doc_extend: epsilon_to_add,
            is_match,
            stack_ptr_circ_count: 0,
            max_branches,
            max_stack,
            num_states,
            kid_padding,
            sol_num: 0,
            stack,
            stack_ptr: 0,
            pc: pcs,
        }
    }

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
            if access_at < self.udoc.len() {
                // this is going to be wrong - TODO
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

    pub fn prover_accepting_state(&self, state: usize) -> u64 {
        let mut out = false;

        if self.is_match {
            // proof of membership
            for a in self.safa.accepting.iter() {
                out = out || a.index() == state;
            }
        } else {
            unimplemented!();
        }

        println!("{:#?} ACCEPTING? {:#?}", state, out);

        if out {
            1
        } else {
            0
        }
    }

    // CIRCUIT

    // check if we need vs as vars
    fn lookup_idxs(&mut self, include_vs: bool) -> Vec<Term> {
        let num_chars = self.safa.ab.len();
        let num_states = self.safa.g.node_count();

        let mut v = vec![];
        for i in 1..(self.batch_size + 1) {
            let v_i = term(
                Op::PfNaryOp(PfNaryOp::Add),
                vec![
                    term(
                        Op::PfNaryOp(PfNaryOp::Add),
                        vec![
                            term(
                                Op::PfNaryOp(PfNaryOp::Add),
                                vec![
                                    term(
                                        Op::PfNaryOp(PfNaryOp::Add),
                                        vec![
                                            term(
                                                Op::PfNaryOp(PfNaryOp::Mul),
                                                vec![
                                                    new_var(format!("state_{}", i - 1)),
                                                    new_const(
                                                        num_states
                                                            * num_chars
                                                            * self.max_offsets
                                                            * 2,
                                                    ),
                                                ],
                                            ),
                                            term(
                                                Op::PfNaryOp(PfNaryOp::Mul),
                                                vec![
                                                    new_var(format!("state_{}", i)),
                                                    new_const(num_chars * self.max_offsets * 2),
                                                ],
                                            ),
                                        ],
                                    ),
                                    term(
                                        Op::PfNaryOp(PfNaryOp::Mul),
                                        vec![
                                            new_var(format!("char_{}", i - 1)),
                                            new_const(self.max_offsets * 2),
                                        ],
                                    ),
                                ],
                            ),
                            term(
                                Op::PfNaryOp(PfNaryOp::Mul),
                                vec![new_var(format!("offset_{}", i - 1)), new_const(2)],
                            ),
                        ],
                    ),
                    new_var(format!("rel_{}", i - 1)),
                ],
            );
            v.push(v_i.clone());
            self.pub_inputs.push(new_var(format!("state_{}", i - 1)));
            self.pub_inputs.push(new_var(format!("char_{}", i - 1)));
            self.pub_inputs.push(new_var(format!("offset_{}", i - 1)));
            self.pub_inputs.push(new_var(format!("rel_{}", i - 1)));

            if include_vs {
                let match_v = term(Op::Eq, vec![new_var(format!("v_{}", i - 1)), v_i]);

                self.assertions.push(match_v);
                self.pub_inputs.push(new_var(format!("v_{}", i - 1)));
            }
        }
        self.pub_inputs
            .push(new_var(format!("state_{}", self.batch_size)));

        v
    }

    fn in_foralls_circuit(&mut self, state_num: usize) -> Term {
        //not reg, trans, accept
        let not_reg = term(
            Op::Not,
            vec![term(
                Op::Eq,
                vec![new_const(0), new_var(format!("rel_{}", state_num))],
            )],
        );
        let not_trans = term(
            Op::Not,
            vec![term(
                Op::Eq,
                vec![new_const(0), new_var(format!("rel_{}", state_num))],
            )],
        );
        let not_acc = term(
            Op::Not,
            vec![term(
                Op::Eq,
                vec![new_const(0), new_var(format!("rel_{}", state_num))],
            )],
        );
        let rel_val = term(
            Op::BoolNaryOp(BoolNaryOp::And),
            vec![
                term(Op::BoolNaryOp(BoolNaryOp::And), vec![not_reg, not_trans]),
                not_acc,
            ],
        );

        rel_val
    }

    fn last_state_accepting_circuit(&mut self, in_var: Term) {
        let match_term = term(
            Op::Ite,
            vec![
                term(
                    Op::Eq,
                    vec![new_const(0), new_var(format!("rel_{}", self.batch_size))],
                ),
                term(Op::Eq, vec![in_var.clone(), new_const(1)]),
                term(Op::Eq, vec![in_var.clone(), new_const(0)]),
            ],
        );

        self.assertions.push(match_term);
        //self.pub_inputs.push(new_var(format!("accepting")));
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

        // LEAVE THIS IN HERE FOR DEBUGGING >:(
        /*for r in circ_r1cs.constraints().clone() {
            println!("{:#?}", circ_r1cs.format_qeq(&r));
        }*/

        circ_r1cs.finalize(&final_cs)
    }

    fn push_ite(&self, i: usize, to_push: Term, b: usize) -> Term {
        let pushed = term(
            Op::Eq,
            vec![new_var(format!("stack_out_{}", i)), to_push.clone()],
        );

        let not_pushed = term(
            Op::Eq,
            vec![
                new_var(format!("stack_out_{}", i)),
                new_var(format!("stack_in_{}", i)),
            ],
        );

        let stack_ptr_add = term(
            Op::Eq,
            vec![
                new_var(format!("stack_ptr_{}", self.stack_ptr_circ_count + 1)),
                term(
                    Op::PfNaryOp(PfNaryOp::Add),
                    vec![
                        new_const(1),
                        new_var(format!("stack_ptr_{}", self.stack_ptr_circ_count)),
                    ],
                ),
            ],
        );

        let stack_ptr_same = term(
            Op::Eq,
            vec![
                new_var(format!("stack_ptr_{}", self.stack_ptr_circ_count + 1)),
                new_var(format!("stack_ptr_{}", self.stack_ptr_circ_count)),
            ],
        );

        term(
            Op::Ite,
            vec![
                term(
                    Op::BoolNaryOp(BoolNaryOp::And),
                    vec![
                        term(
                            Op::Eq,
                            vec![
                                new_var(format!("stack_ptr_{}", self.stack_ptr_circ_count)),
                                new_const(i),
                            ],
                        ),
                        term(
                            Op::Not,
                            vec![term(
                                Op::Eq,
                                vec![
                                    new_var(format!("forall_0_kid_{}", b)),
                                    new_const(self.kid_padding),
                                ],
                            )],
                        ),
                    ],
                ),
                term(Op::BoolNaryOp(BoolNaryOp::And), vec![pushed, stack_ptr_add]),
                term(
                    Op::BoolNaryOp(BoolNaryOp::And),
                    vec![not_pushed, stack_ptr_same],
                ),
            ],
        )
    }

    // stack for cursors
    fn push_stack_circuit(&mut self, forall_state_num: usize, forall_kids: Vec<Term>) -> Term {
        // todo add vars

        // get kids from rel_i hash
        let mut hashed_state_var = new_const(3);
        for k in 0..self.max_branches {
            hashed_state_var = term(
                Op::PfNaryOp(PfNaryOp::Add),
                vec![
                    term(
                        Op::PfNaryOp(PfNaryOp::Mul),
                        vec![
                            new_var(format!("forall_0_kid_{}", k)),
                            new_const(self.num_states),
                        ],
                    ),
                    hashed_state_var,
                ],
            );
        }

        let hashed_kids_eq = term(
            Op::Eq,
            vec![
                hashed_state_var,
                new_var(format!("rel_{}", forall_state_num)),
            ],
        );
        self.assertions.push(hashed_kids_eq);

        // "padding" included in encoding
        assert!(forall_kids.len() == self.max_branches);

        let mut push_stmt = new_bool_const(true);

        for b in 0..self.max_branches {
            //forall_kids.len() {
            let to_push = term(
                Op::PfNaryOp(PfNaryOp::Add),
                vec![
                    term(
                        Op::PfNaryOp(PfNaryOp::Mul),
                        vec![
                            new_var(format!("cursor_{}", forall_state_num + 1)),
                            new_const(self.num_states),
                        ],
                    ),
                    forall_kids[b].clone(),
                ],
            );

            let mut inside_ite = self.push_ite(0, to_push.clone(), b);

            for i in 1..self.max_stack {
                inside_ite = term(
                    Op::Ite,
                    vec![
                        term(
                            Op::Eq,
                            vec![
                                new_var(format!("stack_ptr_{}", self.stack_ptr_circ_count)),
                                new_const(i),
                            ],
                        ),
                        self.push_ite(i, to_push.clone(), b),
                        inside_ite,
                    ],
                );
            }

            self.stack_ptr_circ_count += 1;

            push_stmt = term(Op::BoolNaryOp(BoolNaryOp::And), vec![inside_ite, push_stmt]);
        }
        push_stmt
    }

    fn pop_ite(&self, i: usize, pop_elt: Term) -> Term {
        let popped = term(
            Op::Eq,
            vec![new_var(format!("stack_out_{}", i)), pop_elt.clone()],
        );

        let not_popped = term(
            Op::Eq,
            vec![
                new_var(format!("stack_out_{}", i)),
                new_var(format!("stack_in_{}", i)),
            ],
        );

        let stack_ptr_sub = term(
            Op::Eq,
            vec![
                new_var(format!("stack_ptr_popped")),
                term(
                    Op::PfNaryOp(PfNaryOp::Add),
                    vec![
                        new_const(-1),
                        new_var(format!("stack_ptr_{}", self.stack_ptr_circ_count)),
                    ],
                ),
            ],
        );

        let stack_ptr_same = term(
            Op::Eq,
            vec![
                new_var(format!("stack_ptr_popped")),
                new_var(format!("stack_ptr_{}", self.stack_ptr_circ_count)),
            ],
        );

        term(
            Op::Ite,
            vec![
                term(
                    Op::Eq,
                    vec![
                        new_var(format!("stack_ptr_{}", self.stack_ptr_circ_count)),
                        new_const(i),
                    ],
                ),
                term(Op::BoolNaryOp(BoolNaryOp::And), vec![popped, stack_ptr_sub]),
                term(
                    Op::BoolNaryOp(BoolNaryOp::And),
                    vec![not_popped, stack_ptr_same],
                ),
            ],
        )
    }

    fn pop_stack_circuit(&mut self, cursor_var: Term) -> Term {
        let to_pop = term(
            Op::PfNaryOp(PfNaryOp::Add),
            vec![
                term(
                    Op::PfNaryOp(PfNaryOp::Mul),
                    vec![cursor_var, new_const(self.num_states)],
                ),
                new_var(format!("state_{}", self.batch_size)),
            ],
        );

        let mut inside_ite = self.pop_ite(0, to_pop.clone());

        for i in 1..self.max_stack {
            inside_ite = term(
                Op::Ite,
                vec![
                    term(
                        Op::Eq,
                        vec![
                            new_var(format!("stack_ptr_{}", self.stack_ptr_circ_count)),
                            new_const(i),
                        ],
                    ),
                    self.pop_ite(i, to_pop.clone()),
                    inside_ite,
                ],
            );
        }
        inside_ite
    }

    fn cursor_circuit(&mut self) {
        for j in 0..self.batch_size {
            // if star, geq
            // else normal
            // i_j+1 = i_j + offset

            let cursor_plus = term(
                Op::Eq,
                vec![
                    new_var(format!("cursor_{}", j + 1)), // vanishing
                    term(
                        Op::PfNaryOp(PfNaryOp::Add),
                        vec![
                            new_var(format!("cursor_{}", j)),
                            new_var(format!("offset_{}", j)),
                        ],
                    ),
                ],
            );

            // TODO LIMIT bits here plus the other bullshit
            let cursor_geq = term(
                Op::BvBinPred(BvBinPred::Uge),
                vec![
                    term(Op::PfToBv(254), vec![new_var(format!("cursor_{}", j + 1))]),
                    term(Op::PfToBv(254), vec![new_var(format!("cursor_{}", j))]),
                ],
            );

            let ite_term = term(
                Op::Ite,
                vec![
                    term(
                        Op::Eq,
                        vec![
                            new_const(self.num_ab[&Some('*')]),
                            new_var(format!("char_{}", j)),
                        ],
                    ),
                    cursor_geq,
                    cursor_plus,
                ],
            );

            if j == 0 {
                // if in_state \in forall - only first
                let in_forall = self.in_foralls_circuit(0);

                let mut forall_kids = vec![];
                for k in 0..self.max_branches {
                    forall_kids.push(new_var(format!("forall_0_kid_{}", k)));
                }

                let push_stmt = self.push_stack_circuit(0, forall_kids);

                let do_pushes = term(Op::Ite, vec![in_forall, push_stmt, new_bool_const(true)]);
                self.assertions.push(do_pushes);
            } else {
                // assert not forall
                let in_forall = self.in_foralls_circuit(j);

                let not_in_forall = term(Op::Not, vec![in_forall]);
                self.assertions.push(not_in_forall);
            }

            if j < self.batch_size - 1 {
                self.assertions.push(ite_term);

                // not branch transition
                let not_branch_transition = term(
                    Op::Not,
                    vec![term(
                        Op::Eq,
                        vec![new_var(format!("rel_{}", j)), new_const(1)],
                    )],
                );
                self.assertions.push(not_branch_transition);
            } else if j == self.batch_size - 1 {
                // last (branch trans)
                // assert cursor == EOF
                let eof = term(
                    Op::Eq,
                    vec![
                        new_var(format!("char_{}", j)),
                        new_const(self.num_ab[&Some('!')]),
                    ],
                );

                // cursor = pop stack
                let pop_stmt = self.pop_stack_circuit(new_var(format!("cursor_{}", j + 1)));

                let branch_transition = term(Op::BoolNaryOp(BoolNaryOp::And), vec![pop_stmt, eof]);

                // branch transition rel val -> in is accepting
                let branch_or_not = term(
                    Op::Ite,
                    vec![
                        term(Op::Eq, vec![new_var(format!("rel_{}", j)), new_const(1)]),
                        branch_transition,
                        ite_term,
                    ],
                );

                self.assertions.push(branch_or_not);
            }
        }
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

    fn q_ordering_circuit(&mut self, id: &str) {
        // q relations
        for i in 0..(self.batch_size - 1) {
            // not final q (running claim)

            let mut full_q = new_const(0); // dummy
            let mut next_slot = Integer::from(1);
            let doc_l = logmn(self.udoc.len());
            for j in (0..doc_l).rev() {
                full_q = term(
                    Op::PfNaryOp(PfNaryOp::Add),
                    vec![
                        full_q,
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

            let q_eq = term(
                Op::Eq,
                vec![
                    full_q.clone(),
                    term(
                        Op::Ite,
                        vec![
                            term(
                                Op::Eq,
                                vec![
                                    new_var(format!("char_{}", i)),
                                    new_const(self.num_ab[&None]),
                                ],
                            ),
                            new_const(self.ep_num),
                            term(
                                Op::Ite,
                                vec![
                                    term(
                                        Op::Eq,
                                        vec![
                                            new_var(format!("char_{}", i)),
                                            new_const(self.num_ab[&Some('*')]),
                                        ],
                                    ),
                                    new_const(self.star_num),
                                    new_var(format!("cursor_{}", i)),
                                ],
                            ),
                        ],
                    ),
                ],
            );
            self.assertions.push(q_eq);
        }
    }

    pub fn to_circuit(&mut self) -> (ProverData, VerifierData) {
        let lookups = self.lookup_idxs(true);
        assert_eq!(lookups.len(), self.batch_size);
        self.nlookup_gadget(lookups, self.table.len(), "nl"); // len correct? TODO
        self.cursor_circuit();
        self.last_state_accepting_circuit(new_var(format!("accepting")));

        self.nlookup_doc_commit();

        self.r1cs_conv()
    }

    fn nlookup_doc_commit(&mut self) {
        // TODO - this no longer works, need to bind index to doc
        self.q_ordering_circuit("nldoc");

        // lookups and nl circuit
        let mut char_lookups = vec![];
        for c in 0..(self.batch_size - 1) {
            char_lookups.push(new_var(format!("char_{}", c)));
        }

        self.nlookup_gadget(char_lookups, self.udoc.len(), "nldoc");
    }

    fn nlookup_gadget(&mut self, mut lookup_vals: Vec<Term>, t_size: usize, id: &str) {
        // TODO pub inputs -> can make which priv?
        // last state_batch is final "next_state" output
        // v_{batch-1} = (state_{batch-1}, c, state_batch)
        // v_batch = T eval check (optimization)

        let num_vs = lookup_vals.len();

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
        for i in 0..num_vs + 1 {
            eq_evals.push(self.bit_eq_circuit(sc_l, i, id));
        }
        let eq_eval = horners_circuit_vars(&eq_evals, new_var(format!("{}_claim_r", id)));

        // make combined_q
        self.combined_q_circuit(num_vs, sc_l, id); // running claim q not
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

    fn pop_wit(&mut self, wits: &mut FxHashMap<String, Value>) -> usize {
        let mut popped_elt = self.stack[self.stack_ptr];
        self.stack_ptr -= 1;

        wits.insert(format!("cursor_{}", self.batch_size), new_wit(popped_elt.0));
        wits.insert(format!("state_{}", self.batch_size), new_wit(popped_elt.1));

        // after pop
        wits.insert(format!("stack_ptr_popped"), new_wit(self.stack_ptr));

        // return cursor
        popped_elt.0
    }

    fn push_wit(
        &mut self,
        wits: &mut FxHashMap<String, Value>,
        forall: Option<NodeIndex>,
        cur_cursor: usize,
    ) {
        // assert in foralls sanity check ?

        let mut forall_kids = match forall {
            Some(state) => self.foralls_w_kids[&state.index()].clone(),
            None => vec![],
        };

        while forall_kids.len() < self.max_branches {
            forall_kids.push(self.kid_padding);
        }

        let mut k = 0;
        for i in 0..self.stack_ptr {
            wits.insert(
                format!("stack_in_{}", i),
                new_wit(self.stack[i].0 * self.num_states + self.stack[i].1),
            );
            wits.insert(
                format!("stack_out_{}", i),
                new_wit(self.stack[i].0 * self.num_states + self.stack[i].1),
            );

            wits.insert(format!("stack_ptr_{}", i), new_wit(self.stack_ptr));
        }

        for kid in forall_kids {
            wits.insert(
                format!("stack_in_{}", self.stack_ptr),
                new_wit(
                    self.stack[self.stack_ptr].0 * self.num_states + self.stack[self.stack_ptr].1,
                ),
            );

            self.stack[self.stack_ptr] = (cur_cursor, kid);
            wits.insert(
                format!("stack_out_{}", self.stack_ptr),
                new_wit(kid * self.num_states + cur_cursor),
            );
            wits.insert(format!("forall_kid_{}", k), new_wit(kid));
            k += 1;

            self.stack_ptr += 1;
            wits.insert(
                format!("stack_ptr_{}", self.stack_ptr),
                new_wit(self.stack_ptr),
            );
        }

        for i in (self.stack_ptr + 1)..self.max_stack {
            wits.insert(
                format!("stack_in_{}", i),
                new_wit(self.stack[i].0 * self.num_states + self.stack[i].1),
            );
            wits.insert(
                format!("stack_out_{}", i),
                new_wit(self.stack[i].0 * self.num_states + self.stack[i].1),
            );

            wits.insert(format!("stack_ptr_{}", i), new_wit(self.stack_ptr));
        }
    }

    // returns char_num, is_star
    fn get_char_num(&self, edge: Either<char, OpenSet<usize>>) -> (usize, bool) {
        match edge {
            Either(Err(openset)) => {
                let single = openset.is_single(); // single offset/epsilon
                if single.is_some() {
                    // is single
                    // if offset == 0 { -> doesn't matter, always use epsilon for actual
                    // epsilon and for jumps

                    (self.num_ab[&None], false) //EPSILON
                } else if openset.is_full() {
                    // [0,*]
                    (self.num_ab[&Some('*')], true)
                } else {
                    // ranges
                    (self.num_ab[&None], false) //EPSILON
                }
            }
            Either(Ok(ch)) => (self.num_ab[&Some(ch)], false),
        }
    }

    fn padding_v(
        &self,
        wits: &mut FxHashMap<String, Value>,
        q: &mut Vec<usize>,
        state_i: usize,
        next_state: usize,
        cursor_i: usize,
        i: usize, // this is for naming
    ) -> Integer {
        let char_num = self.num_ab[&None];
        let offset_i = 0;

        let rel_i = if self.safa.g[NodeIndex::new(state_i)].is_and() {
            calc_rel(
                state_i,
                next_state,
                &self.foralls_w_kids[&state_i],
                &self.safa,
                self.num_states,
                false,
            )
        } else {
            calc_rel(
                state_i,
                next_state,
                &vec![],
                &self.safa,
                self.num_states,
                false,
            )
        };

        wits.insert(format!("char_{}", i), new_wit(char_num));
        wits.insert(format!("state_{}", i), new_wit(state_i));
        wits.insert(format!("offset_{}", i), new_wit(offset_i));
        wits.insert(format!("rel_{}", i), new_wit(rel_i));
        wits.insert(format!("cursor_{}", i + 1), new_wit(cursor_i)); // alreaded "added" here

        // v_i =
        let num_states = self.safa.g.node_count();
        let num_chars = self.safa.ab.len();

        // TODO check overflow
        let v_i = Integer::from(
            (state_i * num_states * num_chars * self.max_offsets * 2)
                + (next_state * num_chars * self.max_offsets * 2)
                + (char_num * self.max_offsets * 2)
                + (offset_i * 2)
                + (rel_i),
        )
        .rem_floor(cfg().field().modulus());

        wits.insert(format!("v_{}", i), new_wit(v_i.clone()));

        println!(
            "V_{} = {:#?} from {:#?},{:#?},{:#?},{:#?},{:#?} cursor={:#?}",
            i, v_i, state_i, next_state, char_num, offset_i, rel_i, cursor_i,
        );

        q.push(self.table.iter().position(|val| val == &v_i).unwrap());

        v_i
    }

    fn edge_v(
        &self,
        wits: &mut FxHashMap<String, Value>,
        q: &mut Vec<usize>,
        char_num: usize,
        state_i: usize,
        next_state: usize,
        offset_i: usize,
        cursor_i: usize,
        rel_i: usize,
        i: usize, // this is for naming
    ) -> Integer {
        wits.insert(format!("char_{}", i), new_wit(char_num));
        wits.insert(format!("state_{}", i), new_wit(state_i));
        wits.insert(format!("offset_{}", i), new_wit(offset_i));
        wits.insert(format!("rel_{}", i), new_wit(rel_i));
        wits.insert(format!("cursor_{}", i + 1), new_wit(cursor_i)); // alreaded "added" here

        // v_i =
        let num_states = self.safa.g.node_count();
        let num_chars = self.safa.ab.len();

        // TODO check overflow
        let v_i = Integer::from(
            (state_i * num_states * num_chars * self.max_offsets * 2)
                + (next_state * num_chars * self.max_offsets * 2)
                + (char_num * self.max_offsets * 2)
                + (offset_i * 2)
                + (rel_i),
        )
        .rem_floor(cfg().field().modulus());

        //v.push(v_i.clone());
        wits.insert(format!("v_{}", i), new_wit(v_i.clone()));

        println!(
            "V_{} = {:#?} from {:#?},{:#?},{:#?},{:#?},{:#?} cursor={:#?}",
            i, v_i, state_i, next_state, char_num, offset_i, rel_i, cursor_i,
        );

        q.push(self.table.iter().position(|val| val == &v_i).unwrap());

        v_i
    }

    pub fn gen_wit_i(
        //_nlookup(
        &mut self,
        sols: &mut Vec<LinkedList<TraceElem<char>>>, //move_num: (usize, usize),
        batch_num: usize,
        current_state: usize, // TODO DEL, and TODO DEL start_epsilons
        running_q: Option<Vec<Integer>>,
        running_v: Option<Integer>,
        doc_running_q: Option<Vec<Integer>>,
        doc_running_v: Option<Integer>,
        cursor_0: usize,
    ) -> (
        FxHashMap<String, Value>,
        usize,
        Option<Vec<Integer>>,
        Option<Integer>,
        Option<Vec<Integer>>,
        Option<Integer>,
        usize,
    ) {
        let mut wits = FxHashMap::default();

        // generate claim v's (well, v isn't a real named var, generate the states/chars)
        let mut state_i = 0;
        let mut next_state = 0;
        let mut char_num = self.num_ab[&None];
        let mut offset_i = 0;

        let mut v = vec![];
        let mut q = vec![];
        let mut i = 0;
        let mut cursor_i = cursor_0;
        let mut cursor_access = vec![cursor_0];

        wits.insert(format!("cursor_0"), new_wit(cursor_i));

        while i < self.batch_size {
            if sols[self.sol_num].is_empty() {
                // need to transition
                while i < self.batch_size - 1 {
                    state_i = next_state;
                    v.push(self.padding_v(&mut wits, &mut q, state_i, next_state, cursor_i, i));
                    i += 1;
                }

                char_num = self.num_ab[&None];
                offset_i = 0;
                if self.sol_num == sols.len() {
                    // very last
                    next_state = self.num_states; // TODO
                } else {
                    next_state = sols[self.sol_num + 1].front().unwrap().from_node.index();
                }

                cursor_i = self.pop_wit(&mut wits);

                // transition
                let rel_i = if self.safa.g[NodeIndex::new(state_i)].is_and() {
                    calc_rel(
                        state_i,
                        next_state,
                        &self.foralls_w_kids[&state_i],
                        &self.safa,
                        self.num_states,
                        true,
                    )
                } else {
                    calc_rel(
                        state_i,
                        next_state,
                        &vec![],
                        &self.safa,
                        self.num_states,
                        true,
                    )
                };

                v.push(self.edge_v(
                    &mut wits, &mut q, char_num, state_i, next_state, offset_i, cursor_i, rel_i, i,
                ));
                i += 1;

                self.sol_num += 1;
            } else {
                // from solution
                let te = sols[self.sol_num].pop_front().unwrap();
                println!("{:#?}", te);

                // handle stack pushes during forall
                if self.safa.g[te.from_node].is_and() {
                    // forall
                    if i == 0 {
                        // correct place
                        self.push_wit(&mut wits, Some(te.from_node), cursor_i);
                    } else {
                        // pad out the rest of this loop
                        while i < self.batch_size {
                            v.push(
                                self.padding_v(&mut wits, &mut q, state_i, next_state, cursor_i, i),
                            );
                            i += 1;
                        }
                    }
                } else {
                    // not forall
                    if i == 0 {
                        // must pad out the stack
                        // fill stack vars with padding
                        self.push_wit(&mut wits, None, cursor_i);
                    }
                }

                // normal transition
                let is_star;
                (char_num, is_star) = self.get_char_num(te.edge);
                state_i = te.from_node.index();
                next_state = te.to_node.index();
                println!("NEXT STATE IS {:#?}", next_state);
                offset_i = te.to_cur - te.from_cur;

                cursor_i += offset_i;

                // this is some fucking shit to be fixed
                if is_star {
                    offset_i = 0;
                }

                let rel_i = if self.safa.g[NodeIndex::new(state_i)].is_and() {
                    calc_rel(
                        state_i,
                        next_state,
                        &self.foralls_w_kids[&state_i],
                        &self.safa,
                        self.num_states,
                        false,
                    )
                } else {
                    calc_rel(
                        state_i,
                        next_state,
                        &vec![],
                        &self.safa,
                        self.num_states,
                        false,
                    )
                };
                v.push(self.edge_v(
                    &mut wits, &mut q, char_num, state_i, next_state, offset_i, cursor_i, rel_i, i,
                ));
                i += 1;

                if char_num == self.num_ab[&None] {
                    cursor_access.push(self.ep_num);
                } else if char_num == self.num_ab[&Some('*')] {
                    cursor_access.push(self.star_num);
                } else {
                    cursor_access.push(cursor_i);
                }
            }
        }

        println!("DONE LOOP");

        // last state
        wits.insert(format!("state_{}", self.batch_size), new_wit(next_state));

        assert!(running_q.is_some() || batch_num == 0);
        assert!(running_v.is_some() || batch_num == 0);

        println!("Q,V = {:#?}, {:#?}", q, v);
        println!("TABLE = {:#?}", self.table.clone());
        assert_eq!(v.len(), self.batch_size);
        let (w, next_running_q, next_running_v) =
            self.wit_nlookup_gadget(wits, &self.table, q, v, running_q, running_v, "nl");
        wits = w;

        // accepting
        wits.insert(format!("accepting"), new_wit(1));

        assert!(doc_running_q.is_some() || batch_num == 0);
        assert!(doc_running_v.is_some() || batch_num == 0);
        let (w, next_doc_running_q, next_doc_running_v) = self.wit_nlookup_doc_commit(
            wits,
            batch_num,
            doc_running_q,
            doc_running_v,
            cursor_access,
        );
        wits = w;
        println!("WITS {:#?}", wits);

        (
            wits,
            next_state,
            Some(next_running_q),
            Some(next_running_v),
            Some(next_doc_running_q),
            Some(next_doc_running_v),
            cursor_i,
        )
    }

    fn wit_nlookup_doc_commit(
        &self,
        mut wits: FxHashMap<String, Value>,
        batch_num: usize,
        running_q: Option<Vec<Integer>>,
        running_v: Option<Integer>,
        cursor_access: Vec<usize>,
    ) -> (FxHashMap<String, Value>, Vec<Integer>, Integer) {
        let mut v = vec![];
        let mut q = vec![];

        for i in 0..(self.batch_size - 1) {
            // TODO - make sure epsilon and * are added to the end of doc [ DOC, EOF, epsilon, star
            // ]
            let access_at = cursor_access[i];
            q.push(access_at);
            v.push(self.idoc[access_at].clone());
        }

        println!("DOC NLOOKUP Q V {:#?}, {:#?}", q, v);

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
        let num_vs = v.len();
        assert_eq!(num_vs, q.len());

        // running claim about T (optimization)
        // if first (not yet generated)
        println!("prev running q,v {:#?}, {:#?}", running_q, running_v);
        println!("table again {:#?}", table);

        let prev_running_q = match running_q {
            Some(q) => q,
            None => vec![Integer::from(0); sc_l],
        };
        let prev_running_v = match running_v {
            Some(v) => v,
            None => table[0].clone(),
        };
        println!(
            "prev running q,v {:#?}, {:#?}",
            prev_running_q, prev_running_v
        );

        wits.insert(
            format!("{}_prev_running_claim", id),
            new_wit(prev_running_v.clone()),
        );
        // q.push(prev_running_q);

        // q processing
        let mut combined_qs = vec![];
        let num_cqs = ((num_vs * sc_l) as f64 / 254.0).ceil() as usize;

        //println!("num cqs {:#?}", num_cqs);

        let mut cq = 0;
        while cq < num_cqs {
            let mut combined_q = Integer::from(0);
            let mut next_slot = Integer::from(1);
            for i in 0..num_vs {
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
                    if (i * sc_l) + j >= 254 * (cq + 1) || (i == num_vs - 1 && j == sc_l - 1) {
                        cq += 1;
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

        //println!("combined_qs {:#?}", combined_qs);

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
                SpongeOp::Absorb((num_vs + sc_l + 1 + num_cqs) as u32), // vs, combined_q, running q,v
                SpongeOp::Squeeze(1),
            ],
            "nldoc" => vec![
                SpongeOp::Absorb((num_vs + sc_l + 2 + num_cqs) as u32), // doc commit, vs, combined_q, running q,v
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
                Some(dcs) => vec![dcs.commit_doc_hash],
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
            // sanity
            let prev_g_r = g_xsq.clone() * sc_r.clone() * sc_r.clone()
                + g_x.clone() * sc_r.clone()
                + g_const.clone();

            (sc_r, g_xsq, g_x, g_const) =
                linear_mle_product(&mut sc_table, &mut eq_table, sc_l, i, &mut sponge);
            //prover_mle_sum_eval(table, &sc_rs, &q, &claim_r, Some(&prev_running_q));

            // sanity
            if i > 1 {
                assert_eq!(
                    prev_g_r.clone().rem_floor(cfg().field().modulus()),
                    (g_xsq.clone() + g_x.clone() + g_const.clone() + g_const.clone())
                        .rem_floor(cfg().field().modulus())
                );
            }

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
        println!("LAST CLAIM {:#?}", last_claim);
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
        println!("next running v {:#?}", next_running_v);
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
        println!("EQ TERM {:#?}", eq_term);
        assert_eq!(
            last_claim,
            (eq_term * next_running_v.clone()).rem_floor(cfg().field().modulus())
        );

        // return

        (wits, next_running_q, next_running_v)
    }
}

pub fn ceil_div(a: usize, b: usize) -> usize {
    (a + b - 1) / b
}

#[cfg(test)]
mod tests {

    use crate::backend::costs;
    use crate::backend::r1cs::*;
    use crate::regex::re;
    use crate::safa::SAFA;
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
        let r = re::simpl(re::new(&rstr));
        let safa = SAFA::new(&ab[..], &r);

        let chars: Vec<char> = doc.chars().collect(); //map(|c| c.to_string()).collect();

        for c in vec![JCommit::Nlookup] {
            for b in vec![JBatching::Nlookup] {
                let sc =
                    Sponge::<<G1 as Group>::Scalar, typenum::U4>::api_constants(Strength::Standard);
                let mut r1cs_converter = R1CS::new(&safa, &chars, 0, sc.clone());

                let reef_commit = gen_commitment(r1cs_converter.udoc.clone(), &sc);
                r1cs_converter.reef_commit = Some(reef_commit.clone());

                assert_eq!(expected_match, r1cs_converter.is_match);

                let mut running_q: Option<Vec<Integer>> = None;
                let mut running_v: Option<Integer> = None;
                let mut doc_running_q: Option<Vec<Integer>> = None;
                let mut doc_running_v: Option<Integer> = None;
                let mut doc_idx = 0;

                let (pd, _vd) = r1cs_converter.to_circuit();
                // println!("PD {:#?}", pd);

                let mut values;
                let mut next_state;

                let trace = safa.solve(&chars);
                //println!("TRACE {:#?}", trace);

                let mut sols = trace_preprocessing(&trace, &safa);
                //println!("SOLS {:#?}", sols);

                let num_steps = sols.len();
                /*assert_eq!(
                    num_steps,
                    r1cs_converter
                        .path_count_lookup
                        .values()
                        .cloned()
                        .unique()
                        .count()
                );
                */
                println!("NUM STEPS {:#?}", num_steps);
                let mut current_state = 0; // TODOmoves[0].from_node.index();

                for i in 0..num_steps {
                    (
                        values,
                        next_state,
                        running_q,
                        running_v,
                        doc_running_q,
                        doc_running_v,
                        doc_idx,
                    ) = r1cs_converter.gen_wit_i(
                        &mut sols,
                        i,
                        current_state,
                        running_q.clone(),
                        running_v.clone(),
                        doc_running_q.clone(),
                        doc_running_v.clone(),
                        doc_idx,
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

                final_clear_checks(
                    reef_commit,
                    <G1 as Group>::Scalar::from(1), // dummy, not checked
                    &r1cs_converter.table,
                    r1cs_converter.udoc.len(),
                    rq,
                    rv,
                    drq,
                    drv,
                );

                /*
                println!(
                    "cost model: {:#?}",
                    costs::full_round_cost_model_nohash(
                        &safa,
                        r1cs_converter.batch_size,
                        b.clone(),
                        nfa.is_match(&chars),
                        doc.len(),
                        c,
                    )
                );*/
                println!("actual cost: {:#?}", pd.r1cs.constraints.len());
                println!("\n\n\n");

                /*assert!(
                    pd.r1cs.constraints.len() as usize
                        == costs::full_round_cost_model_nohash(
                            &nfa,
                            r1cs_converter.batch_size,
                            b.clone(),
                            nfa.is_match(&chars),
                            doc.len(),
                            c
                        )
                );*/
            }
        }
    }

    #[test]
    fn naive_test() {
        init();
        test_func_no_hash(
            "abcd".to_string(),
            "^(?=a)ab(?=c)cd$".to_string(),
            "abcd".to_string(),
            vec![1], // 2],
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
    /*
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
    */
    // TODO non match??

    /*
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
    */

    /*#[test]
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
    }*/

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
        /*
              test_func_no_hash(
                  "helowrd".to_string(),
                  "^hello$".to_string(),
                  "helloworld".to_string(),
                  vec![1, 5],
                  false,
              );
        */
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

        /*    test_func_no_hash(
                "helowrd".to_string(),
                "^hello$".to_string(),
                "helloworld".to_string(),
                vec![3, 4, 6, 7],
                false,
            );
        */
    }

    #[test]
    fn r1cs_q_overflow() {
        init();
        test_func_no_hash(
            "abcdefg".to_string(),
            "^gaa*bb*cc*dd*ee*f$".to_string(),
            "gaaaaaabbbbbbccccccddddddeeeeeef".to_string(),
            vec![33],
            true,
        );

        test_func_no_hash(
            "abcdefg".to_string(),
            "^gaaaaaabbbbbbccccccddddddeeeeeef$".to_string(),
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

    /*
    fn test_func_no_hash_kstride(
        ab: String,
        rstr: String,
        doc: String,
        batch_sizes: Vec<usize>,
        k: usize,
    ) {
        let r = re::new(&rstr);
        let mut safa = SAFA::new(&ab[..], r);
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
    }*/
}
