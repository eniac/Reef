use crate::backend::nova::int_to_ff;
use crate::backend::{commitment::*, costs::*, r1cs_helper::*};
use crate::frontend::openset::OpenSet;
use crate::frontend::safa::{Either, Skip, SAFA};
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

pub struct R1CS<'a, F: PrimeField, C: Clone + Eq> {
    pub safa: &'a SAFA<C>,
    foralls_w_kids: FxHashMap<usize, Vec<usize>>,
    pub num_ab: FxHashMap<Option<C>, usize>,
    pub table: Vec<Integer>,
    max_offsets: usize,
    star_offset: usize,
    pub doc_hash: Option<F>,
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
    // circuit crap
    pub max_branches: usize,
    pub max_stack: usize,
    pub num_states: usize,
    pub exit_state: usize,
    pub kid_padding: usize,
    // witness crap
    pub sol_num: usize,
    pub stack: Vec<(usize, usize)>,
    pub stack_ptr: usize,
    pub pc: PoseidonConstants<F, typenum::U4>,
    pub doc_rc_v: Option<Integer>,
    // proj
    pub doc_subset: Option<(usize, usize)>,
    // hybrid
    pub hybrid_len: Option<usize>,
}

impl<'a, F: PrimeField> R1CS<'a, F, char> {
    pub fn new(
        safa: &'a SAFA<char>,
        doc: &Vec<char>,
        batch_size: usize,
        projection: Option<usize>,
        hybrid: bool,
        pcs: PoseidonConstants<F, typenum::U4>,
    ) -> Self {
        // character conversions
        let mut num_ab: FxHashMap<Option<char>, usize> = FxHashMap::default();
        let mut i = 0;
        for c in safa.ab.clone() {
            num_ab.insert(Some(c), i);
            i += 1;
        }
        num_ab.insert(Some('$'), i); // EOF TODO
        num_ab.insert(None, i + 1); // EPSILON

        // generate T
        let mut num_states = safa.g.node_count();
        let kid_padding = num_states;
        num_states += 1;
        let exit_state = num_states;
        num_states += 1;

        let num_chars = num_ab.len();

        let mut max_offsets = safa.max_skip_offset().max(1);
        let star_offset = max_offsets;
        max_offsets += 1;

        let max_branches = safa.max_forall_fanout().max(1);

        let mut set_table: HashSet<Integer> = HashSet::default();

        //safa.write_pdf("safa1").unwrap();

        /*println!(
            "STATES {:#?}",
            safa.g
                .node_indices()
                .for_each(|i| println!("({}) -> {}", i.index(), safa.g[i]))
        );*/

        let mut dfs_alls = Dfs::new(&safa.g, safa.get_init());

        let mut foralls_w_kids: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
        let mut max_stack = 1;
        let mut max_rel = 1;

        while let Some(all_state) = dfs_alls.next(&safa.g) {
            //println!("PROCESS STATE {:#?}", all_state);
            if safa.g[all_state].is_and() {
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
                // add epsilon loop
                let in_state = all_state.index();
                let out_state = all_state.index();
                let lower_offset = 0;
                let upper_offset = 0;
                let c = num_ab[&None]; //EPSILON

                let rel = calc_rel(
                    all_state.index(),
                    out_state,
                    &and_states,
                    kid_padding,
                    max_branches,
                    &safa,
                    num_states,
                    exit_state,
                    false,
                );
                if rel > max_rel {
                    max_rel = rel;
                }
                set_table.insert(
                    Integer::from(
                        (rel * num_states * num_states * num_chars * max_offsets * max_offsets)
                            + (in_state * num_states * num_chars * max_offsets * max_offsets)
                            + (out_state * num_chars * max_offsets * max_offsets)
                            + (c * max_offsets * max_offsets)
                            + (lower_offset * max_offsets)
                            + upper_offset,
                    )
                    .rem_floor(cfg().field().modulus()),
                );

                // children
                for i in 0..and_edges.len() {
                    match and_edges[i].weight().clone() {
                        Either(Err(openset)) => {
                            let single = openset.is_single(); // single offset/epsilon
                            if single.is_some() {
                                // is single
                                let offset = single.unwrap();
                                if offset == 0 {
                                    // epsilon
                                    let lower_offset = 0;
                                    let upper_offset = 0;

                                    // add table
                                    let in_state = all_state.index();
                                    let out_state = and_edges[i].target().index();

                                    let c = num_ab[&None]; //EPSILON

                                    let rel = calc_rel(
                                        all_state.index(),
                                        out_state,
                                        &and_states,
                                        kid_padding,
                                        max_branches,
                                        &safa,
                                        num_states,
                                        exit_state,
                                        false,
                                    );
                                    if rel > max_rel {
                                        max_rel = rel;
                                    }

                                    set_table.insert(
                                        Integer::from(
                                            (rel * num_states
                                                * num_states
                                                * num_chars
                                                * max_offsets
                                                * max_offsets)
                                                + (in_state
                                                    * num_states
                                                    * num_chars
                                                    * max_offsets
                                                    * max_offsets)
                                                + (out_state
                                                    * num_chars
                                                    * max_offsets
                                                    * max_offsets)
                                                + (c * max_offsets * max_offsets)
                                                + (lower_offset * max_offsets)
                                                + upper_offset,
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
            }
        }

        let mut fa = 0;
        for (forall, kids) in &foralls_w_kids {
            for k in 0..kids.len() {
                let backtrace_state = if k == kids.len() - 1 && fa == foralls_w_kids.len() - 1 {
                    exit_state
                } else {
                    *forall
                };

                let sub_max_rel = normal_add_table(
                    &safa,
                    &mut num_ab,
                    &mut set_table,
                    num_states,
                    exit_state,
                    num_chars,
                    kid_padding,
                    max_branches,
                    max_offsets,
                    star_offset,
                    NodeIndex::new(kids[k]),
                    backtrace_state,
                    kids.clone(),
                    false,
                );
                if sub_max_rel > max_rel {
                    max_rel = sub_max_rel;
                }
            }
            fa += 1;
            max_stack += kids.len(); // overestimation - make this tighter
        }

        // in case when we don't start on forall:
        // proceed from the beginning and add states until we reach a forall

        let sub_max_rel = normal_add_table(
            &safa,
            &mut num_ab,
            &mut set_table,
            num_states,
            exit_state,
            num_chars,
            kid_padding,
            max_branches,
            max_offsets,
            star_offset,
            safa.get_init(), //exists_state,
            exit_state,      // backtrace state
            vec![],
            true,
        );
        if sub_max_rel > max_rel {
            max_rel = sub_max_rel;
        }

        // add "last" loop
        let in_state = exit_state;
        let out_state = exit_state;
        let lower_offset = 0;
        let upper_offset = 0;
        let c = num_ab[&None]; //EPSILON
        let rel = 0;

        set_table.insert(
            Integer::from(
                (rel * num_states * num_states * num_chars * max_offsets * max_offsets)
                    + (in_state * num_states * num_chars * max_offsets * max_offsets)
                    + (out_state * num_chars * max_offsets * max_offsets)
                    + (c * max_offsets * max_offsets)
                    + (lower_offset * max_offsets)
                    + upper_offset,
            )
            .rem_floor(cfg().field().modulus()),
        );

        // TODO we have to make sure the multipliers are big enough

        let mut table: Vec<Integer> = set_table.into_iter().collect();

        // need to round out table size ?
        let base: usize = 2;
        let calc_fill = Integer::from(
            (max_rel * num_states * num_states * num_chars * max_offsets * max_offsets)
                + (num_states * num_states * num_chars * max_offsets * max_offsets)
                + (num_states * num_chars * max_offsets * max_offsets)
                + (num_chars * max_offsets * max_offsets)
                + (max_offsets * max_offsets)
                + max_offsets,
        );

        assert!(calc_fill < cfg().field().modulus().clone());
        let calc_fill = calc_fill.rem_floor(cfg().field().modulus());
        while table.len() < base.pow(logmn(table.len()) as u32) {
            table.push(calc_fill.clone());
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

        // EPSILON, STAR
        let ep_num = usize_doc.len();
        let u = num_ab[&None];
        usize_doc.push(u);
        int_doc.push(Integer::from(u));

        let eof_num = usize_doc.len();
        let u = num_ab[&Some('$')];
        usize_doc.push(u);
        int_doc.push(Integer::from(u));

        let mut stack = vec![];
        for _i in 0..max_stack {
            stack.push((0, kid_padding));
        }

        let doc_subset = if projection.is_some() {
            if (usize_doc.len().next_power_of_two() <= table.len()) && hybrid {
                panic!(
                    "Doc len {} <= table size {} already. Projections AND hybrid not useful together, choose one.",
                usize_doc.len().next_power_of_two(), table.len());
            }

            let real_start = projection.unwrap();

            let end = usize_doc.len().next_power_of_two();
            let mut start = end - 1;
            let mut jump = 1;

            while start > real_start && start >= 0 {
                start -= jump;
                jump *= 2;
            }

            // proj vs hybrid calc
            if (end - start < table.len()) && hybrid {
                println!("ALERT: using projections with hybrid, optimal (smallest) projection len < table len, so extending projection len to table len");
                start = end - table.len();
            }
            if start == 0 {
                None
            } else {
                // println!("USING PROJECTION {:#?}", ((start, end)));
                Some((start, end)) // handle doc extension TODO?
            }
        } else {
            None
        };

        let pub_len = table.len();
        let priv_len = if doc_subset.is_some() {
            let ds = doc_subset.unwrap();
            ds.1 - ds.0
        } else {
            usize_doc.len()
        };

        let hybrid_len = if hybrid {
            Some(max(pub_len, priv_len).next_power_of_two() * 2)
        } else {
            None
        };

        assert!(batch_size > 1);

        Self {
            safa,
            foralls_w_kids,
            num_ab,
            table, // TODO fix else
            max_offsets,
            star_offset,
            doc_hash: None,
            assertions: Vec::new(),
            pub_inputs: Vec::new(),
            batch_size,
            udoc: usize_doc, //usizes
            idoc: int_doc,   // big ints
            ep_num,
            max_branches,
            max_stack,
            num_states,
            exit_state,
            kid_padding,
            sol_num: 0,
            stack,
            stack_ptr: 0,
            pc: pcs,
            doc_rc_v: Some(Integer::from(1)), // Convert back to none later
            doc_subset,
            hybrid_len,
        }
    }

    pub fn doc_len(&self) -> usize {
        if self.doc_subset.is_some() {
            let ds = self.doc_subset.unwrap();
            ds.1 - ds.0
        } else {
            self.udoc.len().next_power_of_two()
        }
    }

    pub fn prover_accepting_state(&self, state: usize) -> u64 {
        let mut out = false;

        // proof of membership
        for a in self.safa.accepting().iter() {
            out = out || a.index() == state;
        }

        if out {
            1
        } else {
            0
        }
    }

    // CIRCUIT

    // check if we need vs as vars
    fn lookup_idxs(&mut self, include_vs: bool) -> Vec<Term> {
        let num_chars = self.num_ab.len();

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
                                                Op::PfNaryOp(PfNaryOp::Add),
                                                vec![
                                                    term(
                                                        Op::PfNaryOp(PfNaryOp::Mul),
                                                        vec![
                                                            new_var(format!("rel_{}", i - 1)),
                                                            new_const(
                                                                self.num_states
                                                                    * self.num_states
                                                                    * num_chars
                                                                    * self.max_offsets
                                                                    * self.max_offsets,
                                                            ),
                                                        ],
                                                    ),
                                                    term(
                                                        Op::PfNaryOp(PfNaryOp::Mul),
                                                        vec![
                                                            new_var(format!("state_{}", i - 1)),
                                                            new_const(
                                                                self.num_states
                                                                    * num_chars
                                                                    * self.max_offsets
                                                                    * self.max_offsets,
                                                            ),
                                                        ],
                                                    ),
                                                ],
                                            ),
                                            term(
                                                Op::PfNaryOp(PfNaryOp::Mul),
                                                vec![
                                                    new_var(format!("state_{}", i)),
                                                    new_const(
                                                        num_chars
                                                            * self.max_offsets
                                                            * self.max_offsets,
                                                    ),
                                                ],
                                            ),
                                        ],
                                    ),
                                    term(
                                        Op::PfNaryOp(PfNaryOp::Mul),
                                        vec![
                                            new_var(format!("char_{}", i - 1)),
                                            new_const(self.max_offsets * self.max_offsets),
                                        ],
                                    ),
                                ],
                            ),
                            term(
                                Op::PfNaryOp(PfNaryOp::Mul),
                                vec![
                                    new_var(format!("lower_offset_{}", i - 1)),
                                    new_const(self.max_offsets),
                                ],
                            ),
                        ],
                    ),
                    new_var(format!("upper_offset_{}", i - 1)),
                ],
            );
            v.push(v_i.clone());
            self.pub_inputs.push(new_var(format!("state_{}", i - 1)));
            self.pub_inputs.push(new_var(format!("char_{}", i - 1)));
            self.pub_inputs
                .push(new_var(format!("upper_offset_{}", i - 1)));
            self.pub_inputs
                .push(new_var(format!("lower_offset_{}", i - 1)));
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

    fn last_state_accepting_circuit(&mut self) {
        let match_term = term(
            Op::Ite,
            vec![
                term(
                    Op::Eq,
                    vec![
                        new_const(2),
                        new_var(format!("rel_{}", self.batch_size - 1)),
                    ],
                ),
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

        // LEAVE THIS IN HERE FOR DEBUGGING >:(
        /*for r in circ_r1cs.constraints().clone() {
            println!("{:#?}", circ_r1cs.format_qeq(&r));
        }*/

        circ_r1cs.finalize(&final_cs)
    }

    fn push_ite(&mut self, i: usize, to_push: Term, b: usize) -> Term {
        let pushed = term(
            Op::Eq,
            vec![new_var(format!("stack_{}_{}", b + 1, i)), to_push.clone()],
        );

        let not_pushed = term(
            Op::Eq,
            vec![
                new_var(format!("stack_{}_{}", b + 1, i)),
                new_var(format!("stack_{}_{}", b, i)),
            ],
        );

        let spi = if i == 0 { self.max_stack - 1 } else { i - 1 };
        let spb = if i == 0 { b } else { b + 1 };
        let stack_ptr_add = term(
            Op::Eq,
            vec![
                new_var(format!("stack_ptr_{}_{}", b + 1, i)),
                term(
                    Op::PfNaryOp(PfNaryOp::Add),
                    vec![new_const(1), new_var(format!("stack_ptr_{}_{}", spb, spi))],
                ),
            ],
        );

        let stack_ptr_same = term(
            Op::Eq,
            vec![
                new_var(format!("stack_ptr_{}_{}", b + 1, i)),
                new_var(format!("stack_ptr_{}_{}", spb, spi)),
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
                                new_var(format!("stack_ptr_{}_{}", b, self.max_stack - 1)),
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
    fn push_stack_circuit(&mut self) -> Term {
        let mut forall_kids = vec![];
        for k in 0..self.max_branches {
            forall_kids.push(new_var(format!("forall_0_kid_{}", k)));
        }

        // get kids from rel_i hash
        let mut hashed_state_var = new_const(4);
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

            self.pub_inputs.push(new_var(format!("forall_0_kid_{}", k)));
        }

        let hashed_kids_eq = term(Op::Eq, vec![hashed_state_var, new_var(format!("rel_0"))]);
        let lmtd_push_cond = term(
            Op::Not,
            vec![term(
                Op::Eq,
                vec![new_const(3), new_var(format!("rel_{}", 0))],
            )],
        );
        /*
        let hashed_not_pop = term(
            Op::Ite,
            vec![lmtd_push_cond, hashed_kids_eq, new_bool_const(true)],
        );*/
        //self.assertions.push(hashed_not_pop);

        // "padding" included in encoding
        assert!(forall_kids.len() == self.max_branches);

        let mut push_stmt = new_bool_const(true);
        for b in 0..self.max_branches {
            let to_push = term(
                Op::PfNaryOp(PfNaryOp::Add),
                vec![
                    term(
                        Op::PfNaryOp(PfNaryOp::Mul),
                        vec![new_var(format!("cursor_{}", 0)), new_const(self.num_states)],
                    ),
                    forall_kids[b].clone(),
                ],
            );

            let mut inside_ite = new_bool_const(true);
            for i in 0..self.max_stack {
                self.pub_inputs.push(new_var(format!("stack_{}_{}", b, i)));
                if b > 0 || i == self.max_stack - 1 {
                    self.pub_inputs
                        .push(new_var(format!("stack_ptr_{}_{}", b, i)));
                    // TODO last?
                }

                inside_ite = term(
                    Op::BoolNaryOp(BoolNaryOp::And),
                    vec![self.push_ite(i, to_push.clone(), b), inside_ite],
                );
            }

            push_stmt = term(Op::BoolNaryOp(BoolNaryOp::And), vec![inside_ite, push_stmt]);
        }

        term(
            Op::Ite,
            vec![
                lmtd_push_cond,
                term(
                    Op::BoolNaryOp(BoolNaryOp::And),
                    vec![hashed_kids_eq, push_stmt],
                ),
                new_bool_const(true),
            ],
        )
    }

    fn pop_ite(&self, i: usize, pop_elt: Term) -> Term {
        let popped = term(
            Op::Eq,
            vec![
                new_var(format!("stack_{}_{}", self.max_branches, i)),
                pop_elt.clone(),
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
                        new_var(format!(
                            "stack_ptr_{}_{}",
                            self.max_branches - 1,
                            self.max_stack - 1
                        )),
                    ],
                ),
            ],
        );

        term(
            Op::Ite,
            vec![
                term(
                    Op::Eq,
                    vec![
                        new_var(format!(
                            "stack_ptr_{}_{}",
                            self.max_branches - 1,
                            self.max_stack - 1
                        )),
                        new_const(i + 1),
                    ],
                ),
                term(Op::BoolNaryOp(BoolNaryOp::And), vec![popped, stack_ptr_sub]),
                new_bool_const(true),
            ],
        )
    }

    fn pop_stack_circuit(&mut self) -> Term {
        let cursor_var = new_var(format!("cursor_popped"));

        // pop
        let to_pop = term(
            Op::PfNaryOp(PfNaryOp::Add),
            vec![
                term(
                    Op::PfNaryOp(PfNaryOp::Mul),
                    vec![cursor_var, new_const(self.num_states)],
                ),
                new_var(format!("state_{}", 1)),
            ],
        );

        let mut inside_ite = self.pop_ite(0, to_pop.clone());

        for i in 1..self.max_stack {
            inside_ite = term(
                Op::BoolNaryOp(BoolNaryOp::And),
                vec![self.pop_ite(i, to_pop.clone()), inside_ite],
            );
        }

        let pop_condition = term(Op::Eq, vec![new_const(3), new_var(format!("rel_{}", 0))]);

        let stack_ptr_same = term(
            Op::Eq,
            vec![
                new_var(format!("stack_ptr_popped")),
                new_var(format!(
                    "stack_ptr_{}_{}",
                    self.max_branches - 1,
                    self.max_stack - 1
                )),
            ],
        );

        term(Op::Ite, vec![pop_condition, inside_ite, stack_ptr_same])
    }

    fn not_forall_circ(&self, j: usize) -> Term {
        let rel_0 = term(Op::Eq, vec![new_const(0), new_var(format!("rel_{}", j))]);
        let rel_1 = term(Op::Eq, vec![new_const(1), new_var(format!("rel_{}", j))]);
        let rel_2 = term(Op::Eq, vec![new_const(2), new_var(format!("rel_{}", j))]);

        let others = term(
            Op::BoolNaryOp(BoolNaryOp::Or),
            vec![
                term(Op::BoolNaryOp(BoolNaryOp::Or), vec![rel_0, rel_1]),
                rel_2,
            ],
        );

        // not cycle
        let cycle = term(
            Op::Eq,
            vec![
                new_var(format!("state_{}", j)),
                new_var(format!("state_{}", j + 1)),
            ],
        );

        let special = term(Op::BoolNaryOp(BoolNaryOp::Or), vec![others, cycle]);

        special
    }

    fn cursor_circuit(&mut self) {
        for j in 0..self.batch_size {
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
            self.assertions.push(cursor_plus);
            self.pub_inputs.push(new_var(format!("cursor_{}", j)));

            let bit_limit = logmn(self.udoc.len());
            let cur_overflow = term(
                Op::BvBinPred(BvBinPred::Uge),
                vec![
                    term(
                        Op::PfToBv(bit_limit),
                        vec![new_var(format!("cursor_{}", j + 1))],
                    ),
                    term(
                        Op::PfToBv(bit_limit),
                        vec![new_var(format!("cursor_{}", j))],
                    ),
                ],
            );
            self.assertions.push(cur_overflow);

            let min_offset_leq = term(
                Op::BvBinPred(BvBinPred::Uge),
                vec![
                    term(
                        Op::PfToBv(bit_limit),
                        vec![new_var(format!("offset_{}", j))],
                    ),
                    term(
                        Op::PfToBv(bit_limit),
                        vec![new_var(format!("lower_offset_{}", j))],
                    ),
                ],
            );
            self.assertions.push(min_offset_leq);

            let max_offset_geq = term(
                Op::BvBinPred(BvBinPred::Uge),
                vec![
                    term(
                        Op::PfToBv(bit_limit),
                        vec![new_var(format!("upper_offset_{}", j))],
                    ),
                    term(
                        Op::PfToBv(bit_limit),
                        vec![new_var(format!("offset_{}", j))],
                    ),
                ],
            );

            let ite_upper_off = term(
                Op::Ite,
                vec![
                    term(
                        Op::Eq,
                        vec![
                            new_const(self.star_offset),
                            new_var(format!("upper_offset_{}", j)),
                        ],
                    ),
                    new_bool_const(true),
                    max_offset_geq,
                ],
            );
            self.assertions.push(ite_upper_off);
            if j == 0 {
                // PUSH
                // if in_state \in forall - only first
                let push_stmt = self.push_stack_circuit();

                // POP
                // cursor = pop stack
                let pop_stmt = self.pop_stack_circuit();

                let mut inside_ite = new_bool_const(true);
                for i in 0..self.max_stack {
                    inside_ite = term(
                        Op::BoolNaryOp(BoolNaryOp::And),
                        vec![
                            term(
                                Op::Eq,
                                vec![
                                    new_var(format!("stack_{}_{}", self.max_branches - 1, i)),
                                    new_var(format!("stack_{}_{}", 0, i)),
                                ],
                            ),
                            inside_ite,
                        ],
                    );
                }

                let stack_ptr_same = term(
                    Op::Eq,
                    vec![
                        new_var(format!("stack_ptr_popped")),
                        new_var(format!("stack_ptr_{}_{}", 0, self.max_stack - 1)),
                    ],
                );

                // ite
                let do_what = term(
                    Op::Ite,
                    vec![
                        term(Op::Not, vec![self.not_forall_circ(0)]),
                        term(Op::BoolNaryOp(BoolNaryOp::And), vec![pop_stmt, push_stmt]),
                        term(
                            Op::BoolNaryOp(BoolNaryOp::And),
                            vec![inside_ite, stack_ptr_same],
                        ),
                    ],
                );
                self.assertions.push(do_what);

                // cursor_0
                let pop_condition = term(Op::Eq, vec![new_const(3), new_var(format!("rel_{}", 0))]);
                let c0 = term(
                    Op::Ite,
                    vec![
                        term(
                            Op::BoolNaryOp(BoolNaryOp::And),
                            vec![term(Op::Not, vec![self.not_forall_circ(0)]), pop_condition],
                        ),
                        term(
                            Op::Eq,
                            vec![
                                new_var(format!("cursor_0")),
                                new_var(format!("cursor_popped")),
                            ],
                        ),
                        term(
                            Op::Eq,
                            vec![new_var(format!("cursor_0")), new_var(format!("cursor_in"))],
                        ),
                    ],
                );
                self.assertions.push(c0);
            } else {
                // assert not forall

                self.assertions.push(self.not_forall_circ(j));
            }
            /* // transition?
                // assert cursor == EOF
                let eof = term(
                    Op::Eq,
                    vec![
                        new_var(format!("char_{}", j)),
                        new_const(self.num_ab[&Some('!')]),
                    ],
                );

                // branch transition rel val -> in is accepting
                let branch_or_not = term(
                    Op::Ite,
                    vec![
                        term(Op::Eq, vec![new_var(format!("rel_{}", j)), new_const(1)]),
                        eof,
                        new_bool_const(true),
                    ],
                );

                self.assertions.push(branch_or_not);
            */
        }
        self.pub_inputs
            .push(new_var(format!("cursor_{}", self.batch_size)));
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

    fn q_ordering_circuit(&mut self, id: &str, doc_len: usize) {
        // q relations
        for i in 0..(self.batch_size - 1) {
            // not final q (running claim)

            let mut full_q = new_const(0); // dummy
            let mut next_slot = Integer::from(1);
            let doc_l = logmn(doc_len);
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

            let q_adjust = if self.doc_subset.is_some() {
                let ds = self.doc_subset.unwrap();

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
                        new_const(self.ep_num - ds.0),
                        term(
                            Op::PfNaryOp(PfNaryOp::Add),
                            vec![
                                new_var(format!("cursor_{}", i)),
                                new_const(-1 * (ds.0 as isize)),
                            ],
                        ),
                    ],
                )
            } else {
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
                        new_var(format!("cursor_{}", i)),
                    ],
                )
            };

            let q_eq = term(Op::Eq, vec![full_q, q_adjust]);

            self.assertions.push(q_eq);
        }
    }

    pub fn to_circuit(&mut self) -> (ProverData, VerifierData) {
        let lookups = self.lookup_idxs(true);
        assert_eq!(lookups.len(), self.batch_size);
        let mut char_lookups = vec![];
        for c in 0..self.batch_size {
            char_lookups.push(new_var(format!("char_{}", c)));
        }

        self.cursor_circuit();
        self.last_state_accepting_circuit();

        if self.hybrid_len.is_some() {
            self.nlookup_hybrid(lookups, char_lookups);
        } else {
            self.nlookup_gadget(lookups, self.table.len(), "nl");
            self.nlookup_doc_commit(char_lookups);
        }

        self.r1cs_conv()
    }

    fn nlookup_hybrid(&mut self, mut pub_lookups: Vec<Term>, mut priv_lookups: Vec<Term>) {
        // TODO ordering circuit

        pub_lookups.append(&mut priv_lookups);
        self.nlookup_gadget(pub_lookups, self.hybrid_len.unwrap(), "nlhybrid");
    }

    fn nlookup_doc_commit(&mut self, priv_lookups: Vec<Term>) {
        let len = self.doc_len();
        self.q_ordering_circuit("nldoc", len);
        self.nlookup_gadget(priv_lookups, len, "nldoc");
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
        // println!("lookup rounds CIRC {}", sc_l);

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

    // only call in "active" cases
    fn pop_wit(&mut self, wits: &mut FxHashMap<String, Value>) -> usize {
        self.stack_ptr -= 1;
        let popped_elt = self.stack[self.stack_ptr];

        wits.insert(format!("cursor_popped"), new_wit(popped_elt.0));
        wits.insert(format!("cursor_0"), new_wit(popped_elt.0));

        // after pop
        wits.insert(format!("stack_ptr_popped"), new_wit(self.stack_ptr));

        // return cursor
        popped_elt.0
    }

    // TODO if not forall, pad wits
    //
    fn stack_set(&mut self, wits: &mut FxHashMap<String, Value>, b: usize, push: bool) {
        for i in 0..self.max_stack {
            wits.insert(
                format!("stack_{}_{}", b, i),
                new_wit(self.stack[i].0 * self.num_states + self.stack[i].1),
            );

            if b == 0 {
                if i == self.max_stack - 1 {
                    wits.insert(format!("stack_ptr_{}_{}", b, i), new_wit(self.stack_ptr));
                }
            } else {
                let update_ptr = if push && (i >= self.stack_ptr) {
                    self.stack_ptr + 1
                } else {
                    self.stack_ptr
                };

                wits.insert(
                    format!("stack_ptr_{}_{}", b, i), // updates sp_{+1} <- sp ( + 1)
                    new_wit(update_ptr),
                );
            }
        }
    }

    fn push_wit(
        &mut self,
        wits: &mut FxHashMap<String, Value>,
        forall: Option<NodeIndex>,
        cur_cursor: usize,
    ) {
        let forall_kids = match forall {
            Some(state) => self.foralls_w_kids[&state.index()][1..].to_vec(),
            None => vec![],
        };

        let num_kids = forall_kids.len();

        let mut b = 0;
        self.stack_set(wits, b, false);
        b += 1;

        for kid in forall_kids.into_iter().rev() {
            self.stack[self.stack_ptr] = (cur_cursor, kid);
            self.stack_set(wits, b, true);
            self.stack_ptr += 1;

            wits.insert(format!("forall_0_kid_{}", b - 1), new_wit(kid));

            b += 1;
        }

        let mut pad_kids = vec![];
        while (num_kids + pad_kids.len()) < self.max_branches {
            pad_kids.push(self.kid_padding);
        }
        for pad_kid in pad_kids {
            self.stack_set(wits, b, false);

            wits.insert(format!("forall_0_kid_{}", b - 1), new_wit(pad_kid));
            b += 1;
        }
    }

    // returns char_num, is_star
    fn get_char_num(&self, edge: Either<char, OpenSet<usize>>) -> usize {
        match edge {
            Either(Err(_openset)) => self.num_ab[&None],
            Either(Ok(ch)) => self.num_ab[&Some(ch)],
        }
    }

    fn wit_rel(
        &self,
        state_i: usize,
        next_state: usize,
        children: &Vec<usize>,
        trans: bool,
    ) -> usize {
        calc_rel(
            state_i,
            next_state,
            children,
            self.kid_padding,
            self.max_branches,
            &self.safa,
            self.num_states,
            self.exit_state,
            trans,
        )
    }

    fn padding_v(
        &self,
        wits: &mut FxHashMap<String, Value>,
        q: &mut Vec<usize>,
        cursor_access: &mut Vec<usize>,
        state_i: usize,
        next_state: usize,
        cursor_i: usize,
        i: usize, // this is for naming
    ) -> Integer {
        let char_num = self.num_ab[&None];
        cursor_access.push(self.ep_num);

        let offset_i = 0;
        let lower_offset_i = 0;
        let upper_offset_i = 0;

        let rel_i = if state_i == self.exit_state {
            0
        } else if self.safa.g[NodeIndex::new(state_i)].is_and() {
            self.wit_rel(state_i, next_state, &self.foralls_w_kids[&state_i], false)
        } else {
            self.wit_rel(state_i, next_state, &vec![], false)
        };

        wits.insert(format!("char_{}", i), new_wit(char_num));
        wits.insert(format!("state_{}", i), new_wit(state_i));
        wits.insert(format!("lower_offset_{}", i), new_wit(lower_offset_i));
        wits.insert(format!("upper_offset_{}", i), new_wit(upper_offset_i));
        wits.insert(format!("offset_{}", i), new_wit(offset_i));
        wits.insert(format!("rel_{}", i), new_wit(rel_i));
        wits.insert(format!("cursor_{}", i + 1), new_wit(cursor_i)); // alreaded "added" here

        // v_i =
        let num_chars = self.num_ab.len();

        // TODO check overflow
        let v_i = Integer::from(
            (rel_i
                * self.num_states
                * self.num_states
                * num_chars
                * self.max_offsets
                * self.max_offsets)
                + (state_i * self.num_states * num_chars * self.max_offsets * self.max_offsets)
                + (next_state * num_chars * self.max_offsets * self.max_offsets)
                + (char_num * self.max_offsets * self.max_offsets)
                + (lower_offset_i * self.max_offsets)
                + upper_offset_i,
        )
        .rem_floor(cfg().field().modulus());

        wits.insert(format!("v_{}", i), new_wit(v_i.clone()));
        /*
                println!(
                    "V_{} = {:#?} from {:#?},{:#?},{:#?},{:#?},{:#?} cursor={:#?}",
                    i, v_i, state_i, next_state, char_num, offset_i, rel_i, cursor_i,
                );
        */
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
        let mut lower_offset_i = 0;
        let mut upper_offset_i = 0;

        for edge in self.safa.g.edges(NodeIndex::new(state_i)) {
            if edge.target().index() == next_state {
                let g_edge = edge.weight();

                match g_edge {
                    Either(Err(openset)) => {
                        let single = openset.is_single(); // single offset/epsilon
                        if single.is_some() {
                            lower_offset_i = single.unwrap();
                            upper_offset_i = single.unwrap();
                        } else if openset.is_full() {
                            lower_offset_i = 0;
                            upper_offset_i = self.star_offset;
                        } else {
                            let mut iter = openset.0.iter();
                            if let Some(r) = iter.next() {
                                // ranges
                                lower_offset_i = r.start;
                                upper_offset_i = if r.end.is_some() {
                                    r.end.unwrap()
                                } else {
                                    self.star_offset
                                };
                            } else {
                                panic!("found edge with bad range");
                            }
                        }
                    }
                    Either(Ok(_ch)) => {
                        lower_offset_i = 1;
                        upper_offset_i = 1;
                    }
                }
                break;
            }
        }

        wits.insert(format!("char_{}", i), new_wit(char_num));
        wits.insert(format!("state_{}", i), new_wit(state_i));
        wits.insert(format!("lower_offset_{}", i), new_wit(lower_offset_i));
        wits.insert(format!("upper_offset_{}", i), new_wit(upper_offset_i));
        wits.insert(format!("offset_{}", i), new_wit(offset_i));
        wits.insert(format!("rel_{}", i), new_wit(rel_i));
        wits.insert(format!("cursor_{}", i + 1), new_wit(cursor_i)); // alreaded "added" here

        // v_i =
        let num_chars = self.num_ab.len();

        let v_i = Integer::from(
            (rel_i
                * self.num_states
                * self.num_states
                * num_chars
                * self.max_offsets
                * self.max_offsets)
                + (state_i * self.num_states * num_chars * self.max_offsets * self.max_offsets)
                + (next_state * num_chars * self.max_offsets * self.max_offsets)
                + (char_num * self.max_offsets * self.max_offsets)
                + (lower_offset_i * self.max_offsets)
                + upper_offset_i,
        )
        .rem_floor(cfg().field().modulus());

        wits.insert(format!("v_{}", i), new_wit(v_i.clone()));

        // println!(
        //     "V_{} = {:#?} from {:#?},{:#?},{:#?},{:#?},{:#?} cursor={:#?}",
        //     i, v_i, state_i, next_state, char_num, offset_i, rel_i, cursor_i,
        // );

        q.push(self.table.iter().position(|val| val == &v_i).unwrap());

        v_i
    }

    pub fn gen_wit_i(
        //_nlookup(
        &mut self,
        sols: &mut Vec<LinkedList<TraceElem<char>>>, //move_num: (usize, usize),
        batch_num: usize,
        in_state: usize,
        running_q: Option<Vec<Integer>>,
        running_v: Option<Integer>,
        doc_running_q: Option<Vec<Integer>>,
        doc_running_v: Option<Integer>,
        hybrid_running_q: Option<Vec<Integer>>,
        hybrid_running_v: Option<Integer>,
        cursor_0: usize,
    ) -> (
        FxHashMap<String, Value>,
        usize,
        Option<Vec<Integer>>,
        Option<Integer>,
        Option<Vec<Integer>>,
        Option<Integer>,
        Option<Vec<Integer>>,
        Option<Integer>,
        usize,
    ) {
        let mut wasted = 0;
        let mut wits = FxHashMap::default();

        // generate claim v's (well, v isn't a real named var, generate the states/chars)
        let mut state_i = in_state;
        let mut next_state = 0;
        let mut char_num;
        let mut offset_i;
        let mut rel_i = 0;

        let mut v = vec![];
        let mut q = vec![];
        let mut i = 0;
        let mut cursor_i = cursor_0;
        let mut cursor_access = vec![];

        wits.insert(format!("cursor_in"), new_wit(cursor_i));

        while i < self.batch_size {
            let mut add_normal = true;
            if self.sol_num >= sols.len() {
                // all done, pad to end
                add_normal = false;
                while i < self.batch_size {
                    state_i = next_state;
                    v.push(self.padding_v(
                        &mut wits,
                        &mut q,
                        &mut cursor_access,
                        state_i,
                        next_state,
                        cursor_i,
                        i,
                    ));
                    wasted += 1;
                    i += 1;
                }
            } else if sols[self.sol_num].is_empty() {
                // need to transition

                // not forall (TODO check cursor_i correct)
                if i == 0 {
                    // must pad out the stack
                    // fill stack vars with padding
                    self.push_wit(&mut wits, None, cursor_i);
                    // pad out "popped" vars, since there's no pop
                    wits.insert(format!("cursor_popped"), new_wit(cursor_i));
                    wits.insert(format!("cursor_0"), new_wit(cursor_i));
                    wits.insert(format!("stack_ptr_popped"), new_wit(self.stack_ptr));
                }
                char_num = self.num_ab[&None];
                cursor_access.push(self.ep_num);

                offset_i = 0;
                if self.sol_num + 1 == sols.len() {
                    // very last
                    next_state = self.exit_state;
                } else {
                    next_state = sols[self.sol_num + 1].front().unwrap().from_node.index();
                }

                // transition
                rel_i = if self.safa.g[NodeIndex::new(state_i)].is_and() {
                    self.wit_rel(state_i, next_state, &self.foralls_w_kids[&state_i], true)
                } else {
                    self.wit_rel(state_i, next_state, &vec![], true)
                };

                v.push(self.edge_v(
                    &mut wits, &mut q, char_num, state_i, next_state, offset_i, cursor_i, rel_i, i,
                ));
                i += 1;

                self.sol_num += 1;
            } else {
                // from solution
                let te_peek = sols[self.sol_num].front().unwrap();

                // handle stack pushes during forall
                if self.safa.g[te_peek.from_node].is_and() {
                    // push branch
                    //forall and not coming from
                    //a transition
                    // forall
                    if i == 0 {
                        // correct place

                        if self.foralls_w_kids[&te_peek.from_node.index()][0]
                            == te_peek.to_node.index()
                        {
                            // pushed
                            self.push_wit(&mut wits, Some(te_peek.from_node), cursor_i);
                            // pad pop
                            wits.insert(format!("cursor_popped"), new_wit(cursor_i));
                            wits.insert(format!("cursor_0"), new_wit(cursor_i));
                            wits.insert(format!("stack_ptr_popped"), new_wit(self.stack_ptr));
                        } else {
                            // pad push
                            self.push_wit(&mut wits, None, cursor_i);
                            // popped
                            cursor_i = self.pop_wit(&mut wits);
                        }
                    } else {
                        // pad out the rest of this loop
                        add_normal = false;
                        while i < self.batch_size {
                            state_i = next_state;
                            v.push(self.padding_v(
                                &mut wits,
                                &mut q,
                                &mut cursor_access,
                                state_i,
                                next_state,
                                cursor_i,
                                i,
                            ));
                            wasted += 1;
                            i += 1;
                        }
                    }
                } else {
                    // not forall
                    if i == 0 {
                        // must pad out the stack
                        // fill stack vars with padding
                        self.push_wit(&mut wits, None, cursor_i);
                        // pad out "popped" vars, since there's no pop
                        wits.insert(format!("cursor_popped"), new_wit(cursor_i));
                        wits.insert(format!("cursor_0"), new_wit(cursor_i));
                        wits.insert(format!("stack_ptr_popped"), new_wit(self.stack_ptr));
                    }
                }

                if add_normal {
                    let te = sols[self.sol_num].pop_front().unwrap();
                    // normal transition
                    char_num = self.get_char_num(te.edge);

                    if char_num == self.num_ab[&None] {
                        cursor_access.push(self.ep_num);
                    } else {
                        cursor_access.push(cursor_i);
                    }

                    state_i = te.from_node.index();
                    next_state = te.to_node.index();
                    offset_i = te.to_cur - te.from_cur;

                    cursor_i += offset_i;

                    rel_i = if self.safa.g[NodeIndex::new(state_i)].is_and() {
                        self.wit_rel(state_i, next_state, &self.foralls_w_kids[&state_i], false)
                    } else {
                        self.wit_rel(state_i, next_state, &vec![], false)
                    };
                    v.push(self.edge_v(
                        &mut wits, &mut q, char_num, state_i, next_state, offset_i, cursor_i,
                        rel_i, i,
                    ));

                    i += 1;
                }
            }

            state_i = next_state;
        }

        //println!("DONE LOOP");
        println!("'WASTED' SLOTS THIS ITERATION: {}", wasted);

        // last state
        wits.insert(format!("state_{}", self.batch_size), new_wit(next_state));

        let accept = if rel_i == 2 { 1 } else { 0 }; //todo
        wits.insert(format!("accepting"), new_wit(accept));

        assert_eq!(v.len(), self.batch_size);

        // projections
        let mut doc_v = vec![];
        let mut doc_q = vec![];
        let proj_doc;
        if self.doc_subset.is_some() {
            let ds = self.doc_subset.unwrap();
            proj_doc = &self.idoc[ds.0..ds.1];
            for i in 0..self.batch_size {
                let access_at = cursor_access[i];
                doc_q.push(access_at - ds.0);
                doc_v.push(self.idoc[access_at].clone());
            }
        } else {
            proj_doc = &self.idoc;
            for i in 0..self.batch_size {
                let access_at = cursor_access[i];
                doc_q.push(access_at);
                doc_v.push(self.idoc[access_at].clone());
            }
        };

        let mut next_running_q = None;
        let mut next_running_v = None;
        let mut next_doc_running_q = None;
        let mut next_doc_running_v = None;
        let mut next_hybrid_running_q = None;
        let mut next_hybrid_running_v = None;

        if self.hybrid_len.is_some() {
            // pub T first, then priv D
            let half_len = self.hybrid_len.unwrap() / 2;

            let mut hybrid_table = self.table.clone();
            hybrid_table.append(&mut vec![Integer::from(0); half_len - self.table.len()]);
            hybrid_table.append(&mut proj_doc.to_vec());
            hybrid_table.append(&mut vec![Integer::from(0); half_len - proj_doc.len()]); // need??

            println!("hybrid table {:#?}", hybrid_table.clone());

            let mut hybrid_q = q.clone();
            for qd in doc_q {
                hybrid_q.push(qd + half_len); // idx'd by 1
            }

            let mut hybrid_v = v.clone();
            hybrid_v.extend(doc_v);

            assert!(hybrid_running_q.is_some() || batch_num == 0);
            assert!(hybrid_running_v.is_some() || batch_num == 0);

            let (w, rq, rv) = self.wit_nlookup_gadget(
                wits,
                &hybrid_table,
                hybrid_q,
                hybrid_v,
                hybrid_running_q,
                hybrid_running_v,
                "nlhybrid",
            );
            wits = w;
            next_hybrid_running_q = Some(rq);
            next_hybrid_running_v = Some(rv);
        } else {
            assert!(running_q.is_some() || batch_num == 0);
            assert!(running_v.is_some() || batch_num == 0);
            let (w, rq, rv) =
                self.wit_nlookup_gadget(wits, &self.table, q, v, running_q, running_v, "nl");
            wits = w;
            next_running_q = Some(rq);
            next_running_v = Some(rv);

            assert!(doc_running_q.is_some() || batch_num == 0);
            assert!(doc_running_v.is_some() || batch_num == 0);

            let (w, drq, drv) = self.wit_nlookup_gadget(
                wits,
                proj_doc,
                doc_q,
                doc_v,
                doc_running_q,
                doc_running_v,
                "nldoc",
            );
            wits = w;
            next_doc_running_q = Some(drq);
            next_doc_running_v = Some(drv);
        }

        (
            wits,
            next_state,
            next_running_q,
            next_running_v,
            next_doc_running_q,
            next_doc_running_v,
            next_hybrid_running_q,
            next_hybrid_running_v,
            cursor_i,
        )
    }

    fn wit_nlookup_gadget(
        &self,
        mut wits: FxHashMap<String, Value>,
        table: &[Integer],
        q: Vec<usize>,
        v: Vec<Integer>,
        running_q: Option<Vec<Integer>>,
        running_v: Option<Integer>,
        id: &str,
    ) -> (FxHashMap<String, Value>, Vec<Integer>, Integer) {
        let sc_l = logmn(table.len()); // sum check rounds
                                       //println!("WITNESS SC ROUNDS {}", sc_l);

        let num_vs = v.len();
        assert_eq!(num_vs, q.len());

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
        let num_cqs = ((num_vs * sc_l) as f64 / 254.0).ceil() as usize;

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
                    /*println!(
                        "{}_q_{} = {:#?} from {:#?}",
                        q_name,
                        (sc_l - 1 - j),
                        qj.clone(),
                        q[i].clone()
                    );*/
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
            "nlhybrid" => vec![
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
            "nldoc" => vec![self.doc_hash.unwrap()],
            "nlhybrid" => vec![self.doc_hash.unwrap()],
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
            "nl" => table.to_vec(),
            "nldoc" => {
                let base: usize = 2;
                let len = base.pow(logmn(table.len()) as u32) - table.len();

                let mut sct = table.to_vec();
                sct.extend(vec![Integer::from(0); len]); // ep num = self.nfa.nchars()
                sct
            }
            "nlhybrid" => table.to_vec(),
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
        //println!("EQ TERM {:#?}", eq_term);
        assert_eq!(
            last_claim,
            (eq_term * next_running_v.clone()).rem_floor(cfg().field().modulus())
        );
        (wits, next_running_q, next_running_v)
    }
}

pub fn ceil_div(a: usize, b: usize) -> usize {
    (a + b - 1) / b
}

#[cfg(test)]
mod tests {
    use crate::backend::r1cs::*;
    use crate::frontend::regex::re;
    use crate::frontend::safa::SAFA;
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

            // sanity check
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
        proj: Option<usize>,
        hybrid: bool,
    ) {
        let r = re::simpl(re::new(&rstr));
        let safa = SAFA::new(&ab[..], &r);

        let chars: Vec<char> = doc.chars().collect(); //map(|c| c.to_string()).collect();

        let sc = Sponge::<<G1 as Group>::Scalar, typenum::U4>::api_constants(Strength::Standard);

        for b in batch_sizes {
            let mut r1cs_converter = R1CS::new(&safa, &chars, b, proj, hybrid, sc.clone());
            // TODO hybrid

            let mut reef_commit =
                ReefCommitment::new(r1cs_converter.udoc.clone(), r1cs_converter.hybrid_len, &sc);
            r1cs_converter.doc_hash = Some(reef_commit.doc_commit_hash);

            let mut running_q: Option<Vec<Integer>> = None;
            let mut running_v: Option<Integer> = None;
            let mut doc_running_q: Option<Vec<Integer>> = None;
            let mut doc_running_v: Option<Integer> = None;
            let mut hybrid_running_q: Option<Vec<Integer>> = None;
            let mut hybrid_running_v: Option<Integer> = None;

            let mut doc_idx = 0;

            let (pd, _vd) = r1cs_converter.to_circuit();

            let mut values;
            let mut next_state = 0;

            let trace = safa.solve(&chars);

            let mut sols = trace_preprocessing(&trace, &safa);

            let mut i = 0;
            while r1cs_converter.sol_num < sols.len() {
                println!("STEP {:#?}", i);
                (
                    values,
                    next_state,
                    running_q,
                    running_v,
                    doc_running_q,
                    doc_running_v,
                    hybrid_running_q,
                    hybrid_running_v,
                    doc_idx,
                ) = r1cs_converter.gen_wit_i(
                    &mut sols,
                    i,
                    next_state,
                    running_q.clone(),
                    running_v.clone(),
                    doc_running_q.clone(),
                    doc_running_v.clone(),
                    hybrid_running_q.clone(),
                    hybrid_running_v.clone(),
                    doc_idx,
                );

                pd.check_all(&values);

                // for next i+1 round
                i += 1;
            }

            let rq = match running_q {
                Some(x) => Some(x.into_iter().map(|i| int_to_ff(i)).collect()),
                None => None,
            };
            let rv = match running_v {
                Some(x) => Some(int_to_ff(x)),
                None => None,
            };

            let (priv_rq, priv_rv) = if !hybrid {
                (doc_running_q.unwrap(), doc_running_v.unwrap())
            } else {
                (
                    hybrid_running_q.clone().unwrap(),
                    hybrid_running_v.clone().unwrap(),
                )
            };

            let hrq = match hybrid_running_q {
                Some(x) => Some(x.into_iter().map(|i| int_to_ff(i)).collect()),
                None => None,
            };

            assert_eq!(next_state, r1cs_converter.exit_state);

            let doc_len = r1cs_converter.udoc.len();
            let proj_len = r1cs_converter.doc_len();

            let consist_proof = reef_commit.prove_consistency(
                &r1cs_converter.table,
                proj_len,
                priv_rq,
                priv_rv,
                r1cs_converter.doc_subset.is_some(),
                r1cs_converter.hybrid_len.is_some(),
            );

            let cap_d = consist_proof.hash_d.clone();

            let (t, q_0) = final_clear_checks(
                <G1 as Group>::Scalar::from(r1cs_converter.stack_ptr as u64),
                &r1cs_converter.table,
                rq,
                rv,
                hrq,
            );

            reef_commit.verify_consistency(consist_proof, t, q_0);

            // final accepting
            assert_eq!(next_state, r1cs_converter.exit_state);

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

    #[test]
    fn proj_hybrid() {
        init();
        test_func_no_hash(
            "abcd".to_string(),
            "^.............d$".to_string(),
            "aabbccddaabbdd".to_string(), // really [ aabbcc, EOF, epsilon ]
            vec![2],                      // 2],
            true,
            Some(5), // (4,8)
            true,
        );
    }
    #[test]
    #[should_panic]
    fn proj_hybrid_panic() {
        test_func_no_hash(
            "abcd".to_string(),
            "^.....c$".to_string(),
            "aabbcc".to_string(), // really [ aabbcc, EOF, epsilon ]
            vec![2],              // 2],
            true,
            Some(5), // (4,8)
            true,
        );
    }

    #[test]
    fn hybrid() {
        init();

        test_func_no_hash(
            "ab".to_string(),
            "^ab$".to_string(),
            "ab".to_string(), // really [ aabbcc, EOF, epsilon ]
            vec![2],          // 2],
            true,
            None,
            true,
        );
    }

    #[test]
    fn projections() {
        init();

        // proj upper
        test_func_no_hash(
            "abcd".to_string(),
            "^.....c$".to_string(),
            "aabbcc".to_string(), // really [ aabbcc, EOF, epsilon ]
            vec![2],              // 2],
            true,
            Some(5), // (4,8)
            false,
        );
    }

    #[test]
    fn naive_1() {
        init();
        test_func_no_hash(
            "abcd".to_string(),
            "^(?=a)ab(?=c)cd$".to_string(),
            "abcd".to_string(),
            vec![2], // 2],
            true,
            None,
            false,
        );
    }

    #[test]
    fn naive_2() {
        init();
        test_func_no_hash(
            "abcd".to_string(),
            "(?=a)ab(?=c)cd".to_string(),
            "abcd".to_string(),
            vec![2], // 2],
            true,
            None,
            false,
        );
    }

    #[test]
    fn nfa_2() {
        init();
        test_func_no_hash(
            "ab".to_string(),
            "^ab$".to_string(),
            "ab".to_string(),
            vec![2],
            true,
            None,
            false,
        );
        /*    test_func_no_hash(
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
        );*/
    }

    #[test]
    fn nfa_star() {
        init();
        test_func_no_hash(
            "ab".to_string(),
            "^a*b*$".to_string(),
            "aaab".to_string(),
            vec![2],
            true,
            None,
            false,
        );
        test_func_no_hash(
            "ab".to_string(),
            "^a*b*$".to_string(),
            "aaaaaabbbbbbbbbbbbbb".to_string(),
            vec![2, 4],
            true,
            None,
            false,
        );
        test_func_no_hash(
            "ab".to_string(),
            "^a*b*$".to_string(),
            "aaaaaaaaaaab".to_string(),
            vec![2, 4],
            true,
            None,
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
            vec![2],
            false,
            None,
            false,
        );
    }

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
    fn nfa_ok_substring() {
        init();
        test_func_no_hash(
            "helowrd".to_string(),
            "^hello.*$".to_string(),
            "helloworld".to_string(),
            vec![2],
            true,
            None,
            false,
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
            vec![2, 3, 4, 6, 7],
            true,
            None,
            false,
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
            None,
            false,
        );

        test_func_no_hash(
            "abcdefg".to_string(),
            "^gaaaaaabbbbbbccccccddddddeeeeeef$".to_string(),
            "gaaaaaabbbbbbccccccddddddeeeeeef".to_string(),
            vec![33],
            true,
            None,
            false,
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
            vec![2],
            true,
            None,
            false,
        );
    }
}
