use petgraph::graph::NodeIndex;

use core::fmt;
use core::fmt::{Display, Formatter};
use std::fmt::Debug;
use std::hash::Hash;
use std::collections::LinkedList;
use crate::frontend::safa::{Either, Skip};

/// Type of solver result, a matchign [Trace]
#[derive(Debug, Clone, Hash, PartialOrd, Ord, PartialEq, Eq)]
pub struct Trace<C>(pub LinkedList<TraceElem<C>>);
impl<C: Clone> Trace<C> {
    pub fn new(v: &[TraceElem<C>]) -> Self {
        let mut l = LinkedList::new();
        for x in v.iter() {
            l.push_back(x.clone())
        }
        Trace(l)
    }
    pub fn push_back(&mut self, a: TraceElem<C>) {
        self.0.push_back(a);
    }
    pub fn push_front(&mut self, a: TraceElem<C>) {
        self.0.push_front(a);
    }

    pub fn empty() -> Self {
        Self(LinkedList::new())
    }
    pub fn flatten(s: &Vec<Trace<C>>) -> Trace<C> {
        let mut r = LinkedList::new();
        for i in s {
            for j in i.0.iter() {
                r.push_back(j.clone());
            }
        }
        Trace(r)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct TraceElem<C> {
    pub from_node: NodeIndex<u32>,
    pub edge: Either<C, Skip>,
    pub to_node: NodeIndex<u32>,
    pub from_cur: usize,
    pub to_cur: usize,
}

impl<C: PartialOrd> PartialOrd for TraceElem<C> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.to_node.index().partial_cmp(&other.to_node.index())
    }
}

impl<C: Ord> Ord for TraceElem<C> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.to_node.index().cmp(&other.to_node.index())
    }
}

impl<C: Clone> TraceElem<C> {
    pub fn new(from: usize, e: &Either<C, Skip>, to: usize, i: usize, j: usize) -> Self {
        Self {
            from_node: NodeIndex::new(from),
            edge: e.clone(),
            to_node: NodeIndex::new(to),
            from_cur: i,
            to_cur: j,
        }
    }

    pub fn is_nil(&self) -> bool {
        match self.edge.0 {
            Ok(_) => false,
            Err(ref e) => e.is_nil(),
        }
    }
}

impl<C: Display> Display for TraceElem<C> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{{{} -[ {} ]-> {} @ Doc[{} - {}]}}",
            self.from_node.index(),
            self.edge,
            self.to_node.index(),
            self.from_cur,
            self.to_cur
        )
    }
}

impl<C: Display> Display for Trace<C> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut s = Vec::new();
        for x in self.0.iter() {
            s.push(format!("{}", x));
        }
        write!(f, "{}", s.join(", "))
    }
}
