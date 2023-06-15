use std::collections::LinkedList;

use petgraph::graph::NodeIndex;
use rayon::iter::*;

use core::fmt;
use core::fmt::{Display, Formatter};
use std::fmt::Debug;
use std::hash::Hash;

use crate::safa::{Either, Skip};

/// Type of solver result, a matchign [Trace]
#[derive(Debug, Clone, Hash, PartialOrd, Ord, PartialEq, Eq)]
pub struct Trace<C>(pub LinkedList<TraceElem<C>>);

impl<C: Clone> Trace<C> {
    pub fn new(v: &[TraceElem<C>]) -> Self {
        let mut l = LinkedList::new();
        for x in v.into_iter() {
            l.push_back(x.clone());
        }
        Trace(l)
    }
    pub fn prepend(v: Option<Self>, a: TraceElem<C>) -> Option<Self> {
            let mut l = v?.0;
            l.push_front(a);
            Some(Self(l))
    }
    pub fn empty() -> Self {
        Self(LinkedList::new())
    }
}

#[derive(Debug, Clone, Hash, PartialOrd, Ord, PartialEq, Eq)]
pub struct TraceElem<C> {
    pub from_node: NodeIndex<u32>,
    pub edge: Either<C, Skip>,
    pub to_node: NodeIndex<u32>,
    pub from_cur: usize,
    pub to_cur: usize,
}

impl<C: Clone> TraceElem<C> {
    pub fn new(
        from: usize,
        e: &Either<C, Skip>,
        to: usize,
        i: usize,
        j: usize,
    ) -> Self {
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

