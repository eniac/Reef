use core::fmt;
use core::fmt::{Display, Formatter};
use std::fmt::Debug;
use std::hash::Hash;

use crate::regex::Regex;

use petgraph::graph::NodeIndex;

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Quant<A>(pub A, bool);

impl<A: Clone> Quant<A> {
    pub fn and(a: A) -> Self {
        Self(a, true)
    }
    pub fn or(a: A) -> Self {
        Self(a, false)
    }
    pub fn is_and(&self) -> bool {
        self.1
    }
    pub fn is_or(&self) -> bool {
        !self.1
    }
    pub fn get(&self) -> A {
        self.0.clone()
    }

    pub fn map<B, F>(&self, f: F) -> Quant<B> where F: Fn(A)-> B {
        Quant(f(self.0.clone()), self.1)
    }
}

impl Display for Quant<Regex> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.1 {
            write!(f, "∀ {}", self.0)
        } else {
            write!(f, "∃ {}", self.0)
        }
    }
}

impl Display for Quant<NodeIndex<u32>> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.1 {
            write!(f, "∀ {}", self.0.index())
        } else {
            write!(f, "∃ {}", self.0.index())
        }
    }
}



