use core::fmt;
use core::fmt::{Display, Formatter};
use std::fmt::Debug;
use std::hash::Hash;

use crate::frontend::regex::Regex;

use petgraph::graph::NodeIndex;

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Quant<A> {
    pub inner: A,
    is_and: bool,
    is_neg: bool,
}

impl<A: Clone> Quant<A> {
    pub fn new(inner: A, is_and: bool) -> Self {
        Self {
            inner,
            is_and,
            is_neg: false,
        }
    }
    pub fn and(inner: A) -> Self {
        Self {
            inner,
            is_and: true,
            is_neg: false,
        }
    }
    pub fn or(inner: A) -> Self {
        Self {
            inner,
            is_and: false,
            is_neg: false,
        }
    }
    pub fn is_and(&self) -> bool {
        self.is_and
    }
    pub fn is_or(&self) -> bool {
        !self.is_and
    }
    pub fn negate(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            is_and: !self.is_and,
            is_neg: !self.is_neg,
        }
    }
    pub fn get(&self) -> A {
        self.inner.clone()
    }
    pub fn map<B, F>(&self, f: F) -> Quant<B>
    where
        F: Fn(A) -> B,
    {
        Quant {
            inner: f(self.inner.clone()),
            is_and: self.is_and,
            is_neg: self.is_neg,
        }
    }
}

impl Display for Quant<String> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.is_and {
            write!(f, "∀ {}", self.get())
        } else {
            write!(f, "∃ {}", self.get())
        }
    }
}

impl Display for Quant<NodeIndex<u32>> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.map(|c| c.index().to_string()))
    }
}

impl Display for Quant<Regex> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.map(|c| c.to_string()))
    }
}
