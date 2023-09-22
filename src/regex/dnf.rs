use std::collections::BTreeSet;
use core::{fmt, fmt::Debug, fmt::Display};
use core::fmt::Formatter;
use itertools::Itertools;

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub struct AndSet<T>(BTreeSet<T>);

/// Disjunctive Normal form set of terms
#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub struct OrSet<T>(BTreeSet<AndSet<T>>);

impl<T: Ord + Clone> AndSet<T> {
    /// [a, b, ...] = (a \/ b ...)
    pub fn new(v: &Vec<T>) -> Self {
        AndSet(v.into_iter().map(|t| t.clone()).collect())
    }

    /// ( )
    pub fn empty() -> Self {
        AndSet(BTreeSet::new())
    }

    /// ( t )
    pub fn single(t: &T) -> Self {
        let mut s = BTreeSet::new();
        s.insert(t.clone());
        AndSet(s)
    }

    /// (a /\ b ... ) /\ (x /\ y) = (a /\ b /\ x /\ y ... )
    pub fn and(&self, b: &Self) -> Self {
        let mut s = self.0.clone();
        s.append(&mut b.0.clone());
        AndSet(s)
    }

    /// (a /\ b ... ) \/ z = { (a /\ b ... ) \/ z }
    pub fn or(&self, b: &Self) -> OrSet<T> {
        OrSet(BTreeSet::from([self.clone(), b.clone()]))
    }

    /// (a /\ b ... ) = { (a /\ b ... ) }
    pub fn to_or(&self) -> OrSet<T> {
        OrSet(BTreeSet::from([self.clone()]))
    }
}

impl<T: Ord + Clone> OrSet<T> {
    /// [a, b, ...] = { a /\ b ... }
    pub fn new_and(v: &Vec<T>) -> Self {
        OrSet(BTreeSet::from([AndSet::new(v)]))
    }

    /// [a, b, ...] = { (a \/ b ...) }
    pub fn new_or(v: &Vec<T>) -> Self {
        OrSet(v.into_iter().map(|t| AndSet::single(t)).collect())
    }

    /// { }
    pub fn empty() -> Self {
        OrSet(BTreeSet::new())
    }

    /// { t }
    pub fn single(t: &T) -> Self {
        OrSet(BTreeSet::from([AndSet::single(t)]))
    }

    /// { a \/ b ... } \/ z = { a \/ b \/ z ... }
    pub fn or(&self, b: &Self) -> Self {
        let mut s = self.0.clone();
        s.append(&mut b.0.clone());
        OrSet(s)
    }

    /// { a \/ b ... } /\ { x \/ y ... } = { (a /\ x) \/ (a /\ y) \/ (b /\ x) \/ (b /\ y) }
    pub fn and(&self, b: &Self) -> Self {
        OrSet(self.0
                .iter()
                .cartesian_product(b.0.iter())
                .map(|(a, x)| a.and(x))
                .collect())
    }

    pub fn map<Y: Ord, F>(self, f: F) -> OrSet<Y>
        where F: Fn(T) -> Y {
        OrSet(self.0.into_iter().map(|s| AndSet(s.into_iter().map(&f).collect())).collect())
    }

    pub fn flat_map<Y: Ord + Clone, F>(self, f: F) -> OrSet<Y>
        where F: Fn(T) -> OrSet<Y> {
        let mut oacc = OrSet::empty();
        for mut ands in self.0.into_iter() {
            if let Some(acc) = ands.0.pop_first() {
                oacc = oacc.or(&ands.0.into_iter().fold(f(acc), |acc: OrSet<Y>, x: T| acc.and(&f(x))));
            }
        }
        oacc
    }

}

impl<C: Display> fmt::Display for AndSet<C> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "( {} )", self.0.iter().join(r"/\"))
    }
}

impl<C: Display> fmt::Display for OrSet<C> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{{ {} }}", self.0.iter().join(r"\/"))
    }
}

impl<T> IntoIterator for AndSet<T> {
    type Item = T;
    type IntoIter = std::collections::btree_set::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T> IntoIterator for OrSet<T> {
    type Item = AndSet<T>;
    type IntoIter = std::collections::btree_set::IntoIter<AndSet<T>>;


    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}
