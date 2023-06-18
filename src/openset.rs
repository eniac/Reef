#![allow(dead_code)]
#![allow(missing_docs)]
use core::fmt::Formatter;
use core::{fmt, fmt::Debug, fmt::Display};

use std::collections::BTreeSet;
use std::default::Default;
use std::iter::Step;

/// An Open set of ranges is an efficient representation for ranges of characters, integers etc
/// that might or might not be closed. For example,
/// { (0,3), (4,6), (8, *) }
///
/// It implements the operations [union, negation, concatenation, unit, annhiliation]
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct OpenRange<C> {
    pub start: C,
    pub end: Option<C>,
}

impl<C: Display + Debug + Step + Default + Ord + Copy + Clone> OpenRange<C> {
    pub fn new(start: C, end: Option<C>) -> Self {
        Self { start, end }
    }
    pub fn open(start: C) -> Self {
        Self { start, end: None }
    }
    pub fn closed(start: C, end: C) -> Self {
        Self {
            start,
            end: Some(end),
        }
    }
    pub fn nil() -> Self {
        Self {
            start: Default::default(),
            end: Some(Default::default()),
        }
    }
    pub fn is_open(&self) -> bool {
        self.end.is_none()
    }
    pub fn is_closed(&self) -> bool {
        self.end.is_some()
    }

    pub fn len(&self) -> Option<usize> {
        let e = self.end?;
        Step::steps_between(&self.start, &e)
    }

    pub fn union(&self, o: &Self) -> OpenSet<C> {
        match (self.end, o.end) {
            (None, None) => OpenSet::open(self.start.min(o.start)),
            (Some(e), None) if Step::forward(e, 1) < o.start => {
                OpenSet(BTreeSet::from([self.clone(), o.clone()]))
            } // no overlap
            (None, Some(e)) if Step::forward(e, 1) < self.start => {
                OpenSet(BTreeSet::from([self.clone(), o.clone()]))
            } // no overlap
            (Some(_), None) | (None, Some(_)) => OpenSet::open(self.start.min(o.start)),
            (Some(se), Some(oe)) => {
                let start = self.start.max(o.start);
                let end = se.min(oe);
                if start <= Step::forward(end, 1) {
                    OpenSet::closed(self.start.min(o.start), se.max(oe))
                } else {
                    OpenSet(BTreeSet::from([self.clone(), o.clone()]))
                }
            }
        }
    }

    pub fn negate(&self) -> OpenSet<C> {
        match self.clone() {
            // ! (0,b) = [(b+1, *)]
            Self {
                start,
                end: Some(e),
            } if start == Default::default() => OpenSet::open(Step::forward(e.clone(), 1)),
            // ! (a,b) = [(0, a-1), (b+1, *)]
            Self {
                start,
                end: Some(e),
            } => OpenSet::new(&[
                (Default::default(), Some(Step::backward(start, 1))),
                (Step::forward(e.clone(), 1), None),
            ]),
            // ! (0,*) = []
            Self { start, end: None } if start == Default::default() => OpenSet::empty(),
            // ! (a,*) = [(0, a-1)]
            Self { start, end: None } => {
                OpenSet::closed(Default::default(), Step::backward(start.clone(), 1))
            }
        }
    }
    /// Is [0, *]
    pub fn is_full(&self) -> bool {
        self.start == Default::default() && self.end.is_none()
    }
}

impl<C: PartialOrd> PartialOrd for OpenRange<C> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self.start.partial_cmp(&other.start), &self.end, &other.end) {
            (Some(std::cmp::Ordering::Equal), None, _) => Some(std::cmp::Ordering::Greater),
            (Some(std::cmp::Ordering::Equal), Some(_), None) => Some(std::cmp::Ordering::Less),
            (Some(std::cmp::Ordering::Equal), Some(a), Some(b)) => a.partial_cmp(&b),
            (o, _, _) => o,
        }
    }
}

impl<C: Ord> Ord for OpenRange<C> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self.start.cmp(&other.start), &self.end, &other.end) {
            (std::cmp::Ordering::Equal, None, _) => std::cmp::Ordering::Greater,
            (std::cmp::Ordering::Equal, Some(_), None) => std::cmp::Ordering::Less,
            (std::cmp::Ordering::Equal, Some(a), Some(b)) => a.cmp(b),
            (o, _, _) => o,
        }
    }
}

impl<C: Display + Eq + Default> fmt::Display for OpenRange<C> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.end {
            Some(ref e) if &self.start == e && *e == Default::default() => write!(f, "ε"),
            Some(ref e) if &self.start == e => write!(f, "{}", e),
            Some(ref e) => write!(f, "{}-{}", self.start, e),
            None => write!(f, "{}-*", self.start),
        }
    }
}

#[derive(Debug, Clone, Hash, PartialOrd, Ord, PartialEq, Eq)]
pub struct OpenSet<C>(pub BTreeSet<OpenRange<C>>);

impl<C: Debug + Step + Ord + Eq + Display + Default + Copy> fmt::Display for OpenSet<C> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if let Some(s) = self.is_single() {
            if s == Default::default() {
                return write!(f, "ε");
            } else {
                return write!(f, "{}", s);
            }
        }
        let mut it = self.0.iter();
        if let Some(v) = it.next() {
            write!(f, "[{}", v)?;
            for r in it {
                write!(f, ", {}", r)?;
            }
            write!(f, "]")
        } else {
            write!(f, "∅")
        }
    }
}

impl<T: Step + Copy> Iterator for OpenRange<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let res = self.start;
        match self.end {
            Some(e) if res <= e => {
                self.start = Step::forward(self.start, 1);
                Some(res)
            }
            None => {
                self.start = Step::forward(self.start, 1);
                Some(res)
            }
            _ => None,
        }
    }
}

impl<T: Step + Ord + Copy> Iterator for OpenSet<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let mut h = self.0.pop_first()?;
        if let Some(res) = h.next() {
            self.0.insert(h);
            Some(res)
        } else {
            self.next()
        }
    }
}

impl<C: Display + Debug + Step + Default + Ord + Copy> OpenSet<C> {
    /// Nominal constructor
    pub fn new(v: &[(C, Option<C>)]) -> Self {
        Self::from_iter(v.iter().map(|c| c.clone()))
    }

    pub fn from_iter(v: impl Iterator<Item = (C, Option<C>)>) -> Self {
        Self(v.map(|(start, end)| OpenRange::new(start, end)).collect())
    }

    /// Empty C class (∅)
    pub fn empty() -> Self {
        Self::new(&[])
    }
    /// Single closed range [a,b]
    pub fn closed(from: C, to: C) -> Self {
        if to < from {
            Self::empty()
        } else {
            Self::new(&[(from, Some(to))])
        }
    }
    /// Single open range [a,*]
    pub fn open(a: C) -> Self {
        Self::new(&[(a, None)])
    }
    /// Create a single Cacter
    pub fn single(a: C) -> Self {
        Self::new(&[(a, Some(a))])
    }

    /// Nil set (0 length)
    pub fn nil() -> Self {
        Self::single(Default::default())
    }

    /// Kleene star
    pub fn star() -> Self {
        Self::open(Default::default())
    }

    /// Is it empty (∅)
    pub fn is_empty(&self) -> bool {
        self.0.len() == 0
    }
    /// Set is full (0, *)
    pub fn is_full(&self) -> bool {
        self.0.iter().any(|r| r.is_full())
    }
    /// Is nil
    pub fn is_nil(&self) -> bool {
        if let Some(v) = self.is_single() {
            v == Default::default()
        } else {
            false
        }
    }

    /// Is it a single character, if yes return it
    pub fn is_single(&self) -> Option<C> {
        if self.0.len() == 1 {
            let h = self.0.iter().next()?;
            let end = h.end?;
            if h.start == end {
                Some(end)
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Does it contain [c]
    pub fn contains(&self, c: &C) -> bool {
        self.0
            .iter()
            .any(|r| r.start <= *c && r.end.map_or(true, |b| c <= &b))
    }

    /// Minimum (first) bound
    pub fn start(&self) -> Option<C> {
        self.0.first().map(|r| r.start)
    }

    /// Insert an interval in the range set
    pub fn insert(&mut self, r: &OpenRange<C>) {
        let mut v: BTreeSet<_> = self.0.clone();
        v.insert(r.clone());
        // Guaranteed to have at least one elem
        let mut next: OpenRange<_> = v.first().unwrap().clone();
        let mut acc = next.union(&next);
        for i in v {
            next = acc.0.pop_last().unwrap().clone();
            acc.0.append(&mut next.union(&i).0);
        }
        *self = acc;
    }

    /// The union of two open sets
    pub fn append(&mut self, other: &Self) {
        for r in other.0.iter() {
            self.insert(&r)
        }
    }

    /// The union of two open sets
    pub fn union(&self, other: &Self) -> Self {
        let mut acc = self.clone();
        acc.append(other);
        acc
    }

    /// How many intervals
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Compute the complement set
    pub fn negate(&self) -> Self {
        if self.0.iter().any(|c| c.is_full()) {
            Self::empty()
        } else {
            let mut acc = Self::empty();
            for r in self.0.iter() {
                acc.append(&r.negate());
            }
            acc
        }
    }

    /// The kleene-closure of an Open set
    pub fn kleene(&self) -> Self {
        if self.is_empty() || self.is_nil() {
            Self::nil()
        } else {
            Self::star()
        }
    }
}

impl OpenRange<usize> {
    pub fn times(&self, n: usize) -> Self {
        OpenRange::new(self.start * n, self.end.map(|c| c * n))
    }

    pub fn repeat(&self, i: usize, j: usize) -> Self {
        OpenRange::new(self.start * i, self.end.map(|c| c * j))
    }

    pub fn app(&self, o: &Self) -> Self {
        OpenRange::new(
            self.start + o.start,
            self.end.and_then(|c| o.end.and_then(|x| Some(c + x))),
        )
    }
}

impl OpenSet<usize> {
    pub fn times(&self, n: usize) -> Self {
        if self.is_empty() {
            Self::empty()
        } else {
            let mut r = Self::nil();
            for _ in 0..n {
                r = r.app(self);
            }
            r
        }
    }

    pub fn repeat(&self, i: usize, j: usize) -> Self {
        if self.is_empty() && i == 0 {
            Self::nil()
        } else if self.is_empty() || j < i {
            Self::empty()
        } else if i == j {
            self.times(i)
        } else {
            let mut acc = Self::empty();
            for x in i..=j {
                acc.append(&self.times(x))
            }
            acc
        }
    }

    pub fn app(&self, o: &Self) -> Self {
        let mut acc = Self::empty();
        for x in self.0.iter() {
            for y in o.0.iter() {
                acc.insert(&x.app(&y));
            }
        }
        acc
    }
}

#[test]
fn test_openrange_iter() {
    assert_eq!(
        OpenRange::closed(0, 3).into_iter().collect::<Vec<_>>(),
        vec![0, 1, 2, 3]
    )
}

#[test]
fn test_openset_iter() {
    assert_eq!(
        OpenSet::closed(0, 3)
            .union(&OpenSet::closed(8, 9))
            .into_iter()
            .collect::<Vec<_>>(),
        vec![0, 1, 2, 3, 8, 9]
    )
}

#[test]
fn test_openrange_app() {
    assert_eq!(
        OpenRange::closed(1, 2).app(&OpenRange::closed(4, 6)),
        OpenRange::closed(5, 8)
    )
}

#[test]
fn test_openrange_merge() {
    assert_eq!(
        OpenRange::closed(1, 2).union(&OpenRange::closed(3, 4)),
        OpenSet::closed(1, 4)
    )
}

#[test]
fn test_openset_insert() {
    let mut s = OpenSet::closed(1, 2);
    s.insert(&OpenRange::closed(3, 4));
    assert_eq!(s, OpenSet::closed(1, 4))
}

#[test]
fn test_openset_repeat() {
    assert_eq!(OpenSet::closed(1, 2).repeat(1, 3), OpenSet::closed(1, 6))
}
