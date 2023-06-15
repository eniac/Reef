#![allow(dead_code)]
#![allow(missing_docs)]
use core::{fmt, fmt::Display};
use core::fmt::Formatter;

use std::collections::BTreeSet;
use std::iter::Step;
use std::default::Default;

/// An Open set of ranges is an efficient representation for ranges of characters, integers etc
/// that might or might not be closed. For example,
/// { (0,3), (4,6), (8, *) }
///
/// It implements the operations [union, negation, concatenation, unit, annhiliation]
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct OpenRange<C> {
    pub start: C,
    pub end: Option<C>
}

impl<C: Step + Default + Ord + Copy> OpenRange<C> {
    pub fn new(start: C, end: Option<C>) -> Self {
        Self { start, end }
    }
    pub fn open(start: C) -> Self {
        Self { start, end: None }
    }
    pub fn closed(start: C, end: C) -> Self {
        Self { start, end: Some(end) }
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

    pub fn negate(&self) -> OpenSet<C> {
        match self.clone() {
            // ! (0,b) = [(b+1, *)]
            Self { start, end: Some(e) } if start == Default::default() =>
                OpenSet::open(Step::forward(e.clone(), 1)),
            // ! (a,b) = [(0, a-1), (b+1, *)]
            Self { start, end: Some(e) } =>
                OpenSet::new(&[
                    (Default::default(), Some(Step::backward(start, 1))),
                    (Step::forward(e.clone(), 1), None)]),
            // ! (0,*) = []
            Self { start, end: None } if start == Default::default() => OpenSet::empty(),
            // ! (a,*) = [(0, a-1)]
            Self { start, end: None } =>
                OpenSet::closed(Default::default(), Step::backward(start.clone(), 1))
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
            (o, _, _) => o
        }
    }
}

impl <C: Ord> Ord for OpenRange<C> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self.start.cmp(&other.start), &self.end, &other.end) {
            (std::cmp::Ordering::Equal, None, _) => std::cmp::Ordering::Greater,
            (std::cmp::Ordering::Equal, Some(_), None) => std::cmp::Ordering::Less,
            (std::cmp::Ordering::Equal, Some(a), Some(b)) => a.cmp(b),
            (o, _, _) => o
        }
    }
}

impl<C: Display + Eq + Default> fmt::Display for OpenRange<C> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.end {
            Some(ref e) if &self.start == e && *e == Default::default() =>
              write!(f, "ε"),
            Some(ref e) if &self.start == e => write!(f, "{}", e),
            Some(ref e) => write!(f, "{}-{}", self.start, e),
            None => write!(f, "{}-*", self.start)
        }
    }
}

#[derive(Debug, Clone, Hash, PartialOrd, Ord, PartialEq, Eq)]
pub struct OpenSet<C>(BTreeSet<OpenRange<C>>);

impl<C: Step + Ord + Eq + Display + Default + Copy> fmt::Display for OpenSet<C> {
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
            write!(f, "[ {}", v)?;
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
            Some(e) if e == res => None,
            Some(_) | None => {
                self.start = Step::forward(self.start, 1);
                Some(res)
            }
        }
    }
}

impl<T: Step + Ord + Copy> Iterator for OpenSet<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let mut h = self.0.pop_first()?;
        let res = h.next()?;
        self.0.insert(h);
        Some(res)
    }
}

impl<C: Step + Default + Ord + Copy> OpenSet<C> {
    /// Nominal constructor
    pub fn new(v: &[(C, Option<C>)]) -> Self {
        Self::from_iter(v.iter().map(|c| c.clone()))
    }

    pub fn from_iter(v: impl Iterator<Item=(C, Option<C>)>) -> Self {
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
        } else { false }
    }

    /// Is it a single character, if yes return it
    pub fn is_single(&self) -> Option<C> {
        if self.0.len() == 1 {
            let h = self.0.iter().next()?;
            let end = h.end?;
            if h.start == end {
                Some(end)
            } else { None }
        } else { None }
    }

    /// Does it contain [c]
    pub fn contains(&self, c: &C) -> bool {
        self.0.iter().any(|r| r.start <= *c && r.end.map_or(true, |b| c <= &b))
    }

    /// Minimum (first) bound
    pub fn start(&self) -> Option<C> {
        self.0.first().map(|r| r.start)
    }

    /// Hacky and slow...
    pub fn insert(&mut self, r: &OpenRange<C>) {
        *self = self.union(&Self::new(&[(r.start, r.end)]))
    }

    /// The union of two open sets
    pub fn union(&self, other: &Self) -> Self {
        let mut intervals = self.0.clone();
        intervals.append(&mut other.0.clone());

        if intervals.is_empty() {
            return Self::empty();
        }

        let mut res: Vec<OpenRange<C>> = vec![];
        let mut last: OpenRange<C> = intervals.first().unwrap().clone();

        for item in intervals.into_iter() {
            if let Some(last_end) = last.end {
                if item.start > Step::forward(last_end, 1) {
                    res.push(last.clone());
                    last = item;
                } else {
                    last.end = Some(item.start.max(last_end));
                }
            } else { // (i, *) covers all intervals > (i, *)
                break;
            }
        }

        res.push(last.clone());
        Self(res.into_iter().collect())
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
                acc = acc.union(&r.negate());
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
        match self.end {
            Some(v) => Self::closed(self.start * n, v* n),
            None => Self::open(self.start * n)
        }
    }
    pub fn repeat(&self, i: usize, j: usize) -> OpenSet<usize> {
        let mut acc = OpenSet::empty();
        for x in i..=j {
            acc.insert(&self.times(x));
        }
        acc
    }
    pub fn app(&self, o: &Self) -> Self {
        match (self.end, o.end) {
            (_, None) | (None, _) =>
                Self::open(self.start + o.start),
            (Some(se), Some(oe)) =>
                Self::closed(self.start + o.start, se + oe)
        }
    }
}

impl OpenSet<usize> {
    pub fn repeat(&self, i: usize, j: usize) -> Self {
        if self.is_empty() && i == 0 {
            Self::nil()
        } else if self.is_empty() {
            Self::empty()
        } else {
            let mut acc = Self::empty();
            for r in self.0.iter() {
                acc = acc.union(&r.repeat(i, j))
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
