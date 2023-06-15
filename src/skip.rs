use std::collections::BTreeSet;

use core::fmt;
use core::fmt::Formatter;


#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Skip(BTreeSet<(usize,Option<usize>)>);

/// Combinators on skips; monoid (app, epsilon,star,range)
impl Skip {

    /// A single wildcard (.)
    pub fn single() -> Self {
        Skip::choice(&[1])
    }

    /// No step (unit of app)
    pub fn epsilon() -> Self {
        Skip::choice(&[0])
    }

    /// One offset
    pub fn offset(x: usize) -> Self {
        Skip::choice(&[x])
    }

    /// Inverse of * is the empty set
    pub fn empty() -> Self {
        Skip::Choice(BTreeSet::new())
    }

    /// The first offset of this skip
    pub fn first(&self) -> Option<usize> {
        match self {
            Skip::Choice(cs) =>
                cs.first().map(|c|c.clone()),
            Skip::Star(n) => Some(*n)
        }
    }

    /// Choice between elements
    pub fn choice(v: &[usize]) -> Self {
        if v.len() == 0 {
            Skip::empty()
        } else {
            let mut s = BTreeSet::new();
            for x in v.into_iter() {
                s.insert(x.clone());
            }
            Skip::Choice(s)
        }
    }

    /// Kleene-*
    pub fn star() -> Self {
        Skip::Star(0)
    }

    /// Kleene-* plus
    pub fn starplus(x: usize) -> Self {
        Skip::Star(x)
    }

    /// Inclusive range [from,to]
    pub fn range(from: usize, to: usize) -> Self {
        Skip::Choice((from..=to).collect())
    }

    /// Is it the nil skip
    pub fn is_epsilon(&self) -> bool {
        match self {
            Skip::Choice(xs) if xs.contains(&0) && xs.len() == 1 => true,
            _ => false
        }
    }

    /// Is it the kleene {0,*}
    pub fn is_star(&self) -> bool {
        match self {
            Skip::Star(n) => *n == 0,
            _ => false
        }
    }

    /// Has the 0 step (possibly more as well)
    pub fn has_epsilon(&self) -> bool {
        self.first() == Some(0)
    }

    /// Is it the empty set (no transition exists)
    pub fn is_empty(&self) -> bool {
        match self {
            Skip::Choice(xs) if xs.len() == 0 => true,
            _ => false
        }
    }

    /// Repeat [self] between [i,j] times
    pub fn range_of(&self, i: usize, j: usize) -> Self {
        assert!(i <= j, "Range indices must be 0 < {} <= {}", i, j);
        match self {
            _ if self.is_epsilon() => Skip::epsilon(),
            _ if self.is_empty() =>
                if i == 0 { Skip::epsilon() } else { Skip::empty() },
            Skip::Choice(xs) => {
                let mut s: BTreeSet<usize> = BTreeSet::new();
                for x in xs {
                    for y in i..=j {
                        s.insert(x*y);
                    }
                }
                Skip::Choice(s)
            },
            Skip::Star(n) => Skip::Star(i*n)
        }
    }

    /// The kleene-star of a skip
    pub fn star_of(&self, n: usize) -> Skip {
        match self {
            _ if self.is_empty() || self.is_epsilon() => Skip::epsilon(),
            Skip::Choice(cs) => match cs.first() {
                Some(x) => Skip::Star(n*x),
                None => Skip::epsilon()
            },
            Skip::Star(x) => Skip::Star(n*x)
        }
    }

    /// Sequential composition of two jumps is a jump
    pub fn app(&self, a: &Skip) -> Skip {
        match (self, a) {
            (Skip::Choice(x), Skip::Choice(y)) => {
                let mut s = BTreeSet::new();
                for i in x.into_iter() {
                    for j in y.into_iter() {
                        s.insert(i + j);
                    }
                }
                Skip::Choice(s)
            },
            (Skip::Star(x), Skip::Star(y)) =>
                Skip::Star(x+y),
            (Skip::Star(x), Skip::Choice(cs)) | (Skip::Choice(cs), Skip::Star(x)) =>
                match cs.first() {
                    Some(y) => Skip::Star(x+y),
                    None => Skip::empty()
                }
        }
    }
}

impl fmt::Display for Skip {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            _ if self.is_epsilon() => write!(f, "ε"),
            _ if self.is_empty() => write!(f, "∅"),
            Skip::Choice(us) => write!(f, "{:?}", us),
            Skip::Star(n) if *n == 0 => write!(f, "*"),
            Skip::Star(n) => write!(f, "{{{},*}}", n),
        }
    }
}

#[test]
fn test_skip_app() {
    assert_eq!(Skip::choice(&[1,3]).app(&Skip::offset(2)), Skip::choice(&[3,5]))
}

#[test]
fn test_skip_app2() {
    assert_eq!(Skip::choice(&[1,3]).app(&Skip::choice(&[1,2])), Skip::choice(&[2,3,4,5]))
}

#[test]
fn test_skip_range() {
    assert_eq!(Skip::range(1, 2), Skip::choice(&[1, 2]))
}

#[test]
fn test_skip_range2() {
    assert_eq!(Skip::range(1,3).range_of(1, 2), Skip::choice(&[1, 2, 3, 4, 6]))
}

#[test]
fn test_skip_epsilon() {
    assert_eq!(Skip::choice(&[1,3]).app(&Skip::epsilon()), Skip::choice(&[1,3]))
}

