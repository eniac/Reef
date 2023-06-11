use std::collections::BTreeSet;

use core::fmt;
use core::fmt::Formatter;


#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Skip {
    Choice(BTreeSet<usize>),
    Inverse(Box<Skip>),
    Star
}

/// The kleene algebra of skips
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
        Skip::Inverse(Box::new(Skip::Star))
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

    /// Is it the nil skip
    pub fn is_epsilon(&self) -> bool {
        match self {
            Skip::Choice(xs) if xs.contains(&0) && xs.len() == 1 => true,
            Skip::Inverse(x) => (*x).is_epsilon(),
            _ => false
        }
    }

    /// Is it the empty set (no transition exists)
    pub fn is_empty(&self) -> bool {
        match self {
            Skip::Choice(xs) if xs.len() == 0 => true,
            Skip::Inverse(x) if **x == Skip::Star => true,
            _ => false
        }
    }

    /// Repeat [self] between [i,j] times
    pub fn range(&self, i: usize, j: usize) -> Self {
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
            Skip::Inverse(s) => Skip::Inverse(Box::new((*s).range(i,j))),
            Skip::Star => Skip::Star
        }
    }

    /// Repeat [self] exactly [n] times
    pub fn times(&self, n: usize) -> Self {
        match self {
            Skip::Choice(xs) =>
                Skip::Choice(xs.into_iter().map(|x|x*n).collect()),
            Skip::Star if n == 0 =>
                Skip::epsilon(),
            Skip::Inverse(x) =>
                Skip::Inverse(Box::new((*x).times(n))),
            Skip::Star => Skip::Star
        }
    }

    /// The kleene-star of a skip
    pub fn star(&self) -> Skip {
        match self {
            _ if self.is_empty() || self.is_epsilon() => Skip::epsilon(),
            _ => Skip::Star
        }
    }

    /// Sequential composition of two jumps is a jump
    pub fn app(&self, a: &Skip) -> Skip {
        match (self, a) {
            (Skip::Inverse(x), _) if &**x == a => Skip::epsilon(),
            (_, Skip::Inverse(x)) if &**x == self => Skip::epsilon(),
            (Skip::Inverse(x), Skip::Inverse(y)) =>
                Skip::Inverse(Box::new(Skip::app(&**x, &**y))),
            (Skip::Inverse(_), _) => unreachable!(),
            (_, Skip::Inverse(_)) => unreachable!(),
            (Skip::Choice(x), Skip::Choice(y)) => {
                let mut s = BTreeSet::new();
                for i in x.into_iter() {
                    for j in y.into_iter() {
                        s.insert(i + j);
                    }
                }
                Skip::Choice(s)
            },
            (Skip::Star, _) | (_, Skip::Star) => Skip::Star
        }
    }
}

impl fmt::Display for Skip {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            _ if self.is_epsilon() => write!(f, "ε"),
            _ if self.is_empty() => write!(f, "∅"),
            Skip::Choice(us) => write!(f, "{:?}", us),
            Skip::Inverse(x) => write!(f, "!{}", **x),
            Skip::Star => write!(f, "*")
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
    assert_eq!(Skip::single().range(1, 2), Skip::choice(&[1, 2]))
}

#[test]
fn test_skip_range2() {
    assert_eq!(Skip::single().range(1,3).range(1, 2), Skip::choice(&[1, 2, 3, 4, 6]))
}

#[test]
fn test_skip_epsilon() {
    assert_eq!(Skip::choice(&[1,3]).app(&Skip::epsilon()), Skip::choice(&[1,3]))
}

