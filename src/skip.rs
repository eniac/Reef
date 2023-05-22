use std::collections::BTreeSet;

use core::fmt;
use core::fmt::Formatter;


#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Skip {
    Offset(usize),
    Choice(BTreeSet<usize>),
    Star
}

/// The kleene algebra of skips
impl Skip {

    /// A single wildcard (.)
    pub fn single() -> Self {
        Skip::Offset(1)
    }

    /// No step (unit of app)
    pub fn epsilon() -> Self {
        Skip::Offset(0)
    }

    pub fn choice(v: &[usize]) -> Self {
        assert!(v.len() > 0, "Nullary skip choice not supported");
        if v.len() == 1 {
            return Skip::Offset(1);
        }
        let mut s = BTreeSet::new();
        for x in v.into_iter() {
            s.insert(x.clone());
        }
        Skip::Choice(s)
    }

    /// [i] != 0 ensured by the smart constructor in Regex::range
    pub fn range(&self, i: usize, j: usize) -> Self {
        assert!(0 < i && i <= j, "Range indices must be 0 < {} <= {}", i, j);
        if i == j {
            self.times(i)
        } else {
            (i..=j).map(|n| self.times(n))
                   .reduce(|a, b| a.alt(&b))
                   .unwrap()
        }
    }

    pub fn times(&self, n: usize) -> Self {
        match self {
            Skip::Offset(x) => Skip::Offset(x*n),
            Skip::Choice(xs) =>
                Skip::Choice(xs.into_iter().map(|x|x*n).collect()),
            Skip::Star if n == 0 =>
                Skip::epsilon(),
            Skip::Star => Skip::Star
        }
    }

    /// The kleene-star of a skip
    pub fn star(&self) -> Skip {
        match self {
            Skip::Offset(0) => Skip::Offset(0),
            _ => Skip::Star
        }
    }

    /// Alternation
    pub fn alt(&self, a: &Skip) -> Skip {
        match (self, a) {
            (Skip::Offset(a), Skip::Offset(b)) => Skip::choice(&[*a,*b]),
            (Skip::Choice(c), Skip::Offset(o)) | (Skip::Offset(o), Skip::Choice(c)) => {
                let mut s = c.clone();
                s.insert(*o);
                Skip::Choice(s)
            },
            (Skip::Choice(a), Skip::Choice(b)) => {
                let mut s = a.clone();
                for x in b { s.insert(*x); };
                Skip::Choice(s)
            }
            (Skip::Star, _) | (_, Skip::Star) => Skip::Star
        }
    }

    /// Sequential composition of two jumps is a jump
    pub fn app(&self, a: &Skip) -> Skip {
        match (self, a) {
            (Skip::Offset(0), _) => a.clone(),
            (Skip::Offset(i), Skip::Offset(j)) => Skip::Offset(i+j),
            (Skip::Offset(i), Skip::Choice(x)) | (Skip::Choice(x), Skip::Offset(i)) =>
                Skip::Choice(x.into_iter().map(|x| x + i).collect()),
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
            Skip::Offset(u) if *u == 0 => write!(f, "ε"),
            Skip::Offset(u) => write!(f, "+{}", u),
            Skip::Choice(us) => write!(f, "{:?}", us),
            Skip::Star => write!(f, "*")
        }
    }
}

#[test]
fn test_skip_app() {
    assert_eq!(Skip::choice(&[1,3]).app(&Skip::Offset(2)), Skip::choice(&[3,5]))
}

#[test]
fn test_skip_app2() {
    assert_eq!(Skip::choice(&[1,3]).app(&Skip::choice(&[1,2])), Skip::choice(&[2,3,4,5]))
}


#[test]
fn test_skip_alt() {
    assert_eq!(Skip::choice(&[1,3]).alt(&Skip::choice(&[1,2])), Skip::choice(&[1,2,3]))
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

