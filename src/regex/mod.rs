#![allow(dead_code)]
#![allow(missing_docs)]
use fancy_regex::{Expr, LookAround};
use hashconsing::{consign, HConsed, HashConsign};
use regex_syntax::hir::{Class, HirKind, Literal};

use std::str::FromStr;

use core::fmt;
use core::fmt::Formatter;
use crate::skip::Skip;

#[cfg(fuzz)]
pub mod arbitrary;

/// Hash-consed regex terms
#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Regex(pub HConsed<RegexF>);

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum RegexF {
    Nil,
    Empty,
    Dot,
    Char(char),
    Not(Regex),
    App(Regex, Regex),
    Alt(Regex, Regex),
    Lookahead(Regex),
    Range(Regex, usize, usize),
    Star(Regex),
}

consign! {
    /// Factory for terms.
    let G = consign(10) for RegexF ;
}

impl fmt::Display for Regex {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match &*self.0 {
            RegexF::Nil => write!(f, "ε"),
            RegexF::Empty => write!(f, "∅"),
            RegexF::Dot => write!(f, "."),
            RegexF::Char(c) => write!(f, "{}", c),
            RegexF::Not(c) => write!(f, "! {}", c),
            RegexF::App(x, y) => write!(f, "{}{}", x, y),
            RegexF::Alt(x, y) => write!(f, "({} | {})", x, y),
            RegexF::Star(a) => write!(f, "{}*", a),
            RegexF::Lookahead(a) => write!(f, "(?={})", a),
            RegexF::Range(a, 0, 1) => write!(f, "{}?", a),
            RegexF::Range(a, i, j) if i == j => write!(f, "{}{{{}}}", a, i),
            RegexF::Range(a, i, j) => write!(f, "{}{{{}, {}}}", a, i, j),
        }
    }
}

impl FromStr for Regex {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        fn to_regex_top(e: &Expr) -> Result<Regex, String> {
            match e {
                Expr::Concat(l) => {
                    let mut inner = to_regex(e.clone())?;
                    if let Some(e) = l.get(0) {
                        match e {
                            Expr::StartLine | Expr::StartText => (),
                            _ => inner = Regex::app(Regex::dotstar(), inner),
                        }
                    }

                    if let Some(e) = l.get(l.len() - 1) {
                        match e {
                            Expr::EndLine | Expr::EndText => (),
                            _ => inner = Regex::app(inner, Regex::dotstar()),
                        }
                    }
                    Ok(inner)
                },
                Expr::Group(g) => to_regex_top(&g),
                _ => Ok(Regex::app(
                    Regex::app(Regex::dotstar(), to_regex(e)?),
                    Regex::dotstar(),
                )),
            }
        }

        fn to_regex(e: &Expr) -> Result<Regex, String> {
            match e {
                Expr::Empty => Ok(Regex::empty()),
                Expr::Any { .. } => Ok(Regex::dot()),
                Expr::StartText | Expr::StartLine | Expr::EndText | Expr::EndLine => Ok(Regex::nil()),
                Expr::Literal { val, .. } => val.chars().try_fold(Regex::nil(), |acc, a| {
                    Ok(Regex::app(acc, Regex::character(a)))
                }),
                Expr::Concat(l) => l
                    .iter()
                    .try_fold(Regex::nil(), |acc, a| Ok(Regex::app(acc, to_regex(a)?))),
                Expr::Alt(l) => l
                    .iter()
                    .try_fold(Regex::empty(), |acc, a| Ok(Regex::alt(acc, to_regex(&a)?))),
                Expr::Repeat { child, lo, hi, .. } if *lo == 0 && *hi == usize::MAX => {
                    Ok(Regex::star(to_regex(&*child)?))
                }
                Expr::Repeat { child, lo, hi, .. } if *hi == usize::MAX => {
                    let inner = to_regex(child)?;
                    Ok(Regex::app(inner.repeat(*lo), Regex::star(inner)))
                },
                Expr::Repeat { child, lo, hi, .. } => {
                    println!("Inner range: {:?}", child);
                    Ok(Regex::range(&to_regex(child)?, *lo, *hi))
                },
                Expr::StartLine | Expr::StartText => Ok(Regex(G.mk(RegexF::LineStart))),
                Expr::EndLine | Expr::EndText => Ok(Regex(G.mk(RegexF::LineEnd))),
                Expr::Group(g) => to_regex(&g),
                Expr::LookAround(g, LookAround::LookAhead) => {
                    Ok(Regex::lookahead(to_regex_top(g)?))
                }
                Expr::LookAround(g, LookAround::LookBehind) => {
                    Ok(Regex::lookbehind(to_regex_top(g)?))
                }
                Expr::LookAround(g, LookAround::LookAheadNeg) => {
                    Ok(Regex::lookahead(Regex::not(to_regex_top(g)?)))
                }
                Expr::LookAround(g, LookAround::LookBehindNeg) => {
                    Ok(Regex::lookbehind(Regex::not(to_regex_top(g)?)))
                }
                Expr::Delegate { inner, .. } => {
                    let re = regex_syntax::Parser::new().parse(inner).unwrap();
                    match re.kind() {
                        HirKind::Class(Class::Unicode(ranges)) => {
                            let size = ranges
                                .iter()
                                .fold(0, |a, r| a + (r.end() as u32 - r.start() as u32));
                            if size > 120 {
                                Ok(Regex::dot())
                            } else if size == 0 {
                                Ok(Regex::empty())
                            } else {
                                Ok(ranges
                                    .iter()
                                    .flat_map(|a| (a.start()..=a.end()))
                                    .map(|a| Regex::character(a))
                                    .reduce(Regex::alt)
                                    .unwrap_or(Regex::empty()))
                            }
                        }
                        HirKind::Literal(Literal::Unicode(c)) => Ok(Regex::character(*c)),
                        _ => Err(format!("Unsupported regex (regex_syntax) {:#?}", re.kind())),
                    }
                }
                _ => Err(format!("Unsupported regex (fancy_regex) {:#?}", e)),
            }
        }

        to_regex_top(&Expr::parse_tree(s).unwrap().expr)
    }
}

impl Regex {
    pub fn new<'a>(rstr: &'a str) -> Self {
        Regex::from_str(rstr).unwrap()
    }

    // Smart constructors for regex simplification
    pub fn nil() -> Regex {
        Regex(G.mk(RegexF::Nil))
    }

    pub fn empty() -> Regex {
        Regex(G.mk(RegexF::Empty))
    }

    pub fn character(c: char) -> Regex {
        Regex(G.mk(RegexF::Char(c)))
    }

    pub fn dot() -> Regex {
        Regex(G.mk(RegexF::Dot))
    }

    /// Flatten a tree of alt into a list of alts
    pub fn to_alt_set(&self) -> BTreeSet<Regex> {
        let res = match *self.0 {
            RegexF::Alt(ref a, ref b) => {
                let mut la = a.to_alt_set();
                let mut lb = b.to_alt_set();
                la.append(&mut lb);
                la
            },
            _ => vec![self.clone()]
        }
    }

    /// Subset relation is a partial order
    pub fn partial_le(a: &Regex, b: &Regex) -> Option<bool> {
        match (&*a.0, &*b.0) {
            (x, y) if x == y => Some(true),
            (RegexF::Char(_), RegexF::Dot) => Some(true),
            (RegexF::Dot, RegexF::Char(_)) => Some(false),
            (RegexF::Nil, RegexF::Star(_)) => Some(true),
            (RegexF::Star(_), RegexF::Nil) => Some(false),
            (RegexF::Range(x, _, _), RegexF::Star(y)) if Some(true) == Regex::partial_le(x, y) => {
                Some(true)
            }
            (RegexF::Star(x), RegexF::Range(y, _, _)) if Some(false) == Regex::partial_le(x, y) => {
                Some(true)
            }
            (RegexF::Range(x, i1, j1), RegexF::Range(y, i2, j2))
                if x == y && i1 <= i2 && j2 <= j1 =>
            {
                Some(true)
            }
            (RegexF::Range(x, i1, j1), RegexF::Range(y, i2, j2))
                if x == y && i2 <= i1 && j1 <= j2 =>
            {
                Some(false)
            }
            (RegexF::Empty, _) => Some(true),
            (_, RegexF::Empty) => Some(false),
            // (a|b) >= c if (a >= c)
            (RegexF::Alt(x1, _), x2)
                if Some(false) == Regex::partial_le(x1, &Regex(G.mk(x2.clone()))) =>
            {
                Some(false)
            }
            // (a|b) >= c if (b >= c)
            (RegexF::Alt(_, x1), x2)
                if Some(false) == Regex::partial_le(x1, &Regex(G.mk(x2.clone()))) =>
            {
                Some(false)
            }
            // c <= (a|b) if (c <= a)
            (x1, RegexF::Alt(x2, _))
                if Some(true) == Regex::partial_le(&Regex(G.mk(x1.clone())), x2) =>
            {
                Some(true)
            }
            // c <= (a|b) if (c <= b)
            (x1, RegexF::Alt(_, x2))
                if Some(true) == Regex::partial_le(&Regex(G.mk(x1.clone())), x2) =>
            {
                Some(true)
            }
            (_, RegexF::Star(i)) if *i.0 == RegexF::Dot => Some(true),
            (RegexF::Star(i), _) if *i.0 == RegexF::Dot => Some(false),
            (RegexF::Star(a), RegexF::Star(b)) => Regex::partial_le(a, b),
            (RegexF::App(ref a, ref x), RegexF::App(ref b, ref y)) => {
                let h = Regex::partial_le(a, b)?;
                let t = Regex::partial_le(x, y)?;
                Some(h && t)
            }
            (_, _) => None,
        }
    }

    pub fn app(a: Regex, b: Regex) -> Regex {
        match (&*a.0, &*b.0) {
            // Right-associative [app]
            (RegexF::App(x, y), _) => Regex::app(x.clone(), Regex::app(y.clone(), b)),
            // Monoid on Nil
            (_, RegexF::Nil) => a,
            (RegexF::Nil, _) => b,
            // Empty absorbs everything
            (_, RegexF::Empty) | (RegexF::Empty, _) => Regex::empty(),
            // Range & star index math
            (RegexF::Range(a, i, j), _) if a == &b => a.range(i+1, j+1),
            (_, RegexF::Range(b, i, j)) if &a == b => b.range(i+1, j+1),
            (RegexF::Range(a, i1, j1), RegexF::Range(b, i2, j2)) if a == b => a.range(i1+i2, j1+j2),
            (RegexF::Star(x), RegexF::Range(y, _, _)) if x == y => a,
            (RegexF::Range(y, _, _), RegexF::Star(x)) if x == y => b,
            (RegexF::Star(x), RegexF::Star(y)) if x == y => a,
            (_, _) => Regex(G.mk(RegexF::App(a, b))),
        }
    }

    pub fn alt(a: Regex, b: Regex) -> Regex {
        match (&*a.0, &*b.0) {
            // Idempotent [alt]
            (x, y) if x == y => a,
            // Left-associative [alt]
            (_, RegexF::Alt(x, y)) => Regex::alt(Regex::alt(a, x.clone()), y.clone()),
            // a | b and a <= b -> b
            (_, _) if Some(true) == Regex::partial_le(&a, &b) => b,
            // a | b and a >= b -> a
            (_, _) if Some(false) == Regex::partial_le(&a, &b) => a,
            // The smallest syntactically thing on the left
            (x, y) if x > y => Regex::alt(b, a),
            (_, _) => Regex(G.mk(RegexF::Alt(a, b))),
        }
    }

    pub fn star(a: Regex) -> Regex {
        match &*a.0 {
            RegexF::Star(_) | RegexF::Nil => a,
            RegexF::Empty => Regex::nil(),
            _ => Regex(G.mk(RegexF::Star(a))),
        }
    }

    pub fn dotstar() -> Regex {
        Regex::star(Regex::dot())
    }

    pub fn range(&self, i: usize, j: usize) -> Regex {
        assert!(i <= j, "Range indices must be 0 <= {} <= {}", i, j);
        match *self.0 {
            RegexF::Star(_) | RegexF::Nil => self.clone(),
            RegexF::Empty => Regex::empty(),
            _ if i == 0 && j == 0 => Regex::nil(),
            _ if i == 0 => Regex::alt(Regex::nil(), Regex::range(self, 1, j)),
            _ => Regex(G.mk(RegexF::Range(self.clone(), i, j))),
        }
    }

    pub fn not(a: Regex) -> Regex {
        match &*a.0 {
            RegexF::Not(a) => a.clone(),
            RegexF::Empty => Regex::star(Regex::dot()), // Is that true?
            _ => Regex(G.mk(RegexF::Not(a))),
        }
    }

    pub fn is_nil(&self) -> bool {
        match *self.0 {
            RegexF::Nil => true,
            _ => false,
        }
    }

    pub fn lookahead(a: Regex) -> Regex {
        Regex(G.mk(RegexF::Lookahead(a)))
    }

    pub fn lookbehind(a: Regex) -> Regex {
        a
    }

    /// Nullable regex accept the empty document
    pub fn nullable(&self) -> bool {
        match *self.0 {
            RegexF::Nil | RegexF::Star(_) => true,
            RegexF::Range(_, i, _) if i == 0 => true,
            RegexF::Empty | RegexF::Char(_) | RegexF::Dot | RegexF::Range(_, _, _) | RegexF::Lookahead(_) => false,
            RegexF::Not(ref r) => !r.nullable(),
            RegexF::App(ref a, ref b) => a.nullable() && b.nullable(),
            RegexF::Alt(ref a, ref b) => a.nullable() || b.nullable(),
        }
    }

    /// Does it accept any string
    pub fn accepts_any(&self, ab: &Vec<char>) -> bool {
        ab.iter().all(|c| self.deriv(&c).nullable())
    }

    /// The length of the longest wildcard skip
    pub fn to_skip(&self, ab: &Vec<char>) -> Option<(Skip, Self)> {
        match *self.0 {
            RegexF::Dot => Some((Skip::single(), Regex::nil())),
            // .*
            RegexF::Star(ref a) => {
                let (sa, rem) = a.to_skip(ab)?;
                if rem.is_nil() {
                    Some((sa.star(), Regex::nil()))
                } else {
                    None
                }
            }
            // .{i,j}
            RegexF::Range(ref a, x, y) => {
                let (sa, rem) = a.to_skip(ab)?;
                if rem.is_nil() {
                    Some((sa.range(x, y), Regex::nil()))
                } else {
                    None
                }
            }
            // (r | r')
            RegexF::Alt(ref a, ref b) => {
                let (pa, rema) = a.to_skip(ab)?;
                let (pb, remb) = b.to_skip(ab)?;
                if rema.is_nil() && remb.is_nil() {
                    Some((pa.alt(&pb), Regex::nil()))
                } else {
                    None
                }
            }
            // r1r2
            RegexF::App(ref a, ref b) => {
                let (pa, rema) = a.to_skip(ab)?;
                match b.to_skip(ab) {
                    Some((pb, remb)) => Some((pa.app(&pb), Regex::app(rema, remb))),
                    None => Some((pa, Regex::app(rema, b.clone()))),
                }
            }
            _ => None,
        }
    }

    /// Make [r], [n] into [rrrr....r] n times.
    pub fn repeat(&self, n: usize) -> Regex {
        match std::iter::repeat(self.clone()).take(n).reduce(Regex::app) {
            Some(r) => r,
            None => Regex::nil(),
        }
    }

    /// Derivative
    pub fn deriv(&self, c: &char) -> Regex {
        match *self.0 {
            RegexF::Nil => Regex::empty(),
            RegexF::Empty => Regex::empty(),
            RegexF::Dot => Regex::nil(),
            RegexF::Char(x) if &x == c => Regex::nil(),
            RegexF::Char(_) => Regex::empty(),
            RegexF::Not(ref r) => Regex::not(r.deriv(c)),
            RegexF::App(ref a, ref b) if a.nullable() => {
                Regex::alt(Regex::app(a.deriv(c), b.clone()), b.deriv(c))
            }
            RegexF::App(ref a, ref b) => Regex::app(a.deriv(c), b.clone()),
            RegexF::Alt(ref a, ref b) => Regex::alt(a.deriv(c), b.deriv(c)),
            RegexF::Star(ref a) => Regex::app(a.deriv(c), Regex::star(a.clone())),
            RegexF::Range(ref a, i, j) if i == j => a.repeat(i).deriv(c),
            RegexF::Range(ref a, i, j) if i == 0 => Regex::alt(Regex::nil(), a.clone().range(1, j)).deriv(c),
            RegexF::Range(ref a, i, j) =>
                match (i..=j).map(|i| a.repeat(i)).reduce(Regex::alt) {
                    Some(r) => r.deriv(c),
                    None => Regex::nil()
                },
            _ => panic!("No derivatives for regex {}", self)
        }
    }
}

#[test]
fn test_regex_ord() {
    assert!(Regex::character('a') < Regex::character('b'))
}

#[test]
fn test_regex_zero_length() {
    assert_eq!(
        Regex::app(
            Regex::app(Regex::character('F'), Regex::character('o')),
            Regex::character('o')
        ),
        Regex::new("^Foo$")
    );
}

#[test]
fn test_regex_ranges() {
    assert_eq!(
        Regex::app(
            Regex::app(
                Regex::dotstar(),
                Regex::alt(Regex::character('a'), Regex::character('b'))
            ),
            Regex::dotstar()
        ),
        Regex::new("[a-b]")
    );
}

#[test]
fn test_regex_dot() {
    assert_eq!(
        Regex::app(
            Regex::app(Regex::dotstar(), Regex::character('c')),
            Regex::dotstar()
        ),
        Regex::new("^.*c")
    );
}

#[test]
fn regex_parser_test_repetition_range() {
    assert_eq!(Regex::character('a').range(1, 3), Regex::new("a{1,3}"));
}
