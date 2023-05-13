#![allow(dead_code)]
#![allow(missing_docs)]
use hashconsing::{consign, HConsed, HashConsign};
use fancy_regex::{Expr, LookAround};
use regex_syntax::hir::{HirKind, Class, Literal};
use regex_syntax::ast::parse::ParserBuilder;
use regex_syntax::hir::translate::Translator;

use std::str::FromStr;
use std::collections::HashSet;

use core::fmt;
use core::fmt::Formatter;

/// Hash-consed regex terms
#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Regex(HConsed<RegexF>);

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum RegexF {
    Nil,
    Empty,
    Dot,
    LineStart,
    LineEnd,
    Char(String),
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

pub enum Jump {
    Constant(usize),
    Choice(HashSet<usize>),
    Star
}

use Jump::*;
impl Jump {
    fn or(&self, a: &Jump) -> Jump {
        match (self, a) {
            (Constant(i), Constant(j)) => Choice(HashSet::from([*i, *j])),
            (Constant(i), Choice(x)) | (Choice(x), Constant(i)) => {
                let mut s = x.clone();
                s.insert(*i);
                Choice(s)
            },
            (Choice(x), Choice(y)) => { Choice(x.union(y).map(|c|*c).collect()) },
            (Star, _) | (_, Star) => Star
        }
    }
}

impl fmt::Display for Regex {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match &*self.0 {
            RegexF::Nil => write!(f, "ε"),
            RegexF::Empty => write!(f, "∅"),
            RegexF::Dot => write!(f, "."),
            RegexF::LineStart => write!(f, "^"),
            RegexF::LineEnd => write!(f, "$"),
            RegexF::Char(c) => write!(f, "{}", c),
            RegexF::Not(c) => write!(f, "! {}", c),
            RegexF::App(x, y) => write!(f, "{}{}", x, y),
            RegexF::Alt(x, y) => write!(f, "({} | {})", x, y),
            RegexF::Star(a) => write!(f, "{}*", a),
            RegexF::Lookahead(a) => write!(f, "(?={})", a),
            RegexF::Range(a, i, j) if i == j => write!(f, "{}{{{}}}", a, i),
            RegexF::Range(a, i, j) => write!(f, "{}{{{}, {}}}", a, i, j)
        }
    }
}

impl FromStr for Regex {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        fn to_regex(e: &Expr) -> Result<Regex, String> {
            match e {
                Expr::Empty => Ok(Regex::empty()),
                Expr::Any { .. } => Ok(Regex::dot()),
                Expr::Literal { val, .. } => Ok(Regex::character(val)),
                Expr::Concat(l) =>
                   l.iter()
                    .try_fold(Regex::nil(),
                        |acc, a| Ok(Regex::app(acc, to_regex(&a)?))),
                Expr::Alt(l) =>
                   l.iter()
                    .try_fold(Regex::empty(),
                        |acc, a| Ok(Regex::alt(acc, to_regex(&a)?))),
                Expr::Repeat { child, lo, hi, .. } if *lo == 0 && *hi == usize::MAX =>
                    Ok(Regex::star(to_regex(&*child)?)),
                Expr::Repeat { child, lo, hi, .. } if *hi == usize::MAX => {
                    let inner = to_regex(child)?;
                    Ok(Regex::app(inner.repeat(*lo), Regex::star(inner)))
                },
                Expr::Repeat { child, lo, hi, .. } =>
                    Ok(Regex::range(to_regex(child)?, *lo, *hi)),
                Expr::StartLine | Expr::StartText => Ok(Regex(G.mk(RegexF::LineStart))),
                Expr::EndLine | Expr::EndText => Ok(Regex(G.mk(RegexF::LineEnd))),
                Expr::Group(g) => to_regex(&g),
                Expr::LookAround(g, LookAround::LookAhead) => Ok(Regex::lookahead(to_regex(g)?)),
                Expr::LookAround(g, LookAround::LookBehind) => Ok(Regex::lookbehind(to_regex(g)?)),
                Expr::LookAround(g, LookAround::LookAheadNeg) => Ok(Regex::lookahead(Regex::not(to_regex(g)?))),
                Expr::LookAround(g, LookAround::LookBehindNeg) => Ok(Regex::lookbehind(Regex::not(to_regex(g)?))),
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
                                  .flat_map(|a| (a.start()..= a.end()))
                                  .map(|a| Regex::character(&a.to_string()))
                                  .reduce(Regex::alt)
                                  .unwrap_or(Regex::empty()))
                          }
                        },
                        HirKind::Literal(Literal::Unicode(c)) => Ok(Regex::character(&c.to_string())),
                        _ => Err(format!("Unsupported regex (regex_syntax) {:#?}", re.kind())),
                    }
                },
                _ => Err(format!("Unsupported regex (fancy_regex) {:#?}", e))
            }
        }

        let expr = Expr::parse_tree(s).unwrap().expr;
        to_regex(&expr)
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

    pub fn character(c: &str) -> Regex {
        Regex(G.mk(RegexF::Char(c.to_string())))
    }

    pub fn dot() -> Regex {
        Regex(G.mk(RegexF::Dot))
    }

    pub fn line_start() -> Regex {
        Regex(G.mk(RegexF::LineStart))
    }

    pub fn line_end() -> Regex {
        Regex(G.mk(RegexF::LineEnd))
    }

    pub fn app(a: Regex, b: Regex) -> Regex {
        match (&*a.0, &*b.0) {
            (RegexF::App(x, y), _) => Regex::app(x.clone(), Regex::app(y.clone(), b)),
            (_, RegexF::Nil) => a,
            (RegexF::Nil, _) => b,
            (RegexF::Star(x), RegexF::Star(y)) if x == y => a,
            (_, RegexF::Empty) | (RegexF::Empty, _) => Regex::empty(),
            (RegexF::LineStart, RegexF::LineStart) |
                (RegexF::LineEnd, RegexF::LineEnd) => a,
            (RegexF::LineStart, RegexF::LineEnd) => Regex::empty(),
            (_, _) => Regex(G.mk(RegexF::App(a, b))),
        }
    }

    pub fn alt(a: Regex, b: Regex) -> Regex {
        match (&*a.0, &*b.0) {
            (x, y) if x == y => a,
            (_, RegexF::Alt(x, y)) => Regex::alt(Regex::alt(a.clone(), x.clone()), y.clone()),
            (RegexF::Alt(x1, _), x2) if *x1.0 == *x2 => a,
            (RegexF::Alt(_, x1), x2) if *x1.0 == *x2 => a,
            (RegexF::Not(inner), _) if *inner.0 == RegexF::Empty => {
                Regex(G.mk(RegexF::Not(Regex::empty())))
            }
            (RegexF::Empty, _) => b,
            (RegexF::Dot, RegexF::Char(_)) => a,
            (RegexF::Char(_), RegexF::Dot) => b,
            (_, RegexF::Empty) => a,
            (x, y) if y < x => Regex::alt(b, a),
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

    pub fn range(a: Regex, i: usize, j: usize) -> Regex {
        assert!(0 < i && i <= j, "Range indices {{{}, {}}} must be 0 < {} <= {}", i, j, i, j);
        match &*a.0 {
            RegexF::Star(_) | RegexF::Nil => a,
            RegexF::Empty => Regex::empty(),
            _ => Regex(G.mk(RegexF::Range(a, i, j)))
        }
    }

    pub fn not(a: Regex) -> Regex {
        match &*a.0 {
            RegexF::Not(a) => a.clone(),
            _ => Regex(G.mk(RegexF::Not(a))),
        }
    }

    pub fn lookahead(a: Regex) -> Regex {
        Regex(G.mk(RegexF::Lookahead(a)))
    }

    pub fn lookbehind(a: Regex) -> Regex {
        a
    }

    pub fn nullable(&self) -> bool {
        match *self.0 {
            RegexF::Nil | RegexF::LineEnd | RegexF::LineStart | RegexF::Star(_) => true,
            RegexF::Empty | RegexF::Char(_) | RegexF::Dot | RegexF::Range(_, _, _) | RegexF::Lookahead(_) => false,
            RegexF::Not(ref r) => !r.nullable(),
            RegexF::App(ref a, ref b) => a.nullable() && b.nullable(),
            RegexF::Alt(ref a, ref b) => a.nullable() || b.nullable(),
        }
    }

    pub fn is_start_anchored(&self) -> bool {
        match *self.0 {
            RegexF::LineStart => true,
            RegexF::App(ref a, _) => a.is_start_anchored(),
            _ => false
        }
    }

    pub fn is_end_anchored(&self) -> bool {
        match *self.0 {
            RegexF::LineEnd => true,
            RegexF::App(_, ref a) => a.is_end_anchored(),
            _ => false
        }
    }

    pub fn accepts_any(&self, ab: &String) -> bool {
        ab.chars().all(|c| self.deriv(&c).nullable())
    }

    pub fn is_jump(&self, ab: &String) -> Option<Jump> {
        match *self.0 {
            RegexF::Star(ref a) if a.accepts_any(ab) => Some(Star),
            RegexF::Alt(ref a, ref b) =>
                match (a.is_jump(ab), b.is_jump(ab)) {
                    (Some(a), Some(b)) => Some(a.or(&b)),
                    (None, a) | (a, None) => a,
                },
            RegexF::App(ref a, _) => a.is_jump(ab),
            RegexF::Range(ref a, i, j) if i == j && a.accepts_any(ab) => Some(Constant(i)),
            RegexF::Range(ref a, i, j) if a.accepts_any(ab) => Some(Choice((i..=j).collect())),
            _ => None,
        }
    }

    pub fn repeat(&self, n: usize) -> Regex {
        match std::iter::repeat(self.clone()).take(n).reduce(Regex::app) {
            Some(r) => r,
            None => Regex::nil()
        }
    }

    pub fn deriv(&self, c: &char) -> Regex {
        match *self.0 {
            RegexF::Nil => Regex::empty(),
            RegexF::Empty => Regex::empty(),
            RegexF::Dot => Regex::nil(),
            RegexF::Char(ref x) if x == &c.to_string() => Regex::nil(),
            RegexF::Char(_) => Regex::empty(),
            RegexF::Not(ref r) => Regex::not(r.deriv(c)),
            RegexF::App(ref a, ref b) if *a.0 == RegexF::LineStart => b.deriv(c),
            RegexF::App(ref a, ref b) if *b.0 == RegexF::LineEnd => a.deriv(c),
            RegexF::App(ref a, ref b) if a.nullable() =>
                Regex::alt(Regex::app(a.deriv(c), b.clone()), b.deriv(c)),
            RegexF::App(ref a, ref b) => Regex::app(a.deriv(c), b.clone()),
            RegexF::Alt(ref a, ref b) => Regex::alt(a.deriv(c), b.deriv(c)),
            RegexF::Star(ref a) => Regex::app(a.deriv(c), Regex::star(a.clone())),
            RegexF::Range(ref a, i, j) if i == j =>
                a.repeat(i).deriv(c),
            RegexF::Range(ref a, i, j) =>
                match (i..=j).map(|i| a.repeat(i)).reduce(Regex::alt) {
                    Some(r) => r.deriv(c),
                    None => Regex::nil()
                },
            RegexF::LineStart | RegexF::LineEnd | RegexF::Lookahead(_) =>
                panic!("No derivatives for zero-length assertions (^, $, (?=r))")
        }
    }
}

#[test]
fn regex_parser_test_zero_length() {
    assert_eq!(Regex::app(Regex::app(Regex::app(Regex::app(Regex::line_start(), Regex::character("F")), Regex::character("o")), Regex::character("o")), Regex::line_end()), Regex::new("^Foo$"));
}

#[test]
fn regex_parser_test_char_ranges() {
    assert_eq!(Regex::app(Regex::app(Regex::line_start(), Regex::alt(Regex::character("a"), Regex::character("b"))), Regex::line_end()), Regex::new("^[a-b]$"));
}

#[test]
fn regex_parser_test_dot() {
    assert_eq!(Regex::app(Regex::app(Regex::line_start(), Regex::star(Regex::dot())), Regex::character("c")), Regex::new("^.*c"));
}

#[test]
fn regex_parser_test_repetition_range() {
    assert_eq!(Regex::range(Regex::character("a"), 1, 3), Regex::new("a{1,3}"));
}
