#![allow(dead_code)]
#![allow(missing_docs)]
use hashconsing::{consign, HConsed, HashConsign};
use fancy_regex::{Expr, LookAround};
use regex_syntax::hir::{HirKind, Class, Literal};

use std::str::FromStr;
use std::collections::BTreeSet;

use core::fmt;
use core::fmt::Formatter;

pub mod arbitrary;

/// Hash-consed regex terms
#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Regex(pub HConsed<RegexF>);

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum RegexF {
    Nil,
    Empty,
    Dot,
    LineStart,
    LineEnd,
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

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum JumpType {
    Offset(usize),
    Choice(BTreeSet<usize>),
    Star
}

impl JumpType {
    pub fn range(i: usize, j: usize) -> Self {
        if i == j {
            JumpType::Offset(i)
        } else {
            JumpType::Choice((i..=j).collect())
        }
    }

    /// Union of two jumps is a jump
    fn or(&self, a: &JumpType) -> JumpType {
        match (self, a) {
            (JumpType::Offset(i), JumpType::Offset(j)) => JumpType::Choice(BTreeSet::from([*i, *j])),
            (JumpType::Offset(i), JumpType::Choice(x)) | (JumpType::Choice(x), JumpType::Offset(i)) => {
                let mut s = x.clone();
                s.insert(*i);
                JumpType::Choice(s)
            },
            (JumpType::Choice(x), JumpType::Choice(y)) => JumpType::Choice(x.union(y).map(|c|*c).collect()),
            (JumpType::Star, _) | (_, JumpType::Star) => JumpType::Star
        }
    }

    /// Sequential composition of two jumps is a jump
    fn then(&self, a: &JumpType) -> JumpType {
        match (self, a) {
            (JumpType::Offset(0), _) => a.clone(),
            (JumpType::Offset(i), JumpType::Offset(j)) => JumpType::Offset(i+j),
            (JumpType::Offset(i), JumpType::Choice(x)) | (JumpType::Choice(x), JumpType::Offset(i)) =>
                JumpType::Choice(x.into_iter().map(|x| x + i).collect()),
            (JumpType::Choice(x), JumpType::Choice(y)) => {
                let mut s = BTreeSet::new();
                for i in x.into_iter() {
                    for j in y.into_iter() {
                        s.insert(i + j);
                    }
                }
                JumpType::Choice(s)
            },
            (JumpType::Star, _) | (_, JumpType::Star) => JumpType::Star
        }
    }
}

impl fmt::Display for JumpType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            JumpType::Offset(u) => write!(f, "offset({})", u),
            JumpType::Choice(us) => write!(f, "choice({:?})", us),
            JumpType::Star => write!(f, "*")
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
            RegexF::Range(a, 0, 1) => write!(f, "{}?", a),
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
                Expr::Literal { val, .. } =>
                    val.chars()
                       .try_fold(Regex::nil(),
                        |acc, a| Ok(Regex::app(acc, Regex::character(a)))),
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
                                  .map(|a| Regex::character(a))
                                  .reduce(Regex::alt)
                                  .unwrap_or(Regex::empty()))
                          }
                        },
                        HirKind::Literal(Literal::Unicode(c)) => Ok(Regex::character(*c)),
                        _ => Err(format!("Unsupported regex (regex_syntax) {:#?}", re.kind())),
                    }
                },
                _ => Err(format!("Unsupported regex (fancy_regex) {:#?}", e))
            }
        }

        to_regex(&Expr::parse_tree(s).unwrap().expr)
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

    pub fn line_start() -> Regex {
        Regex(G.mk(RegexF::LineStart))
    }

    pub fn line_end() -> Regex {
        Regex(G.mk(RegexF::LineEnd))
    }

    /// Subset relation is a partial order
    pub fn partial_le(a: &Regex, b: &Regex) -> Option<bool> {
        match (&*a.0, &*b.0) {
            (x, y) if x == y => Some(true),
            (RegexF::Char(_), RegexF::Dot) => Some(true),
            (RegexF::Dot, RegexF::Char(_)) => Some(false),
            (RegexF::Nil, RegexF::Star(_)) => Some(true),
            (RegexF::Star(_), RegexF::Nil) => Some(false),
            (RegexF::Range(x, _, _), RegexF::Star(y)) if Some(true) == Regex::partial_le(x, y) => Some(true),
            (RegexF::Star(x), RegexF::Range(y, _, _)) if Some(false) == Regex::partial_le(x, y) => Some(true),
            (RegexF::Range(x, i1, j1), RegexF::Range(y, i2, j2)) if x == y && i1 <= i2 && j2 <= j1 => Some(true),
            (RegexF::Range(x, i1, j1), RegexF::Range(y, i2, j2)) if x == y && i2 <= i1 && j1 <= j2 => Some(false),
            (RegexF::Empty, _) => Some(true),
            (_, RegexF::Empty) => Some(false),
            // (a|b) >= c if (a >= c)
            (RegexF::Alt(x1, _), x2) if Some(false) == Regex::partial_le(x1, &Regex(G.mk(x2.clone()))) => Some(false),
            // (a|b) >= c if (b >= c)
            (RegexF::Alt(_, x1), x2) if Some(false) == Regex::partial_le(x1, &Regex(G.mk(x2.clone()))) => Some(false),
            // c <= (a|b) if (c <= a)
            (x1, RegexF::Alt(x2, _)) if Some(true) == Regex::partial_le(&Regex(G.mk(x1.clone())), x2) => Some(true),
            // c <= (a|b) if (c <= b)
            (x1, RegexF::Alt(_, x2)) if Some(true) == Regex::partial_le(&Regex(G.mk(x1.clone())), x2) => Some(true),
            (_, RegexF::Star(i)) if *i.0 == RegexF::Dot => Some(true),
            (RegexF::Star(i), _) if *i.0 == RegexF::Dot => Some(false),
            (RegexF::Star(a), RegexF::Star(b)) => Regex::partial_le(a, b),
            (RegexF::App(ref a, ref x), RegexF::App(ref b, ref y)) => {
                let h = Regex::partial_le(a, b)?;
                let t = Regex::partial_le(x, y)?;
                Some(h && t)
            },
            (_, _) => None
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
            (RegexF::Range(a, i, j), _) if a == &b => Regex::range(a.clone(), i+1, j+1),
            (_, RegexF::Range(b, i, j)) if &a == b => Regex::range(b.clone(), i+1, j+1),
            (RegexF::Range(a, i1, j1), RegexF::Range(b, i2, j2)) if a == b => Regex::range(a.clone(), i1+i2, j1+j2),
            (RegexF::Star(x), RegexF::Range(y, _, _)) if x == y => a,
            (RegexF::Range(y, _, _), RegexF::Star(x)) if x == y => b,
            (RegexF::Star(x), RegexF::Star(y)) if x == y => a,
            // ^, $ idempotent
            (RegexF::LineStart, RegexF::LineStart) |
                (RegexF::LineEnd, RegexF::LineEnd) => a,
            (RegexF::LineStart, RegexF::LineEnd) => Regex::empty(),
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
        assert!(i <= j, "Range indices {{{}, {}}} must be 0 <= {} <= {}", i, j, i, j);
        match &*a.0 {
            RegexF::Star(_) | RegexF::Nil => a,
            RegexF::Empty => Regex::empty(),
            _ => Regex(G.mk(RegexF::Range(a, i, j)))
        }
    }

    pub fn not(a: Regex) -> Regex {
        match &*a.0 {
            RegexF::Not(a) => a.clone(),
            RegexF::Empty => Regex::star(Regex::dot()), // Is that true?
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

    pub fn has_zero_length_assertions(&self) -> bool {
        match *self.0 {
            RegexF::LineEnd | RegexF:: LineStart | RegexF::Lookahead(_) => true,
            RegexF::App(ref a, ref b) => a.has_zero_length_assertions() || b.has_zero_length_assertions(),
            RegexF::Alt(ref a, ref b) => a.has_zero_length_assertions() || b.has_zero_length_assertions(),
            RegexF::Star(ref a) => a.has_zero_length_assertions(),
            _ => false
        }
    }

    /// Does it accept any string
    pub fn accepts_any(&self, ab: &Vec<char>) -> bool {
        ab.iter().all(|c| self.deriv(&c).nullable())
    }

    /// Make [r], [n] into [rrrr....r] n times.
    pub fn repeat(&self, n: usize) -> Regex {
        match std::iter::repeat(self.clone()).take(n).reduce(Regex::app) {
            Some(r) => r,
            None => Regex::nil()
        }
    }

    /// Extract the longest possible wildcard jump and two continuation regexs
    ///
    ///   self ---[J]--> Regex -> NFA
    ///              |
    ///              --> Regex' -> NFA'
    ///
    pub fn has_jump(&self, ab: &Vec<char>) -> Option<(JumpType, Option<Regex>, Regex)> {
        match *self.0 {
            RegexF::Star(ref a) if a.accepts_any(ab) => Some((JumpType::Star, None, Regex::nil())),
            RegexF::Range(ref a, i, j) if i == j && a.accepts_any(ab) =>
                Some((JumpType::Offset(i), None, Regex::nil())),
            RegexF::Range(ref a, i, j) if a.accepts_any(ab) =>
                Some((JumpType::Choice((i..=j).collect()), None, Regex::nil())),
            RegexF::Lookahead(ref a) => Some((JumpType::Offset(0), Some(a.clone()), Regex::nil())),
            RegexF::App(ref a, ref b) =>
                if let Some((ja, ra, ca)) = a.has_jump(ab) {
                    Some((ja, ra, Regex::app(ca, b.clone())))
                } else { None },
            RegexF::Alt(ref a, ref b) =>
                match (a.has_jump(ab), b.has_jump(ab)) {
                    // Both jump, two forks and two continuations
                    (Some((ja, Some(ra), ca)), Some((jb, Some(rb), cb))) =>
                        Some((ja.or(&jb), Some(Regex::alt(ra, rb)), Regex::alt(ca, cb))),
                    // Both jump, one fork and two continuations
                    (Some((ja, Some(ra), ca)), Some((jb, None, cb))) =>
                        Some((ja.or(&jb), Some(ra), Regex::alt(ca, cb))),
                    (Some((ja, None, ca)), Some((jb, Some(rb), cb))) =>
                        Some((ja.or(&jb), Some(rb), Regex::alt(ca, cb))),
                    // Both jump, no fork and two continuations
                    (Some((ja, None, ca)), Some((jb, None, cb))) =>
                        Some((ja.or(&jb), None, Regex::alt(ca, cb))),
                    // One jump, one fork and one continuations
                    (Some((j, Some(r), c)), None) =>
                        Some((j, Some(Regex::alt(r, b.clone())), c)),
                    (None, Some((j, Some(r), c))) =>
                        Some((j, Some(Regex::alt(a.clone(), r)), c)),
                    // One jump, no fork and one continuations
                    (Some((j, None, c)), None) =>
                        Some((j, Some(b.clone()), c)),
                    (None, Some((j, None, c))) =>
                        Some((j, Some(a.clone()), c)),
                    (None, None) => None
                },
            _ => None
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
            RegexF::App(ref a, ref b) if *a.0 == RegexF::LineStart => b.deriv(c),
            RegexF::App(ref a, ref b) if *b.0 == RegexF::LineEnd => a.deriv(c),
            RegexF::App(ref a, ref b) if a.nullable() =>
                Regex::alt(Regex::app(a.deriv(c), b.clone()), b.deriv(c)),
            RegexF::App(ref a, ref b) => Regex::app(a.deriv(c), b.clone()),
            RegexF::Alt(ref a, ref b) => Regex::alt(a.deriv(c), b.deriv(c)),
            RegexF::Star(ref a) => Regex::app(a.deriv(c), Regex::star(a.clone())),
            RegexF::Range(ref a, i, j) if i == j => a.repeat(i).deriv(c),
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
fn regex_parser_test_zero_length() {
    assert_eq!(Regex::app(Regex::app(Regex::app(Regex::app(Regex::line_start(), Regex::character('F')), Regex::character('o')), Regex::character('o')), Regex::line_end()), Regex::new("^Foo$"));
}

#[test]
fn regex_parser_test_char_ranges() {
    assert_eq!(Regex::app(Regex::app(Regex::line_start(), Regex::alt(Regex::character('a'), Regex::character('b'))), Regex::line_end()), Regex::new("^[a-b]$"));
}

#[test]
fn regex_parser_test_dot() {
    assert_eq!(Regex::app(Regex::app(Regex::line_start(), Regex::star(Regex::dot())), Regex::character('c')), Regex::new("^.*c"));
}

#[test]
fn regex_parser_test_repetition_range() {
    assert_eq!(Regex::range(Regex::character('a'), 1, 3), Regex::new("a{1,3}"));
}
