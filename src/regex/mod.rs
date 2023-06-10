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
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Regex(pub HConsed<RegexF>);

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
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

#[derive(Clone,Debug,PartialEq,Eq,PartialOrd,Ord)]
struct CharacterClass(Vec<ClassUnicodeRange>);
impl CharacterClass {
    fn chars_len(self) -> u32 { 
       let size = self.0.iter().fold(0, |a, r| a + (r.end() as u32 - r.start() as u32)); 
       size
    }

    fn negate(self) -> CharacterClass {
        let self_v = self.0;
        let mut v: Vec<ClassUnicodeRange> = vec![];
        let max_char = std::char::MAX;
        if self_v.len() == 1 {
            let lower = self_v[0].start() as u8;
            let upper = self_v[0].end() as u8;
            if lower == 0 {
                v.push(ClassUnicodeRange::new((upper + 1) as char, max_char));
            } else {
                v.push(ClassUnicodeRange::new(0 as char, (lower-1) as char));
                v.push(ClassUnicodeRange::new((upper+1) as char, max_char));
            }
        } else {
            for r in 1..self_v.len() {
                let prev_upper = self_v[r-1].end() as u8;
                let curr_lower = self_v[r].start() as u8;
                //assert_ne!(prev_upper+1, curr_lower-1);
                v.push(ClassUnicodeRange::new((prev_upper+1) as char, (curr_lower-1) as char));
            }
        }

        CharacterClass(v)
    }
    fn to_regex(&self) -> Regex {
        let size = self.clone().chars_len();
        let char_max: u32 = std::char::MAX as u32;
        if size == 0 {
            return Regex::empty() //empty
        } else if size >= char_max && self.0.len()==1 {
            return Regex::dot() //check that this is correct
        } else {
            if char_max - size < size {
                let neg = self.clone().negate();
                let to_neg: Regex = neg.0.iter().flat_map(|a| (a.start()..=a.end())).map(|a| Regex::character(a)).reduce(Regex::alt).unwrap_or(Regex::empty());
                return Regex::not(to_neg)
            } else {
                return self.0.iter().flat_map(|a| (a.start()..=a.end())).map(|a| Regex::character(a)).reduce(Regex::alt).unwrap_or(Regex::empty())
            }
        }
    }
}

impl Regex {
    pub fn new<'a>(rstr: &'a str) -> Self {
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
                }
                Expr::Group(g) => to_regex_top(&g),
                _ => Ok(Regex::app(
                    Regex::app(Regex::dotstar(), to_regex(e)?),
                    Regex::dotstar(),
                )),
            }
        }

        fn to_regex(e: &Expr) -> Result<Regex, String> {
            println!("Raw regex {:?}", e);
            match e {
                Expr::Empty => Ok(Regex::empty()),
                Expr::Any { .. } => Ok(Regex::dot()),
                Expr::StartText | Expr::StartLine | Expr::EndText | Expr::EndLine => {
                    Ok(Regex::nil())
                }
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
                    println!("RAW DELEGATED REGEX {:?}", re.kind());
                    match re.kind() {
                        HirKind::Class(Class::Unicode(ranges)) => {
                            let cc: CharacterClass = CharacterClass(ranges.ranges().to_vec());
                            Ok(cc.to_regex())
                            
                            // let size = ranges
                            //     .iter()
                            //     .fold(0, |a, r| a + (r.end() as u32 - r.start() as u32));
                            // if size > 120 {
                            //     Ok(Regex::dot())
                            // } else if size == 0 {
                            //     Ok(Regex::empty())
                            // } else {
                            //     Ok(ranges
                            //         .iter()
                            //         .flat_map(|a| (a.start()..=a.end()))
                            //         .map(|a| Regex::character(a))
                            //         .reduce(Regex::alt)
                            //         .unwrap_or(Regex::empty()))
                            // }
                        }
                        HirKind::Literal(Literal::Unicode(c)) => Ok(Regex::character(*c)),
                        _ => Err(format!("Unsupported regex (regex_syntax) {:#?}", re.kind())),
                    }
                }
                _ => Err(format!("Unsupported regex (fancy_regex) {:#?}", e)),
            }
        }

        to_regex_top(&Expr::parse_tree(rstr).unwrap().expr).unwrap()
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
        match *self.0 {
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
            // Bot
            (RegexF::Empty, _) => Some(true),
            // Top
            (_, RegexF::Star(i)) if *i.0 == RegexF::Dot => Some(true),
            // Refl
            (x, y) if x == y => Some(true),
            // Dot
            (RegexF::Char(_), RegexF::Dot) => Some(true),
            // Nil
            (RegexF::Nil, _) if b.nullable() => Some(true),
            // Range*
            (RegexF::Range(x, i, _), RegexF::Star(y))
                if *i == 0 && Some(true) == Regex::partial_le(x, y) =>
                Some(true),
            // Range
            (RegexF::Range(x, i1, j1), RegexF::Range(y, i2, j2))
                if Regex::partial_le(x, y) == Some(true) && i1 >= i2 && j1 <= j2 =>
                Some(true),
            // Star
            (RegexF::Star(a), RegexF::Star(b)) => Regex::partial_le(a, b),
            // AltL
            (RegexF::Alt(x1, x2), _)
                if Some(true) == Regex::partial_le(x1, b) &&
                   Some(true) == Regex::partial_le(x2, b) =>
                Some(true),
            // AltR
            (_, RegexF::Alt(x1, x2))
                if Some(true) == Regex::partial_le(a, x1) &&
                   Some(true) == Regex::partial_le(a, x2) =>
                Some(true),
            // App
            (RegexF::App(ref a, ref x), RegexF::App(ref b, ref y))
                if a == b && Regex::partial_le(x, y) == Some(true) =>
                Some(true),
            (_, _) if Regex::partial_le(b, a) == Some(true) =>
                Some(false),
            (_, _) if Regex::partial_le(b, a) == Some(false) =>
                Some(true),
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
            //if r \in r{i,j} then r{i,j}^* = r^*
            RegexF::Range(ref x, i, j) if *i <= 1 && 1 <= *j => Regex::star(x.clone()),
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

    pub fn extract_lookahead(&self) -> Option<BTreeSet<Regex>> {
        match *self.0 {
            // (?=r)
            RegexF::Lookahead(ref a) => Some(BTreeSet::from([a.clone()])),
            // (?=r1)r2
            RegexF::App(ref a, ref b) => {
                let mut la = a.extract_lookahead()?;
                match b.extract_lookahead() {
                    Some(mut lb) => {
                        la.append(&mut lb);
                    },
                    None => {
                        la.insert(b.clone());
                    }
                };
                Some(la)
            },
            _ => None
        }
    }

    /// Extract a fork (and, or) from a regex and return the rest
    pub fn extract_alt(&self) -> Option<BTreeSet<Regex>> {
        match *self.0 {
            // (r | r')
            RegexF::Alt(_, _) => Some(self.to_alt_set()),
            // r1r2
            RegexF::App(ref a, ref b) =>
                a.extract_alt()
                 .map(|children| {
                    children
                        .into_iter()
                        .map(|c| Regex::app(c, b.clone()))
                        .collect()
                }),
            // Reduce ranges to or, since there are no skips
            RegexF::Range(ref a, i, j) =>
                Some((i..=j).map(|x| a.repeat(x)).collect()),
            _ => None,
        }
    }

    /// Extract a skip from a regex and return the rest
    pub fn extract_skip(&self, ab: &Vec<char>) -> Option<(Skip, Self)> {
        match *self.0 {
            RegexF::Dot => Some((Skip::single(), Regex::nil())),
            // .*
            RegexF::Star(ref a) => {
                let (sa, rem) = a.extract_skip(ab)?;
                if rem.is_nil() {
                    Some((sa.star(), Regex::nil()))
                } else {
                    None
                }
            }
            // .{i,j}
            RegexF::Range(ref a, x, y) => {
                let (sa, rem) = a.extract_skip(ab)?;
                if rem.is_nil() {
                    Some((sa.range(x, y), Regex::nil()))
                } else {
                    None
                }
            }
            // (r | r')
            RegexF::Alt(ref a, ref b) => {
                let (pa, rema) = a.extract_skip(ab)?;
                let (pb, remb) = b.extract_skip(ab)?;
                if rema.is_nil() && remb.is_nil() {
                    Some((pa.alt(&pb), Regex::nil()))
                } else {
                    None
                }
            }
            // r1r2
            RegexF::App(ref a, ref b) => {
                let (pa, rema) = a.extract_skip(ab)?;
                match b.extract_skip(ab) {
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

#[test]
fn test_regex_negative_char_class() {
    assert_eq!(
        Regex::app(
            Regex::app(
                Regex::app(
                    Regex::dotstar(),
                    Regex::not(Regex::character('a'))),
                Regex::character('b')),
            Regex::dotstar()),
        Regex::new("[^a]b")
    );
}


#[test]
fn test_regex_negative_char_class2() {
    assert_eq!(
        Regex::app(
            Regex::app(
                Regex::app(
                    Regex::dotstar(),
                    Regex::not(
                        Regex::alt(
                            Regex::character('a'),
                            Regex::character('b'),
                        )
                    )
                ),
                Regex::character('c')),
            Regex::dotstar()),
        Regex::new("[^ab]c")
    );
}

//add test for :space:, alphanum, etc
