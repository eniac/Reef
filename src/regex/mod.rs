#![allow(dead_code)]
#![allow(missing_docs)]
use hashconsing::{consign, HConsed, HashConsign};
use std::collections::BTreeSet;

use core::fmt;
use core::fmt::Formatter;
use crate::skip::Skip;
use crate::regex::charclass::CharClass;
use crate::regex::parser::RegexParser;

#[cfg(fuzz)]
pub mod arbitrary;

pub mod charclass;
pub mod parser;
pub mod ord;


/// Hash-consed regex terms
pub type Regex = HConsed<RegexF>;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum RegexF {
    Nil,
    Dot,
    CharClass(CharClass),
    Not(Regex),
    App(Regex, Regex),
    Alt(Regex, Regex),
    And(Regex, Regex),
    Range(Regex, usize, usize),
    Star(Regex),
}

consign! {
    /// Factory for terms.
    let G = consign(10) for RegexF ;
}

impl fmt::Display for RegexF {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            RegexF::Nil => write!(f, "ε"),
            RegexF::Dot => write!(f, "."),
            RegexF::CharClass(c) => write!(f, "{}", c),
            RegexF::Not(c) => write!(f, "(! {})", c),
            RegexF::App(x, y) => write!(f, "{}{}", x, y),
            RegexF::Alt(ref x, ref y) =>
                match (&*x.clone(), &*y.clone()) {
                    (RegexF::Nil, RegexF::Range(a, 1, j)) |
                    (RegexF::Range(a, 1, j), RegexF::Nil) =>
                        write!(f, "{}{{0,{}}}", a, j),
                    (x, y) => write!(f, "({} | {})", x, y)
                },
            RegexF::Star(a) => write!(f, "{}*", a),
            RegexF::And(a, b) => write!(f, "(?={}){}", a, b),
            RegexF::Range(a, 0, 1) => write!(f, "{}?", a),
            RegexF::Range(a, i, j) if i == j => write!(f, "{}{{{}}}", a, i),
            RegexF::Range(a, i, j) => write!(f, "{}{{{}, {}}}", a, i, j),
        }
    }
}

impl RegexF {
    /// Recursive algebraic simplification
    pub fn simpl(&self) -> RegexF {
        match self {
            RegexF::Nil | RegexF::Dot | RegexF::CharClass(_) => self.clone(),
            RegexF::Not(c) => RegexF::not(&c.simpl()),
            RegexF::App(x, y) => RegexF::app(&x.simpl(), &y.simpl()),
            RegexF::Alt(x, y) => RegexF::alt(&x.simpl(), &y.simpl()),
            RegexF::Star(a) => RegexF::star(&a.simpl()),
            RegexF::And(a, b) => RegexF::and(&a.simpl(), &b.simpl()),
            RegexF::Range(a, i, j) => RegexF::range(&a.simpl(), *i, *j)
        }
    }

    /// Is empty set (∅)?
    pub fn is_empty(&self) -> bool {
        match self {
            RegexF::CharClass(c) => c.is_empty(),
            _ => false,
        }
    }

    /// Empty set
    pub fn empty() -> RegexF {
        RegexF::CharClass(CharClass(vec![]))
    }

    /// Matches empty string (ε)
    pub fn nil() -> RegexF {
        RegexF::Nil
    }

    /// A single character ([c] character class)
    pub fn character(c: char) -> RegexF {
        RegexF::CharClass(CharClass::single(c))
    }

    /// Wildcard (matches any one character)
    pub fn dot() -> RegexF {
        RegexF::Dot
    }

    /// Wildcard-closure
    pub fn dotstar() -> RegexF {
        RegexF::star(&RegexF::dot())
    }

    /// Create a character class
    pub fn charclass(v: Vec<(char, char)>) -> RegexF {
        let c = CharClass::new(v);
        let size = c.interv_len();
        let char_max: usize = std::char::MAX as usize;
        if size == 0 {
            RegexF::empty() //empty
        } else if size >= char_max && c.len() == 1 {
            RegexF::dot() //check that this is correct
        } else {
            RegexF::CharClass(c.clone())
        }
    }

    /// Subset relation is a partial order
    /// a <= b -> true (a indeeed <= b)
    /// a <= b -> false (don't know!)
    pub fn partial_le(a: &Self, b: &Self) -> bool {
        match (a, b) {
            // Bot
            (_, _) if a.is_empty() => true,
            // Refl
            (x, y) if x == y => true,
            // Dot
            (RegexF::CharClass(_), RegexF::Dot) => true,
            // Nil
            (RegexF::Nil, _) if b.nullable() => true,
            // Range*
            (RegexF::Range(x, i, _), RegexF::Star(y))
                if *i == 0 && RegexF::partial_le(x, y) => true,
            // Range
            (RegexF::Range(x, i1, j1), RegexF::Range(y, i2, j2))
                if RegexF::partial_le(x, y) && i1 >= i2 && j1 <= j2 => true,
            // Star
            (RegexF::Star(a), RegexF::Star(b)) => RegexF::partial_le(a, b),
            // AltOpp
            (RegexF::Alt(x1, x2), _)
                if RegexF::partial_le(x1, b) && RegexF::partial_le(x2, b) => true,
            // AltR
            (_, RegexF::Alt(x1, _)) if RegexF::partial_le(a, x1) => true,
            // AltR
            (_, RegexF::Alt(_, x2)) if RegexF::partial_le(a, x2) => true,
            // App
            (RegexF::App(ref a, ref x), RegexF::App(ref b, ref y))
                if RegexF::partial_le(a, b) && RegexF::partial_le(b, a) =>
                RegexF::partial_le(x, y),
            (_, _) => false,
        }
    }

    pub fn partial_eq(a: &Self, b: &Self) -> bool {
        RegexF::partial_le(a, b) && RegexF::partial_le(b, a)
    }

    /// Smart constructor [and] for approx. notion of equivalence
    pub fn and(a: &Self, b: &Self) -> Self {
        match (a, b) {
            (_, _) if RegexF::partial_eq(a, b) => a.clone(),
            (_, _) if a.is_empty() || b.is_empty() => RegexF::empty(),
            // a & b and a <= b -> a
            (_, _) if RegexF::partial_le(&a, &b) => a.clone(),
            // a & b and a >= b -> b
            (_, _) if RegexF::partial_le(&b, &a) => b.clone(),
            (RegexF::Not(o), x)  | (x, RegexF::Not(o))  if o.is_empty() => x.clone(),
            (RegexF::Star(d), x) | (x, RegexF::Star(d)) if **d == RegexF::dot() => x.clone(),
            // Left-associative [and]
            (x, RegexF::And(y, z)) => RegexF::and(&RegexF::and(x, y), z),
            (_, _) => RegexF::And(G.mk(a.clone()), G.mk(b.clone())),
        }
    }

    /// Smart constructor [app] for approx. notion of equivalence
    pub fn app(a: &Self, b: &Self) -> Self {
        let res = match (a, b) {
            // Monoid on Nil
            (x, RegexF::Nil) | (RegexF::Nil, x) => x.clone(),
            // Empty absorbs everything
            (_, _) if a.is_empty() || b.is_empty() => RegexF::empty(),
            // Range & star index math
            (RegexF::Range(a, i, j), x) | (x, RegexF::Range(a, i, j))
                if RegexF::partial_eq(&a, x) => RegexF::range(a, i + 1, j + 1),
            (RegexF::Range(a, i1, j1), RegexF::Range(b, i2, j2)) if RegexF::partial_eq(a, b) =>
                RegexF::range(a, i1 + i2, j1 + j2),
            (RegexF::Star(x), RegexF::Star(y)) if RegexF::partial_le(x, y) =>
                b.clone(),
            (RegexF::Star(x), RegexF::Star(y)) if RegexF::partial_le(y, x) =>
                a.clone(),
            // And distributivity (not explosive): (a & b)c == (a.*) & bc
            (RegexF::And(a, b), c) =>
                RegexF::and(&RegexF::app(a, &RegexF::dotstar()), &RegexF::app(b, c)),
            // Alt distributivity (explosive!): (a | b)c == ac | bc
            // (RegexF::Alt(a, b), c) =>
            //    RegexF::and(&RegexF::app(a, c), &RegexF::app(b, c)),
            // Right-associative [app]
            (RegexF::App(x, y), z) => RegexF::app(x, &RegexF::app(y, z)),
            (_, _) => RegexF::App(G.mk(a.clone()), G.mk(b.clone())),
        };

        println!("Appending {} ++ {} = {}", a, b, res);
        res
    }

    /// Smart constructor [alt] for approx. notion of equivalence
    pub fn alt(a: &Self, b: &Self) -> Self {
        match (a, b) {
            // Idempotent [alt]
            (x, y) if x == y => a.clone(),
            // Left-associative [alt]
            (_, RegexF::Alt(x, y)) => RegexF::alt(&RegexF::alt(a, x), y),
            (RegexF::CharClass(a), RegexF::CharClass(b)) => RegexF::CharClass(a.union(b)),
            // a | b and a <= b -> b
            (_, _) if RegexF::partial_le(&a, &b) => b.clone(),
            // a | b and a >= b -> a
            (_, _) if RegexF::partial_le(&b, &a) => a.clone(),
            // The smallest syntactically thing on the left
            (_, _) if a > b => RegexF::alt(b, a),
            (_, _) => RegexF::Alt(G.mk(a.clone()), G.mk(b.clone())),
        }
    }

    /// Smart constructor [star] for approx. notion of equivalence
    pub fn star(a: &Self) -> Self {
        match a {
            RegexF::Star(_) | RegexF::Nil => a.clone(),
            _ if a.is_empty() => RegexF::nil(),
            //if r \in r{i,j} then r{i,j}^* = r^*
            RegexF::Range(x, i, j) if *i <= 1 && 1 <= *j => RegexF::star(x),
            _ => RegexF::Star(G.mk(a.clone())),
        }
    }

    /// At least [n] times [a]
    pub fn starplus(a: &Self, n: usize) -> Self {
        RegexF::app(&RegexF::range(a, 0, n), &RegexF::star(a))
    }

    /// Shorthand for building alternation trees
    pub fn alts(v: &[RegexF]) -> RegexF {
        match v {
            [] => RegexF::empty(),
            vs => RegexF::alt(&vs[0], &RegexF::alts(&vs[1..]))
        }
    }

    /// Bounded repetion of [self] from [i, j] times (inclusive)
    pub fn range(&self, i: usize, j: usize) -> Self {
        assert!(i <= j, "Range indices must be 0 <= {} <= {}", i, j);
        match self {
            RegexF::Star(_) | RegexF::Nil => self.clone(),
            _ if i == 1 && j == 1 => self.clone(),
            _ if self.is_empty() => RegexF::empty(),
            _ if i == 0 && j == 0 => RegexF::nil(),
            _ if i == 0 => RegexF::alt(&RegexF::nil(), &RegexF::range(self, 1, j)),
            _ => RegexF::Range(G.mk(self.clone()), i, j),
        }
    }

    /// Negation of regex
    pub fn not(a: &Self) -> Self {
        let res = match a {
            RegexF::Not(ref a) => (**a).clone(),
            RegexF::CharClass(c) => RegexF::CharClass(c.negate()),
            // ! . = nil | .. .*
            // RegexF::Dot => RegexF::alt(&RegexF::nil(), &RegexF::starplus(&RegexF::Dot, 2)),
            RegexF::Alt(a, b) => RegexF::and(&RegexF::not(a), &RegexF::not(b)),
            RegexF::And(a, b) => RegexF::alt(&RegexF::not(a), &RegexF::not(b)),
            // The negation of !(ab) = (!a) b | b (!a) | (!a)(!b)
            RegexF::App(x, y) =>
                RegexF::alts(&[
                    RegexF::app(x, &RegexF::not(&y)),
                    RegexF::app(&RegexF::not(&x), y),
                    RegexF::app(&RegexF::not(&x), &RegexF::not(&y))
                ]),
            // The negation of !r{i,j} = .{0,i-1} | {i,j}!r | .{j+1, *}
            RegexF::Range(ref x, i, j) =>
                RegexF::alts(&[
                    RegexF::range(&RegexF::not(x), *i, *j),
                    RegexF::range(x, 0, i - 1),
                    RegexF::starplus(&RegexF::dot(), j + 1)
                ]),
            _ if a.is_empty() => RegexF::dotstar(),
            _ => RegexF::Not(G.mk(a.clone())),
        };
        println!("Negating ! ({}) = {}", a, res);
        res
    }

    /// Is regex exactly [nil]
    pub fn is_nil(&self) -> bool {
        self == &RegexF::Nil
    }

    /// Nullable regex accept the empty document
    pub fn nullable(&self) -> bool {
        match self {
            _ if self.is_empty() => false,
            RegexF::Nil | RegexF::Star(_) => true,
            RegexF::Range(_, i, _) if *i == 0 => true,
            RegexF::CharClass(_) | RegexF::Dot | RegexF::Range(_, _, _) => false,
            RegexF::Not(ref r) => !r.nullable(),
            RegexF::And(ref a, ref b) | RegexF::App(ref a, ref b) => a.nullable() && b.nullable(),
            RegexF::Alt(ref a, ref b) => a.nullable() || b.nullable(),
        }
    }

    /// Does it accept any string
    pub fn accepts_any(&self, ab: &Vec<char>) -> bool {
        ab.iter().all(|c| self.deriv(&c).nullable())
    }

    /// Extract an [and] set from a regex, for [(a & b)c => [a, bc]]
    pub fn to_and_set(&self) -> BTreeSet<RegexF> {
        match self {
            // (r | r' | ...) => [r, r', ...]
            RegexF::And(ref a, ref b) => {
                let mut l = a.to_and_set();
                let mut r = b.to_and_set();
                l.append(&mut r);
                l
            },
            o => BTreeSet::from([o.clone()])
        }
    }

    /// Extract an [alt] set from a regex, use distributivity to append the rest
    pub fn to_alt_set(&self) -> BTreeSet<RegexF> {
        match self {
            // (r | r' | ...) => [r, r', ...]
            RegexF::Alt(ref a, ref b) => {
                let mut l = a.to_alt_set();
                let mut r = b.to_alt_set();
                l.append(&mut r);
                l
            },
            o => BTreeSet::from([o.clone()])
        }
    }

    /// Extract a skip from a regex and return the rest
    pub fn extract_skip(&self, ab: &Vec<char>) -> Option<(Skip, Self)> {
        match self {
            RegexF::Dot => Some((Skip::single(), RegexF::nil())),
            // .*
            RegexF::Star(ref a) => {
                let (sa, rem) = a.extract_skip(ab)?;
                if rem.is_nil() {
                    Some((sa.star_of(0), RegexF::nil()))
                } else {
                    None
                }
            }
            // .{i,j}
            RegexF::Range(ref a, x, y) => {
                let (sa, rem) = a.extract_skip(ab)?;
                if rem.is_nil() {
                    Some((sa.range_of(*x, *y), RegexF::nil()))
                } else {
                    None
                }
            }
            // r1r2
            RegexF::App(ref a, ref b) => {
                let (pa, rema) = a.extract_skip(ab)?;
                match b.extract_skip(ab) {
                    Some((pb, remb)) if rema.is_nil() => Some((pa.app(&pb), remb)),
                    _ => Some((pa, RegexF::app(&rema, b))),
                }
            }
            _ => None,
        }
    }

    /// Make [self] given [n] into [rrrr....r] n-times.
    pub fn repeat(&self, n: usize) -> RegexF {
        match n {
            0 => RegexF::nil(),
            1 => self.clone(),
            n => RegexF::app(&self.repeat(n - 1), &self),
        }
    }

    /// Derivative
    pub fn deriv(&self, c: &char) -> Self {
        match self {
            RegexF::Nil => RegexF::empty(),
            RegexF::CharClass(cs) if cs.is_empty() => RegexF::empty(),
            RegexF::CharClass(cs) if cs.contains(c) => RegexF::nil(),
            RegexF::CharClass(_) => RegexF::empty(),
            RegexF::Not(ref r) => RegexF::not(&r.deriv(c)),
            RegexF::App(ref a, ref b) if a.nullable() => {
                RegexF::alt(&RegexF::app(&a.deriv(c), b), &b.deriv(c))
            }
            RegexF::App(ref a, ref b) => RegexF::app(&a.deriv(c), b),
            RegexF::Alt(ref a, ref b) => RegexF::alt(&a.deriv(c), &b.deriv(c)),
            RegexF::Star(ref a) => RegexF::app(&a.deriv(c), &RegexF::star(a)),
            _ => panic!("No derivatives for regex {}", self),
        }
    }
}

/// Top level module with hash-consing constructors
pub mod re {
    use crate::regex::charclass::CharClass;
    use crate::regex::G;
    use crate::regex::{parser::RegexParser,Regex, RegexF};
    use crate::skip::Skip;
    use hashconsing::HashConsign;
    use std::collections::BTreeSet;

    /// Constructor
    pub fn new<'a>(s: &'a str) -> Regex {
        RegexParser::parse(s)
    }

    /// Matches empty string (ε)
    pub fn nil() -> Regex {
        G.mk(RegexF::Nil)
    }

    /// Matches nothing, empty set (∅)
    pub fn empty() -> Regex {
        G.mk(RegexF::CharClass(CharClass::empty()))
    }

    /// A single character ([c] character class)
    pub fn character(c: char) -> Regex {
        G.mk(RegexF::CharClass(CharClass::single(c)))
    }

    /// Concatenation
    pub fn app(a: Regex, b: Regex) -> Regex {
        G.mk(RegexF::app(&*a, &*b))
    }

    /// Alternation
    pub fn alt(a: Regex, b: Regex) -> Regex {
        G.mk(RegexF::alt(&*a, &*b))
    }

    /// Conjunction
    pub fn and(a: Regex, b: Regex) -> Regex {
        G.mk(RegexF::and(&*a, &*b))
    }
    /// Wildcard (matches any one character)
    pub fn dot() -> Regex {
        G.mk(RegexF::Dot)
    }

    /// Negation
    pub fn not(a: Regex) -> Regex {
        G.mk(RegexF::not(&*a))
    }

    /// Wildcard-closure
    pub fn dotstar() -> Regex {
        G.mk(RegexF::star(&RegexF::dot()))
    }

    /// Kleene-closure
    pub fn star(a: Regex) -> Regex {
        G.mk(RegexF::star(&*a))
    }

    /// Bounded repetition
    pub fn range(a: Regex, i: usize, j: usize) -> Regex {
        G.mk(RegexF::range(&*a, i, j))
    }

    /// Exact repetition
    pub fn repeat(a: Regex, i: usize) -> Regex {
        G.mk(RegexF::range(&*a, i, i))
    }

    /// Kleene-closure after exactly [n] matches
    pub fn starplus(a: Regex, n: usize) -> Regex {
        G.mk(RegexF::starplus(&*a, n))
    }

    /// A list of character ranges
    pub fn charclass(v: Vec<(char,char)>) -> Regex {
        G.mk(RegexF::charclass(v))
    }
    /// Derivative
    pub fn deriv(a: &Regex, c: &char) -> Regex {
        G.mk(RegexF::deriv(&*a, c))
    }

    /// Nullable regex accept the empty document
    pub fn nullable(a: &Regex) -> bool {
        (*a).nullable()
    }

    /// Extract a skip from a regex and return the rest
    pub fn extract_skip(a: &Regex, ab: &Vec<char>) -> Option<(Skip, Regex)> {
        let (s, rem) = (*a).extract_skip(ab)?;
        Some((s, G.mk(rem)))
    }

    /// Extract an [alt] set from a regex, use distributivity to append the rest
    pub fn to_alt_set(a: &Regex) -> BTreeSet<Regex> {
        (*a).to_alt_set()
            .into_iter().map(|rf| G.mk(rf)).collect()
    }

    /// Extract an [and] set from a regex, for [(a & b)c => [a, bc]]
    pub fn to_and_set(a: &Regex) -> BTreeSet<Regex> {
        (*a).to_and_set()
            .into_iter().map(|rf| G.mk(rf)).collect()
    }
}

#[test]
fn test_regex_ord() {
    assert!(re::character('a') < re::character('b'))
}

#[test]
fn test_regex_zero_length() {
    assert_eq!(
        re::app(
            re::app(re::character('F'), re::character('o')),
            re::character('o')
        ),
        re::new("^Foo$")
    );
}

#[test]
fn test_regex_ranges() {
    assert_eq!(
        re::app(
            re::app(
                re::dotstar(),
                re::alt(re::character('a'), re::character('b'))
            ),
            re::dotstar()
        ),
        re::new("[a-b]")
    );
}

#[test]
fn test_regex_dot_star() {
    assert_eq!(
        re::app(re::app(re::dotstar(), re::character('c')), re::dotstar()),
        re::new("^.*c")
    );
}

#[test]
fn regex_parser_test_repetition_range() {
    assert_eq!(re::range(re::character('a'), 1, 3), re::new("^a{1,3}$"));
}

#[test]
fn test_regex_negative_char_class() {
    assert_eq!(
        re::app(re::not(re::character('a')), re::character('b')),
        re::new("^[^a]b$")
    );
}

#[test]
fn test_regex_negative_char_class2() {
    //unsafe { backtrace_on_stack_overflow::enable() };
    assert_eq!(
        re::app(
            re::app(
                re::app(
                    re::dotstar(),
                    re::not(re::alt(re::character('a'), re::character('b'),))
                ),
                re::character('c')
            ),
            re::dotstar()
        ),
        re::new("[^ab]c")
    );
}

#[test]
fn test_regex_dot() {
    assert_eq!(re::app(re::dot(), re::character('a'),), re::new("^.a$"));
}

#[test]
fn test_regex_negate_class() {
    assert_eq!(re::charclass(vec![('\0', '`'), ('b', '\u{10ffff}')]), re::new("^[^a]$"))
}

#[test]
fn test_regex_lookahead() {
    assert_eq!(re::app(re::character('a'), re::dotstar()), re::new("^(?=a)"))
}

#[test]
fn test_regex_negative_lookahead() {
    assert_eq!(re::and(re::not(re::character('a')), re::nil()), re::new("^(?!a)$"))
}

#[test]
fn test_regex_negative_range() {
    let r = re::new("^(?=.{2,3}a)");
    let rn =re::new("^(?!.{2,3}a)");
   println!("Pos {}, Neg {}", r, rn);
   println!("Pos Simpl {}, Neg Simpl {}", r.simpl(), rn.simpl());

    assert_eq!(re::alt(
        re::alt(
            re::range(re::dot(), 0, 1),
            re::range(re::not(re::character('a')), 2,3)),
        re::starplus(re::character('a'), 4)),
        re::new("^(?!.{2,3}a)"))
}

#[test]
fn test_regex_negative_char_class_range() {
    assert_eq!(
        re::app(
            re::app(
                re::app(
                    re::dotstar(),
                    re::not(re::alt(
                        re::character('a'),
                        re::alt(
                            re::character('b'),
                            re::alt(re::character('c'), re::character('d'),)
                        )
                    ))
                ),
                re::character('e')
            ),
            re::dotstar()
        ),
        re::new("[^a-d]e")
    );
}
//add test for :space:, alphanum, etc
