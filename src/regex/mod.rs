#![allow(dead_code)]
#![allow(missing_docs)]
use hashconsing::{consign, HConsed, HashConsign};
use std::collections::BTreeSet;

use crate::openset::{OpenRange, OpenSet};
use crate::safa::Skip;
use core::fmt;
use core::fmt::Formatter;

use self::re::projection;

#[cfg(fuzz)]
pub mod arbitrary;

pub mod ord;
pub mod parser;

/// the type of character classes
pub type CharClass = OpenSet<char>;

/// Hash-consed regex terms
pub type Regex = HConsed<RegexF>;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum RegexF {
    Nil,
    Dot,
    CharClass(CharClass),
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
            RegexF::App(x, y) => write!(f, "{}{}", x, y),
            RegexF::Alt(ref x, ref y) => write!(f, "({} | {})", x, y),
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
            RegexF::App(x, y) => RegexF::app(&x.simpl(), &y.simpl()),
            RegexF::Alt(x, y) => RegexF::alt(&x.simpl(), &y.simpl()),
            RegexF::Star(a) => RegexF::star(&a.simpl()),
            RegexF::And(a, b) => RegexF::and(&a.simpl(), &b.simpl()),
            RegexF::Range(a, i, j) => RegexF::range(&a.simpl(), *i, *j),
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
        RegexF::CharClass(CharClass::empty())
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
    pub fn charclass(v: Vec<(char, Option<char>)>) -> RegexF {
        let c = CharClass::from_iter(v.into_iter());
        if c.negate().is_empty() {
            RegexF::dot()
        } else if c.is_empty() {
            RegexF::empty()
        } else {
            RegexF::CharClass(c.clone())
        }
    }

    /// Subset relation is a partial order
    /// a <= b -> true (a <= b)
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
            (RegexF::Range(x, i, _), RegexF::Star(y)) if *i == 0 && RegexF::partial_le(x, y) => {
                true
            }
            // Range
            (RegexF::Range(x, i1, j1), RegexF::Range(y, i2, j2))
                if RegexF::partial_le(x, y) && i1 >= i2 && j1 <= j2 =>
            {
                true
            }
            // Star
            (RegexF::Star(a), RegexF::Star(b)) => RegexF::partial_le(a, b),
            // AltOpp
            (RegexF::Alt(x1, x2), _) if RegexF::partial_le(x1, b) && RegexF::partial_le(x2, b) => {
                true
            }
            // AltR
            (_, RegexF::Alt(x1, _)) if RegexF::partial_le(a, x1) => true,
            // AltR
            (_, RegexF::Alt(_, x2)) if RegexF::partial_le(a, x2) => true,
            // App
            (RegexF::App(ref a, ref x), RegexF::App(ref b, ref y))
                if RegexF::partial_le(a, b) && RegexF::partial_le(b, a) =>
            {
                RegexF::partial_le(x, y)
            }
            (_, _) => false,
        }
    }

    /// a == b  = a <= b && b <= a
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
            (RegexF::Star(d), x) | (x, RegexF::Star(d)) if **d == RegexF::dot() => x.clone(),
            // Left-associative [and]
            (x, RegexF::And(y, z)) => RegexF::and(&RegexF::and(x, y), z),
            // Whenever (a & b) -> (a.* & b) we don't need to check postfixes twice
            (_, _) => RegexF::And(
                G.mk(RegexF::app(&a.clone(), &RegexF::dotstar())),
                G.mk(b.clone()),
            ),
        }
    }

    /// Smart constructor [app] for approx. notion of equivalence
    pub fn app(a: &Self, b: &Self) -> Self {
        match (a, b) {
            // Monoid on Nil
            (x, RegexF::Nil) | (RegexF::Nil, x) => x.clone(),
            // Empty absorbs everything
            (_, _) if a.is_empty() || b.is_empty() => RegexF::empty(),
            // Range & star index math
            (RegexF::Range(a, i, j), x) | (x, RegexF::Range(a, i, j))
                if RegexF::partial_eq(&a, x) =>
                RegexF::range(a, i + 1, j + 1),
            (RegexF::Range(a, i1, j1), RegexF::Range(b, i2, j2))
                if RegexF::partial_eq(a, b) =>
                RegexF::range(a, i1 + i2, j1 + j2),
            (RegexF::Star(x), RegexF::Star(y)) if RegexF::partial_le(x, y) => b.clone(),
            (RegexF::Star(x), RegexF::Star(y)) if RegexF::partial_le(y, x) => a.clone(),
            // And distributivity (not explosive): (a & b)c == (a.*) & bc
            (RegexF::And(a, b), c) =>
                RegexF::and(&RegexF::app(a, &RegexF::dotstar()), &RegexF::app(b, c)),
            // Alt distributivity (explosive!): (a | b)c == ac | bc
            // (RegexF::Alt(a, b), c) =>
            //    RegexF::and(&RegexF::app(a, c), &RegexF::app(b, c)),
            // Lef-associative [app]
            (x, RegexF::App(y, z)) => RegexF::app(&RegexF::app(x, y), z),
            (_, _) => RegexF::App(G.mk(a.clone()), G.mk(b.clone())),
        }
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

    /// Shallow not
    pub fn not(a: &Self) -> Self {
        match a {
            RegexF::CharClass(c) => RegexF::CharClass(c.negate()),
            _ => panic!("Negation of {} not implemented!", a),
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
            vs => RegexF::alt(&vs[0], &RegexF::alts(&vs[1..])),
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
            RegexF::And(ref a, ref b) | RegexF::App(ref a, ref b) => a.nullable() && b.nullable(),
            RegexF::Alt(ref a, ref b) => a.nullable() || b.nullable(),
        }
    }

    /// Does it accept any string
    pub fn accepts_any(&self, ab: &Vec<char>) -> bool {
        ab.iter().all(|c| self.deriv(&c).nullable())
    }

    /// Extract a skip from a regex and return the rest
    pub fn extract_skip(&self, ab: &Vec<char>) -> Option<(Skip, Self)> {
        let res = match self {
            RegexF::Dot => Some((Skip::single(1), RegexF::nil())),
            // .*
            RegexF::Star(ref a) => {
                let (sa, rem) = a.extract_skip(ab)?;
                if rem.is_nil() {
                    Some((sa.kleene(), RegexF::nil()))
                } else {
                    None
                }
            }
            // .{i,j}
            RegexF::Range(ref a, x, y) => {
                let (sa, rem) = a.extract_skip(ab)?;
                if rem.is_nil() {
                    Some((sa.repeat(*x, *y), RegexF::nil()))
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
        };
        res
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
            RegexF::Dot => RegexF::nil(),
            RegexF::CharClass(_) => RegexF::empty(),
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
    use crate::openset::OpenSet;
    use crate::regex::{parser::RegexParser, Regex, RegexF};
    use crate::regex::{CharClass, G};
    use crate::safa::Skip;
    use gmp_mpfr_sys::mpc::pow;
    use hashconsing::HashConsign;
    use std::array::TryFromSliceError;
    use std::collections::BTreeSet;

    /// Constructor
    pub fn new<'a>(s: &'a str) -> Regex {
        RegexParser::parse(s)
    }

    /// Algebraic simplification
    pub fn simpl(a: Regex) -> Regex {
        G.mk(RegexF::simpl(&*a))
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

    /// Range of characters
    pub fn charclass(v: &[(char, Option<char>)]) -> Regex {
        G.mk(RegexF::CharClass(OpenSet::from_iter(
            v.into_iter().map(|(a, b)| (*a, *b)),
        )))
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

    pub fn projection_intervals(r: &RegexF) -> Vec<(u32, u32)> {
        let mut intervals = Vec::new();
        let mut outR = r.clone();
        let mut start: u32 = 0;
        let mut end: u32 = 0;
        let mut trailing_dot: u32 = 0;
        while !outR.is_empty() {
            outR = match outR {
                RegexF::App(l, r) => {
                    match l.simpl() {
                        RegexF::Range(c, i, j) => {
                            if i == j {
                                match c.simpl() {
                                    RegexF::Dot => {
                                        if start == 0 && end == 0 {
                                            start = start + (i as u32);
                                            end = end + (i as u32);
                                        } else {
                                            if trailing_dot == 0 {
                                                intervals.push((start, end));
                                            }
                                            trailing_dot = trailing_dot + (i as u32);
                                        }
                                    }
                                    RegexF::CharClass(_) => {
                                        if trailing_dot != 0 {
                                            start = end + trailing_dot;
                                            end = end + trailing_dot + (i as u32);
                                            trailing_dot = 0;
                                        } else {
                                            end = end + (i as u32);
                                        }
                                    }
                                    _ => (),
                                }
                            }
                        }
                        RegexF::CharClass(_) => {
                            if trailing_dot != 0 {
                                start = end + trailing_dot;
                                end = end + trailing_dot + 1;
                                trailing_dot = 0;
                            } else {
                                end = end + 1
                            }
                        }
                        RegexF::Dot => {
                            if start == 0 && end == 0 {
                                start = start + 1;
                                end = end + 1
                            } else {
                                if trailing_dot == 0 {
                                    intervals.push((start, end));
                                }
                                trailing_dot = trailing_dot + 1
                            }
                        }
                        RegexF::Star(_) => {
                            return vec![(0, 0)];
                        }
                        RegexF::Alt(opt1, opt2) => {
                            let opt1_len = get_len(&opt1, 0, true);
                            let opt2_len = get_len(&opt2, 0, true);
                            if opt1_len == opt2_len {
                                if trailing_dot != 0 {
                                    start = end + trailing_dot;
                                    end = end + trailing_dot;
                                    trailing_dot = 0;
                                }
                                end = end + opt1_len;
                            } else {
                                return vec![(0, 0)];
                            }
                        }
                        _ => {}
                    }
                    let out = r.simpl();
                    out.to_owned()
                }
                RegexF::Star(c) => match c.simpl() {
                    RegexF::Dot => {
                        intervals.push((start, end));
                        return intervals;
                    }
                    _ => {
                        return vec![(0, 0)];
                    }
                },
                RegexF::CharClass(_) => {
                    if trailing_dot != 0 {
                        start = end + trailing_dot;
                        end = end + trailing_dot;
                        trailing_dot = 0;
                    }
                    end = end + 1;
                    intervals.push((start, end));
                    return intervals;
                }
                RegexF::Range(c, i, j) => {
                    if i == j {
                        match c.simpl() {
                            RegexF::Dot => {
                                if trailing_dot == 0 {
                                    intervals.push((start, end));
                                }
                            }
                            RegexF::CharClass(_) => {
                                if trailing_dot != 0 {
                                    start = end + trailing_dot;
                                    end = end + trailing_dot + (i as u32);
                                    trailing_dot = 0;
                                } else {
                                    end = end + (i as u32);
                                }
                                intervals.push((start, end));
                            }
                            _ => (),
                        }
                        return intervals;
                    } else {
                        return vec![(0, 0)];
                    }
                }
                _ => outR,
            };
        }
        intervals
    }

    pub fn get_len(r: &RegexF, size: u32, and_char: bool) -> u32 {
        let mut out = 0;
        match &r {
            RegexF::Dot => {
                out = 1;
            }
            RegexF::Nil | RegexF::CharClass(_) => {
                if and_char {
                    out = 1;
                } else {
                    out = 0;
                }
            }
            RegexF::App(x, y) => {
                let l = get_len(&x.simpl(), size, and_char);
                let r = get_len(&y.simpl(), size, and_char);
                if l > 0 {
                    out = l + r;
                } else {
                    out = l;
                }
            }
            RegexF::Alt(x, y) => {
                let l = get_len(&x.simpl(), size, and_char);
                let r = get_len(&x.simpl(), size, and_char);
                if l == r {
                    out = 0;
                } else {
                    out = l;
                }
            }
            RegexF::Star(a) => out = 0,
            RegexF::And(x, y) => {
                let l = get_len(&x.simpl(), size, and_char);
                let r = get_len(&y.simpl(), size, and_char);
                if l > 0 {
                    out = l + r;
                } else {
                    out = l;
                }
            }
            RegexF::Range(a, i, j) => {
                if i == j {
                    out = get_len(&a.simpl(), size, and_char) * (*i as u32);
                } else {
                    out = 0;
                }
            }
        }
        return out;
    }

    pub fn projection(r: &RegexF) -> Vec<(u32, u32)> {
        let mut intervals = projection_intervals(r);
        intervals.dedup_by(|(a, b), (c, d)| a == c);
        println!("{:#?}", intervals);
        let mut pow2_intervals: Vec<(u32, u32)> = Vec::new();
        if intervals[0].0 == 0 && intervals[0].1 == 0 {
            return vec![(0, 0)];
        }
        let mut l;
        let mut r;
        let mut original_size;
        let mut pow2padding;
        let base: i32 = 2;
        for i in 0..intervals.len() {
            println!("{:#?}", i);
            //always try and draw from the left
            l = intervals[i].0;
            r = intervals[i].1;
            original_size = r - l;
            pow2padding =
                (base.pow((original_size as f32).log2().ceil() as u32) as u32) - original_size;
            println!("{:#?},{:#?},{:#?}", l, r, pow2padding);
            let last_interval = pow2_intervals.pop();
            let mut new_interval: (u32, u32);
            match last_interval {
                None => {
                    if l < pow2padding {
                        new_interval = (0, r + (pow2padding - l) - 1);
                    } else {
                        new_interval = (l - pow2padding, r - 1);
                    }
                }
                Some(v) => {
                    if l - pow2padding < v.1 {
                        new_interval = (v.1 + 1, r + (pow2padding - (l - v.1)) - 1);
                    } else {
                        new_interval = (l - pow2padding, r - 1);
                    }
                    pow2_intervals.push(v);
                }
            }
            pow2_intervals.push(new_interval)
        }
        pow2_intervals
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
        re::simpl(re::new("^Foo$"))
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
        re::simpl(re::new("[a-b]"))
    );
}

#[test]
fn test_regex_dot_star() {
    assert_eq!(
        re::app(re::app(re::dotstar(), re::character('c')), re::dotstar()),
        re::simpl(re::new("^.*c"))
    );
}

#[test]
fn regex_parser_test_repetition_range() {
    assert_eq!(
        re::range(re::character('a'), 1, 3),
        re::simpl(re::new("^a{1,3}$"))
    );
}

#[test]
fn test_regex_negative_char_class() {
    assert_eq!(
        re::app(re::not(re::character('a')), re::character('b')),
        re::simpl(re::new("^[^a]b$"))
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
        re::simpl(re::new("[^ab]c"))
    );
}

#[test]
fn test_regex_dot() {
    assert_eq!(
        re::app(re::dot(), re::character('a'),),
        re::simpl(re::new("^.a$"))
    );
}

#[test]
fn test_regex_negate_class() {
    assert_eq!(
        re::charclass(&[('\0', Some('`')), ('b', None)]),
        re::simpl(re::new("^[^a]$"))
    )
}

#[test]
fn test_regex_lookahead() {
    assert_eq!(
        re::app(re::character('a'), re::dotstar()),
        re::simpl(re::new("^(?=a)"))
    )
}

#[test]
fn test_regex_lookahead_app() {
    assert_eq!(
        re::and(
            re::app(re::character('a'), re::dotstar()),
            re::app(
                re::character('b'),
                re::app(re::character('c'), re::dotstar())
            )
        ),
        re::simpl(re::new("^(?=a)bc"))
    )
}

#[test]
fn test_regex_lookahead_dotstar() {
    assert_eq!(
        re::and(
            re::app(re::character('a'), re::dotstar()),
            re::app(re::dotstar(), re::app(re::character('b'), re::dotstar()))
        ),
        re::simpl(re::new(r"^(?=a).*b"))
    )
}

#[test]
fn test_regex_negative_char_class_range() {
    assert_eq!(
        re::app(
            re::app(
                re::app(re::dotstar(), re::not(re::charclass(&[('a', Some('d'))]))),
                re::character('e')
            ),
            re::dotstar()
        ),
        re::simpl(re::new("[^a-d]e"))
    );
}

#[test]
fn test_for_proj() {
    let r = re::simpl(re::new(r"^.a(b|c)d{2}.{5}e{3}$"));
    // println!("{:#?}",r);
    println!("Intervals {:#?}", projection(r.get()));
    // println!("{:#?}",re::get_proj_size(r.get(), 0, false));
    // println!("{:#?}",re::get_proj_size(r.get(), 0, true));
    // println!("{:#?}",re::projection_pow2(r.get()));
    // println!("{:#?}",re::strip(r.get(),2));
    // .abdd.....eee
}

#[test]
fn test_proj_cons() {
    let r = re::simpl(re::new(r"^.{3}.{4}a$"));
    println!("Regex {:#?}", r);
    println!("Intervals {:#?}", projection(r.get()));
    // LEF: Should be [(7, 8)]
}

#[test]
fn test_proj_alt() {
    let r = re::simpl(re::new(r"^(.{3}|.{4})a$"));
    println!("Intervals {:#?}", projection(r.get()));
    // LEF: Unsure what the answer should be, either [(3,4)] or [(3,5)]
}
