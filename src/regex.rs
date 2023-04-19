#![allow(dead_code)]
#![allow(missing_docs)]
use hashconsing::{consign, HConsed, HashConsign};
use regex_syntax::hir::{Hir, HirKind, Anchor, Class, RepetitionKind, RepetitionRange, Literal};
use regex_syntax::Parser;

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
    Char(char),
    Not(Regex),
    App(Regex, Regex),
    Alt(Regex, Regex),
    Range(Regex, usize, usize),
    Star(Regex),
}

consign! {
    /// Factory for terms.
    let G = consign(10) for RegexF ;
}

use core::fmt;
use core::fmt::Formatter;

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
            RegexF::Range(a, i, j) => write!(f, "{}{{{}, {}}}", a, i, j)
        }
    }
}

impl Regex {
    pub fn new<'a>(r: &'a str) -> Self {
        fn to_regex<'a>(h: &'a Hir) -> Regex {
            match h.kind() {
                HirKind::Concat(l) => l
                    .iter()
                    .map(|a| to_regex(&a))
                    .reduce(Regex::app)
                    .unwrap_or(Regex::nil()),
                HirKind::Alternation(l) => l
                    .iter()
                    .map(|a| to_regex(&a))
                    .reduce(Regex::alt)
                    .unwrap_or(Regex::empty()),
                HirKind::Repetition(r) => {
                    let inner = to_regex(&r.hir);
                    match r.kind {
                        RepetitionKind::OneOrMore => Regex::app(inner.clone(), Regex::star(inner)),
                        RepetitionKind::ZeroOrMore => Regex::star(inner),
                        RepetitionKind::Range(RepetitionRange::Bounded(i, j)) => Regex::range(inner, i as usize, j as usize),
                        RepetitionKind::Range(RepetitionRange::Exactly(i)) => Regex::range(inner, i as usize, i as usize),
                        _ => panic!("Supported repetition operators [+,*, {{i}}, {{i, j}}]: {:?}", r),
                    }
                },
                HirKind::Anchor(Anchor::StartText) => Regex(G.mk(RegexF::LineStart)),
                HirKind::Anchor(Anchor::EndText) => Regex(G.mk(RegexF::LineEnd)),
                HirKind::Group(g) => to_regex(&g.hir),
                HirKind::Class(Class::Unicode(ranges)) => {
                    let size = ranges
                                 .iter()
                                 .fold(0, |a, r| a + (r.end() as u32 - r.start() as u32));
                    if size > 100 {
                        Regex::dot()
                    } else if size == 0 {
                        Regex::empty()
                    } else {
                        ranges
                            .iter()
                            .flat_map(|a| (a.start()..= a.end()))
                            .map(|a| Regex::character(a))
                            .reduce(Regex::alt)
                            .unwrap_or(Regex::empty())
                    }
                },
                HirKind::Literal(Literal::Unicode(c)) => Regex::character(*c),
                _ => panic!("Unsupported regex {:?}", h),
            }
        }
        match Parser::new().parse(r) {
            Ok(hir) => to_regex(&hir),
            Err(e) => panic!("Error parsing regexp {}", e),
        }
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
            (RegexF::Alt(x, y), _) => Regex::alt(x.clone(), Regex::alt(y.clone(), b)),
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
        assert!(0 < i && i < j, "Range indices {{{}, {}}} must be 0 < {} < {}", i, j, i, j);
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

    pub fn nullable(&self) -> bool {
        match *self.0 {
            RegexF::Nil | RegexF::LineEnd | RegexF::LineStart | RegexF::Star(_) => true,
            RegexF::Empty | RegexF::Char(_) | RegexF::Dot | RegexF::Range(_, _, _) => false,
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

    pub fn deriv(&self, c: &char) -> Regex {
        match *self.0 {
            RegexF::Nil => Regex::empty(),
            RegexF::Empty => Regex::empty(),
            RegexF::Dot => Regex::nil(),
            RegexF::Char(ref x) if x == c => Regex::nil(),
            RegexF::Char(_) => Regex::empty(),
            RegexF::Not(ref r) => Regex::not(r.deriv(c)),
            RegexF::App(ref a, ref b) if *a.0 == RegexF::LineStart => b.deriv(c),
            RegexF::App(ref a, ref b) if *b.0 == RegexF::LineEnd => a.deriv(c),
            RegexF::App(ref a, ref b) if a.nullable() =>
                Regex::alt(Regex::app(a.deriv(c), b.clone()), b.deriv(c)),
            RegexF::App(ref a, ref b) => Regex::app(a.deriv(c), b.clone()),
            RegexF::Alt(ref a, ref b) => Regex::alt(a.deriv(c), b.deriv(c)),
            RegexF::Star(ref a) => Regex::app(a.deriv(c), Regex::star(a.clone())),
            RegexF::Range(ref a, i, j) if i == 1 && j == 1 => a.deriv(c),
            RegexF::Range(ref a, i, j) if i == j => Regex::app(a.deriv(c), Regex::range(a.clone(), i-1, j-1)),
            RegexF::Range(ref a, i, j) => Regex::app(a.deriv(c), Regex::range(a.clone(), i+1, j)),
            RegexF::LineStart | RegexF::LineEnd => panic!("No derivatives for ^, $")
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
