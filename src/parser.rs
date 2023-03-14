#![allow(dead_code)]
#![allow(missing_docs)]
use regex_syntax::hir::Hir;
use regex_syntax::hir::HirKind::{Alternation, Class, Concat, Group, Literal, Repetition};
use regex_syntax::hir::Literal::Unicode;
use regex_syntax::hir::RepetitionKind::{OneOrMore, ZeroOrMore};
use regex_syntax::Parser;
use hashconsing::{consign, HConsed, HashConsign};

/// Hash-consed regex terms
#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Regex(HConsed<RegexF>);

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum RegexF {
    Nil,
    Empty,
    Dot,
    Char(String),
    Not(Regex),
    App(Regex, Regex),
    Alt(Regex, Regex),
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
        match *self.0 {
            RegexF::Nil => write!(f, "ε"),
            RegexF::Empty => write!(f, "∅"),
            RegexF::Dot => write!(f, "."),
            RegexF::Char(c) => write!(f, "{}", c),
            RegexF::Not(c) => write!(f, "! {}", c),
            RegexF::App(x, y) => write!(f, "{}{}", x, y),
            RegexF::Alt(x, y) => write!(f, "({} | {})", x, y),
            RegexF::Star(a) => write!(f, "{}*", a)
        }
    }
}

impl Regex {
    fn new<'a>(r: &'a str) -> Self {
        fn to_regex<'a>(h: &'a Hir) -> Regex {
            match h.kind() {
                Concat(l) => l
                    .iter()
                    .map(|a| to_regex(&a))
                    .reduce(Regex::app)
                    .unwrap_or(Regex::nil()),
                Alternation(l) => l
                    .iter()
                    .map(|a| to_regex(&a))
                    .reduce(Regex::alt)
                    .unwrap_or(Regex::empty()),
                Repetition(r) => {
                    let inner = to_regex(&r.hir);
                    match r.kind {
                        OneOrMore => Regex::app(inner.clone(), Regex::star(inner)),
                        ZeroOrMore => Regex::star(inner),
                        _ => panic!("Supported repetition operators [+,*]: {:?}", r),
                    }
                }
                Group(g) => to_regex(&g.hir),
                Class(_) => Regex::dot(),
                Literal(Unicode(c)) => Regex::character(c.to_string()),
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

    pub fn character(c: String) -> Regex {
        Regex(G.mk(RegexF::Char(c.clone())))
    }

    pub fn dot() -> Regex {
        Regex(G.mk(RegexF::Dot))
    }

    pub fn app(a: Regex, b: Regex) -> Regex {
        match (*a.0, *b.0) {
            (RegexF::App(x, y), _) => Regex::app(x.clone(), Regex::app(y.clone(), b)),
            (_, RegexF::Nil) => a,
            (RegexF::Nil, _) => b,
            (RegexF::Star(x), RegexF::Star(y)) if x.0 == y.0 => a,
            (_, RegexF::Empty) | (RegexF::Empty, _) => Regex::empty(),
            (_, _) => Regex(G.mk(RegexF::App(a, b))),
        }
    }

    pub fn alt(a: Regex, b: Regex) -> Regex {
        match (*a.0, *b.0) {
            (x, y) if x == y => a,
            (RegexF::Alt(x, y), _) => Regex::alt(x.clone(), Regex::alt(y.clone(), b)),
            (RegexF::Not(inner), _) if *inner.0 == RegexF::Empty => Regex(G.mk(RegexF::Not(Regex::empty()))),
            (RegexF::Empty, _) => b,
            (RegexF::Dot, RegexF::Char(_)) => a,
            (RegexF::Char(_), RegexF::Dot) => b,
            (_, RegexF::Empty) => a,
            (x, y) if y < x => Regex::alt(b, a),
            (_, _) => Regex(G.mk(RegexF::Alt(a, b))),
        }
    }

    pub fn star(a: Regex) -> Regex {
        match *a.0 {
            RegexF::Star(_) | RegexF::Nil => a,
            RegexF::Empty => Regex::nil(),
            _ => Regex(G.mk(RegexF::Star(a))),
        }
    }

    pub fn not(a: Regex) -> Regex {
        match *a.0 {
            RegexF::Not(a) => a.clone(),
            _ => Regex(G.mk(RegexF::Not(a))),
        }
    }
}

