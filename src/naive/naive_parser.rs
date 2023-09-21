#![allow(dead_code)]
#![allow(missing_docs)]
use regex_syntax::hir::Hir;
use regex_syntax::hir::HirKind::{Alternation, Class, Concat, Group, Literal, Repetition};
use regex_syntax::hir::Literal::Unicode;
use regex_syntax::hir::RepetitionKind::{OneOrMore, ZeroOrMore};
use regex_syntax::Parser;


pub mod re {
    use hashconsing::{consign, HConsed, HashConsign};

    pub type Regex = HConsed<RegexF>;

    #[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
    pub enum RegexF {
        Nil,
        Empty,
        Dot,
        Char(char),
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

    impl fmt::Display for RegexF {
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
            match &self {
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
    // Smart constructors for regex simplification
    pub fn nil() -> Regex {
        G.mk(RegexF::Nil)
    }

    pub fn empty() -> Regex {
        G.mk(RegexF::Empty)
    }

    pub fn character(c: char) -> Regex {
        G.mk(RegexF::Char(c))
    }

    pub fn dot() -> Regex {
        G.mk(RegexF::Dot)
    }

    pub fn app(a: Regex, b: Regex) -> Regex {
        match (&*a, &*b) {
            (RegexF::App(x, y), _) => app(x.clone(), app(y.clone(), b)),
            (_, RegexF::Nil) => a,
            (RegexF::Nil, _) => b,
            (RegexF::Star(x), RegexF::Star(y)) if *x == *y => a,
            (_, RegexF::Empty) | (RegexF::Empty, _) => empty(),
            (_, _) => G.mk(RegexF::App(a, b)),
        }
    }

    pub fn alt(a: Regex, b: Regex) -> Regex {
        match (&*a, &*b) {
            (x, y) if x == y => a,
            (RegexF::Alt(x, y), _) => alt(x.clone(), alt(y.clone(), b)),
            (RegexF::Not(inner), _) if *inner == empty() => G.mk(RegexF::Not(empty())),
            (RegexF::Empty, _) => b,
            (RegexF::Dot, RegexF::Char(_)) => a,
            (RegexF::Char(_), RegexF::Dot) => b,
            (_, RegexF::Empty) => a,
            (x, y) if y < x => alt(b, a),
            (_, _) => G.mk(RegexF::Alt(a, b)),
        }
    }

    pub fn star(a: Regex) -> Regex {
        match *a {
            RegexF::Star(_) | RegexF::Nil => a,
            RegexF::Empty => nil(),
            _ => G.mk(RegexF::Star(a)),
        }
    }

    pub fn not(a: Regex) -> Regex {
        match &*a {
            RegexF::Not(a) => a.clone(),
            _ => G.mk(RegexF::Not(a)),
        }
    }
}

use re::Regex;

/// Parser based on crate regex-syntax
fn to_regex<'a>(h: &'a Hir, ab: &'a str) -> Regex {
    match h.kind() {
        Concat(l) => l
            .iter()
            .map(|a| to_regex(&a, ab))
            .reduce(re::app)
            .unwrap_or(re::nil()),
        Alternation(l) => l
            .iter()
            .map(|a| to_regex(&a, ab))
            .reduce(re::alt)
            .unwrap_or(re::empty()),
        Repetition(r) => {
            let inner = to_regex(&r.hir, ab);
            match r.kind {
                OneOrMore => re::app(inner.clone(), re::star(inner)),
                ZeroOrMore => re::star(inner),
                _ => panic!("Supported repetition operators [+,*]: {:?}", r),
            }
        }
        Group(g) => to_regex(&g.hir, ab),
        Class(_) => re::dot(),
        Literal(Unicode(c)) => re::character(*c),
        _ => panic!("Unsupported regex {:?}", h),
    }
}

pub fn regex_parser<'a>(r: &'a str, ab: &'a str) -> Regex {
    match Parser::new().parse(r) {
        Ok(hir) => to_regex(&hir, &ab),
        Err(e) => panic!("Error parsing regexp {}", e),
    }
}