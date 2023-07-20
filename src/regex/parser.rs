use fancy_regex::{Expr, LookAround};
use hashconsing::HashConsign;
use regex_syntax::hir::{Class, HirKind, Literal};
use crate::regex::{RegexF, Regex, re, G};

pub struct RegexParser();
impl RegexParser {
    /// Read a string to a regex
    pub fn parse<'a>(rstr: &'a str) -> Regex {
        Self::to_regex_top(&Expr::parse_tree(rstr).unwrap().expr).unwrap()
    }

    /// Preprocessing regex for exact match
    /// ^r$ -> r
    /// r$  -> .*r
    /// ^r  -> ^r.*
    /// r   -> .*r.*
    fn to_regex_top(e: &Expr) -> Result<Regex, String> {
        match e {
            Expr::Concat(l) => {
                let mut inner = Self::to_regex(e.clone())?;
                if let Some(e) = l.get(0) {
                    match e {
                        Expr::StartLine | Expr::StartText => (),
                        _ => inner = re::app(re::dotstar(), inner),
                    }
                }

                if let Some(e) = l.get(l.len() - 1) {
                    match e {
                        Expr::EndLine | Expr::EndText => (),
                        _ => inner = re::app(inner, re::dotstar()),
                    }
                }
                Ok(inner)
            }
            Expr::Group(g) => Self::to_regex_top(&g),
            _ => Ok(re::app(re::dotstar(),
                        re::app(Self::to_regex(e)?, re::dotstar()))),
        }
    }

    fn shallow_app(a: &Expr, b: RegexF) -> Result<RegexF, String> {
        match a {
            Expr::LookAround(g, LookAround::LookAhead) =>
                Ok(RegexF::And(Self::to_regex(g)?, G.mk(b))),
            Expr::LookAround(g, LookAround::LookBehind) =>
                Ok(RegexF::App(Self::to_regex(g)?, G.mk(b))),
            Expr::Group(g) => Self::shallow_app(g, b),
            _ => Ok(RegexF::App(Self::to_regex(a)?, G.mk(b)))
        }
    }

    fn to_regex(e: &Expr) -> Result<Regex, String> {
        fn try_fold_right<F>(v: &Vec<Expr>, init: RegexF, f: F) -> Result<Regex, String>
            where F: Fn(&Expr, RegexF)-> Result<RegexF, String> {
            let mut acc : RegexF = init.clone();

            for r in v.iter().rev() {
                match f(&r, acc) {
                    Ok(v) => { acc = v; },
                    Err(er) => { return Err(er); }
                }
            }
            Ok(G.mk(acc))
        }

        match e {
            Expr::Empty => Ok(re::empty()),
            Expr::Any { .. } => Ok(re::dot()),
            Expr::StartText | Expr::StartLine | Expr::EndText | Expr::EndLine => {
                Ok(re::nil())
            }
            Expr::Literal { val, .. } => val.chars().try_fold(re::nil(), |acc, a| {
                Ok(G.mk(RegexF::App(acc, re::character(a))))
            }),
            Expr::Concat(l) =>
                try_fold_right(l, RegexF::nil(), Self::shallow_app),
            Expr::Alt(l) =>
                try_fold_right(l, RegexF::empty(),
                    |e, acc| Ok(RegexF::Alt(Self::to_regex(e)?, G.mk(acc)))),
            Expr::Repeat { child, lo, hi, .. } if *lo == 0 && *hi == usize::MAX => {
                Ok(G.mk(RegexF::Star(Self::to_regex(&child)?)))
            }
            Expr::Repeat { child, lo, hi, .. } if *hi == usize::MAX => {
                let inner = &Self::to_regex(child)?;
                Ok(G.mk(RegexF::App(G.mk(RegexF::repeat(inner, *lo)), G.mk(RegexF::Star(inner.clone())))))
            }
            Expr::Repeat { child, lo, hi, .. } => Ok(G.mk(RegexF::Range(Self::to_regex(child)?, *lo, *hi))),
            Expr::Group(g) => Self::to_regex(&g),
            Expr::LookAround(g, LookAround::LookAhead) => Self::to_regex(g),
            Expr::LookAround(g, LookAround::LookBehind) => Self::to_regex(g),
            Expr::Delegate { inner, .. } => {
                let re = regex_syntax::Parser::new().parse(inner).unwrap();
                match re.kind() {
                    HirKind::Class(Class::Unicode(ranges)) =>
                        Ok(G.mk(
                          RegexF::charclass(
                            ranges.ranges()
                                  .into_iter()
                                  .map(|s| if s.end() == '\u{10ffff}' {
                                      (s.start(), None)
                                    } else {
                                      (s.start(), Some(s.end()))
                                    }).collect()))),
                    HirKind::Literal(Literal::Unicode(c)) => Ok(re::character(*c)),
                    _ => Err(format!("Unsupported regex (regex_syntax) {:#?}", re.kind())),
                }
            }
            _ => Err(format!("Unsupported regex (fancy_regex) {:#?}", e)),
        }
    }

}

