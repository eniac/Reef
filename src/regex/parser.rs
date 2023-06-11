use fancy_regex::{Expr, LookAround};
use regex_syntax::hir::{Class, HirKind, Literal};
use crate::regex::RegexF;

pub struct RegexParser();
impl RegexParser {
    /// Read a string to a regex
    pub fn parse<'a>(rstr: &'a str) -> RegexF {
        Self::to_regex_top(&Expr::parse_tree(rstr).unwrap().expr).unwrap()
    }

    /// Preprocessing regex for exact match
    /// ^r$ -> r
    /// r$  -> .*r
    /// ^r  -> ^r.*
    /// r   -> .*r.*
    fn to_regex_top(e: &Expr) -> Result<RegexF, String> {
        match e {
            Expr::Concat(l) => {
                let mut inner = Self::to_regex(e.clone())?;
                if let Some(e) = l.get(0) {
                    match e {
                        Expr::StartLine | Expr::StartText => (),
                        _ => inner = RegexF::app(&RegexF::dotstar(), &inner),
                    }
                }

                if let Some(e) = l.get(l.len() - 1) {
                    match e {
                        Expr::EndLine | Expr::EndText => (),
                        _ => inner = RegexF::app(&inner, &RegexF::dotstar()),
                    }
                }
                Ok(inner)
            }
            Expr::Group(g) => Self::to_regex_top(&g),
            _ => Ok(RegexF::app(
                &RegexF::app(&RegexF::dotstar(), &Self::to_regex(e)?),
                &RegexF::dotstar(),
            )),
        }
    }

    fn shallow_app(a: &Expr, b: &RegexF) -> Result<RegexF, String> {
        match a {
            Expr::LookAround(g, LookAround::LookAhead) =>
                Ok(RegexF::and(&Self::to_regex(g)?, b)),
            Expr::LookAround(g, LookAround::LookBehind) =>
                Ok(RegexF::app(&Self::to_regex(g)?, b)),
            Expr::LookAround(g, LookAround::LookAheadNeg) =>
                Ok(RegexF::and(&RegexF::not(&Self::to_regex(g)?), b)),
            Expr::LookAround(g, LookAround::LookBehindNeg) =>
                Ok(RegexF::app(&RegexF::not(&Self::to_regex(g)?), b)),
            Expr::Group(g) => Self::shallow_app(g, b),
            _ => Ok(RegexF::app(&Self::to_regex(a)?, b))
        }
    }

    fn to_regex(e: &Expr) -> Result<RegexF, String> {
        fn try_fold_right<F>(v: &Vec<Expr>, init: &RegexF, f: F) -> Result<RegexF, String>
            where F: Fn(&Expr, &RegexF)-> Result<RegexF, String> {
            let mut acc : RegexF = init.clone();

            for r in v.iter().rev() {
                match f(&r, &acc) {
                    Ok(v) => { acc = v; },
                    Err(er) => { return Err(er); }
                }
            }
            Ok(acc)
        }

        match e {
            Expr::Empty => Ok(RegexF::empty()),
            Expr::Any { .. } => Ok(RegexF::dot()),
            Expr::StartText | Expr::StartLine | Expr::EndText | Expr::EndLine => {
                Ok(RegexF::nil())
            }
            Expr::Literal { val, .. } => val.chars().try_fold(RegexF::nil(), |acc, a| {
                Ok(RegexF::app(&acc, &RegexF::character(a)))
            }),
            Expr::Concat(l) =>
                try_fold_right(l, &RegexF::nil(), Self::shallow_app),
            Expr::Alt(l) =>
                try_fold_right(l, &RegexF::empty(),
                    |e, acc| Ok(RegexF::alt(&Self::to_regex(e)?,acc))),
            Expr::Repeat { child, lo, hi, .. } if *lo == 0 && *hi == usize::MAX => {
                Ok(RegexF::star(&Self::to_regex(&*child)?))
            }
            Expr::Repeat { child, lo, hi, .. } if *hi == usize::MAX => {
                let inner = &Self::to_regex(child)?;
                Ok(RegexF::app(&inner.repeat(*lo), &RegexF::star(inner)))
            }
            Expr::Repeat { child, lo, hi, .. } => Ok(RegexF::range(&Self::to_regex(child)?, *lo, *hi)),
            Expr::Group(g) => Self::to_regex(&g),
            Expr::LookAround(g, LookAround::LookAhead) => Self::to_regex(g),
            Expr::LookAround(g, LookAround::LookBehind) => Self::to_regex(g),
            Expr::LookAround(g, LookAround::LookAheadNeg) => Self::to_regex(g),
            Expr::LookAround(g, LookAround::LookBehindNeg) => Self::to_regex(g),
            Expr::Delegate { inner, .. } => {
                let re = regex_syntax::Parser::new().parse(inner).unwrap();
                match re.kind() {
                    HirKind::Class(Class::Unicode(ranges)) =>
                        Ok(RegexF::charclass(
                            ranges.ranges()
                                  .into_iter()
                                  .map(|s| (s.start(), s.end()))
                                  .collect())),
                    HirKind::Literal(Literal::Unicode(c)) => Ok(RegexF::character(*c)),
                    _ => Err(format!("Unsupported regex (regex_syntax) {:#?}", re.kind())),
                }
            }
            _ => Err(format!("Unsupported regex (fancy_regex) {:#?}", e)),
        }
    }

}

