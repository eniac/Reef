use crate::naive::naive_parser::re::{self, Regex, RegexF};

pub fn nullable(r: &Regex) -> bool {
    match &**r {
        RegexF::Nil | RegexF::Star(_) => true,
        RegexF::Empty | RegexF::Char(_) | RegexF::Dot => false,
        RegexF::Not(ref r) => !nullable(r),
        RegexF::App(ref a, ref b) => nullable(a) && nullable(b),
        RegexF::Alt(ref a, ref b) => nullable(a) || nullable(b),
    }
}

pub fn deriv(c: char, r: &Regex) -> Regex {
    match &**r {
        RegexF::Nil => re::empty(),
        RegexF::Empty => re::empty(),
        RegexF::Dot => re::nil(),
        RegexF::Char(x) if *x == c => re::nil(),
        RegexF::Char(_) => re::empty(),
        RegexF::Not(ref r) => re::not(deriv(c, r)),
        RegexF::App(ref a, ref b) if nullable(a) => {
            re::alt(re::app(deriv(c, a), b.clone()), deriv(c, b))
        }
        RegexF::App(ref a, ref b) => re::app(deriv(c, a), b.clone()),
        RegexF::Alt(ref a, ref b) => re::alt(deriv(c, a), deriv(c, b)),
        RegexF::Star(ref a) => re::app(deriv(c, a), re::star(a.clone())),
    }
}