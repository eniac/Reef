use crate::parser::re::{self, Regex, RegexF};
use crate::dfa::DFA;

pub fn nullable(r: &Regex) -> bool {
    match &**r {
        RegexF::Nil | RegexF::Star(_) => true,
        RegexF::Empty | RegexF::Char(_) => false,
        RegexF::Not(ref r) => !nullable(r),
        RegexF::App(ref a, ref b) => nullable(a) && nullable(b),
        RegexF::Alt(ref a, ref b) => nullable(a) || nullable(b),
    }
}

pub fn deriv(c: char, r: &Regex) -> Regex {
    match &**r {
        RegexF::Nil => re::empty(),
        RegexF::Empty => re::empty(),
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

/// Top level, generate a DFA using derivatives [Owens et al. 06]
pub fn mk_dfa(q: &Regex, ab: &String, d: &mut DFA) {
    // Add to DFA if not already there
    d.add_state(q);

    // Explore derivatives
    for c in ab.chars() {
        let q_c = deriv(c, q);
        d.add_transition(q, c, &q_c);
        if d.contains_state(&q_c) {
            continue;
        } else {
            mk_dfa(&q_c, ab, d);
        }
    }
}
