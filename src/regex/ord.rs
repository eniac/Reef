#![allow(missing_docs)]
use crate::regex::{RegexF, RegexF::*};

impl PartialOrd for RegexF {
    fn partial_cmp(&self, other: &RegexF) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Nil, Nil) => Some(std::cmp::Ordering::Equal),
            (Dot, Dot) => Some(std::cmp::Ordering::Equal),
            (RegexF::CharClass(a), RegexF::CharClass(b)) => a.partial_cmp(b),
            (App(ref a, ref b), App(ref c, ref d)) => match a.partial_cmp(c) {
                Some(std::cmp::Ordering::Equal) => b.partial_cmp(d),
                ordering => ordering,
            },
            (Alt(ref a, ref b), Alt(ref c, ref d)) => match a.partial_cmp(c) {
                Some(std::cmp::Ordering::Equal) => b.partial_cmp(d),
                ordering => ordering,
            },
            (And(ref a, ref b), And(ref c, ref d)) => match a.partial_cmp(c) {
                Some(std::cmp::Ordering::Equal) => b.partial_cmp(d),
                ordering => ordering,
            },
            (Range(ref a, ia, ja), Range(ref b, ib, jb)) => match a.partial_cmp(b) {
                Some(std::cmp::Ordering::Equal) => match ia.partial_cmp(ib) {
                    Some(std::cmp::Ordering::Equal) => ja.partial_cmp(jb),
                    ordering => ordering,
                },
                ordering => ordering,
            },
            (Star(ref a), Star(ref b)) => a.partial_cmp(b),
            _ => None,
        }
    }
}

impl Ord for RegexF {
    fn cmp(&self, other: &RegexF) -> std::cmp::Ordering {
        match (self, other) {
            (Nil, Nil) => std::cmp::Ordering::Equal,
            (Dot, Dot) => std::cmp::Ordering::Equal,
            (RegexF::CharClass(a), RegexF::CharClass(b)) => a.cmp(&b),
            (App(ref a, ref b), App(ref c, ref d)) => match a.cmp(c) {
                std::cmp::Ordering::Equal => b.cmp(d),
                ordering => ordering,
            },
            (Alt(ref a, ref b), Alt(ref c, ref d)) => match a.cmp(c) {
                std::cmp::Ordering::Equal => b.cmp(d),
                ordering => ordering,
            },
            (And(ref a, ref b), And(ref c, ref d)) => match a.cmp(c) {
                std::cmp::Ordering::Equal => b.cmp(d),
                ordering => ordering,
            },
            (Range(ref a, ia, ja), Range(ref b, ib, jb)) => match a.cmp(b) {
                std::cmp::Ordering::Equal => match ia.cmp(&ib) {
                    std::cmp::Ordering::Equal => ja.cmp(&jb),
                    ordering => ordering,
                },
                ordering => ordering,
            },
            (Star(ref a), Star(ref b)) => a.cmp(b),
            // Arbitrary order
            (Nil, _) => std::cmp::Ordering::Less,
            (_, Nil) => std::cmp::Ordering::Greater,
            (Dot, _) => std::cmp::Ordering::Less,
            (_, Dot) => std::cmp::Ordering::Greater,
            (RegexF::CharClass(_), _) => std::cmp::Ordering::Less,
            (_, RegexF::CharClass(_)) => std::cmp::Ordering::Greater,
            (App(_, _), _) => std::cmp::Ordering::Less,
            (_, App(_, _)) => std::cmp::Ordering::Greater,
            (Alt(_, _), _) => std::cmp::Ordering::Less,
            (_, Alt(_, _)) => std::cmp::Ordering::Greater,
            (And(_,_), _) => std::cmp::Ordering::Less,
            (_, And(_,_)) => std::cmp::Ordering::Greater,
            (Range(_, _, _), _) => std::cmp::Ordering::Less,
            (_, Range(_, _, _)) => std::cmp::Ordering::Greater,
        }
    }
}
