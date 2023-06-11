#![allow(missing_docs)]
use crate::regex::{CharClass, RegexF, RegexF::*};

impl Ord for CharClass {
    fn cmp(&self, other: &CharClass) -> std::cmp::Ordering {
        if self.is_empty() && other.is_empty() {
            std::cmp::Ordering::Equal
        } else {
            for x in self.0.iter() {
                for y in other.0.iter() {
                    let r0 = x.0.cmp(&y.0);
                    let r1 = x.1.cmp(&y.1);
                    if r0 != std::cmp::Ordering::Equal {
                        return r0;
                    } else if r1 != std::cmp::Ordering::Equal {
                        return r1;
                    }
                }
            }
            std::cmp::Ordering::Equal
        }
    }
}

impl PartialOrd for CharClass {
    fn partial_cmp(&self, other: &CharClass) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialOrd for RegexF {
    fn partial_cmp(&self, other: &RegexF) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Nil, Nil) => Some(std::cmp::Ordering::Equal),
            (Dot, Dot) => Some(std::cmp::Ordering::Equal),
            (RegexF::CharClass(a), RegexF::CharClass(b)) => a.partial_cmp(b),
            (Not(ref a), Not(ref b)) => a.partial_cmp(b),
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
            (Not(ref a), Not(ref b)) => a.cmp(b),
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
            (Not(_), _) => std::cmp::Ordering::Less,
            (_, Not(_)) => std::cmp::Ordering::Greater,
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
