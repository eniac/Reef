#![allow(dead_code)]
#![allow(missing_docs)]
use core::fmt;
use core::fmt::Formatter;

#[cfg(fuzz)]
pub mod arbitrary;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct CharClass(pub Vec<(char,char)>);

impl fmt::Display for CharClass {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.is_empty() {
            write!(f, "∅")
        } else {
            match self.is_single() {
                Some(c) => write!(f, "{}", c),
                None =>
                    write!(f, "[{}]",
                        self.0.iter()
                              .map(|(a,b)| format!("{}-{}",a,b))
                              .collect::<Vec<_>>()
                              .join(","))
            }
        }
    }
}

impl CharClass {
    /// Nominal constructor
    pub fn new(v: Vec<(char,char)>) -> Self {
        Self(v)
    }
    /// Create a single character
    pub fn single(c: char) -> Self {
        Self(vec![(c,c)])
    }
    /// Empty char class (∅)
    pub fn empty() -> Self {
        Self(vec![])
    }
    /// Create a range of characters
    pub fn range(from: char, to: char) -> Self {
        assert!(from <= to, "Cannot create char range {}-{}", from, to);
        CharClass(vec![(from, to)])
    }

    /// Does it contain character [c]
    pub fn contains(&self, c: &char) -> bool {
        self.0.iter().any(|(a,b)| a <= c && c <= b)
    }

    /// Is it empty (∅)
    pub fn is_empty(&self) -> bool {
        self.0.len() == 0
    }

    /// The union of two character classes
    pub fn union(&self, other: &CharClass) -> CharClass {
        let mut intervals = self.0.clone();
        intervals.append(&mut other.0.clone());

        if intervals.is_empty() {
            return Self::empty();
        }

        let mut intervals = intervals;
        let mut res: Vec<(char,char)> = vec![];

        intervals.sort();

        let mut last = intervals[0].clone();

        for item in intervals.into_iter() {
            if item.0 as u8 > (last.1 as u8 + 1 as u8) {
                res.push(last);
                last = item;
            } else {
                last.1 = item.1.max(last.1);
            }
        }

        res.push(last);
        CharClass(res)
    }

    /// Is it a single character, if yes return it
    pub fn is_single(&self) -> Option<char> {
        if self.0.len() == 1 {
            let h = self.0.iter().next()?;
            if h.0 == h.1 {
                Some(h.0)
            } else { None }
        } else { None }
    }

    /// Total interval of all ranges added together
    pub fn interv_len(&self) -> usize {
       self.0.iter().fold(0, |a, r| a + ((r.1 as usize - r.0 as usize)))
    }
    /// How many intervals in the character class
    pub fn len(&self) -> usize {
        self.0.len()
    }
    /// Compute the complement set (Unicode / self)
    pub fn negate(&self) -> Self {
        let self_v = &self.0;
        let mut v: Vec<(char,char)> = vec![];
        let max_char = std::char::MAX;
        if self_v.len() == 1 {
            let lower = self_v[0].0 as u8;
            let upper = self_v[0].1 as u8;
            if lower == 0 {
                v.push(((upper + 1) as char, max_char));
            } else {
                v.push((0 as char, (lower-1) as char));
                v.push(((upper+1) as char, max_char));
            }
        } else {
            for r in 1..self_v.len() {
                let prev_upper = self_v[r-1].1 as u8;
                let curr_lower = self_v[r].0 as u8;
                //assert_ne!(prev_upper+1, curr_lower-1);
                v.push(((prev_upper+1) as char, (curr_lower-1) as char));
            }
        }
        println!("Negation of ({:?}) => ({:?})", self, v);
        Self(v)
    }
}
