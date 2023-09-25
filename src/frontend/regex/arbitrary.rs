#![allow(missing_docs)]
use crate::regex::Regex;

use arbitrary::{Result, Arbitrary, Unstructured};

impl<'a> Arbitrary<'a> for Regex {
    fn arbitrary(g: &mut Unstructured<'a> ) -> Result<Self> {
        // Generate a random index for the enum variant
        let i = g.int_in_range(0..=8)?;
        let mut r = match i {
            0 => Regex::nil(),
            1 => Regex::empty(),
            2 => Regex::dot(),
            3 => Regex::character(*g.choose(&('a'..='z').collect::<Vec<_>>()).unwrap()),
            4 => Regex::not(Regex::arbitrary(g)?),
            5 => Regex::app(Regex::arbitrary(g)?, Regex::arbitrary(g)?),
            6 => Regex::alt(Regex::arbitrary(g)?, Regex::arbitrary(g)?),
            7 => {
                let start = g.int_in_range(0..=10)?;
                let end = g.int_in_range(start..=100)?;
                Regex::range(Regex::arbitrary(g)?, start, end)
            },
            8 => Regex::star(Regex::arbitrary(g)?),
            _ => unreachable!(),
        };

        // Fixed start
        if bool::arbitrary(g)? {
            r = Regex::app(Regex::line_start(), r);
        }
        // Fixed end
        if bool::arbitrary(g)? {
            r = Regex::app(r, Regex::line_end());
        }
        println!("CREATED {}", r);
        Ok(r)
    }
}
