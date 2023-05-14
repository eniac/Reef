#![no_main]
use arbitrary::{Unstructured, Arbitrary};
use libfuzzer_sys::fuzz_target;
use reef::regex::Regex;
use reef::regex::arbitrary::*;

/// a < b == true <-> b > a == false
fuzz_target!(|data: &[u8]| {
    let mut u = Unstructured::new(data);
    let a = Arbitrary::arbitrary(&mut u).unwrap();
    let b = Arbitrary::arbitrary(&mut u).unwrap();

    if let Some(x) = Regex::partial_le(&a, &b) {
        if a != b {
            assert_eq!(Regex::partial_le(&b, &a), Some(!x), "Expected {} < {}", a, b)
        }
    } else {
        assert_eq!(Regex::partial_le(&b, &a), None, "No ordering between {}, {}", a, b)
    }
});

