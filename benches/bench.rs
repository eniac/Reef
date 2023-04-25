use reef::regex::Regex;
use reef::dfa::NFA;

use itertools::Itertools;
use criterion::*;

static MICRO_REGEX : [&'static str; 4] = [ ".*ab", "(a|b)*c", "a{5}", "[a-z]*" ];
static MICRO_AB : &'static str = "abcdefghijklmnopqrstuvwxyz ";
static MICRO_DOC: [&'static str; 8] = [ "aaaaaab", "abababac", "d", "", "dddd", "aaaaa", "y", "hello ab"];

fn regex_parser(c: &mut Criterion) {

    let mut group = c.benchmark_group("regex_parser");
    for rstr in MICRO_REGEX.iter() {
        group.bench_with_input(BenchmarkId::from_parameter(rstr), rstr, |b, &rstr| {
            b.iter(|| Regex::new(rstr));
        });
    }
    group.finish();
}

fn nfa_compiler(c: &mut Criterion) {
    let mut group = c.benchmark_group("nfa_compiler");
    for rstr in MICRO_REGEX.iter() {
        let re = &Regex::new(rstr);
        group.bench_with_input(BenchmarkId::from_parameter(rstr), re, |b, re| {
            b.iter(|| NFA::new(&MICRO_AB[..], re.clone()));
        });
    }
    group.finish();
}

fn nfa_matcher(c: &mut Criterion) {
    let mut group = c.benchmark_group("nfa_matcher");
    for (rstr, doc) in MICRO_REGEX.iter().cartesian_product(MICRO_DOC) {
        let nfa = NFA::new(&MICRO_AB[..], Regex::new(rstr));
        let d = doc.chars().map(|c|c.to_string()).collect();

        group.bench_with_input(BenchmarkId::from_parameter(format!("{} @ {}", rstr, doc)), &(nfa, d), |b, (nfa, doc)| {
            b.iter(|| nfa.is_match(doc));
        });
    }
    group.finish();
}


criterion_group!(benches, regex_parser, nfa_compiler, nfa_matcher);
criterion_main!(benches);

