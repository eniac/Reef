use reef::backend::costs::*;
use reef::backend::framework::*;
use reef::backend::r1cs::init;
use reef::dfa::NFA;
use reef::regex::Regex;

use criterion::*;
use itertools::Itertools;

static MICRO_REGEX: [&'static str; 4] = [".*ab", "(a|b)*c", "a{5}", "[a-z]*"];
static MICRO_AB: &'static str = "abcdefghijklmnopqrstuvwxyz";
static MICRO_DOC: [&'static str; 8] = [
    "aaaaaab", "abababac", "d", "", "dddd", "aaaaa", "y", "helloab",
];
static MAX_K: usize = 4;
static MAX_BATCH: usize = 4;

fn regex_parser(c: &mut Criterion) {
    let mut group = c.benchmark_group("regex_parser");
    group.sample_size(10);

    for rstr in MICRO_REGEX.iter() {
        group.bench_with_input(BenchmarkId::from_parameter(rstr), rstr, |b, &rstr| {
            b.iter(|| Regex::new(rstr));
        });
    }
    group.finish();
}

fn nfa_compiler(c: &mut Criterion) {
    let mut group = c.benchmark_group("nfa_compiler");
    group.sample_size(10);
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
    group.sampling_mode(SamplingMode::Flat).sample_size(10);

    for (rstr, doc) in MICRO_REGEX.iter().cartesian_product(MICRO_DOC) {
        let nfa = NFA::new(&MICRO_AB[..], Regex::new(rstr));
        let d = doc.chars().map(|c| c.to_string()).collect();

        group.bench_with_input(
            BenchmarkId::from_parameter(format!("{} @ {}", rstr, doc)),
            &(nfa, d),
            |b, (nfa, doc)| {
                b.iter(|| nfa.is_match(doc));
            },
        );
    }
    group.finish();
}

fn nfa_kstride_compiler(c: &mut Criterion) {
    let mut group = c.benchmark_group("nfa_kstride_compiler");
    group.sampling_mode(SamplingMode::Flat).sample_size(10);
    for (rstr, doc) in MICRO_REGEX.iter().cartesian_product(MICRO_DOC) {
        let d: Vec<String> = doc.chars().map(|c| c.to_string()).collect();

        for k in 1..MAX_K {
            group.bench_with_input(
                BenchmarkId::from_parameter(format!("{} @ {} with k = {}", rstr, d.join(""), k)),
                &k,
                |b, &k| {
                    b.iter(|| NFA::new(&MICRO_AB[..], Regex::new(rstr)).k_stride(k, &d));
                },
            );
        }
    }
    group.finish();
}

fn nfa_kstride_matcher(c: &mut Criterion) {
    let mut group = c.benchmark_group("nfa_kstride_matcher");
    group.sampling_mode(SamplingMode::Flat).sample_size(10);
    for (rstr, doc) in MICRO_REGEX.iter().cartesian_product(MICRO_DOC) {
        for k in 1..MAX_K {
            let mut d: Vec<String> = doc.chars().map(|c| c.to_string()).collect();
            let mut new_re = "^".to_owned();
            new_re.push_str(rstr);
            new_re.push_str("$");
            let mut nfa = NFA::new(&MICRO_AB[..], Regex::new(&new_re));
            d = nfa.k_stride(k, &d);
            group.bench_with_input(
                BenchmarkId::from_parameter(format!("{} @ {} with k = {}", rstr, doc, k)),
                &k,
                |b, &_k| {
                    b.iter(|| nfa.is_match(&d));
                },
            );
        }
    }
    group.finish();
}

fn prove_verify(c: &mut Criterion) {
    let mut group = c.benchmark_group("prove");
    for (rstr, doc) in MICRO_REGEX.iter().cartesian_product(MICRO_DOC) {
        let nfa = NFA::new(&MICRO_AB[..], Regex::new(rstr));
        let d = doc.chars().map(|c| c.to_string()).collect();
        nfa.well_formed(&d);

        let eval_type = Some(JBatching::Nlookup);
        let commit_type = Some(JCommit::Nlookup);

        init();

        group.sampling_mode(SamplingMode::Flat).sample_size(10);
        for batch_size in 1..MAX_BATCH {
            group.throughput(Throughput::Bytes(batch_size as u64));
            // Less sampling, we are testing many inputs here
            group.bench_with_input(
                BenchmarkId::from_parameter(format!(
                    "{} @ {} (NLOOKUP, batch_size = {})",
                    rstr, doc, batch_size
                )),
                &batch_size,
                |b, &batch_size| {
                    b.iter(|| run_backend(&nfa, &d, eval_type, commit_type, batch_size));
                },
            );
        }
    }
    group.finish();
}

criterion_group!(compiler, regex_parser, nfa_compiler, nfa_kstride_compiler);
criterion_group!(solver, nfa_matcher, nfa_kstride_matcher, prove_verify);
criterion_group!(backend, prove_verify);
criterion_main!(compiler, solver, backend);
