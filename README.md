
[![CircleCI](https://circleci.com/gh/elefthei/rezk.svg?style=svg&circle-token=88c4900395a0fc7ac7d9d63b3186d31c9d840ef2)](https://app.circleci.com/pipelines/github/elefthei/rezk?branch=main&circle-token=88c4900395a0fc7ac7d9d63b3186d31c9d840ef2)

# Reef

This is an implementation of Reef, a system for generating zero-knowledge proofs that a committed document matches or does not match a regular expression.
The details of Reef are described in our paper: [Reef: Fast Succinct Non-Interactive Zero-Knowledge Regex Proofs](https://eprint.iacr.org/2023/1886).

## Compile

```
cargo build
```

With metrics:
```
cargo build --feature metrics
```

## Usage
```
Usage: reef [OPTIONS] <--commit|--prove|--verify|--e2e> [ALPHABET]

Alphabet:
  ascii  Accepts ASCII regular-expressions and documents
  utf8   Accepts UTF8 regular-expressions and documents
  dna    Accepts DNA base ASCII files
  help   Print this message or the help of the given subcommand(s)

Options:
      --commit
      --prove
      --verify
      --e2e
  -f, --file-name <FILE>    Optional name for .cmt and .proof files
  -d, --doc <FILE>
      --metrics <FILE>      Metrics and other output information
  -r, --re <RE>             Perl-style regular expression
  -b, --batch-size <USIZE>  Batch size (override auto select) [default: 0]
  -p, --projections         Use document projections
  -y, --hybrid              Use hybrid nlookup
  -m, --merkle              Use merkle tree for document commitment
  -n, --negate              Negate the match result
  -h, --help                Print help
  -V, --version             Print version
```

There are four different "parties" that can run reef. They all require an
`alphabet` mode. Running `--commit` requires `--doc`. Running `--prove` (or
`--e2e`) requires `--doc` and `--re`. Running `--verify` only requires `--re`.
It's important that each party uses the same alphabet, document, and regular
expression.

A good starting point is to generate the proof that `aaaaaaaab` matches the regex `.*b`.
```
$ echo aaaaaaaab > document.txt
$ reef -d document.txt --commit ascii
$ reef -d document.txt -r ".*b" --prove ascii
$ reef -r ".*b" --verify ascii
```
Note that you can use the same document commitment to generate proofs for
multiple different regexes.

Or another example, with metrics and end-to-end running.
```
$ echo "hello world happy to be here" > hello.txt
$ reef -d hello.txt --metrics metrics.txt -r "hello.*" --e2e ascii
```

## Reproducing Baseline Results
If you're interested in reproducing our baseline results (DFA and DFA with recursion), you'll need to checkout the branch reef_with_baselines and build as follows: 

For DFA 
```
cargo build --feature naive
```

For DFA with Recursion
```
cargo build --feature nwr
```

Thank you for using Reef,
Happy proving!
