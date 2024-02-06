
[![CircleCI](https://circleci.com/gh/elefthei/rezk.svg?style=svg&circle-token=88c4900395a0fc7ac7d9d63b3186d31c9d840ef2)](https://app.circleci.com/pipelines/github/elefthei/rezk?branch=main&circle-token=88c4900395a0fc7ac7d9d63b3186d31c9d840ef2)

# Reef

This is an implementation of Reef, a system for generating zero-knowledge proofs that a committed document matches or does not match a regular expression.
The details of Reef are described in our paper: [Reef: Fast Succinct Non-Interactive Zero-Knowledge Regex Proofs](https://eprint.iacr.org/2023/1886).

## Compile

```
cargo build --release
```

With metrics:
```
cargo build --release --features metrics
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
      --cmt-name <FILE>     Optional name for .cmt file
      --proof-name <FILE>   Optional name for .proof file
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
It's important that each party uses the same alphabet, document, regular
expression, and merkle/projection/hybrid flags (when appropriate).

Note that you can use `--cmt-name` and `--proof-name` to choose names for your
commitment and proof files. This is optional - Reef will choose a name for the
commitment/proof based on the document/regex if you do not - except in the case of
verification, when you are required to specify the commitment file name
(verification does not read the document).

A good starting point is to generate the proof that `aaaaaaaab` matches the regex `.*b`.
```
$ echo aaaaaaaab > document
$ reef -d document --commit ascii
$ reef -d document -r ".*b" --prove ascii
$ reef -r ".*b" --verify --cmt-name document.cmt ascii
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
cargo build --release --features naive
```

For DFA with Recursion
```
cargo build --release --features nwr
```

Thank you for using Reef,
Happy proving!
