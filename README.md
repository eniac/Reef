
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
Usage: reef [OPTIONS] --input <FILE> --output <FILE> --re <RE> <COMMAND>

Commands:
  ascii  Accepts ASCII regular-expressions and documents
  utf8   Accepts UTF8 regular-expressions and documents
  dna    Accepts DNA base ASCII files
  help   Print this message or the help of the given subcommand(s)

Options:
  -i, --input <FILE>
  -o, --output <FILE>
  -r, --re <RE>             Perl-style regular expression
  -b, --batch-size <USIZE>  Batch size (override auto select) [default: 0]
  -p, --projections         Use document projections
  -y, --hybrid              Use hybrid nlookup
  -m, --merkle              Use merkle tree for document commitment
  -n, --negate              Negate the match result
  -h, --help                Print help
  -V, --version             Print version
```

A good starting point is to generate the proof that `aaaaaaaab` matches the regex `.*b`.

```
$ echo aaaaaaaab > input.txt
$ reef -i input.txt -o metrics.txt -r ".*b" ascii
```

or another example
```
$ echo "hello world happy to be here" > hello.txt
$ reef -i hello.txt -o metrics.txt -r "hello.*" ascii
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
