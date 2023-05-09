[![CircleCI](https://dl.circleci.com/status-badge/img/gh/elefthei/rezk/tree/main.svg?style=svg)](https://dl.circleci.com/status-badge/redirect/gh/elefthei/rezk/tree/main)

# Reef

## Authors
- Lef Ioannidis `elefthei at seas.upenn.edu`
- Eli Margolin `ecmargo at seas.upenn.edu`
- Jess Woods `jkwoods at seas.upenn.edu`

## Description

A zero-knowledge regular expression matching scheme based on polynomials.

## Useage

There are four subcommands in Reef.
```
Usage: reef <COMMAND>

Commands:
  ascii  Accepts ASCII regular-expressions and documents
  utf8   Accepts UTF8 regular-expressions and documents
  dna    Accepts DNA base encoded binary files (2-bits/base)
  auto   Infer the smallest alphabet that works from the regular expression and document
  help   Print this message or the help of the given subcommand(s)

Options:
  -h, --help     Print help
  -V, --version  Print version
```

A good starting point is to generate the proof that `aaaaaaaab` matches the regex `.*b`.

```
$ echo aaaaaaaab > input.txt
$ reef auto -i input.txt -r ".*b"
```

For ASCII and UTF8 documents, Reef supports any subset of the following rules

- `ignore-whitespace` ignore space, tabs, carriage returns and newlines in the input document.
- `alpha-numeric` reduce the alphabet to the alphanumeric charset of ASCII.
- `case-insensitive` ignore upper/lowercasing in the document (regex must be uppercase).

For example, Reef runs all the rules in an input with mixed casing, whitespace, alphanumeric characters

```
$ echo -n "aA\tb" > input.txt
$ reef ascii -t ignore-whitespace,alpha-numeric,case-insensitive -i input.txt -r ".*B"
```

or another example
```
$ echo "hello world happy to be here" > hello.txt
$ reef ascii -t ignore-whitespace,alpha-numeric -i hello.txt -r "hello.*"
```

Thank you for using Reef,
Happy proving!
