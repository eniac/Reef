use regex_syntax::Parser;
use regex_syntax::hir::Hir;

use structopt::StructOpt;
use std::path::PathBuf;

use std::fmt::Display;

fn regex_parser(r: &str) -> Hir {
    Parser::new().parse(r).unwrap()
}

fn backend_parser(a: &str) -> Backend {
    if a == "nova" || a == "Nova" || a == "n" {
            Backend::Nova
    } else if a == "spartan" || a == "Spartan" || a == "n" {
            Backend::Spartan
    } else {
            panic!("Unknown backend option {}", a)
    }
}

#[derive(Debug, StructOpt)]
#[structopt(name = "rezk", about = "Rezk: The regex to circuit compiler")]
struct Options {
    /// regular expression
    #[structopt(short = "r", long = "regex", parse(from_str = regex_parser))]
    regex: Hir,

    #[structopt(short = "i", long = "input", parse(from_os_str))]
    input: PathBuf,

    #[structopt(long = "r1cs", default_value, parse(from_str = backend_parser))]
    backend: Backend,
}

#[derive(Debug, Default, enum_display_derive::Display)]
enum Backend {
    /// Nova (hide recursion length)
    #[default]
    Nova,
    /// Spartan R1CS back-end (public doc length)
    Spartan
}

fn main() {
  let opt = Options::from_args();

  println!("{}", opt.regex);
}
