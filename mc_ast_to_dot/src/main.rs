#![deny(missing_debug_implementations, rust_2018_idioms)]

use std::path::PathBuf;
use std::process::exit;

use clap::{value_t, App, Arg};

use mc_common::{input, output};

#[cfg_attr(tarpaulin, skip)]
fn main() {
  let matches = App::new("mC AST to DOT Converter")
    .set_term_width(0)
    .max_term_width(0)
    .about(
      "Utility for printing an abstract syntax tree in the DOT format. The output can be visualised using Graphviz. Errors are reported on invalid inputs."
    )
    .arg(
      Arg::from_usage("-o, --output <out-file> 'output file (defaults to stdout)'").required(false),
    )
    .arg(Arg::from_usage(
      "<file> 'input file (use '-' to read from stdin)'",
    ))
    .get_matches();

  let out_file = value_t!(matches, "output", PathBuf).ok();
  let in_file = value_t!(matches, "file", PathBuf).unwrap();

  let input = input(in_file);
  let output = output(out_file);
  if let Err(exit_code) = mc_ast_to_dot::cli(input, output) {
    exit(exit_code);
  }
}
