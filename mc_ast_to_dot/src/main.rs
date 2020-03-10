#![deny(missing_debug_implementations, rust_2018_idioms)]

use std::fs::File;
use std::io::stdout;

use clap::{value_t, App, Arg};
use mc_ast_to_dot::mc_ast_to_dot;

fn main() -> std::io::Result<()> {
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

  let out_file = value_t!(matches, "output", String).ok();
  let in_file = value_t!(matches, "file", String).unwrap();

  if let Some(out_file) = out_file.map(File::create) {
    mc_ast_to_dot(in_file, out_file?)
  } else {
    mc_ast_to_dot(in_file, stdout())
  }
}
