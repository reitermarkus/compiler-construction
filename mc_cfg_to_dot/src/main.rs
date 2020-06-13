#![deny(missing_debug_implementations, rust_2018_idioms)]

use std::fs::File;
use std::io::stdout;

use clap::{value_t, App, Arg};

use mc_cfg_to_dot::mc_cfg_to_dot;

#[cfg_attr(tarpaulin, skip)]
fn main() -> std::io::Result<()> {
  let matches = App::new("mC CFG to DOT Converter")
    .set_term_width(0)
    .max_term_width(0)
    .about(
      "Utility for printing a control flow graph in the DOT format. The output can be visualised using graphviz. Errors are reported on invalid inputs."
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
    mc_cfg_to_dot(in_file, out_file?)
  } else {
    mc_cfg_to_dot(in_file, stdout())
  }
}