#![deny(missing_debug_implementations, rust_2018_idioms)]

use clap::{value_t, App, Arg};

fn main() {
  let matches = App::new("mC IR Viewer")
    .set_term_width(0)
    .max_term_width(0)
    .about("Utility for viewing the generated intermediate representation. Errors are reported on invalid inputs.")
    .arg(Arg::from_usage("-o, --output <out-file> 'output file (defaults to stdout)'").required(false))
    .arg(Arg::from_usage("<file> 'input file (use '-' to read from stdin)'"))
    .get_matches();

  let _out_file = value_t!(matches, "output", String).ok();
  let _in_file = value_t!(matches, "file", String).unwrap();
}
