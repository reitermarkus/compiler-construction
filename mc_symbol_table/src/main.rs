#![deny(missing_debug_implementations, rust_2018_idioms)]

use std::fs::File;
use std::io::{self, stdin, stdout, Read, Write};
use std::path::{Path, PathBuf};
use std::process::exit;

use clap::{value_t, App, Arg};
use either::Either;

fn input(in_file: PathBuf) -> impl Read {
  if in_file == Path::new("-") {
    Either::Left(stdin())
  } else {
    match File::open(&in_file) {
      Ok(in_file) => Either::Right(in_file),
      Err(err) => {
        eprintln!("Error opening input file {:?}:", in_file);
        eprintln!("{}", err);
        exit(1);
      }
    }
  }
}

fn output(out_file: Option<PathBuf>) -> impl Write {
  if let Some(out_file) = out_file {
    match File::create(&out_file) {
      Ok(out_file) => Either::Right(out_file),
      Err(err) => {
        eprintln!("Error creating output file {:?}:", out_file);
        eprintln!("{}", err);
        exit(1);
      }
    }
  } else {
    Either::Left(stdout())
  }
}

#[cfg_attr(tarpaulin, skip)]
fn main() -> io::Result<()> {
  let matches = App::new("mC Symbol Table Viewer")
    .set_term_width(0)
    .max_term_width(0)
    .about("Utility for viewing the generated intermediate representation. Errors are reported on invalid inputs.")
    .arg(Arg::from_usage("-o, --output <out-file> 'output file (defaults to stdout)'").required(false))
    .arg(Arg::from_usage("<file> 'input file (use '-' to read from stdin)'"))
    .get_matches();

  let out_file = value_t!(matches, "output", PathBuf).ok();
  let in_file = value_t!(matches, "file", PathBuf).unwrap();

  let input = input(in_file);
  let output = output(out_file);
  mc_symbol_table::cli(input, output)?;

  Ok(())
}
