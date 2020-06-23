use std::fs::File;
use std::io::{stdin, stdout, Read, Write};
use std::path::{Path, PathBuf};
use std::process::exit;

use either::Either;

/// Try opening an input file for reading, otherwise print an error and exit.
pub fn input(in_file: PathBuf) -> impl Read {
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

/// Try opening an output file for writing, otherwise print an error and exit.
pub fn output(out_file: Option<PathBuf>) -> impl Write {
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
