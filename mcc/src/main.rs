#![deny(missing_debug_implementations, rust_2018_idioms)]

use std::path::PathBuf;
use std::process::exit;

use clap::{value_t, App, Arg};

use mc_common::input;

fn main() {
  let matches = App::new("mC Compiler")
    .set_term_width(0)
    .max_term_width(0)
    .about(
      "The mC compiler. It takes an mC input file and produces an executable. Errors are reported on invalid inputs.",
    )
    .arg(Arg::from_usage("-q, --quiet 'suppress error output'").required(false))
    .arg(Arg::from_usage("-o, --output <out-file> 'output file (defaults to 'a.out')'").required(false))
    .arg(
      Arg::from_usage("--backend <backend> 'override the back-end compiler (defaults to 'gcc')'")
        .env("MCC_BACKEND")
        .required(false),
    )
    .arg(
      Arg::from_usage("--docker-image <backend> 'run the back-end compiler inside a Docker image'")
        .env("MCC_DOCKER_IMAGE")
        .required(false),
    )
    .arg(Arg::from_usage("<file> 'input file (use '-' to read from stdin)'"))
    .get_matches();

  let quiet = matches.is_present("quiet");
  let out_file = value_t!(matches, "output", PathBuf).unwrap_or_else(|_| "a.out".into());
  let in_file = value_t!(matches, "file", PathBuf).unwrap();
  let backend = value_t!(matches, "backend", String).unwrap_or_else(|_| "gcc".into());
  let docker_image = value_t!(matches, "docker-image", String).ok();

  let input = input(in_file);

  if let Err(exit_code) = mcc::cli(input, out_file, backend, docker_image, quiet) {
    exit(exit_code)
  }
}
