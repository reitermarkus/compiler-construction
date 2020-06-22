#![deny(missing_debug_implementations, rust_2018_idioms)]

use std::fs::File;
use std::io::{stdin, stdout, Read};
use std::path::{Path, PathBuf};
use std::process::exit;

use clap::{value_t, App, Arg};
use mc_symbol_table::mc_symbol_table;

#[cfg_attr(tarpaulin, skip)]
fn main() -> std::io::Result<()> {
  let matches = App::new("mC Symbol Table Viewer")
    .set_term_width(0)
    .max_term_width(0)
    .about("Utility for viewing the generated intermediate representation. Errors are reported on invalid inputs.")
    .arg(Arg::from_usage("-o, --output <out-file> 'output file (defaults to stdout)'").required(false))
    .arg(Arg::from_usage("<file> 'input file (use '-' to read from stdin)'"))
    .get_matches();

  let out_file = value_t!(matches, "output", String).ok();
  let in_file = value_t!(matches, "file", PathBuf).unwrap();

  let mut contents = String::new();
  if in_file == Path::new("-") {
    stdin().read_to_string(&mut contents)?;
  } else {
    File::open(in_file)?.read_to_string(&mut contents)?;
  }

  let table = mc_symbol_table(&contents);

  match table {
    Ok(table) => {
      if let Some(out_file) = out_file.map(File::create) {
        table.print(&mut out_file?)?;
      } else {
        table.print(&mut stdout())?;
      };

      Ok(())
    }
    Err(err) => {
      eprintln!("{}", err);
      exit(1);
    }
  }
}
