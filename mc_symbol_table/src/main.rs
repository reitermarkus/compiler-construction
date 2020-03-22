#![deny(missing_debug_implementations, rust_2018_idioms)]
#[macro_use]
extern crate prettytable;

use std::fs::File;
use std::io::{prelude::*, stdin, stdout};
use std::path::Path;

use clap::{value_t, App, Arg};

mod symbol_table;
use symbol_table::{Scope, ScopeTable};

mod to_symbol_table;
use to_symbol_table::ToSymbolTable;

mod format_symbol_table;

fn main() -> std::io::Result<()> {
  let matches = App::new("mC Symbol Table Viewer")
    .set_term_width(0)
    .max_term_width(0)
    .about("Utility for viewing the generated intermediate representation. Errors are reported on invalid inputs.")
    .arg(Arg::from_usage("-o, --output <out-file> 'output file (defaults to stdout)'").required(false))
    .arg(Arg::from_usage("<file> 'input file (use '-' to read from stdin)'"))
    .get_matches();

  let out_file = value_t!(matches, "output", String).ok();
  let in_file = value_t!(matches, "file", String).unwrap();

  let mut contents = String::new();

  if AsRef::<Path>::as_ref(&in_file) == Path::new("-") {
    stdin().read_to_string(&mut contents)?;
  } else {
    File::open(in_file)?.read_to_string(&mut contents)?;
  }

  let ast = mc_parser::parse(&contents).expect("failed to parse program");

  let mut table = ScopeTable::default();
  let root = Scope::default().child("root".to_owned());

  let symbol_table = ast.to_symbol_table(&mut table, root);

  if let Some(out_file) = out_file.map(File::create) {
    writeln!(out_file?, "{:#?}", symbol_table)?;
  } else {
    writeln!(stdout(), "{:#?}", symbol_table)?;
  }

  Ok(())
}
