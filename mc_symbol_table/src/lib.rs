#![deny(missing_debug_implementations, rust_2018_idioms)]
#[macro_use]
extern crate prettytable;

use std::fs::File;
use std::io::{prelude::*, stdin};
use std::path::Path;

mod format_symbol_table;

mod symbol_table;
use symbol_table::{Scope, ScopeTable};

mod to_symbol_table;
use to_symbol_table::ToSymbolTable;

pub fn mc_view_symbol_table(in_file: impl AsRef<Path>, mut out_stream: impl Write) -> std::io::Result<()> {
  let mut contents = String::new();

  if in_file.as_ref() == Path::new("-") {
    stdin().read_to_string(&mut contents)?;
  } else {
    File::open(in_file)?.read_to_string(&mut contents)?;
  }

  let ast = mc_parser::parse(&contents).expect("failed to parse program");

  let mut table = ScopeTable::default();
  let root = Scope::default().child("root".to_owned());
  ast.to_symbol_table(&mut table, root);

  let formatted_tables = table.to_pretty_tables();

  writeln!(out_stream, "Symbol Tables:")?;

  for formatted_table in formatted_tables {
    formatted_table.print(&mut out_stream)?;
  }

  writeln!(out_stream, " ")
}
