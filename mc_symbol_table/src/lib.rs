#![deny(missing_debug_implementations, rust_2018_idioms)]
#[macro_use]
extern crate prettytable;
use prettytable::Table;

use std::fs::File;
use std::io::{prelude::*, stdin};
use std::path::Path;

mod format_symbol_table;

mod symbol_table;
use symbol_table::Scope;

mod add_to_scope;
use add_to_scope::AddToScope;

pub fn mc_view_symbol_table(in_file: impl AsRef<Path>, mut out_stream: impl Write) -> std::io::Result<()> {
  let mut contents = String::new();

  if in_file.as_ref() == Path::new("-") {
    stdin().read_to_string(&mut contents)?;
  } else {
    File::open(in_file)?.read_to_string(&mut contents)?;
  }

  let ast = mc_parser::parse(&contents).expect("failed to parse program");

  let scope = Scope::new();
  ast.add_to_scope(&scope);

  let mut table = Table::new();
  scope.borrow().to_pretty_table(&mut table);
  table.print(&mut out_stream)?;

  Ok(())
}
