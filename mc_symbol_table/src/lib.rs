#![deny(missing_debug_implementations, rust_2018_idioms)]
#[macro_use]
extern crate prettytable;
use prettytable::Table;

use mc_parser::ast::Program;
use std::cell::RefCell;
use std::fs::File;
use std::io::{prelude::*, stdin};
use std::path::Path;
use std::rc::Rc;

mod format_symbol_table;

mod symbol_table;
use symbol_table::{Scope, Symbol};

mod add_to_scope;
use add_to_scope::AddToScope;

mod semantic_error;
use semantic_error::SemanticError;

mod semantic_checks;

#[macro_export]
macro_rules! push_error {
  ($res:expr, $err:expr) => {
    match $res {
      Ok(_) => {
        $res = Err(vec![$err]);
      }
      Err(ref mut errors) => {
        errors.push($err);
      }
    }
  };
}

#[macro_export]
macro_rules! extend_errors {
  ($res:expr, $err:expr) => {
    if let Err(err) = $err {
      match $res {
        Ok(_) => {
          $res = Err(err);
        }
        Err(ref mut errors) => {
          errors.extend(err);
        }
      }
    }
  };
}

pub fn mc_symbol_table(in_file: impl AsRef<Path>, mut out_stream: impl Write) -> std::io::Result<()> {
  let mut contents = String::new();

  if in_file.as_ref() == Path::new("-") {
    stdin().read_to_string(&mut contents)?;
  } else {
    File::open(in_file)?.read_to_string(&mut contents)?;
  }

  let ast = mc_parser::parse(&contents).expect("failed to parse program");

  let scope = mc_check_semantics(&ast).expect("semantic checks failed");

  let mut table = Table::new();
  scope.borrow().to_pretty_table(&mut table);
  table.print(&mut out_stream)?;

  Ok(())
}

pub fn mc_check_semantics(ast: &Program<'_>) -> Result<Rc<RefCell<Scope>>, ()> {
  let scope = Scope::new();

  if let Err(errors) = ast.add_to_scope(&scope) {
    for error in errors {
      eprintln!("{}", error);
    }

    Err(())
  } else {
    Ok(scope)
  }
}
