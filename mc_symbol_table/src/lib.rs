#![deny(missing_debug_implementations, rust_2018_idioms)]

use std::cell::RefCell;
use std::io::{Read, Write};
use std::rc::Rc;

#[macro_use]
extern crate prettytable;
use prettytable::Table;

use mc_common::input_to_string;
use mc_parser::ast::Program;

mod format_symbol_table;

mod symbol_table;
use symbol_table::{Scope, Symbol};

mod add_to_scope;
use add_to_scope::AddToScope;

use mc_common::error::*;

pub mod semantic_checks;

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

pub fn cli(input: impl Read, mut output: impl Write) -> Result<(), i32> {
  let contents = input_to_string(input)?;
  let ast = match mc_parser::parse(&contents) {
    Ok(program) => program,
    Err(err) => {
      eprintln!("{}", SuperWauError2000::from(err));
      return Err(1);
    }
  };
  match crate::check_semantics(&ast).map(|scope| crate::symbol_table(&scope.borrow())) {
    Ok(table) => match table.print(&mut output) {
      Ok(_) => Ok(()),
      Err(err) => {
        eprintln!("Error printing symbol table: {}", err);
        Err(1)
      }
    },
    Err(err) => {
      eprintln!("{}", err);
      Err(1)
    }
  }
}

/// Check semantics of a given `Program` and return the resulting `Scope` or `SemanticError`s.
pub fn check_semantics<'a>(ast: &Program<'a>) -> Result<Rc<RefCell<Scope<'a>>>, SuperWauError2000<'a>> {
  let scope = Scope::new();
  ast.add_to_scope(&scope)?;
  Ok(scope)
}

/// Generate a symbol table for a given scope.
pub fn symbol_table(scope: &Scope<'_>) -> Table {
  let mut table = Table::new();
  scope.to_pretty_table(&mut table);
  table
}
