#![deny(missing_debug_implementations, rust_2018_idioms)]
#[macro_use]
extern crate prettytable;
use prettytable::Table;

use mc_parser::ast::Program;
use std::cell::RefCell;
use std::rc::Rc;

mod format_symbol_table;

mod symbol_table;
use symbol_table::{Scope, Symbol};

mod add_to_scope;
use add_to_scope::AddToScope;

use mc_common::error::*;

mod cli;
pub mod semantic_checks;
pub use cli::cli;

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

/// Check semantics of a given `Program` and return the resulting `Scope` or `SemanticError`s.
pub fn check_semantics<'a>(ast: &Program<'a>) -> Result<Rc<RefCell<Scope>>, SuperWauError2000<'a>> {
  let scope = Scope::new();
  ast.add_to_scope(&scope)?;
  Ok(scope)
}

/// Generate a symbol table for a given scope.
pub fn symbol_table(scope: &Scope) -> Table {
  let mut table = Table::new();
  scope.to_pretty_table(&mut table);
  table
}
