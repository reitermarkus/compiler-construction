#![deny(missing_debug_implementations, rust_2018_idioms)]
#[macro_use]
extern crate prettytable;
use prettytable::Table;
use from_pest::ConversionError;

use mc_parser::ast::Program;
use std::cell::RefCell;
use std::io;
use std::rc::Rc;

mod format_symbol_table;

mod symbol_table;
use symbol_table::{Scope, Symbol};

mod add_to_scope;
use add_to_scope::AddToScope;

mod semantic_error;
use semantic_error::SemanticError;

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

pub fn mc_symbol_table<'a>(contents: &'a str) -> Result<Table, SuperWauError2000<'a>> {
  let ast: Program<'a> = mc_parser::parse(contents)?;

  let scope = mc_check_semantics(&ast)?;

  let mut table = Table::new();
  scope.borrow().to_pretty_table(&mut table);
  Ok(table)
}

pub fn mc_check_semantics<'a, 'b>(ast: &'a Program<'b>) -> Result<Rc<RefCell<Scope>>, Vec<SemanticError<'b>>> {
  let scope = Scope::new();
  ast.add_to_scope(&scope)?;
  Ok(scope)
}

#[derive(Debug)]
pub enum SuperWauError2000<'a> {
  Io(io::Error),
  ParseError(ConversionError<String>),
  SemanticError(Vec<SemanticError<'a>>),
}

impl<'a> From<io::Error> for SuperWauError2000<'a> {
  fn from(error: io::Error) -> Self {
    Self::Io(error)
  }
}

impl From<ConversionError<String>> for SuperWauError2000<'_> {
  fn from(error: ConversionError<String>) -> Self {
    Self::ParseError(error)
  }
}

impl<'a> From<Vec<SemanticError<'a>>> for SuperWauError2000<'a> {
  fn from(errors: Vec<SemanticError<'a>>) -> Self {
    Self::SemanticError(errors)
  }
}
