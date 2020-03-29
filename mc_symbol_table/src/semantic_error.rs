use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;

use pest::Span;

use mc_parser::ast::*;

use crate::*;

pub enum SemanticError<'a> {
  #[allow(dead_code)]
  Type {
    span: Span<'a>,
    expected: Ty,
    actual: Ty,
  },
  NotDeclared {
    span: Span<'a>,
    identifier: Identifier,
  },
}

macro_rules! write_err {
  ($f:expr, $span:expr, $($args:expr),*) => {{
    let (start_line, start_col) = $span.start_pos().line_col();
    let (end_line, end_col) = $span.end_pos().line_col();
    write!($f, "{}:{}-{}:{} ", start_line, start_col, end_line, end_col)?;
    write!($f, $($args,)*)
  }}
}

impl fmt::Display for SemanticError<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Type { span, expected, actual } => write_err!(f, span, "expected type {}, found type {}", expected, actual),
      Self::NotDeclared { span, identifier } => {
        write_err!(f, span, "variable '{}' not declared in this scope", identifier)
      }
    }
  }
}

pub trait CheckSemantics {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>>;
}

impl CheckSemantics for Expression<'_> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    match self {
      Self::Literal { .. } => Ok(()),
      Self::Variable { identifier, span, .. } => {
        let mut errors = Vec::new();

        if Scope::lookup(scope, identifier) == None {
          errors.push(SemanticError::NotDeclared { span: span.clone(), identifier: identifier.clone() });
        }

        Ok(())
      }
      _unreachable => Ok(()),
    }
  }
}
