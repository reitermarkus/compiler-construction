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
  IndexError {
    span: Span<'a>,
    identifier: Identifier,
  },
  IndexOutOfBound {
    span: Span<'a>,
    identifier: Identifier,
    size: usize,
    actual: usize,
  },
  WrongUseOfFunction {
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
      },
      Self::IndexError { span, identifier } => {
        write_err!(f, span, "wrong index expression for '{}'", identifier)
      },
      Self::IndexOutOfBound { span, identifier, size, actual } => {
        write_err!(f, span, "index {} out of bound for '{}' with size {}", actual, identifier, size)
      },
      Self::WrongUseOfFunction { span, identifier } => {
        write_err!(f, span, "wrong use of function '{}'", identifier)
      },
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
      Self::Variable { identifier, span, index_expression } => {
        let mut errors = Vec::new();

        if let Some(var) = Scope::lookup(scope, identifier) {
          if let Symbol::Function(..) = var {
            errors.push(SemanticError::WrongUseOfFunction { span: span.clone(), identifier: identifier.clone() })
          }

          if let Some(index) = index_expression {
            match index.check_index_semantics(&var, identifier).err() {
              Some(Some(e)) => { errors.push(e); },
              Some(None) => { errors.push(SemanticError::IndexError { span: span.clone(), identifier: identifier.clone()}) }
              None => {}
            }
          }
        } else {
          errors.push(SemanticError::NotDeclared { span: span.clone(), identifier: identifier.clone() });
        }

        if errors.is_empty() {
          Ok(())
        } else {
          Err(errors)
        }
      }
      _unreachable => Ok(()),
    }
  }
}

trait CheckIndexSemantics {
  fn check_index_semantics(&self, symbol: &Symbol, identifier: &Identifier) -> Result<(), Option<SemanticError<'_>>>;
}

impl CheckIndexSemantics for Expression<'_> {
  fn check_index_semantics(&self, symbol: &Symbol, identifier: &Identifier) -> Result<(), Option<SemanticError<'_>>> {
    if let Symbol::Variable( .., Some(size) ) = symbol {

      match self {
        Self::Literal { literal, span } => {

          if let Literal::Int(index) = literal {
            if *index < *size as i64 {
              Ok(())
            } else {
              Err(Some(SemanticError::IndexOutOfBound { span: span.clone(), identifier: identifier.clone(), size: size.clone(), actual: index.clone() as usize }))
            }
          } else {
            Err(Some(SemanticError::IndexError { span: span.clone(), identifier: identifier.clone()}))
          }
        },
        _unreachable => {
          Err(None)
        }
      }
    } else {
      Err(None)
    }
  }
}