use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;

use pest::Span;

use mc_parser::ast::*;

use crate::*;

#[derive(PartialEq, Debug)]
pub enum SemanticError<'a> {
  #[allow(dead_code)]
  Type {
    span: &'a Span<'a>,
    expected: Ty,
    actual: Ty,
  },
  NotDeclared {
    span: &'a Span<'a>,
    identifier: Identifier,
  },
  ArrayError {
    span: &'a Span<'a>,
    identifier: Identifier,
  },
  IndexOutOfBounds {
    span: &'a Span<'a>,
    identifier: Identifier,
    size: usize,
    actual: usize,
  },
  WrongUseOfFunction {
    span: &'a Span<'a>,
    identifier: Identifier,
  },
  NotAFunction {
    span: &'a Span<'a>,
    identifier: Identifier,
  },
  UnaryOperatorTypeError {
    span: &'a Span<'a>,
    op: &'a UnaryOp,
    ty: Ty,
  },
  UnaryOperatorCombinationError {
    span: &'a Span<'a>,
    outer: &'a UnaryOp,
    inner: &'a UnaryOp,
  },
  ReturnTypeExpectet {
    span: &'a Span<'a>,
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
      Self::ArrayError { span, identifier } => write_err!(f, span, "variable '{}' is not an array", identifier),
      Self::IndexOutOfBounds { span, identifier, size, actual } => {
        write_err!(f, span, "index {} out of bound for '{}' with size {}", actual, identifier, size)
      }
      Self::WrongUseOfFunction { span, identifier } => write_err!(f, span, "wrong use of function '{}'", identifier),
      Self::NotAFunction { span, identifier } => write_err!(f, span, "'{}' is not a function", identifier),
      Self::UnaryOperatorTypeError { span, op, ty } => {
        write_err!(f, span, "operator '{}' cannot be used with type '{}'", op, ty)
      }
      Self::UnaryOperatorCombinationError { span, outer, inner } => {
        write_err!(f, span, "operator '{}' cannot be combined with operator '{}'", inner, outer)
      }
      Self::ReturnTypeExpectet { span, identifier } => {
        write_err!(f, span, "expected return type for function '{}'", identifier)
      }
    }
  }
}

pub trait CheckSemantics {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>>;
}

impl CheckSemantics for Expression<'_> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    let mut errors = Vec::new();

    match self {
      Self::Literal { .. } => {}
      Self::Variable { identifier, span, index_expression } => {
        if let Some(error) = check_variable(scope, identifier, span, index_expression) {
          errors.push(error);
        }
      }
      Self::Unary { op, expression, span } => errors.extend(check_unary_expression(scope, op, expression, span)),
      _ => todo!(),
    };

    if errors.is_empty() {
      Ok(())
    } else {
      Err(errors)
    }
  }
}

#[cfg(test)]
mod test {
  use pest::Span;

  use super::*;

  #[test]
  fn semantic_expression_variable_check() {
    let variable_without_index = Expression::Variable {
      identifier: Identifier::from("x"),
      span: Span::new("x", 0, 1).unwrap(),
      index_expression: None,
    };

    let variable_with_index = Expression::Variable {
      identifier: Identifier::from("x"),
      span: Span::new("x[10]", 0, 5).unwrap(),
      index_expression: Some(Box::new(Expression::Literal {
        span: Span::new("x[10]", 2, 4).unwrap(),
        literal: Literal::Int(10),
      })),
    };

    let mut scope = Scope::new();

    let mut result = variable_without_index.check_semantics(&scope);
    let mut errors = result.expect_err("no errors found");
    assert!(errors.contains(&SemanticError::NotDeclared {
      span: &Span::new("x", 0, 1).unwrap(),
      identifier: Identifier::from("x")
    }));
    assert_eq!(errors.len(), 1);

    scope.borrow_mut().symbols.insert(Identifier::from("x"), Symbol::Variable(Ty::Int, None));
    result = variable_without_index.check_semantics(&scope);
    assert_eq!(result, Ok(()));

    scope = Scope::new();
    scope.borrow_mut().symbols.insert(Identifier::from("x"), Symbol::Variable(Ty::Int, Some(5)));
    result = variable_with_index.check_semantics(&scope);
    errors = result.expect_err("no errors found");
    assert!(errors.contains(&SemanticError::IndexOutOfBounds {
      span: &Span::new("x[10]", 2, 4).unwrap(),
      identifier: Identifier::from("x"),
      actual: 10,
      size: 5
    }));
    assert_eq!(errors.len(), 1);

    scope = Scope::new();
    scope.borrow_mut().symbols.insert(Identifier::from("x"), Symbol::Function(Some(Ty::Int)));
    result = variable_with_index.check_semantics(&scope);
    errors = result.expect_err("no errors found");
    assert!(errors.contains(&SemanticError::WrongUseOfFunction {
      span: &Span::new("x[10]", 0, 5).unwrap(),
      identifier: Identifier::from("x")
    }));
    assert_eq!(errors.len(), 1);
  }
}
