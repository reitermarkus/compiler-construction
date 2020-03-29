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
  UnaryOperatorTypeError {
    span: Span<'a>,
    op: &'a UnaryOp,
    ty: Ty,
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
      Self::IndexError { span, identifier } => write_err!(f, span, "wrong index expression for '{}'", identifier),
      Self::IndexOutOfBound { span, identifier, size, actual } => {
        write_err!(f, span, "index {} out of bound for '{}' with size {}", actual, identifier, size)
      }
      Self::WrongUseOfFunction { span, identifier } => write_err!(f, span, "wrong use of function '{}'", identifier),
      Self::UnaryOperatorTypeError { span, op, ty } => {
        write_err!(f, span, "operator '{}' cannot be used with type '{}'", op, ty)
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
        if let Some(var) = Scope::lookup(scope, identifier) {
          if let Symbol::Function(..) = var {
            errors.push(SemanticError::WrongUseOfFunction { span: span.clone(), identifier: identifier.clone() });
          } else {
            if let Some(index) = index_expression {
              match index.check_index_semantics(&var, identifier).err() {
                Some(Some(e)) => {
                  errors.push(e);
                }
                Some(None) => {
                  errors.push(SemanticError::IndexError { span: span.clone(), identifier: identifier.clone() });
                }
                None => {}
              }
            }
          }
        } else {
          errors.push(SemanticError::NotDeclared { span: span.clone(), identifier: identifier.clone() });
        }
      }
      Self::Unary { op, expression, span } => {
        // check semantics of expression
        let res = expression.check_semantics(scope);
        if let Err(err) = res {
          errors.extend(err);
        }

        match &**expression {
          Self::Literal { literal, .. } => match literal {
            Literal::Bool(_) => {
              if *op == UnaryOp::Minus {
                errors.push(SemanticError::UnaryOperatorTypeError { span: span.clone(), op, ty: Ty::from(literal) });
              }
            }
            Literal::Int(_) | Literal::Float(_) => {
              if *op == UnaryOp::Not {
                errors.push(SemanticError::UnaryOperatorTypeError { span: span.clone(), op, ty: Ty::from(literal) });
              }
            }
            Literal::String(_) => {
              errors.push(SemanticError::UnaryOperatorTypeError { span: span.clone(), op, ty: Ty::from(literal) });
            }
          },
          Self::Variable { identifier, index_expression, .. } => {
            if let Some(symbol) = Scope::lookup(scope, identifier) {
              if let Symbol::Variable(ty, size) = symbol {
                if size.is_some() != index_expression.is_some() {
                  // yield error
                }

                match ty {
                  Ty::Bool => {
                    if *op == UnaryOp::Minus {
                      errors.push(SemanticError::UnaryOperatorTypeError { span: span.clone(), op, ty });
                    }
                  }
                  Ty::Int | Ty::Float => {
                    if *op == UnaryOp::Not {
                      errors.push(SemanticError::UnaryOperatorTypeError { span: span.clone(), op, ty });
                    }
                  }
                  Ty::String => {
                    errors.push(SemanticError::UnaryOperatorTypeError { span: span.clone(), op, ty });
                  }
                }
              } else {
                errors.push(SemanticError::WrongUseOfFunction { span: span.clone(), identifier: identifier.clone() })
              }
            } else {
              errors.push(SemanticError::NotDeclared { span: span.clone(), identifier: identifier.clone() });
            }
          }
          _ => todo!(),
        }
      }
      _ => todo!(),
    };

    if errors.is_empty() {
      Ok(())
    } else {
      Err(errors)
    }
  }
}

trait CheckIndexSemantics {
  fn check_index_semantics(&self, symbol: &Symbol, identifier: &Identifier) -> Result<(), Option<SemanticError<'_>>>;
}

impl CheckIndexSemantics for Expression<'_> {
  fn check_index_semantics(&self, symbol: &Symbol, identifier: &Identifier) -> Result<(), Option<SemanticError<'_>>> {
    if let Symbol::Variable(.., Some(size)) = symbol {
      match self {
        Self::Literal { literal, span } => {
          if let Literal::Int(index) = literal {
            if *index < *size as i64 {
              Ok(())
            } else {
              Err(Some(SemanticError::IndexOutOfBound {
                span: span.clone(),
                identifier: identifier.clone(),
                size: size.clone(),
                actual: index.clone() as usize,
              }))
            }
          } else {
            Err(Some(SemanticError::IndexError { span: span.clone(), identifier: identifier.clone() }))
          }
        }
        _ => Err(None),
      }
    } else {
      Err(None)
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
      span: Span::new("x", 0, 1).unwrap(),
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
    assert!(errors.contains(&SemanticError::IndexOutOfBound {
      span: Span::new("x[10]", 2, 4).unwrap(),
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
      span: Span::new("x[10]", 0, 5).unwrap(),
      identifier: Identifier::from("x")
    }));
    assert_eq!(errors.len(), 1);
  }
}
