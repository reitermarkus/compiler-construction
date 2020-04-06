use std::cell::RefCell;
use std::rc::Rc;

use pest::Span;

use mc_parser::ast::*;

use crate::*;

pub fn check_variable<'a>(
  scope: &Rc<RefCell<Scope>>,
  identifier: &Identifier,
  span: &'a Span<'_>,
  index_expression: &'a Option<Box<Expression<'a>>>,
) -> Option<SemanticError<'a>> {
  match Scope::lookup(scope, identifier) {
    Some(Symbol::Function(..)) => Some(SemanticError::WrongUseOfFunction { span, identifier: identifier.clone() }),
    Some(Symbol::Variable(.., size)) => check_variable_index(identifier, span, size, index_expression),
    None => Some(SemanticError::NotDeclared { span, identifier: identifier.clone() }),
  }
}

pub fn check_variable_for_unary_operator<'a>(
  scope: &Rc<RefCell<Scope>>,
  identifier: &Identifier,
  span: &'a Span<'_>,
  index_expression: &'a Option<Box<Expression<'a>>>,
  op: &'a UnaryOp,
) -> Option<SemanticError<'a>> {
  match Scope::lookup(scope, identifier) {
    Some(Symbol::Function(..)) => Some(SemanticError::WrongUseOfFunction { span, identifier: identifier.clone() }),
    Some(Symbol::Variable(ty, size)) => {
      if let Some(error) = check_variable_index(identifier, span, size, index_expression) {
        Some(error)
      } else {
        check_unary_operator_compatability(op, ty, span)
      }
    }
    None => Some(SemanticError::NotDeclared { span, identifier: identifier.clone() }),
  }
}

pub fn check_variable_index<'a>(
  identifier: &Identifier,
  span: &'a Span<'_>,
  size: Option<usize>,
  index_expression: &'a Option<Box<Expression<'a>>>,
) -> Option<SemanticError<'a>> {
  match (size, index_expression) {
    (Some(size), Some(index_expression)) => {
      if let Expression::Literal { literal: Literal::Int(index), span } = &**index_expression {
        if *index < 0 || *index as usize >= size {
          return Some(SemanticError::IndexOutOfBounds {
            span: &span,
            identifier: identifier.clone(),
            size: size as usize,
            actual: *index as usize,
          });
        }
      }

      None
    }
    (None, Some(_)) => Some(SemanticError::ArrayError { span, identifier: identifier.clone() }),
    _ => None,
  }
}

pub fn check_function_call_for_unary_operator<'a>(
  scope: &Rc<RefCell<Scope>>,
  identifier: &Identifier,
  span: &'a Span<'_>,
  arguments: &[Expression<'a>],
  op: &'a UnaryOp,
) -> Option<SemanticError<'a>> {
  match Scope::lookup(scope, identifier) {
    Some(Symbol::Function(Some(ty), ..)) => {
      if let Some(error) = check_function_call_arguments(scope, identifier, span, arguments) {
        Some(error)
      } else {
        check_unary_operator_compatability(op, ty, span)
      }
    }
    Some(Symbol::Function(None, ..)) => {
      Some(SemanticError::ReturnTypeExpected { span, identifier: identifier.clone() })
    }
    Some(Symbol::Variable(..)) => Some(SemanticError::NotAFunction { span, identifier: identifier.clone() }),
    None => Some(SemanticError::NotDeclared { span, identifier: identifier.clone() }),
  }
}

#[allow(unused_variables)]
pub fn check_function_call_arguments<'a>(
  scope: &Rc<RefCell<Scope>>,
  identifier: &Identifier,
  span: &'a Span<'_>,
  arguments: &[Expression<'a>],
) -> Option<SemanticError<'a>> {
  if let Some(Symbol::Function(_, args)) = Scope::lookup(scope, identifier) {
    if args.len() != arguments.len() {
      return Some(SemanticError::InvalidAmountOfArguemnts {
        span,
        identifier: identifier.clone(),
        expected: args.len(),
        actual: arguments.len(),
      });
    }
  }

  None
}

pub fn check_unary_expression<'a>(
  scope: &Rc<RefCell<Scope>>,
  op: &'a UnaryOp,
  expression: &'a Expression<'a>,
  span: &'a Span<'_>,
) -> Vec<SemanticError<'a>> {
  let mut errors = Vec::new();

  match expression {
    Expression::Literal { literal, .. } => {
      if let Some(error) = check_unary_operator_compatability(op, Ty::from(literal), span) {
        errors.push(error)
      }
    }
    Expression::Variable { identifier, index_expression, .. } => {
      if let Some(error) = check_variable_for_unary_operator(scope, identifier, span, index_expression, op) {
        errors.push(error)
      }
    }
    Expression::FunctionCall { identifier, arguments, .. } => {
      if let Some(error) = check_function_call_for_unary_operator(scope, identifier, span, arguments, op) {
        errors.push(error)
      }
    }
    Expression::Unary { op: inner_op, .. } => {
      if let Err(exp_errors) = expression.check_semantics(scope) {
        errors.extend(exp_errors)
      }
      if let Some(error) = check_unary_operator_combination(inner_op, op, span) {
        errors.push(error)
      }
    }
    _ => {}
  }

  errors
}

pub fn check_unary_operator_compatability<'a>(
  op: &'a UnaryOp,
  ty: Ty,
  span: &'a Span<'_>,
) -> Option<SemanticError<'a>> {
  match ty {
    Ty::Bool if *op == UnaryOp::Minus => Some(SemanticError::UnaryOperatorTypeError { span, op, ty }),
    Ty::Int | Ty::Float if *op == UnaryOp::Not => Some(SemanticError::UnaryOperatorTypeError { span, op, ty }),
    Ty::String => Some(SemanticError::UnaryOperatorTypeError { span, op, ty }),
    _ => None,
  }
}

pub fn check_unary_operator_combination<'a>(
  inner: &'a UnaryOp,
  outer: &'a UnaryOp,
  span: &'a Span<'_>,
) -> Option<SemanticError<'a>> {
  match outer {
    UnaryOp::Not if *inner == UnaryOp::Minus => {
      Some(SemanticError::UnaryOperatorCombinationError { span, inner, outer })
    }
    UnaryOp::Minus if *inner == UnaryOp::Not => {
      Some(SemanticError::UnaryOperatorCombinationError { span, inner, outer })
    }
    _ => None,
  }
}
