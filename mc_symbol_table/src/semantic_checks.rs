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
