use std::cell::RefCell;
use std::rc::Rc;

use pest::Span;

use mc_parser::ast::*;

use crate::*;

pub fn check_variable_declared<'a>(
  errors: &mut Vec<SemanticError<'a>>,
  scope: &Rc<RefCell<Scope>>,
  identifier: &Identifier,
  span: &'a Span<'a>,
) {
  match Scope::lookup(scope, identifier) {
    Some(Symbol::Variable(..)) => {}
    Some(Symbol::Function(..)) => {
      errors.push(SemanticError::WrongUseOfFunction { identifier: identifier.clone(), span })
    }
    None => errors.push(SemanticError::NotDeclared { identifier: identifier.clone(), span }),
  }
}
