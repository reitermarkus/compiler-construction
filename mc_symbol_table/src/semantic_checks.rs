use std::cell::RefCell;
use std::rc::Rc;

use pest::Span;

use mc_parser::ast::*;

use super::extend_errors;
use crate::*;

pub trait CheckSemantics {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>>;
}

impl CheckSemantics for Expression<'_> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    let mut res = Ok(());

    match self {
      Self::Literal { .. } => {}
      Self::Variable { identifier, span, index_expression } => {
        extend_errors!(res, check_variable(scope, identifier, span, index_expression));
      }
      Self::Unary { op, expression, span } => extend_errors!(res, check_unary_expression(scope, op, expression, span)),
      Self::FunctionCall { identifier, arguments, span } => {
        extend_errors!(res, check_function_call(scope, identifier, span, arguments));
      }
      Self::Binary { op, lhs, rhs, span } => {
        extend_errors!(res, check_binary_expression(scope, op, lhs, rhs, span));
      }
    };

    res
  }
}

impl CheckSemantics for Assignment<'_> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    let mut res = Ok(());

    match Scope::lookup(scope, &self.identifier) {
      Some(Symbol::Function(..)) => {
        push_error!(res, SemanticError::WrongUseOfFunction { span: &self.span, identifier: self.identifier.clone() });
      }
      Some(Symbol::Variable(ty, size)) => {
        extend_errors!(res, check_variable_index(&self.identifier, &self.span, size, &self.index_expression));

        if let Some(r_ty) = get_expression_type(scope, &self.rvalue) {
          if ty != r_ty {
            push_error!(
              res,
              SemanticError::InvalidDeclarationType {
                span: &self.span,
                identifier: self.identifier.clone(),
                expected: ty,
                actual: r_ty,
              }
            );
          }
        };
      }
      None => push_error!(res, SemanticError::NotDeclared { span: &self.span, identifier: self.identifier.clone() }),
    };

    res
  }
}

impl CheckSemantics for Declaration<'_> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    if Scope::lookup_in_scope(scope, &self.identifier).is_some() {
      Err(vec![SemanticError::AlreadyDeclared { span: &self.span, identifier: self.identifier.clone() }])
    } else {
      Ok(())
    }
  }
}

impl CheckSemantics for Parameter<'_> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    if Scope::lookup(scope, &self.identifier).is_some() {
      Err(vec![SemanticError::AlreadyDeclared { span: &self.span, identifier: self.identifier.clone() }])
    } else {
      Ok(())
    }
  }
}

impl CheckSemantics for IfStatement<'_> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    check_condition(scope, &self.condition, &self.span)
  }
}

impl CheckSemantics for WhileStatement<'_> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    check_condition(scope, &self.condition, &self.span)
  }
}

impl CheckSemantics for ReturnStatement<'_> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    let mut res = Ok(());

    if let Some(return_expression) = &self.expression {
      extend_errors!(res, return_expression.check_semantics(scope));
    }

    res
  }
}

type StatementsReturn<'a> = Option<Vec<(&'a str, usize, Option<Span<'a>>, &'a ReturnStatement<'a>)>>;

fn recurse_statements<'a>(from: &'a str, smt: &'a Statement<'a>) -> StatementsReturn<'a> {
  match smt {
    Statement::Ret(ret) => Some(vec![("main", 0, None, ret)]),
    Statement::If(if_smt) => {
      if let Some(else_block) = &if_smt.else_block {
        Some(
          recurse_statements("if", &if_smt.block)
            .iter()
            .chain(recurse_statements("if", &else_block).iter())
            .flat_map(|smt| smt.clone())
            .map(|(from, level, _, smt)| {
              if from == "if" {
                ("if", level + 1, Some(if_smt.span.clone()), smt)
              } else {
                ("if", level, Some(if_smt.span.clone()), smt)
              }
            })
            .collect::<Vec<_>>(),
        )
      } else {
        Some(
          recurse_statements("if", &if_smt.block)
            .iter()
            .flat_map(|smt| smt.clone())
            .map(|(from, level, _, smt)| {
              if from == "if" {
                ("if", level + 1, Some(if_smt.span.clone()), smt)
              } else {
                ("if", level, Some(if_smt.span.clone()), smt)
              }
            })
            .collect::<Vec<_>>(),
        )
      }
    }
    Statement::Compound(compound_smt) => {
      Some(compound_smt.statements.iter().filter_map(|s| recurse_statements(from, s)).flatten().collect::<Vec<_>>())
    }
    _ => None,
  }
}

impl CheckSemantics for FunctionDeclaration<'_> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    let mut res = Ok(());

    let ret_expressions = self
      .body
      .statements
      .iter()
      .filter_map(|x| recurse_statements("", x))
      .flatten()
      .map(|(from, level, span, x)| (from, level, span, x.expression.as_ref()))
      .collect::<Vec<_>>();

    // Check that return statements match the functions type.
    if let Some(function_ty) = &self.ty {
      if ret_expressions.is_empty() {
        push_error!(res, SemanticError::ReturnTypeExpected { identifier: self.identifier.clone(), span: &self.span })
      }

      if ret_expressions.iter().all(|(from, _, _, _)| *from != "main") {
        let if_returns = ret_expressions.iter().filter(|(from, _, _, _)| *from == "if").collect::<Vec<_>>();

        if if_returns.len() >= 2 {
          for chunk in if_returns.chunks(2) {
            if chunk.len() == 2 {
              if chunk[0].1 != chunk[1].1 {
                push_error!(res, SemanticError::MatchingReturnError { span: chunk[0].2.clone().unwrap() })
              }
            } else if chunk[0].1 != 0 {
              push_error!(res, SemanticError::MatchingReturnError { span: chunk[0].2.clone().unwrap() })
            }
          }
        } else if if_returns.len() == 1 {
          push_error!(res, SemanticError::MatchingReturnError { span: if_returns[0].2.clone().unwrap() })
        }
      }

      for (_, _, _, ret_expr) in ret_expressions.iter() {
        if let Some(ret) = ret_expr {
          if let Some(expr_ty) = get_expression_type(scope, ret) {
            if expr_ty != *function_ty {
              push_error!(
                res,
                SemanticError::InvalidReturnType {
                  identifier: self.identifier.clone(),
                  span: ret.get_span(),
                  expected: function_ty.clone(),
                  actual: expr_ty,
                }
              )
            }
          }
        }
      }
    } else if !ret_expressions.is_empty() {
      for (_, _, _, ret_expr) in ret_expressions.iter() {
        if let Some(ret) = ret_expr {
          if let Some(expr_ty) = get_expression_type(scope, ret) {
            push_error!(
              res,
              SemanticError::NoReturnTypeExpected {
                identifier: self.identifier.clone(),
                span: ret.get_span(),
                actual: expr_ty,
              }
            )
          }
        }
      }
    }

    res
  }
}

impl CheckSemantics for Program<'_> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    if !matches!(Scope::lookup(scope, &Identifier::from("main")), Some(Symbol::Function(..))) {
      return Err(vec![SemanticError::NoMainFunction { span: &self.span }]);
    }

    Ok(())
  }
}

// Only used to get the return type of an expression.
// Does not perform semantic checks on the expression.
pub fn get_expression_type<'a>(scope: &Rc<RefCell<Scope>>, expression: &'a Expression<'a>) -> Option<Ty> {
  match expression {
    Expression::Literal { literal, .. } => Some(Ty::from(literal)),
    Expression::Variable { identifier, .. } | Expression::FunctionCall { identifier, .. } => {
      match Scope::lookup(scope, identifier) {
        Some(Symbol::Variable(ty, ..)) => Some(ty),
        Some(Symbol::Function(Some(ty), ..)) => Some(ty),
        _ => None,
      }
    }
    Expression::Unary { op, expression: inner_exp, .. } => match op {
      UnaryOp::Minus => get_expression_type(scope, &inner_exp),
      UnaryOp::Not => Some(Ty::Bool),
    },
    Expression::Binary { op, lhs, .. } => match op {
      BinaryOp::Times | BinaryOp::Divide | BinaryOp::Plus | BinaryOp::Minus => get_expression_type(scope, lhs),
      _ => Some(Ty::Bool),
    },
  }
}

pub fn check_variable<'a>(
  scope: &Rc<RefCell<Scope>>,
  identifier: &Identifier,
  span: &'a Span<'_>,
  index_expression: &'a Option<Box<Expression<'a>>>,
) -> Result<(), Vec<SemanticError<'a>>> {
  match Scope::lookup(scope, identifier) {
    Some(Symbol::Function(..)) => Err(vec![SemanticError::WrongUseOfFunction { span, identifier: identifier.clone() }]),
    Some(Symbol::Variable(.., size)) => check_variable_boxed_index(identifier, span, size, index_expression),
    None => Err(vec![SemanticError::NotDeclared { span, identifier: identifier.clone() }]),
  }
}

pub fn index_bounds_check<'a>(
  index: usize,
  size: usize,
  identifier: &Identifier,
  span: &'a Span<'_>,
) -> Result<(), Vec<SemanticError<'a>>> {
  if index as usize >= size {
    Err(vec![SemanticError::IndexOutOfBounds { span: &span, identifier: identifier.clone(), size, actual: index }])
  } else {
    Ok(())
  }
}

pub fn check_variable_boxed_index<'a>(
  identifier: &Identifier,
  span: &'a Span<'_>,
  size: Option<usize>,
  index_expression: &'a Option<Box<Expression<'a>>>,
) -> Result<(), Vec<SemanticError<'a>>> {
  match (size, index_expression) {
    (Some(size), Some(index_expression)) => {
      if let Expression::Literal { literal: Literal::Int(index), span } = &**index_expression {
        index_bounds_check(*index as usize, size, identifier, span)
      } else {
        Ok(())
      }
    }
    (None, Some(_)) => Err(vec![SemanticError::ArrayError { span, identifier: identifier.clone() }]),
    _ => Ok(()),
  }
}

pub fn check_variable_index<'a>(
  identifier: &Identifier,
  span: &'a Span<'_>,
  size: Option<usize>,
  index_expression: &'a Option<Expression<'a>>,
) -> Result<(), Vec<SemanticError<'a>>> {
  match (size, index_expression) {
    (Some(size), Some(index_expression)) => {
      if let Expression::Literal { literal: Literal::Int(index), span } = index_expression {
        index_bounds_check(*index as usize, size, identifier, span)
      } else {
        Ok(())
      }
    }
    (None, Some(_)) => Err(vec![SemanticError::ArrayError { span, identifier: identifier.clone() }]),
    _ => Ok(()),
  }
}

pub fn check_condition<'a>(
  scope: &Rc<RefCell<Scope>>,
  condition: &'a Expression<'a>,
  span: &'a Span<'_>,
) -> Result<(), Vec<SemanticError<'a>>> {
  let mut res = if let Some(condition_ty) = get_expression_type(scope, condition) {
    if condition_ty != Ty::Bool {
      Err(vec![SemanticError::InvalidConditionType { span, actual: condition_ty }])
    } else {
      Ok(())
    }
  } else {
    Err(vec![SemanticError::InvalidCondition { span }])
  };

  extend_errors!(res, condition.check_semantics(scope));

  res
}

pub fn check_function_identifier_available<'a>(
  scope: &Rc<RefCell<Scope>>,
  identifier: &Identifier,
  span: &'a Span<'_>,
) -> Result<(), Vec<SemanticError<'a>>> {
  if Scope::lookup(scope, identifier).is_some() {
    Err(vec![SemanticError::AlreadyDeclared { span, identifier: identifier.clone() }])
  } else {
    Ok(())
  }
}

pub fn check_function_call<'a>(
  scope: &Rc<RefCell<Scope>>,
  identifier: &Identifier,
  span: &'a Span<'_>,
  arguments: &'a [Expression<'a>],
) -> Result<(), Vec<SemanticError<'a>>> {
  match Scope::lookup(scope, identifier) {
    Some(Symbol::Function(..)) => check_function_call_arguments(scope, identifier, span, arguments),
    Some(Symbol::Variable(..)) => Err(vec![SemanticError::NotAFunction { span, identifier: identifier.clone() }]),
    None => Err(vec![SemanticError::NotDeclared { span, identifier: identifier.clone() }]),
  }
}

pub fn check_function_call_arguments<'a>(
  scope: &Rc<RefCell<Scope>>,
  identifier: &Identifier,
  span: &'a Span<'_>,
  arguments: &'a [Expression<'a>],
) -> Result<(), Vec<SemanticError<'a>>> {
  if let Some(Symbol::Function(_, args)) = Scope::lookup(scope, identifier) {
    if args.len() != arguments.len() {
      return Err(vec![SemanticError::InvalidAmountOfArguments {
        span,
        identifier: identifier.clone(),
        expected: args.len(),
        actual: arguments.len(),
      }]);
    }

    let mut res = Ok(());

    for r in args
      .iter()
      .zip(arguments.iter())
      .map(|(arg, argument)| check_function_call_argument_type(scope, arg, argument, identifier, span))
    {
      extend_errors!(res, r);
    }

    return res;
  }

  Ok(())
}

pub fn check_function_call_argument_type<'a>(
  scope: &Rc<RefCell<Scope>>,
  symbol_arg: &(Ty, Option<usize>),
  arg_expression: &'a Expression<'a>,
  identifier: &Identifier,
  span: &'a Span<'_>,
) -> Result<(), Vec<SemanticError<'a>>> {
  if arg_expression.check_semantics(scope).is_err() {
    Err(vec![SemanticError::InvalidArgument { span, identifier: identifier.clone() }])
  } else if let Some(ty) = get_expression_type(scope, arg_expression) {
    if ty != symbol_arg.0 {
      return Err(vec![SemanticError::InvalidArgumentType {
        span,
        identifier: identifier.clone(),
        expected: symbol_arg.0.clone(),
        actual: ty,
      }]);
    }

    Ok(())
  } else {
    Err(vec![SemanticError::ReturnTypeExpected { span, identifier: identifier.clone() }])
  }
}

pub fn check_unary_expression<'a>(
  scope: &Rc<RefCell<Scope>>,
  op: &'a UnaryOp,
  expression: &'a Expression<'a>,
  span: &'a Span<'_>,
) -> Result<(), Vec<SemanticError<'a>>> {
  let mut res = Ok(());

  match expression {
    Expression::Literal { literal, .. } => {
      extend_errors!(res, check_unary_operator_compatability(op, Ty::from(literal), span));
    }
    Expression::Variable { identifier, index_expression, .. } => {
      extend_errors!(res, check_variable(scope, identifier, span, index_expression));

      if let Some(ty) = get_expression_type(scope, expression) {
        extend_errors!(res, check_unary_operator_compatability(op, ty, span));
      }
    }
    Expression::FunctionCall { identifier, arguments, .. } => {
      extend_errors!(res, check_function_call(scope, identifier, span, arguments));

      if let Some(ty) = get_expression_type(scope, expression) {
        extend_errors!(res, check_unary_operator_compatability(op, ty, span));
      }
    }
    Expression::Unary { op: inner_op, .. } => {
      extend_errors!(res, expression.check_semantics(scope));
      extend_errors!(res, check_unary_operator_combination(inner_op, op, span));
    }
    Expression::Binary { op: binary_op, .. } => {
      extend_errors!(res, expression.check_semantics(scope));
      extend_errors!(res, check_operator_combination(op, binary_op, span));
    }
  }

  res
}

pub fn check_binary_expression<'a>(
  scope: &Rc<RefCell<Scope>>,
  op: &'a BinaryOp,
  lhs: &'a Expression<'a>,
  rhs: &'a Expression<'a>,
  span: &'a Span<'_>,
) -> Result<(), Vec<SemanticError<'a>>> {
  let mut res = Ok(());

  extend_errors!(res, lhs.check_semantics(scope));
  extend_errors!(res, rhs.check_semantics(scope));

  if let (Some(lhs_ty), Some(rhs_ty)) = (get_expression_type(scope, lhs), get_expression_type(scope, rhs)) {
    if lhs_ty != rhs_ty {
      push_error!(res, SemanticError::BinaryOperatorTypeCombinationError { span, op, lhs_ty, rhs_ty });
    } else {
      extend_errors!(res, check_binary_opeartor_compatability(op, lhs_ty, span));
    }
  }

  // Determine the right span, when nesting a call to a `void` function in a binary expression.
  for exp in [lhs, rhs].iter() {
    if let Expression::FunctionCall { identifier, span, .. } = exp {
      if let Some(Symbol::Function(None, ..)) = Scope::lookup(scope, identifier) {
        push_error!(res, SemanticError::ReturnTypeExpected { span, identifier: identifier.clone() })
      }
    }
  }

  res
}

pub fn check_unary_operator_compatability<'a>(
  op: &'a UnaryOp,
  ty: Ty,
  span: &'a Span<'_>,
) -> Result<(), Vec<SemanticError<'a>>> {
  match ty {
    Ty::Bool if *op == UnaryOp::Minus => Err(vec![SemanticError::UnaryOperatorTypeError { span, op, ty }]),
    Ty::Int | Ty::Float if *op == UnaryOp::Not => Err(vec![SemanticError::UnaryOperatorTypeError { span, op, ty }]),
    Ty::String => Err(vec![SemanticError::UnaryOperatorTypeError { span, op, ty }]),
    _ => Ok(()),
  }
}

pub fn check_binary_opeartor_compatability<'a>(
  op: &'a BinaryOp,
  ty: Ty,
  span: &'a Span<'_>,
) -> Result<(), Vec<SemanticError<'a>>> {
  match ty {
    Ty::Bool if [BinaryOp::Divide, BinaryOp::Times, BinaryOp::Minus, BinaryOp::Plus].contains(op) => {
      Err(vec![SemanticError::BinaryOperatorTypeError { span, op, ty }])
    }
    Ty::Int | Ty::Float if [BinaryOp::Land, BinaryOp::Lor].contains(op) => {
      Err(vec![SemanticError::BinaryOperatorTypeError { span, op, ty }])
    }
    Ty::String if ![BinaryOp::Eq, BinaryOp::Neq].contains(op) => {
      Err(vec![SemanticError::BinaryOperatorTypeError { span, op, ty }])
    }
    _ => Ok(()),
  }
}

pub fn check_unary_operator_combination<'a>(
  inner: &'a UnaryOp,
  outer: &'a UnaryOp,
  span: &'a Span<'_>,
) -> Result<(), Vec<SemanticError<'a>>> {
  match outer {
    UnaryOp::Not if *inner == UnaryOp::Minus => {
      Err(vec![SemanticError::UnaryOperatorCombinationError { span, inner, outer }])
    }
    UnaryOp::Minus if *inner == UnaryOp::Not => {
      Err(vec![SemanticError::UnaryOperatorCombinationError { span, inner, outer }])
    }
    _ => Ok(()),
  }
}

pub fn check_operator_combination<'a>(
  unary_op: &'a UnaryOp,
  binary_op: &'a BinaryOp,
  span: &'a Span<'_>,
) -> Result<(), Vec<SemanticError<'a>>> {
  match unary_op {
    UnaryOp::Not if [BinaryOp::Divide, BinaryOp::Times, BinaryOp::Minus, BinaryOp::Plus].contains(binary_op) => {
      Err(vec![SemanticError::OperatorCombinationError { span, unary_op, binary_op }])
    }
    UnaryOp::Minus if ![BinaryOp::Divide, BinaryOp::Times, BinaryOp::Minus, BinaryOp::Plus].contains(binary_op) => {
      Err(vec![SemanticError::OperatorCombinationError { span, unary_op, binary_op }])
    }
    _ => Ok(()),
  }
}

#[cfg(test)]
mod tests {
  use std::convert::TryFrom;

  use super::*;

  #[test]
  fn check_return_statement() {
    let scope = Scope::new();
    FunctionDeclaration::try_from(
      r#"
      bool ageforalco(int n) {
        if (n < 21) {
          return false;
        }

        return true;
      }
      "#
      .trim(),
    )
    .unwrap()
    .add_to_scope(&scope)
    .unwrap();

    let scope = Scope::new();
    FunctionDeclaration::try_from(
      r#"
      bool ageforalco(int n) {
        if (n < 21) {
          return false;
        } else {
          return true;
        }
      }
      "#
      .trim(),
    )
    .unwrap()
    .add_to_scope(&scope)
    .unwrap();

    let scope = Scope::new();
    FunctionDeclaration::try_from(
      r#"
      bool ageforalco(int n) {
        if (n < 21) {

        } else {
          return true;
        }

        return false;
      }
      "#
      .trim(),
    )
    .unwrap()
    .add_to_scope(&scope)
    .unwrap();

    let scope = Scope::new();
    FunctionDeclaration::try_from(
      r#"
      bool ageforalco(int n) {
        if (n < 21) {
          return false;
        }
      }
      "#
      .trim(),
    )
    .unwrap()
    .add_to_scope(&scope)
    .unwrap_err();

    let scope = Scope::new();
    FunctionDeclaration::try_from(
      r#"
      bool ageforalco(int n) {
        if (n < 21) {

        } else {
          return true;
        }
      }
      "#
      .trim(),
    )
    .unwrap()
    .add_to_scope(&scope)
    .unwrap_err();
  }
}
