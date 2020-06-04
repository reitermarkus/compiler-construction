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

    extend_errors!(res, check_variable(scope, &self.identifier, &self.span, &self.index_expression));

    extend_errors!(res, self.rvalue.check_semantics(scope));

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

    let expected_return_type = Scope::return_type(scope);
    let actual_return_type = if let Some(return_expression) = &self.expression {
      extend_errors!(res, return_expression.check_semantics(scope));
      get_expression_type(scope, return_expression)
    } else {
      None
    };

    if actual_return_type != expected_return_type {
      push_error!(
        res,
        SemanticError::InvalidReturnType {
          span: &self.span,
          expected: expected_return_type,
          actual: actual_return_type,
        }
      )
    }

    res
  }
}

fn check_main_return_type<'a>(function_declaration: &'a FunctionDeclaration<'a>) -> Result<(), Vec<SemanticError<'a>>> {
  let mut res = Ok(());

  if function_declaration.identifier == "main".into() {
    let actual_return_type = function_declaration.ty;
    let expected_return_type = Some(Ty::Int);

    if actual_return_type != expected_return_type {
      push_error!(
        res,
        SemanticError::InvalidReturnType {
          span: &function_declaration.span,
          actual: actual_return_type,
          expected: expected_return_type
        }
      );
    }
  }

  res
}

pub trait FindReturnStatement {
  fn find_return_statement(&self) -> bool;
}

impl FindReturnStatement for Statement<'_> {
  fn find_return_statement(&self) -> bool {
    match self {
      Statement::Compound(compound_statement) => compound_statement.find_return_statement(),
      Statement::If(if_statement) => if_statement.find_return_statement(),
      Statement::Ret(_) => true,
      _ => false,
    }
  }
}

impl FindReturnStatement for CompoundStatement<'_> {
  fn find_return_statement(&self) -> bool {
    for statement in &self.statements {
      if statement.find_return_statement() {
        return true;
      }
    }

    false
  }
}

impl FindReturnStatement for IfStatement<'_> {
  fn find_return_statement(&self) -> bool {
    if let Some(else_block) = &self.else_block {
      self.block.find_return_statement() && else_block.find_return_statement()
    } else {
      false
    }
  }
}

impl FindReturnStatement for FunctionDeclaration<'_> {
  fn find_return_statement(&self) -> bool {
    self.body.find_return_statement()
  }
}

fn check_missing_return<'a>(function_declaration: &'a FunctionDeclaration<'a>) -> Result<(), Vec<SemanticError<'a>>> {
  let mut res = Ok(());

  if function_declaration.ty.is_some() && !function_declaration.body.find_return_statement() {
    push_error!(
      res,
      SemanticError::MissingReturnStatement {
        identifier: function_declaration.identifier.clone(),
        span: &function_declaration.span
      }
    );
  }

  res
}

impl CheckSemantics for FunctionDeclaration<'_> {
  fn check_semantics(&self, _scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    let mut res = Ok(());

    extend_errors!(res, check_main_return_type(self));
    extend_errors!(res, check_missing_return(self));

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

pub fn check_variable<'a, E>(
  scope: &Rc<RefCell<Scope>>,
  identifier: &Identifier,
  span: &'a Span<'_>,
  index_expression: &'a Option<E>,
) -> Result<(), Vec<SemanticError<'a>>>
where
  E: AsRef<Expression<'a>>,
{
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

pub fn check_variable_boxed_index<'a, E>(
  identifier: &Identifier,
  span: &'a Span<'_>,
  size: Option<usize>,
  index_expression: &'a Option<E>,
) -> Result<(), Vec<SemanticError<'a>>>
where
  E: AsRef<Expression<'a>>,
{
  match (size, index_expression) {
    (Some(size), Some(index_expression)) => {
      if let Expression::Literal { literal: Literal::Int(index), span } = index_expression.as_ref() {
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
    return Err(vec![SemanticError::InvalidArgument { span, identifier: identifier.clone() }]);
  }

  let ty = get_expression_type(scope, arg_expression);

  if ty != Some(symbol_arg.0) {
    return Err(vec![SemanticError::InvalidArgumentType {
      span,
      identifier: identifier.clone(),
      expected: symbol_arg.0,
      actual: ty,
    }]);
  }

  Ok(())
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

  let lhs_ty = get_expression_type(scope, lhs);
  let rhs_ty = get_expression_type(scope, rhs);

  if (lhs_ty != rhs_ty) || lhs_ty.is_none() || rhs_ty.is_none() {
    push_error!(res, SemanticError::BinaryOperatorTypeError { span, op, lhs_ty, rhs_ty });
  } else {
    extend_errors!(res, check_binary_operator_compatibility(op, lhs_ty, rhs_ty, span));
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

pub fn check_binary_operator_compatibility<'a>(
  op: &'a BinaryOp,
  lhs_ty: Option<Ty>,
  rhs_ty: Option<Ty>,
  span: &'a Span<'_>,
) -> Result<(), Vec<SemanticError<'a>>> {
  match lhs_ty.expect("no ty") {
    Ty::Bool if [BinaryOp::Divide, BinaryOp::Times, BinaryOp::Minus, BinaryOp::Plus].contains(op) => {
      Err(vec![SemanticError::BinaryOperatorTypeError { span, op, lhs_ty, rhs_ty }])
    }
    Ty::Int | Ty::Float if [BinaryOp::Land, BinaryOp::Lor].contains(op) => {
      Err(vec![SemanticError::BinaryOperatorTypeError { span, op, lhs_ty, rhs_ty }])
    }
    Ty::String if ![BinaryOp::Eq, BinaryOp::Neq].contains(op) => {
      Err(vec![SemanticError::BinaryOperatorTypeError { span, op, lhs_ty, rhs_ty }])
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

  macro_rules! expect_error {
    ($ty:ident, $input:expr, $error:expr) => {
      let scope = Scope::new();
      let ast = $ty::try_from($input.trim()).expect("failed to convert input to AST");
      let res = ast.add_to_scope(&scope);

      let error: Option<&str> = $error;
      if let Some(expected_error) = error {
        let errors = res.unwrap_err();
        let error_output = errors.iter().map(|err| err.to_string()).collect::<Vec<_>>().join("\n");

        if !error_output.contains(expected_error) {
          panic!("expected output {:?} to contain {:?}", error_output, expected_error);
        }
      } else {
        res.unwrap();
      }
    };
  }

  #[test]
  fn wrong_main_return_type() {
    expect_error!(
      FunctionDeclaration,
      r#"
        void main() {
        }
      "#,
      Some("expected return type int, found void")
    );
  }

  #[test]
  fn void_without_return() {
    expect_error!(
      FunctionDeclaration,
      r#"
        void example() {
        }
      "#,
      None
    );
  }

  #[test]
  fn wrong_return_type() {
    expect_error!(
      FunctionDeclaration,
      r#"
        void example() {
          return true;
        }
      "#,
      Some("expected return type void, found bool")
    );

    expect_error!(
      FunctionDeclaration,
      r#"
      int example() {
          return;
        }
      "#,
      Some("expected return type int, found void")
    );
  }

  #[test]
  fn no_missing_return_statement() {
    expect_error!(
      FunctionDeclaration,
      r#"
        bool ageforalco(int n) {
          if (n < 21) {
            return false;
          }

          return true;
        }
      "#,
      None
    );

    expect_error!(
      FunctionDeclaration,
      r#"
        bool ageforalco(int n) {
          if (n < 21) {
            return false;
          } else {
            return true;
          }
        }
      "#,
      None
    );

    expect_error!(
      FunctionDeclaration,
      r#"
        bool ageforalco(int n) {
          if (n < 21) {

          } else {
            return true;
          }

          return false;
        }
      "#,
      None
    );
  }

  #[test]
  fn return_statement_after_if() {
    expect_error!(
      FunctionDeclaration,
      r#"
        bool ageforalco(int n) {
          if (n < 21) {
            return false;
          }
        }
      "#,
      Some("missing return statement in function 'ageforalco'")
    );
  }

  #[test]
  fn missing_return_if_else() {
    expect_error!(
      FunctionDeclaration,
      r#"
        bool ageforalco(int n) {
          if (n < 21) {

          } else {
            return true;
          }
        }
      "#,
      Some("missing return statement in function 'ageforalco'")
    );
  }

  #[test]
  fn nested_if_return() {
    expect_error!(
      FunctionDeclaration,
      r#"
        bool ageforalco(int n) {
          if (n < 21) {
            if (n > 2) {
              return false;
            } else {
              return true;
            }
          } else {
            return true;
          }
        }
      "#,
      None
    );
  }

  #[test]
  fn nested_if_main_return() {
    expect_error!(
      FunctionDeclaration,
      r#"
        bool ageforalco(int n) {
          if (n < 21) {
            if (n > 2) {
              return false;
            }
          } else {
            return true;
          }

          return false;
        }
      "#,
      None
    );
  }

  #[test]
  fn nested_if_return_error() {
    expect_error!(
      FunctionDeclaration,
      r#"
        bool ageforalco(int n) {
          if (n < 21) {
            if (n > 2) {
              return false;
            }
          } else {
            return true;
          }
        }
      "#,
      Some("missing return statement in function 'ageforalco'")
    );
  }

  #[test]
  fn binary_operator_type_error() {
    expect_error!(Expression, "true + 5", Some("operator '+' cannot be used with types 'bool' and 'int'"));
  }
}
