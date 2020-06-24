use std::cell::RefCell;
use std::rc::Rc;

use pest::Span;

use mc_common::error::*;
use mc_parser::ast::*;

use super::extend_errors;
use crate::*;

pub trait CheckSemantics<'a> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope<'a>>>) -> Result<(), Vec<SemanticError<'a>>>;
}

impl<'a> CheckSemantics<'a> for Expression<'a> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope<'a>>>) -> Result<(), Vec<SemanticError<'a>>> {
    let mut res = Ok(());

    match self {
      Self::Literal { .. } => {}
      Self::Variable { identifier, span, index_expression } => {
        extend_errors!(res, check_variable(scope, identifier, span, index_expression));
      }
      Self::Unary { op, expression, span } => extend_errors!(res, check_unary_expression(scope, *op, expression, span)),
      Self::FunctionCall { identifier, arguments, span } => {
        extend_errors!(res, check_function_call(scope, identifier, span, arguments));
      }
      Self::Binary { op, lhs, rhs, span } => {
        extend_errors!(res, check_binary_expression(scope, *op, lhs, rhs, span));
      }
    };

    res
  }
}

impl<'a> CheckSemantics<'a> for Assignment<'a> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope<'a>>>) -> Result<(), Vec<SemanticError<'a>>> {
    let mut res = Ok(());

    match Scope::lookup(scope, &self.identifier) {
      Some(Symbol::Function(..)) => {
        push_error!(
          res,
          SemanticError::WrongUseOfFunction { span: self.span.clone(), identifier: self.identifier.clone() }
        );
      }
      Some(Symbol::Variable(ty, size)) => {
        extend_errors!(res, check_variable_index(&self.identifier, &self.span, size, &self.index_expression));

        if let Some(r_ty) = get_expression_type(scope, &self.rvalue) {
          if ty != r_ty {
            push_error!(
              res,
              SemanticError::InvalidDeclarationType {
                span: self.span.clone(),
                identifier: self.identifier.clone(),
                expected: ty,
                actual: r_ty,
              }
            );
          }
        };
      }
      None => {}
    };

    extend_errors!(res, check_variable(scope, &self.identifier, &self.span, &self.index_expression));

    extend_errors!(res, self.rvalue.check_semantics(scope));

    res
  }
}

impl<'a> CheckSemantics<'a> for Declaration<'a> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope<'a>>>) -> Result<(), Vec<SemanticError<'a>>> {
    if Scope::lookup_in_scope(scope, &self.identifier).is_some() {
      Err(vec![SemanticError::AlreadyDeclared { span: self.span.clone(), identifier: self.identifier.clone() }])
    } else {
      Ok(())
    }
  }
}

impl<'a> CheckSemantics<'a> for IfStatement<'a> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope<'a>>>) -> Result<(), Vec<SemanticError<'a>>> {
    check_condition(scope, &self.condition, &self.span)
  }
}

impl<'a> CheckSemantics<'a> for WhileStatement<'a> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope<'a>>>) -> Result<(), Vec<SemanticError<'a>>> {
    check_condition(scope, &self.condition, &self.span)
  }
}

impl<'a> CheckSemantics<'a> for ReturnStatement<'a> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope<'a>>>) -> Result<(), Vec<SemanticError<'a>>> {
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
          span: self.span.clone(),
          expected: expected_return_type,
          actual: actual_return_type,
        }
      )
    }

    res
  }
}

fn check_main_return_type<'a>(function_declaration: &FunctionDeclaration<'a>) -> Result<(), Vec<SemanticError<'a>>> {
  let mut res = Ok(());

  if function_declaration.identifier == "main".into() {
    let actual_return_type = function_declaration.ty;
    let expected_return_type = Some(Ty::Int);

    if actual_return_type != expected_return_type {
      push_error!(
        res,
        SemanticError::InvalidReturnType {
          span: function_declaration.span.clone(),
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

fn check_missing_return<'a>(function_declaration: &FunctionDeclaration<'a>) -> Result<(), Vec<SemanticError<'a>>> {
  let mut res = Ok(());

  if function_declaration.ty.is_some() && !function_declaration.body.find_return_statement() {
    push_error!(
      res,
      SemanticError::MissingReturnStatement {
        identifier: function_declaration.identifier.clone(),
        span: function_declaration.span.clone()
      }
    );
  }

  res
}

impl<'a> CheckSemantics<'a> for FunctionDeclaration<'a> {
  fn check_semantics(&self, _scope: &Rc<RefCell<Scope<'a>>>) -> Result<(), Vec<SemanticError<'a>>> {
    let mut res = Ok(());

    extend_errors!(res, check_main_return_type(self));
    extend_errors!(res, check_missing_return(self));

    res
  }
}

impl<'a> CheckSemantics<'a> for Program<'a> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope<'a>>>) -> Result<(), Vec<SemanticError<'a>>> {
    if !matches!(Scope::lookup(scope, &Identifier::from("main")), Some(Symbol::Function(..))) {
      return Err(vec![SemanticError::NoMainFunction { span: self.span.clone() }]);
    }

    Ok(())
  }
}

// Only used to get the return type of an expression.
// Does not perform semantic checks on the expression.
pub fn get_expression_type<'a>(scope: &Rc<RefCell<Scope<'a>>>, expression: &Expression<'a>) -> Option<Ty> {
  match expression {
    Expression::Literal { literal, .. } => Some(literal.ty()),
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
  scope: &Rc<RefCell<Scope<'a>>>,
  identifier: &Identifier<'a>,
  span: &Span<'a>,
  index_expression: &Option<E>,
) -> Result<(), Vec<SemanticError<'a>>>
where
  E: AsRef<Expression<'a>>,
{
  match Scope::lookup(scope, identifier) {
    Some(Symbol::Function(..)) => {
      Err(vec![SemanticError::WrongUseOfFunction { span: span.clone(), identifier: identifier.clone() }])
    }
    Some(Symbol::Variable(.., size)) => check_variable_boxed_index(identifier, span, size, index_expression),
    None => Err(vec![SemanticError::NotDeclared { span: span.clone(), identifier: identifier.clone() }]),
  }
}

pub fn index_bounds_check<'a>(
  index: usize,
  size: usize,
  identifier: &Identifier<'a>,
  span: &Span<'a>,
) -> Result<(), Vec<SemanticError<'a>>> {
  if index as usize >= size {
    Err(vec![SemanticError::IndexOutOfBounds {
      span: span.clone(),
      identifier: identifier.clone(),
      size,
      actual: index,
    }])
  } else {
    Ok(())
  }
}

pub fn check_variable_boxed_index<'a, E>(
  identifier: &Identifier<'a>,
  span: &Span<'a>,
  size: Option<usize>,
  index_expression: &Option<E>,
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
    (None, Some(_)) => Err(vec![SemanticError::ArrayError { span: span.clone(), identifier: identifier.clone() }]),
    _ => Ok(()),
  }
}

pub fn check_variable_index<'a>(
  identifier: &Identifier<'a>,
  span: &Span<'a>,
  size: Option<usize>,
  index_expression: &Option<Expression<'a>>,
) -> Result<(), Vec<SemanticError<'a>>> {
  match (size, index_expression) {
    (Some(size), Some(index_expression)) => {
      if let Expression::Literal { literal: Literal::Int(index), span } = index_expression {
        index_bounds_check(*index as usize, size, identifier, span)
      } else {
        Ok(())
      }
    }
    (None, Some(_)) => Err(vec![SemanticError::ArrayError { span: span.clone(), identifier: identifier.clone() }]),
    _ => Ok(()),
  }
}

pub fn check_condition<'a>(
  scope: &Rc<RefCell<Scope<'a>>>,
  condition: &Expression<'a>,
  span: &Span<'a>,
) -> Result<(), Vec<SemanticError<'a>>> {
  let mut res = if let Some(condition_ty) = get_expression_type(scope, condition) {
    if condition_ty != Ty::Bool {
      Err(vec![SemanticError::InvalidConditionType { span: span.clone(), actual: condition_ty }])
    } else {
      Ok(())
    }
  } else {
    Err(vec![SemanticError::InvalidCondition { span: span.clone() }])
  };

  extend_errors!(res, condition.check_semantics(scope));

  res
}

pub fn check_function_identifier_available<'a>(
  scope: &Rc<RefCell<Scope<'a>>>,
  identifier: &Identifier<'a>,
  span: &Span<'a>,
) -> Result<(), Vec<SemanticError<'a>>> {
  if Scope::lookup(scope, identifier).is_some() {
    Err(vec![SemanticError::AlreadyDeclared { span: span.clone(), identifier: identifier.clone() }])
  } else {
    Ok(())
  }
}

pub fn check_function_call<'a>(
  scope: &Rc<RefCell<Scope<'a>>>,
  identifier: &Identifier<'a>,
  span: &Span<'a>,
  arguments: &[Expression<'a>],
) -> Result<(), Vec<SemanticError<'a>>> {
  match Scope::lookup(scope, identifier) {
    Some(Symbol::Function(..)) => check_function_call_arguments(scope, identifier, span, arguments),
    Some(Symbol::Variable(..)) => {
      Err(vec![SemanticError::NotAFunction { span: span.clone(), identifier: identifier.clone() }])
    }
    None => Err(vec![SemanticError::NotDeclared { span: span.clone(), identifier: identifier.clone() }]),
  }
}

pub fn check_function_call_arguments<'a>(
  scope: &Rc<RefCell<Scope<'a>>>,
  identifier: &Identifier<'a>,
  span: &Span<'a>,
  arguments: &[Expression<'a>],
) -> Result<(), Vec<SemanticError<'a>>> {
  if let Some(Symbol::Function(_, args)) = Scope::lookup(scope, identifier) {
    if args.len() != arguments.len() {
      return Err(vec![SemanticError::InvalidAmountOfArguments {
        span: span.clone(),
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
  scope: &Rc<RefCell<Scope<'a>>>,
  symbol_arg: &(Ty, Option<usize>),
  arg_expression: &Expression<'a>,
  identifier: &Identifier<'a>,
  span: &Span<'a>,
) -> Result<(), Vec<SemanticError<'a>>> {
  if arg_expression.check_semantics(scope).is_err() {
    return Err(vec![SemanticError::InvalidArgument { span: span.clone(), identifier: identifier.clone() }]);
  }

  let ty = get_expression_type(scope, arg_expression);

  if ty != Some(symbol_arg.0) {
    return Err(vec![SemanticError::InvalidArgumentType {
      span: span.clone(),
      identifier: identifier.clone(),
      expected: symbol_arg.0,
      actual: ty,
    }]);
  }

  Ok(())
}

pub fn check_unary_expression<'a>(
  scope: &Rc<RefCell<Scope<'a>>>,
  op: UnaryOp,
  expression: &Expression<'a>,
  span: &Span<'a>,
) -> Result<(), Vec<SemanticError<'a>>> {
  let mut res = Ok(());

  match expression {
    Expression::Literal { literal, .. } => {
      extend_errors!(res, check_unary_operator_compatability(op, literal.ty(), span));
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
      extend_errors!(res, check_unary_operator_combination(*inner_op, op, span));
    }
    Expression::Binary { op: binary_op, .. } => {
      extend_errors!(res, expression.check_semantics(scope));
      extend_errors!(res, check_operator_combination(op, *binary_op, span));
    }
  }

  res
}

pub fn check_binary_expression<'a>(
  scope: &Rc<RefCell<Scope<'a>>>,
  op: BinaryOp,
  lhs: &Expression<'a>,
  rhs: &Expression<'a>,
  span: &Span<'a>,
) -> Result<(), Vec<SemanticError<'a>>> {
  let mut res = Ok(());

  extend_errors!(res, lhs.check_semantics(scope));
  extend_errors!(res, rhs.check_semantics(scope));

  let lhs_ty = get_expression_type(scope, lhs);
  let rhs_ty = get_expression_type(scope, rhs);

  if (lhs_ty != rhs_ty) || lhs_ty.is_none() || rhs_ty.is_none() {
    push_error!(res, SemanticError::BinaryOperatorTypeError { span: span.clone(), op, lhs_ty, rhs_ty });
  } else {
    extend_errors!(res, check_binary_operator_compatibility(op, lhs_ty, rhs_ty, span));
  }

  res
}

pub fn check_unary_operator_compatability<'a>(
  op: UnaryOp,
  ty: Ty,
  span: &Span<'a>,
) -> Result<(), Vec<SemanticError<'a>>> {
  match ty {
    Ty::Bool if op == UnaryOp::Minus => Err(vec![SemanticError::UnaryOperatorTypeError { span: span.clone(), op, ty }]),
    Ty::Int | Ty::Float if op == UnaryOp::Not => {
      Err(vec![SemanticError::UnaryOperatorTypeError { span: span.clone(), op, ty }])
    }
    Ty::String => Err(vec![SemanticError::UnaryOperatorTypeError { span: span.clone(), op, ty }]),
    _ => Ok(()),
  }
}

pub fn check_binary_operator_compatibility<'a>(
  op: BinaryOp,
  lhs_ty: Option<Ty>,
  rhs_ty: Option<Ty>,
  span: &Span<'a>,
) -> Result<(), Vec<SemanticError<'a>>> {
  match lhs_ty.expect("no ty") {
    Ty::Bool if [BinaryOp::Divide, BinaryOp::Times, BinaryOp::Minus, BinaryOp::Plus].contains(&op) => {
      Err(vec![SemanticError::BinaryOperatorTypeError { span: span.clone(), op, lhs_ty, rhs_ty }])
    }
    Ty::Int | Ty::Float if [BinaryOp::Land, BinaryOp::Lor].contains(&op) => {
      Err(vec![SemanticError::BinaryOperatorTypeError { span: span.clone(), op, lhs_ty, rhs_ty }])
    }
    Ty::String if ![BinaryOp::Eq, BinaryOp::Neq].contains(&op) => {
      Err(vec![SemanticError::BinaryOperatorTypeError { span: span.clone(), op, lhs_ty, rhs_ty }])
    }
    _ => Ok(()),
  }
}

pub fn check_unary_operator_combination<'a>(
  inner: UnaryOp,
  outer: UnaryOp,
  span: &Span<'a>,
) -> Result<(), Vec<SemanticError<'a>>> {
  match outer {
    UnaryOp::Not if inner == UnaryOp::Minus => {
      Err(vec![SemanticError::UnaryOperatorCombinationError { span: span.clone(), inner, outer }])
    }
    UnaryOp::Minus if inner == UnaryOp::Not => {
      Err(vec![SemanticError::UnaryOperatorCombinationError { span: span.clone(), inner, outer }])
    }
    _ => Ok(()),
  }
}

pub fn check_operator_combination<'a>(
  unary_op: UnaryOp,
  binary_op: BinaryOp,
  span: &Span<'a>,
) -> Result<(), Vec<SemanticError<'a>>> {
  match unary_op {
    UnaryOp::Not if [BinaryOp::Divide, BinaryOp::Times, BinaryOp::Minus, BinaryOp::Plus].contains(&binary_op) => {
      Err(vec![SemanticError::OperatorCombinationError { span: span.clone(), unary_op, binary_op }])
    }
    UnaryOp::Minus if ![BinaryOp::Divide, BinaryOp::Times, BinaryOp::Minus, BinaryOp::Plus].contains(&binary_op) => {
      Err(vec![SemanticError::OperatorCombinationError { span: span.clone(), unary_op, binary_op }])
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

#[cfg(test)]
mod test {
  use pest::Span;

  use crate::semantic_checks::CheckSemantics;
  use crate::*;

  use super::*;

  #[test]
  fn semantic_program_check() {
    let program = Program { function_declarations: Vec::new(), span: Span::new("", 0, 0).unwrap() };

    let scope = Scope::new();
    let result = program.check_semantics(&scope);
    let errors = result.expect_err("no errors found");

    assert!(errors.contains(&SemanticError::NoMainFunction { span: Span::new("", 0, 0).unwrap() }))
  }

  #[test]
  fn semantic_function_declaration_check() {
    let function_declaration = FunctionDeclaration {
      ty: Some(Ty::Float),
      identifier: Identifier::from("sum"),
      parameters: vec![
        Declaration { ty: Ty::Int, count: None, identifier: Identifier::from("n"), span: Span::new("", 0, 0).unwrap() },
        Declaration { ty: Ty::Int, count: None, identifier: Identifier::from("m"), span: Span::new("", 0, 0).unwrap() },
      ],
      body: CompoundStatement {
        statements: vec![Statement::Ret(ReturnStatement {
          expression: Some(Expression::Binary {
            op: BinaryOp::Plus,
            lhs: Box::new(Expression::Variable {
              identifier: Identifier::from("n"),
              index_expression: None,
              span: Span::new("", 0, 0).unwrap(),
            }),
            rhs: Box::new(Expression::Variable {
              identifier: Identifier::from("m"),
              index_expression: None,
              span: Span::new("", 0, 0).unwrap(),
            }),
            span: Span::new("", 0, 0).unwrap(),
          }),
          span: Span::new("", 0, 0).unwrap(),
        })],
        span: Span::new("", 0, 0).unwrap(),
      },
      span: Span::new("", 0, 0).unwrap(),
    };

    let scope = Scope::new();

    let function_scope = Scope::new_child(&scope, "function");
    let param_n_id = Identifier::from("n");
    let param_symbol = Symbol::Variable(Ty::Int, None);
    let param_m_id = Identifier::from("m");

    function_scope.borrow_mut().insert(param_n_id.clone(), param_symbol.clone());
    function_scope.borrow_mut().insert(param_m_id.clone(), param_symbol.clone());

    scope.borrow_mut().symbols.insert(Identifier::from("sum"), Symbol::Function(Some(Ty::Float), Vec::new()));

    let result = function_declaration.add_to_scope(&scope.borrow().children[0]);
    let errors = result.expect_err("no errors found");

    assert!(errors.contains(&SemanticError::InvalidReturnType {
      span: Span::new("", 0, 0).unwrap(),
      expected: Some(Ty::Float),
      actual: Some(Ty::Int)
    }));
  }

  #[test]
  fn semantic_expression_funcion_call_type_check() {
    let expr = "pi(true, 5.0)";
    let function_call = Expression::FunctionCall {
      identifier: Identifier::from("pi"),
      arguments: vec![
        Expression::Literal { literal: Literal::Bool(true), span: Span::new(&expr, 3, 7).unwrap() },
        Expression::Literal { literal: Literal::Float(5.0), span: Span::new(&expr, 9, 12).unwrap() },
      ],
      span: Span::new(&expr, 0, 13).unwrap(),
    };

    let scope = Scope::new();

    scope
      .borrow_mut()
      .symbols
      .insert(Identifier::from("pi"), Symbol::Function(Some(Ty::Int), vec![(Ty::Bool, None), (Ty::Int, None)]));

    let result = function_call.check_semantics(&scope);
    let errors = result.expect_err("no errors found");

    assert!(errors.contains(&SemanticError::InvalidArgumentType {
      span: Span::new(&expr, 0, 13).unwrap(),
      identifier: Identifier::from("pi"),
      expected: Ty::Int,
      actual: Some(Ty::Float)
    }));

    assert_eq!(errors.len(), 1);
  }

  #[test]
  fn semantic_expression_funcion_call_arguments_count_check() {
    let expr = "pi(true, 5)";
    let function_call = Expression::FunctionCall {
      identifier: Identifier::from("pi"),
      arguments: vec![
        Expression::Literal { literal: Literal::Bool(true), span: Span::new(&expr, 3, 7).unwrap() },
        Expression::Literal { literal: Literal::Int(5), span: Span::new(&expr, 9, 10).unwrap() },
      ],
      span: Span::new(&expr, 0, 11).unwrap(),
    };

    let scope = Scope::new();

    scope.borrow_mut().symbols.insert(
      Identifier::from("pi"),
      Symbol::Function(Some(Ty::Int), vec![(Ty::Bool, None), (Ty::Int, None), (Ty::Int, None)]),
    );

    let result = function_call.check_semantics(&scope);
    let errors = result.expect_err("no errors found");

    assert!(errors.contains(&SemanticError::InvalidAmountOfArguments {
      span: Span::new(&expr, 0, 11).unwrap(),
      identifier: Identifier::from("pi"),
      expected: 3,
      actual: 2
    }));

    assert_eq!(errors.len(), 1);
  }

  #[test]
  fn assignment_type_check() {
    let assignment_str = "x = 2.0";

    let assignment = Assignment {
      identifier: Identifier::from("x"),
      span: Span::new(assignment_str, 0, 7).unwrap(),
      index_expression: None,
      rvalue: Expression::Literal { literal: Literal::Float(2.0), span: Span::new(assignment_str, 4, 7).unwrap() },
    };

    let scope = Scope::new();

    let mut result = assignment.check_semantics(&scope);
    let mut errors = result.expect_err("no errors found");

    assert!(errors.contains(&SemanticError::NotDeclared {
      span: Span::new(assignment_str, 0, 7).unwrap(),
      identifier: Identifier::from("x")
    }));

    scope.borrow_mut().symbols.insert(Identifier::from("x"), Symbol::Variable(Ty::Int, None));
    result = assignment.check_semantics(&scope);
    errors = result.expect_err("no errors found");

    assert!(errors.contains(&SemanticError::InvalidDeclarationType {
      span: Span::new(assignment_str, 0, 7).unwrap(),
      identifier: Identifier::from("x"),
      expected: Ty::Int,
      actual: Ty::Float
    }));
  }

  #[test]
  fn semantic_declaration_check() {
    let declaration_str = "int x = 1";

    let declaration = Declaration {
      identifier: Identifier::from("x"),
      span: Span::new(declaration_str, 0, 9).unwrap(),
      ty: Ty::Int,
      count: None,
    };

    let scope = Scope::new();

    let mut result = declaration.check_semantics(&scope);
    assert_eq!(result, Ok(()));

    scope.borrow_mut().symbols.insert(Identifier::from("x"), Symbol::Variable(Ty::Int, None));
    result = declaration.check_semantics(&scope);
    let errors = result.expect_err("no errors found");

    assert!(errors.contains(&SemanticError::AlreadyDeclared {
      span: Span::new(declaration_str, 0, 9).unwrap(),
      identifier: Identifier::from("x")
    }));

    let child = Scope::new_child(&scope, "block");
    result = declaration.check_semantics(&child);
    assert_eq!(result, Ok(()));
  }

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

    assert!(errors.contains(&SemanticError::IndexOutOfBounds {
      span: Span::new("x[10]", 2, 4).unwrap(),
      identifier: Identifier::from("x"),
      actual: 10,
      size: 5
    }));

    assert_eq!(errors.len(), 1);

    scope = Scope::new();
    scope.borrow_mut().symbols.insert(Identifier::from("x"), Symbol::Function(Some(Ty::Int), Vec::new()));
    result = variable_with_index.check_semantics(&scope);
    errors = result.expect_err("no errors found");

    assert!(errors.contains(&SemanticError::WrongUseOfFunction {
      span: Span::new("x[10]", 0, 5).unwrap(),
      identifier: Identifier::from("x")
    }));

    assert_eq!(errors.len(), 1);
  }

  #[test]
  fn semantic_unary_expression_check() {
    let mut expr = "!variable";
    let mut unary = Expression::Unary {
      op: UnaryOp::Not,
      expression: Box::new(Expression::Variable {
        identifier: Identifier::from("variable"),
        index_expression: None,
        span: Span::new(&expr, 1, 9).unwrap(),
      }),
      span: Span::new(&expr, 0, 9).unwrap(),
    };

    let scope = Scope::new();

    scope.borrow_mut().symbols.insert(Identifier::from("variable"), Symbol::Variable(Ty::Int, None));

    let result = unary.check_semantics(&scope);
    let errors = result.expect_err("no errors found");

    assert!(errors.contains(&SemanticError::UnaryOperatorTypeError {
      span: Span::new(&expr, 0, 9).unwrap(),
      op: UnaryOp::Not,
      ty: Ty::Int,
    }));

    assert_eq!(errors.len(), 1);

    expr = "-!variable";
    unary = Expression::Unary {
      op: UnaryOp::Minus,
      expression: Box::new(Expression::Unary {
        op: UnaryOp::Not,
        expression: Box::new(Expression::Variable {
          identifier: Identifier::from("variable"),
          index_expression: None,
          span: Span::new(&expr, 2, 10).unwrap(),
        }),
        span: Span::new(&expr, 1, 10).unwrap(),
      }),
      span: Span::new(&expr, 0, 10).unwrap(),
    };

    let result = unary.check_semantics(&scope);
    let errors = result.expect_err("no errors found");

    assert!(errors.contains(&SemanticError::UnaryOperatorTypeError {
      span: Span::new(&expr, 1, 10).unwrap(),
      op: UnaryOp::Not,
      ty: Ty::Int,
    }));
    assert!(errors.contains(&SemanticError::UnaryOperatorCombinationError {
      span: Span::new(&expr, 0, 10).unwrap(),
      outer: UnaryOp::Minus,
      inner: UnaryOp::Not,
    }));

    assert_eq!(errors.len(), 2);
  }

  #[test]
  fn semantic_binary_expression_check() {
    let mut expr = "var + !5";
    let mut binary = Expression::Binary {
      op: BinaryOp::Plus,
      lhs: Box::new(Expression::Variable {
        identifier: Identifier::from("var"),
        index_expression: None,
        span: Span::new(&expr, 0, 3).unwrap(),
      }),
      rhs: Box::new(Expression::Unary {
        op: UnaryOp::Not,
        expression: Box::new(Expression::Literal { literal: Literal::Int(5), span: Span::new(&expr, 7, 8).unwrap() }),
        span: Span::new(&expr, 6, 8).unwrap(),
      }),
      span: Span::new(&expr, 0, 8).unwrap(),
    };

    let scope = Scope::new();

    scope.borrow_mut().symbols.insert(Identifier::from("var"), Symbol::Variable(Ty::String, None));

    let result = binary.check_semantics(&scope);
    let errors = result.expect_err("no errors found");

    assert!(errors.contains(&SemanticError::UnaryOperatorTypeError {
      span: Span::new(&expr, 6, 8).unwrap(),
      op: UnaryOp::Not,
      ty: Ty::Int,
    }));
    assert!(errors.contains(&SemanticError::BinaryOperatorTypeError {
      span: Span::new(&expr, 0, 8).unwrap(),
      op: BinaryOp::Plus,
      lhs_ty: Some(Ty::String),
      rhs_ty: Some(Ty::Bool),
    }));

    assert_eq!(errors.len(), 2);

    expr = "var + var2";
    binary = Expression::Binary {
      op: BinaryOp::Plus,
      lhs: Box::new(Expression::Variable {
        identifier: Identifier::from("var"),
        index_expression: None,
        span: Span::new(&expr, 0, 3).unwrap(),
      }),
      rhs: Box::new(Expression::Variable {
        identifier: Identifier::from("var2"),
        index_expression: None,
        span: Span::new(&expr, 6, 10).unwrap(),
      }),
      span: Span::new(&expr, 0, 10).unwrap(),
    };

    scope.borrow_mut().symbols.insert(Identifier::from("var2"), Symbol::Variable(Ty::String, None));

    let result = binary.check_semantics(&scope);
    let errors = result.expect_err("no errors found");

    assert!(errors.contains(&SemanticError::BinaryOperatorTypeError {
      span: Span::new(&expr, 0, 10).unwrap(),
      op: BinaryOp::Plus,
      lhs_ty: Some(Ty::String),
      rhs_ty: Some(Ty::String),
    }));

    assert_eq!(errors.len(), 1);
  }

  #[test]
  fn semantic_binary_expression_check_for_void_function_call() {
    let expr = "lol() + 5";
    let binary = Expression::Binary {
      op: BinaryOp::Plus,
      lhs: Box::new(Expression::FunctionCall {
        identifier: Identifier::from("lol"),
        arguments: Vec::new(),
        span: Span::new(&expr, 0, 5).unwrap(),
      }),
      rhs: Box::new(Expression::Literal { literal: Literal::Int(5), span: Span::new(&expr, 8, 9).unwrap() }),
      span: Span::new(&expr, 0, 9).unwrap(),
    };

    let scope = Scope::new();
    scope.borrow_mut().symbols.insert(Identifier::from("lol"), Symbol::Function(None, Vec::new()));

    let result = binary.check_semantics(&scope);
    let errors = result.expect_err("no errors found");

    assert!(errors.contains(&SemanticError::BinaryOperatorTypeError {
      span: Span::new(&expr, 0, 9).unwrap(),
      op: BinaryOp::Plus,
      lhs_ty: None,
      rhs_ty: Some(Ty::Int),
    }));

    assert_eq!(errors.len(), 1);
  }

  #[test]
  fn semantic_if_statement_check() {
    let expr = "if (10 - 9)
      var = 1;";
    let if_statement = IfStatement {
      condition: Expression::Binary {
        op: BinaryOp::Minus,
        lhs: Box::new(Expression::Literal { literal: Literal::Int(10), span: Span::new(&expr, 4, 5).unwrap() }),
        rhs: Box::new(Expression::Literal { literal: Literal::Int(9), span: Span::new(&expr, 9, 10).unwrap() }),
        span: Span::new(&expr, 4, 10).unwrap(),
      },
      block: Statement::Assignment(Box::new(Assignment {
        identifier: Identifier::from("var"),
        index_expression: None,
        rvalue: Expression::Literal { literal: Literal::Int(1), span: Span::new(&expr, 24, 25).unwrap() },
        span: Span::new(&expr, 18, 25).unwrap(),
      })),
      else_block: None,
      span: Span::new(&expr, 0, 26).unwrap(),
    };

    let scope = Scope::new();
    let result = if_statement.check_semantics(&scope);
    let errors = result.expect_err("no errors found");

    assert!(
      errors.contains(&SemanticError::InvalidConditionType { span: Span::new(&expr, 0, 26).unwrap(), actual: Ty::Int })
    );

    assert_eq!(errors.len(), 1);
  }

  #[test]
  fn semantic_while_and_return_statement_check() {
    let expr = "while (0)
      return 1;";
    let while_statement = WhileStatement {
      condition: Expression::Literal { literal: Literal::Int(0), span: Span::new(&expr, 7, 8).unwrap() },
      block: Statement::Ret(ReturnStatement {
        expression: Some(Expression::Literal { literal: Literal::Int(1), span: Span::new(&expr, 23, 24).unwrap() }),
        span: Span::new(&expr, 16, 24).unwrap(),
      }),
      span: Span::new(&expr, 0, 25).unwrap(),
    };

    let scope = Scope::new();
    let result = while_statement.check_semantics(&scope);
    let errors = result.expect_err("no errors found");

    assert!(
      errors.contains(&SemanticError::InvalidConditionType { span: Span::new(&expr, 0, 25).unwrap(), actual: Ty::Int })
    );

    assert_eq!(errors.len(), 1);
  }
}
