use std::cell::RefCell;
use std::rc::Rc;

use pest::Span;

use mc_parser::ast::*;

use crate::*;

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
      Self::FunctionCall { identifier, arguments, span } => {
        errors.extend(check_function_call(scope, identifier, span, arguments));
      }
      Self::Binary { op, lhs, rhs, span } => errors.extend(check_binary_expression(scope, op, lhs, rhs, span)),
    };

    if errors.is_empty() {
      Ok(())
    } else {
      Err(errors)
    }
  }
}

impl CheckSemantics for Assignment<'_> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    let mut errors = Vec::new();

    match Scope::lookup(scope, &self.identifier) {
      Some(Symbol::Function(..)) => {
        errors.push(SemanticError::WrongUseOfFunction { span: &self.span, identifier: self.identifier.clone() })
      }
      Some(Symbol::Variable(ty, size)) => {
        if let Some(error) = check_variable_index(&self.identifier, &self.span, size, &self.index_expression) {
          errors.push(error)
        }

        if let Some(r_ty) = get_expression_type(scope, &self.rvalue) {
          if ty != r_ty {
            errors.push(SemanticError::InvalidDeclarationType {
              span: &self.span,
              identifier: self.identifier.clone(),
              expected: ty,
              actual: r_ty,
            });
          }
        };
      }
      None => errors.push(SemanticError::NotDeclared { span: &self.span, identifier: self.identifier.clone() }),
    };

    if !errors.is_empty() {
      Err(errors)
    } else {
      Ok(())
    }
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
    let mut errors = Vec::new();

    errors.extend(check_condition(scope, &self.condition, &self.span));

    if let Err(if_errors) = self.block.check_semantics(scope) {
      errors.extend(if_errors)
    }

    if let Some(else_statement) = &self.else_block {
      if let Err(else_errors) = else_statement.check_semantics(scope) {
        errors.extend(else_errors)
      }
    }

    if !errors.is_empty() {
      Err(errors)
    } else {
      Ok(())
    }
  }
}

impl CheckSemantics for WhileStatement<'_> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    let mut errors = Vec::new();

    errors.extend(check_condition(scope, &self.condition, &self.span));

    if let Err(while_errors) = self.block.check_semantics(scope) {
      errors.extend(while_errors)
    }

    if !errors.is_empty() {
      Err(errors)
    } else {
      Ok(())
    }
  }
}

impl CheckSemantics for ReturnStatement<'_> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    let mut errors = Vec::new();

    //TODO: check if return is allowed with correct type

    if let Some(return_expression) = &self.expression {
      if let Err(return_expression_errors) = return_expression.check_semantics(scope) {
        errors.extend(return_expression_errors)
      }
    }

    if !errors.is_empty() {
      Err(errors)
    } else {
      Ok(())
    }
  }
}

impl CheckSemantics for CompoundStatement<'_> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    let mut errors = Vec::new();

    for statement in &self.statements {
      if let Err(statement_errors) = statement.check_semantics(scope) {
        errors.extend(statement_errors)
      }
    }

    if !errors.is_empty() {
      Err(errors)
    } else {
      Ok(())
    }
  }
}

impl CheckSemantics for Statement<'_> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    match self {
      Self::Assignment(assignment) => assignment.check_semantics(scope),
      Self::Decl(declaration) => declaration.check_semantics(scope),
      Self::Expression(expression) => expression.check_semantics(scope),
      Self::If(if_statement) => if_statement.check_semantics(scope),
      Self::While(while_statement) => while_statement.check_semantics(scope),
      Self::Ret(ret_statement) => ret_statement.check_semantics(scope),
      Self::Compound(compound) => compound.check_semantics(scope),
    }
  }
}

impl CheckSemantics for FunctionDeclaration<'_> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    let mut errors = Vec::new();

    if self.ty.is_some() {
      let return_type = self
        .body
        .statements
        .iter()
        .map(|x| match x {
          Statement::Ret(ret) => Some(ret),
          _ => None,
        })
        .next()
        .and_then(|ret| ret)
        .and_then(|ret| ret.expression.as_ref())
        .and_then(|expr| get_expression_type(scope, &expr));

      if let Some(ty) = return_type {
        if &ty != self.ty.as_ref().unwrap() {
          errors.push(SemanticError::InvalidReturnType {
            identifier: self.identifier.clone(),
            span: &self.span,
            expected: self.ty.clone().unwrap(),
            actual: ty,
          })
        };
      } else {
        errors.push(SemanticError::ReturnTypeExpected { identifier: self.identifier.clone(), span: &self.span });
      }
    }

    if !errors.is_empty() {
      Err(errors)
    } else {
      Ok(())
    }
  }
}

impl CheckSemantics for Program<'_> {
  fn check_semantics(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    let mut errors = Vec::new();

    if let Some(Symbol::Function(..)) = Scope::lookup(scope, &Identifier::from("main")) {
    } else {
      errors.push(SemanticError::NoMainFunction { span: &self.span })
    }

    if !errors.is_empty() {
      Err(errors)
    } else {
      Ok(())
    }
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
) -> Option<SemanticError<'a>> {
  match Scope::lookup(scope, identifier) {
    Some(Symbol::Function(..)) => Some(SemanticError::WrongUseOfFunction { span, identifier: identifier.clone() }),
    Some(Symbol::Variable(.., size)) => check_variable_boxed_index(identifier, span, size, index_expression),
    None => Some(SemanticError::NotDeclared { span, identifier: identifier.clone() }),
  }
}

pub fn index_bounds_check<'a>(
  index: usize,
  size: usize,
  identifier: &Identifier,
  span: &'a Span<'_>,
) -> Option<SemanticError<'a>> {
  if index as usize >= size {
    Some(SemanticError::IndexOutOfBounds { span: &span, identifier: identifier.clone(), size, actual: index })
  } else {
    None
  }
}

pub fn check_variable_boxed_index<'a>(
  identifier: &Identifier,
  span: &'a Span<'_>,
  size: Option<usize>,
  index_expression: &'a Option<Box<Expression<'a>>>,
) -> Option<SemanticError<'a>> {
  match (size, index_expression) {
    (Some(size), Some(index_expression)) => {
      if let Expression::Literal { literal: Literal::Int(index), span } = &**index_expression {
        index_bounds_check(*index as usize, size, identifier, span)
      } else {
        None
      }
    }
    (None, Some(_)) => Some(SemanticError::ArrayError { span, identifier: identifier.clone() }),
    _ => None,
  }
}

pub fn check_variable_index<'a>(
  identifier: &Identifier,
  span: &'a Span<'_>,
  size: Option<usize>,
  index_expression: &'a Option<Expression<'a>>,
) -> Option<SemanticError<'a>> {
  match (size, index_expression) {
    (Some(size), Some(index_expression)) => {
      if let Expression::Literal { literal: Literal::Int(index), span } = index_expression {
        index_bounds_check(*index as usize, size, identifier, span)
      } else {
        None
      }
    }
    (None, Some(_)) => Some(SemanticError::ArrayError { span, identifier: identifier.clone() }),
    _ => None,
  }
}

pub fn check_condition<'a>(
  scope: &Rc<RefCell<Scope>>,
  condition: &'a Expression<'a>,
  span: &'a Span<'_>,
) -> Vec<SemanticError<'a>> {
  let mut errors = Vec::new();

  if let Some(condition_ty) = get_expression_type(scope, condition) {
    if condition_ty != Ty::Bool {
      errors.push(SemanticError::InvalidConditionType { span, actual: condition_ty })
    }
  } else {
    errors.push(SemanticError::InvalidCondition { span })
  }

  if let Err(expression_errors) = condition.check_semantics(scope) {
    errors.extend(expression_errors)
  }

  errors
}

pub fn check_function_call<'a>(
  scope: &Rc<RefCell<Scope>>,
  identifier: &Identifier,
  span: &'a Span<'_>,
  arguments: &'a [Expression<'a>],
) -> Vec<SemanticError<'a>> {
  match Scope::lookup(scope, identifier) {
    Some(Symbol::Function(..)) => check_function_call_arguments(scope, identifier, span, arguments),
    Some(Symbol::Variable(..)) => vec![SemanticError::NotAFunction { span, identifier: identifier.clone() }],
    None => vec![SemanticError::NotDeclared { span, identifier: identifier.clone() }],
  }
}

pub fn check_function_call_arguments<'a>(
  scope: &Rc<RefCell<Scope>>,
  identifier: &Identifier,
  span: &'a Span<'_>,
  arguments: &'a [Expression<'a>],
) -> Vec<SemanticError<'a>> {
  if let Some(Symbol::Function(_, args)) = Scope::lookup(scope, identifier) {
    if args.len() != arguments.len() {
      return vec![SemanticError::InvalidAmountOfArguments {
        span,
        identifier: identifier.clone(),
        expected: args.len(),
        actual: arguments.len(),
      }];
    }

    return args
      .iter()
      .zip(arguments.iter())
      .filter_map(|(arg, argument)| check_function_call_argument_type(scope, arg, argument, identifier, span))
      .collect();
  }

  Vec::with_capacity(0)
}

pub fn check_function_call_argument_type<'a>(
  scope: &Rc<RefCell<Scope>>,
  symbol_arg: &(Ty, Option<usize>),
  arg_expression: &'a Expression<'a>,
  identifier: &Identifier,
  span: &'a Span<'_>,
) -> Option<SemanticError<'a>> {
  if arg_expression.check_semantics(scope).is_err() {
    Some(SemanticError::InvalidArgument { span, identifier: identifier.clone() })
  } else if let Some(ty) = get_expression_type(scope, arg_expression) {
    if ty != symbol_arg.0 {
      return Some(SemanticError::InvalidArgumentType {
        span,
        identifier: identifier.clone(),
        expected: symbol_arg.0.clone(),
        actual: ty,
      });
    }
    None
  } else {
    Some(SemanticError::ReturnTypeExpected { span, identifier: identifier.clone() })
  }
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
      if let Some(error) = check_variable(scope, identifier, span, index_expression) {
        errors.push(error)
      } else if let Some(ty) = get_expression_type(scope, expression) {
        if let Some(error) = check_unary_operator_compatability(op, ty, span) {
          errors.push(error)
        }
      }
    }
    Expression::FunctionCall { identifier, arguments, .. } => {
      errors.extend(check_function_call(scope, identifier, span, arguments));

      if let Some(ty) = get_expression_type(scope, expression) {
        if let Some(error) = check_unary_operator_compatability(op, ty, span) {
          errors.push(error)
        }
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
    Expression::Binary { op: binary_op, .. } => {
      if let Err(exp_errors) = expression.check_semantics(scope) {
        errors.extend(exp_errors)
      }
      if let Some(error) = check_operator_combination(op, binary_op, span) {
        errors.push(error)
      }
    }
  }

  errors
}

pub fn check_binary_expression<'a>(
  scope: &Rc<RefCell<Scope>>,
  op: &'a BinaryOp,
  lhs: &'a Expression<'a>,
  rhs: &'a Expression<'a>,
  span: &'a Span<'_>,
) -> Vec<SemanticError<'a>> {
  let mut errors = Vec::new();

  if let Err(lhs_errors) = lhs.check_semantics(scope) {
    errors.extend(lhs_errors)
  }
  if let Err(rhs_errors) = rhs.check_semantics(scope) {
    errors.extend(rhs_errors)
  }

  if let (Some(lhs_ty), Some(rhs_ty)) = (get_expression_type(scope, lhs), get_expression_type(scope, rhs)) {
    if lhs_ty != rhs_ty {
      errors.push(SemanticError::BinaryOperatorTypeCombinationError { span, op, lhs_ty, rhs_ty })
    } else if let Some(error) = check_binary_opeartor_compatability(op, lhs_ty, span) {
      errors.push(error)
    }
  }

  // Determine the right span, when nesting a call to a `void` function in a binary expression.
  for exp in [lhs, rhs].iter() {
    if let Expression::FunctionCall { identifier, span, .. } = exp {
      if let Some(Symbol::Function(None, ..)) = Scope::lookup(scope, identifier) {
        errors.push(SemanticError::ReturnTypeExpected { span, identifier: identifier.clone() })
      }
    }
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

pub fn check_binary_opeartor_compatability<'a>(
  op: &'a BinaryOp,
  ty: Ty,
  span: &'a Span<'_>,
) -> Option<SemanticError<'a>> {
  match ty {
    Ty::Bool if [BinaryOp::Divide, BinaryOp::Times, BinaryOp::Minus, BinaryOp::Plus].contains(op) => {
      Some(SemanticError::BinaryOperatorTypeError { span, op, ty })
    }
    Ty::Int | Ty::Float if [BinaryOp::Land, BinaryOp::Lor].contains(op) => {
      Some(SemanticError::BinaryOperatorTypeError { span, op, ty })
    }
    Ty::String if ![BinaryOp::Eq, BinaryOp::Neq].contains(op) => {
      Some(SemanticError::BinaryOperatorTypeError { span, op, ty })
    }
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

pub fn check_operator_combination<'a>(
  unary_op: &'a UnaryOp,
  binary_op: &'a BinaryOp,
  span: &'a Span<'_>,
) -> Option<SemanticError<'a>> {
  match unary_op {
    UnaryOp::Not if [BinaryOp::Divide, BinaryOp::Times, BinaryOp::Minus, BinaryOp::Plus].contains(binary_op) => {
      Some(SemanticError::OperatorCombinationError { span, unary_op, binary_op })
    }
    UnaryOp::Minus if ![BinaryOp::Divide, BinaryOp::Times, BinaryOp::Minus, BinaryOp::Plus].contains(binary_op) => {
      Some(SemanticError::OperatorCombinationError { span, unary_op, binary_op })
    }
    _ => None,
  }
}
