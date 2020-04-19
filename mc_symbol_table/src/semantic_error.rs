use std::fmt;

use pest::Span;

use mc_parser::ast::*;

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
  AlreadyDeclared {
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
  ReturnTypeExpected {
    span: &'a Span<'a>,
    identifier: Identifier,
  },
  InvalidAmountOfArguments {
    span: &'a Span<'a>,
    identifier: Identifier,
    expected: usize,
    actual: usize,
  },
  InvalidArgumentType {
    span: &'a Span<'a>,
    identifier: Identifier,
    expected: Ty,
    actual: Ty,
  },
  InvalidDeclarationType {
    span: &'a Span<'a>,
    identifier: Identifier,
    expected: Ty,
    actual: Ty,
  },
  InvalidReturnType {
    span: &'a Span<'a>,
    expected: Option<Ty>,
    actual: Option<Ty>,
  },
  MatchingReturnError {
    span: Span<'a>,
  },
  InvalidArgument {
    span: &'a Span<'a>,
    identifier: Identifier,
  },
  OperatorCombinationError {
    span: &'a Span<'a>,
    unary_op: &'a UnaryOp,
    binary_op: &'a BinaryOp,
  },
  BinaryOperatorTypeCombinationError {
    span: &'a Span<'a>,
    op: &'a BinaryOp,
    lhs_ty: Ty,
    rhs_ty: Ty,
  },
  BinaryOperatorTypeError {
    span: &'a Span<'a>,
    op: &'a BinaryOp,
    ty: Ty,
  },
  NoMainFunction {
    span: &'a Span<'a>,
  },
  InvalidConditionType {
    span: &'a Span<'a>,
    actual: Ty,
  },
  InvalidCondition {
    span: &'a Span<'a>,
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
      Self::AlreadyDeclared { span, identifier } => {
        write_err!(f, span, "variable '{}' already declared in this scope", identifier)
      }
      Self::ArrayError { span, identifier } => write_err!(f, span, "variable '{}' is not an array", identifier),
      Self::IndexOutOfBounds { span, identifier, size, actual } => {
        write_err!(f, span, "index {} out of bound for '{}' with size {}", actual, identifier, size)
      }
      Self::WrongUseOfFunction { span, identifier } => write_err!(f, span, "wrong use of function '{}'", identifier),
      Self::NotAFunction { span, identifier } => write_err!(f, span, "'{}' is not a function", identifier),
      Self::InvalidAmountOfArguments { span, identifier, expected, actual } => write_err!(
        f,
        span,
        "Invalid amount of arguemnts in fucntion '{}': expected '{}' arguments, found '{}' arguments",
        identifier,
        expected,
        actual
      ),
      Self::InvalidArgumentType { span, identifier, expected, actual } => {
        write_err!(f, span, "function '{}' expected argument of type {}, found {}", identifier, expected, actual)
      }
      Self::InvalidDeclarationType { span, identifier, expected, actual } => {
        write_err!(f, span, "variable '{}' expected type {}, found {}", identifier, expected, actual)
      }
      Self::InvalidReturnType { span, expected, actual } => write_err!(
        f,
        span,
        "expected return type {}, found {}",
        expected.as_ref().map(|ty| ty.to_string()).unwrap_or_else(|| "void".into()),
        actual.as_ref().map(|ty| ty.to_string()).unwrap_or_else(|| "void".into())
      ),
      Self::InvalidArgument { span, identifier } => {
        write_err!(f, span, "invalid argument supplied to function '{}'", identifier)
      }
      Self::UnaryOperatorTypeError { span, op, ty } => {
        write_err!(f, span, "operator '{}' cannot be used with type '{}'", op, ty)
      }
      Self::UnaryOperatorCombinationError { span, outer, inner } => {
        write_err!(f, span, "operator '{}' cannot be combined with operator '{}'", inner, outer)
      }
      Self::OperatorCombinationError { span, unary_op, binary_op } => {
        write_err!(f, span, "unary operator '{}' cannot be combined with binary operator '{}'", unary_op, binary_op)
      }
      Self::MatchingReturnError { span } => write_err!(f, span, "if statement expects matching return statement"),
      Self::ReturnTypeExpected { span, identifier } => {
        write_err!(f, span, "expected return type for function '{}'", identifier)
      }
      Self::BinaryOperatorTypeCombinationError { span, op, lhs_ty, rhs_ty } => {
        write_err!(f, span, "operator '{}' cannot be used with types '{}' ans '{}'", op, lhs_ty, rhs_ty)
      }
      Self::BinaryOperatorTypeError { span, op, ty } => {
        write_err!(f, span, "operator '{}' cannot be used with type '{}'", op, ty)
      }
      Self::NoMainFunction { span } => write_err!(f, span, "required function 'main' not found"),
      Self::InvalidCondition { span } => write_err!(f, span, "invalid condition"),
      Self::InvalidConditionType { span, actual } => {
        write_err!(f, span, "expected type '{}' for condition, found '{}'", Ty::Bool, actual)
      }
    }
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

    assert!(errors.contains(&SemanticError::NoMainFunction { span: &Span::new("", 0, 0).unwrap() }))
  }

  #[test]
  fn semantic_function_declaration_check() {
    let function_declaration = FunctionDeclaration {
      ty: Some(Ty::Float),
      identifier: Identifier::from("sum"),
      parameters: vec![
        Parameter { ty: Ty::Int, count: None, identifier: Identifier::from("n"), span: Span::new("", 0, 0).unwrap() },
        Parameter { ty: Ty::Int, count: None, identifier: Identifier::from("m"), span: Span::new("", 0, 0).unwrap() },
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
      span: &Span::new("", 0, 0).unwrap(),
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
      span: &Span::new(&expr, 0, 13).unwrap(),
      identifier: Identifier::from("pi"),
      expected: Ty::Int,
      actual: Ty::Float
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
      span: &Span::new(&expr, 0, 11).unwrap(),
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
      span: &Span::new(assignment_str, 0, 7).unwrap(),
      identifier: Identifier::from("x")
    }));

    scope.borrow_mut().symbols.insert(Identifier::from("x"), Symbol::Variable(Ty::Int, None));
    result = assignment.check_semantics(&scope);
    errors = result.expect_err("no errors found");

    assert!(errors.contains(&SemanticError::InvalidDeclarationType {
      span: &Span::new(assignment_str, 0, 7).unwrap(),
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
      span: &Span::new(declaration_str, 0, 9).unwrap(),
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
    scope.borrow_mut().symbols.insert(Identifier::from("x"), Symbol::Function(Some(Ty::Int), Vec::new()));
    result = variable_with_index.check_semantics(&scope);
    errors = result.expect_err("no errors found");

    assert!(errors.contains(&SemanticError::WrongUseOfFunction {
      span: &Span::new("x[10]", 0, 5).unwrap(),
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
      span: &Span::new(&expr, 0, 9).unwrap(),
      op: &UnaryOp::Not,
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
      span: &Span::new(&expr, 1, 10).unwrap(),
      op: &UnaryOp::Not,
      ty: Ty::Int,
    }));
    assert!(errors.contains(&SemanticError::UnaryOperatorCombinationError {
      span: &Span::new(&expr, 0, 10).unwrap(),
      outer: &UnaryOp::Minus,
      inner: &UnaryOp::Not,
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
      span: &Span::new(&expr, 6, 8).unwrap(),
      op: &UnaryOp::Not,
      ty: Ty::Int,
    }));
    assert!(errors.contains(&SemanticError::BinaryOperatorTypeCombinationError {
      span: &Span::new(&expr, 0, 8).unwrap(),
      op: &BinaryOp::Plus,
      lhs_ty: Ty::String,
      rhs_ty: Ty::Bool,
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
      span: &Span::new(&expr, 0, 10).unwrap(),
      op: &BinaryOp::Plus,
      ty: Ty::String,
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

    assert!(errors
      .contains(&SemanticError::InvalidConditionType { span: &Span::new(&expr, 0, 26).unwrap(), actual: Ty::Int }));

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

    assert!(errors
      .contains(&SemanticError::InvalidConditionType { span: &Span::new(&expr, 0, 25).unwrap(), actual: Ty::Int }));

    assert_eq!(errors.len(), 1);
  }
}
