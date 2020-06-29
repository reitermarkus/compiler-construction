use std::fmt;

use colored::*;
use pest::Span;

use mc_parser::ast::*;

#[derive(PartialEq, Debug)]
pub enum SemanticError<'a> {
  Type {
    span: Span<'a>,
    expected: Ty,
    actual: Ty,
  },
  NotDeclared {
    span: Span<'a>,
    identifier: Identifier<'a>,
  },
  AlreadyDeclared {
    span: Span<'a>,
    identifier: Identifier<'a>,
  },
  ArrayError {
    span: Span<'a>,
    identifier: Identifier<'a>,
  },
  IndexOutOfBounds {
    span: Span<'a>,
    identifier: Identifier<'a>,
    size: usize,
    actual: usize,
  },
  WrongUseOfFunctionAsVariable {
    span: Span<'a>,
    identifier: Identifier<'a>,
  },
  FunctionAssignment {
    span: Span<'a>,
    identifier: Identifier<'a>,
  },
  NotAFunction {
    span: Span<'a>,
    identifier: Identifier<'a>,
  },
  UnaryOperatorTypeError {
    span: Span<'a>,
    op: UnaryOp,
    ty: Ty,
  },
  UnaryOperatorCombinationError {
    span: Span<'a>,
    outer: UnaryOp,
    inner: UnaryOp,
  },
  /// Error when a non-void function is missing a return statement.
  MissingReturnStatement {
    span: Span<'a>,
    identifier: Identifier<'a>,
  },
  InvalidAmountOfArguments {
    span: Span<'a>,
    identifier: Identifier<'a>,
    expected: usize,
    actual: usize,
  },
  InvalidArgumentType {
    span: Span<'a>,
    identifier: Identifier<'a>,
    expected: Ty,
    actual: Option<Ty>,
  },
  InvalidDeclarationType {
    span: Span<'a>,
    identifier: Identifier<'a>,
    expected: Ty,
    actual: Ty,
  },
  InvalidReturnType {
    span: Span<'a>,
    expected: Option<Ty>,
    actual: Option<Ty>,
  },
  OperatorCombinationError {
    span: Span<'a>,
    unary_op: UnaryOp,
    binary_op: BinaryOp,
  },
  BinaryOperatorTypeError {
    span: Span<'a>,
    op: BinaryOp,
    lhs_ty: Option<Ty>,
    rhs_ty: Option<Ty>,
  },
  NoMainFunction {
    span: Span<'a>,
  },
  InvalidConditionType {
    span: Span<'a>,
    actual: Ty,
  },
  InvalidCondition {
    span: Span<'a>,
  },
}

macro_rules! write_err {
  ($f:expr, $span:expr, $($args:expr),*) => {{
    let (start_line, start_col) = $span.start_pos().line_col();
    let (end_line, end_col) = $span.end_pos().line_col();

    let line_count = end_line + 1 - start_line;
    let skip_lines = if line_count <= 3 { 0 } else { line_count - 3 };

    for (line_number, line) in (start_line..=end_line).zip($span.lines()).skip(skip_lines) {
      write!($f, "{}: {}", line_number.to_string().blue(), line)?;
    }

    let line_number_len = (start_line as f64 + 1.0).log10().ceil() as usize;
    let span_len = end_col - start_col;

    write!($f, "{0: <indentation$}", "", indentation = start_col - 1 + line_number_len + 2)?;

    write!($f, "{} ", format!("{0:^<1$}", "", span_len).red())?;
    write!($f, "{}", format!($($args,)*).red())
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
      Self::WrongUseOfFunctionAsVariable { span, identifier } => {
        write_err!(f, span, "wrong use of function '{}' as variable", identifier)
      }
      Self::FunctionAssignment { span, identifier } => {
        write_err!(f, span, "cannot assign to function '{}'", identifier)
      }
      Self::NotAFunction { span, identifier } => write_err!(f, span, "'{}' is not a function", identifier),
      Self::InvalidAmountOfArguments { span, identifier, expected, actual } => write_err!(
        f,
        span,
        "Invalid amount of arguemnts in fucntion '{}': expected '{}' arguments, found '{}' arguments",
        identifier,
        expected,
        actual
      ),
      Self::InvalidArgumentType { span, identifier, expected, actual } => write_err!(
        f,
        span,
        "function '{}' expected argument of type {}, found {}",
        identifier,
        expected,
        actual.as_ref().map(|ty| ty.to_string()).unwrap_or_else(|| "void".into())
      ),
      Self::InvalidDeclarationType { span, identifier, expected, actual } => {
        write_err!(f, span, "cannot assign {} to variable '{}' of type {}", actual, identifier, expected)
      }
      Self::InvalidReturnType { span, expected, actual } => write_err!(
        f,
        span,
        "expected return type {}, found {}",
        expected.as_ref().map(|ty| ty.to_string()).unwrap_or_else(|| "void".into()),
        actual.as_ref().map(|ty| ty.to_string()).unwrap_or_else(|| "void".into())
      ),
      Self::UnaryOperatorTypeError { span, op, ty } => {
        write_err!(f, span, "operator '{}' cannot be used with type '{}'", op, ty)
      }
      Self::UnaryOperatorCombinationError { span, outer, inner } => {
        write_err!(f, span, "operator '{}' cannot be combined with operator '{}'", inner, outer)
      }
      Self::OperatorCombinationError { span, unary_op, binary_op } => {
        write_err!(f, span, "unary operator '{}' cannot be combined with binary operator '{}'", unary_op, binary_op)
      }
      Self::MissingReturnStatement { span, identifier } => {
        write_err!(f, span, "missing return statement in function '{}'", identifier)
      }
      Self::BinaryOperatorTypeError { span, op, lhs_ty, rhs_ty } => write_err!(
        f,
        span,
        "operator '{}' cannot be used with types '{}' and '{}'",
        op,
        lhs_ty.as_ref().map(|ty| ty.to_string()).unwrap_or_else(|| "void".into()),
        rhs_ty.as_ref().map(|ty| ty.to_string()).unwrap_or_else(|| "void".into())
      ),
      Self::NoMainFunction { span } => write_err!(f, span, "required function 'main' not found"),
      Self::InvalidCondition { span } => write_err!(f, span, "invalid condition"),
      Self::InvalidConditionType { span, actual } => {
        write_err!(f, span, "expected type '{}' for condition, found '{}'", Ty::Bool, actual)
      }
    }
  }
}
