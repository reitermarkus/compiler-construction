use std::fmt;

use from_pest::{ConversionError, FromPest};
use pest::{
  iterators::{Pair, Pairs}
};

use crate::Rule;

#[derive(Debug)]
pub enum Ty {
  Bool,
  Int,
  Float,
  String,
}

impl fmt::Display for Ty {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Bool => "bool",
      Self::Int => "int",
      Self::Float => "float",
      Self::String => "string",
    }
    .fmt(f)
  }
}

impl FromPest<'_> for Ty {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(
    pest: &mut Pairs<'_, Self::Rule>,
  ) -> Result<Self, ConversionError<Self::FatalError>> {
    let pair = pest.next().unwrap();
    assert!(pest.next().is_none());

    Ok(match pair.as_rule() {
      Rule::boolean => Self::Bool,
      Rule::int => Self::Int,
      Rule::float => Self::Float,
      Rule::string => Self::String,
      rule => {
        return Err(ConversionError::Malformed(format!(
          "unknown literal: {:?}",
          rule
        )))
      }
    })
  }
}

#[derive(Debug)]
pub enum Literal {
  Bool(bool),
  Int(i64),
  Float(f64),
  String(String),
}

#[derive(Debug)]
pub enum UnaryOp {
  Minus,
  Not,
}

impl fmt::Display for UnaryOp {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Minus => "-",
      Self::Not => "!",
    }
    .fmt(f)
  }
}

impl FromPest<'_> for UnaryOp {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(
    pest: &mut Pairs<'_, Self::Rule>,
  ) -> Result<Self, ConversionError<Self::FatalError>> {
    let op = pest.next().unwrap();
    assert!(pest.next().is_none());

    Ok(match op.as_rule() {
      Rule::unary_minus => Self::Minus,
      Rule::not => Self::Not,
      rule => {
        return Err(ConversionError::Malformed(format!(
          "unknown unary operation: {:?}",
          rule
        )))
      }
    })
  }
}

#[derive(Debug)]
pub enum BinaryOp {
  Plus,
  Minus,
  Times,
  Divide,
  Eq,
  Neq,
  Lte,
  Lt,
  Gte,
  Gt,
  Land,
  Lor,
}

impl fmt::Display for BinaryOp {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Plus => "+",
      Self::Minus => "-",
      Self::Times => "*",
      Self::Divide => "/",
      Self::Eq => "==",
      Self::Neq => "!=",
      Self::Lte => "<=",
      Self::Lt => "<",
      Self::Gte => ">=",
      Self::Gt => ">",
      Self::Land => "&&",
      Self::Lor => "||",
    }
    .fmt(f)
  }
}

impl FromPest<'_> for BinaryOp {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(
    pest: &mut Pairs<'_, Self::Rule>,
  ) -> Result<Self, ConversionError<Self::FatalError>> {
    let op = pest.next().unwrap();
    assert!(pest.next().is_none());

    Ok(match op.as_rule() {
      Rule::plus => Self::Plus,
      Rule::minus => Self::Minus,
      Rule::times => Self::Times,
      Rule::divide => Self::Divide,
      Rule::eq => Self::Eq,
      Rule::neq => Self::Neq,
      Rule::lte => Self::Lte,
      Rule::lt => Self::Lt,
      Rule::gte => Self::Gte,
      Rule::gt => Self::Gt,
      Rule::land => Self::Land,
      Rule::lor => Self::Lor,
      rule => {
        return Err(ConversionError::Malformed(format!(
          "unknown binary operation: {:?}",
          rule
        )))
      }
    })
  }
}

#[derive(Debug)]
pub enum Expression {
  Literal(Literal),
  Variable {
    identifier: String,
    index_expression: Option<Box<Expression>>,
  },
  FunctionCall {
    identifier: String,
    arguments: Vec<Expression>,
  },
  Unary {
    op: UnaryOp,
    expression: Box<Expression>,
  },
  Binary {
    op: BinaryOp,
    lhs: Box<Expression>,
    rhs: Box<Expression>,
  },
}

#[derive(Debug)]
pub struct Parameter {
  pub ty: String,
  pub identifier: String,
}

#[derive(Debug)]
pub struct Assignment {
  pub identifier: String,
  pub index_expression: Option<Expression>,
  pub rvalue: Expression,
}

#[derive(Debug)]
pub struct Declaration {
  pub ty: Ty,
  pub count: Option<usize>,
  pub identifier: String,
}

#[derive(Debug)]
pub struct IfStatement {
  pub condition: Expression,
  pub block: Statement,
  pub else_block: Option<Statement>,
}

#[derive(Debug)]
pub struct WhileStatement {
  pub condition: Expression,
  pub block: Statement,
}

#[derive(Debug)]
pub struct ReturnStatement {
  pub expression: Expression,
}

#[derive(Debug)]
pub enum Statement {
  If(Box<IfStatement>),
  While(Box<WhileStatement>),
  Ret(ReturnStatement),
  Decl(Declaration),
  Assignment(Assignment),
  Expression(Expression),
  Compound(CompoundStatement),
}

#[derive(Debug)]
pub struct CompoundStatement {
  pub statements: Vec<Statement>,
}

#[derive(Debug)]
pub struct FunctionDeclaration {
  pub ty: Option<String>,
  pub identifier: String,
  pub parameters: Vec<Parameter>,
  pub body: CompoundStatement,
}

#[derive(Debug)]
pub struct Program {
  pub function_declarations: Vec<FunctionDeclaration>,
}
