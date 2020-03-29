use std::fmt;

use from_pest::{ConversionError, FromPest};
use pest::{
  iterators::{Pair, Pairs},
  prec_climber::{Assoc, Operator, PrecClimber},
  Span,
};

use crate::Rule;

pub fn climber() -> PrecClimber<Rule> {
  // Reference: https://en.cppreference.com/w/c/language/operator_precedence
  PrecClimber::new(vec![
    Operator::new(Rule::lor, Assoc::Left),
    Operator::new(Rule::land, Assoc::Left),
    Operator::new(Rule::eq, Assoc::Left) | Operator::new(Rule::neq, Assoc::Left),
    Operator::new(Rule::lte, Assoc::Left)
      | Operator::new(Rule::lt, Assoc::Left)
      | Operator::new(Rule::gte, Assoc::Left)
      | Operator::new(Rule::gt, Assoc::Left),
    Operator::new(Rule::plus, Assoc::Left) | Operator::new(Rule::minus, Assoc::Left),
    Operator::new(Rule::times, Assoc::Left) | Operator::new(Rule::divide, Assoc::Left),
    Operator::new(Rule::not, Assoc::Left) | Operator::new(Rule::unary_minus, Assoc::Left),
  ])
}

#[derive(Clone, PartialEq, Debug)]
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

impl<'a> FromPest<'a> for Ty {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pest: &mut Pairs<'a, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let pair = pest.next().unwrap();

    Ok(match pair.as_str() {
      "bool" => Self::Bool,
      "int" => Self::Int,
      "float" => Self::Float,
      "string" => Self::String,
      _ => return Err(ConversionError::Malformed(format!("expected type, found {:?}", pair))),
    })
  }
}

impl From<&Literal> for Ty {
  fn from(literal: &Literal) -> Ty {
    match literal {
      Literal::Bool(_) => Self::Bool,
      Literal::Int(_) => Self::Int,
      Literal::Float(_) => Self::Float,
      Literal::String(_) => Self::String,
    }
  }
}

#[derive(PartialEq, Debug)]
pub enum Literal {
  Bool(bool),
  Int(i64),
  Float(f64),
  String(String),
}

impl<'a> FromPest<'a> for Literal {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pest: &mut Pairs<'a, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let pair = pest.next().unwrap();

    Ok(match pair.as_rule() {
      Rule::float => Self::Float(pair.as_str().parse::<f64>().expect("failed to parse float")),
      Rule::int => Self::Int(pair.as_str().parse::<i64>().expect("failed to parse int")),
      Rule::boolean => Self::Bool(pair.as_str().parse::<bool>().expect("failed to parse bool")),
      Rule::string => {
        Self::String(pair.into_inner().next().expect("failed to get inner string value").as_str().to_owned())
      }
      _ => return Err(ConversionError::Malformed(format!("expected literal, found {:?}", pair))),
    })
  }
}

#[derive(PartialEq, Debug)]
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

impl<'a> FromPest<'a> for UnaryOp {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pest: &mut Pairs<'a, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let op = pest.next().unwrap();

    Ok(match op.as_rule() {
      Rule::unary_minus => Self::Minus,
      Rule::not => Self::Not,
      rule => return Err(ConversionError::Malformed(format!("unknown unary operation: {:?}", rule))),
    })
  }
}

#[derive(PartialEq, Debug)]
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

impl<'a> FromPest<'a> for BinaryOp {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pest: &mut Pairs<'a, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let op = pest.next().unwrap();

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
      _ => return Err(ConversionError::Malformed(format!("expected binary operation, found {:?}", op))),
    })
  }
}

#[derive(PartialEq, Debug)]
pub enum Expression<'a> {
  Literal { literal: Literal, span: Span<'a> },
  Variable { identifier: Identifier, index_expression: Option<Box<Expression<'a>>>, span: Span<'a> },
  FunctionCall { identifier: Identifier, arguments: Vec<Expression<'a>>, span: Span<'a> },
  Unary { op: UnaryOp, expression: Box<Expression<'a>>, span: Span<'a> },
  Binary { op: BinaryOp, lhs: Box<Expression<'a>>, rhs: Box<Expression<'a>>, span: Span<'a> },
}

impl<'a> Expression<'a> {
  fn consume(
    pair: Pair<'a, Rule>,
    climber: &PrecClimber<Rule>,
  ) -> Result<(Self, Span<'a>), ConversionError<<Self as FromPest<'a>>::FatalError>> {
    let primary = |pair| Self::consume(pair, climber);

    let infix =
      |lhs: Result<(Expression<'a>, Span<'a>), ConversionError<<Self as FromPest<'a>>::FatalError>>,
       op: Pair<'a, Rule>,
       rhs: Result<(Expression<'a>, Span<'a>), ConversionError<<Self as FromPest<'a>>::FatalError>>| {
        let lhs = lhs?;
        let rhs = rhs?;

        let span = lhs.1.start_pos().span(&rhs.1.end_pos());

        let expr = Expression::Binary {
          op: BinaryOp::from_pest(&mut Pairs::single(op))?,
          lhs: Box::new(lhs.0),
          rhs: Box::new(rhs.0),
          span: span.clone(),
        };

        Ok((expr, span))
      };

    let outer_span = pair.as_span();

    let expr = match pair.as_rule() {
      Rule::unary_expression => {
        let span = pair.as_span();

        let mut pairs = pair.into_inner();

        Expression::Unary {
          op: UnaryOp::from_pest(&mut pairs)?,
          expression: Box::new(climber.climb(pairs, primary, infix)?.0),
          span,
        }
      }
      Rule::expression | Rule::par_expression => climber.climb(pair.into_inner(), primary, infix)?.0,
      Rule::call_expr => {
        let span = pair.as_span();

        let mut pairs = pair.into_inner();

        let identifier = Identifier::from_pest(&mut pairs)?;

        let arguments = pairs
          .next()
          .map(|args| {
            args
              .into_inner()
              .map(|p| Ok(climber.climb(p.into_inner(), primary, infix)?.0))
              .collect::<Result<Vec<_>, _>>()
          })
          .unwrap_or_else(|| Ok(Vec::new()))?;

        Expression::FunctionCall { identifier, arguments, span }
      }
      Rule::literal => {
        let span = pair.as_span();
        Expression::Literal { literal: Literal::from_pest(&mut pair.into_inner())?, span }
      }
      Rule::identifier => {
        let span = pair.as_span();

        let mut pairs = Pairs::single(pair);

        let identifier = Identifier::from_pest(&mut pairs)?;

        Expression::Variable {
          identifier,
          index_expression: pairs
            .next()
            .map(|index| Expression::from_pest(&mut Pairs::single(index)))
            .transpose()?
            .map(Box::new),
          span,
        }
      }
      _ => unreachable!(),
    };

    Ok((expr, outer_span))
  }
}

impl<'a> FromPest<'a> for Expression<'a> {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pest: &mut Pairs<'a, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let pair = pest.next().expect("no expression found");
    let climber = climber();
    Self::consume(pair, &climber).map(|r| r.0)
  }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Identifier(pub String);

impl fmt::Display for Identifier {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.0.fmt(f)
  }
}

impl FromPest<'_> for Identifier {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'_, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let identifier = pairs.next().expect("no identifier found").as_str();
    Ok(Self(identifier.into()))
  }
}

impl From<&str> for Identifier {
  fn from(identifier: &str) -> Self {
    Identifier(identifier.into())
  }
}

#[derive(PartialEq, Debug)]
pub struct Parameter {
  pub ty: Ty,
  pub count: Option<usize>,
  pub identifier: Identifier,
}

impl FromPest<'_> for Parameter {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'_, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let mut inner = pairs.next().expect("no parameter found").into_inner();

    let mut param_type = inner.next().expect("no declaration type").into_inner();
    let (ty, count) = match (param_type.next(), param_type.next()) {
      (Some(ty), Some(int)) => (Ty::from_pest(&mut Pairs::single(ty))?, Some(int.as_str().parse::<usize>().unwrap())),
      (Some(ty), None) => (Ty::from_pest(&mut Pairs::single(ty))?, None),
      _ => unreachable!(),
    };

    let identifier = Identifier::from_pest(&mut inner)?;

    Ok(Self { ty, count, identifier })
  }
}

#[derive(PartialEq, Debug)]
pub struct Assignment<'a> {
  pub identifier: Identifier,
  pub index_expression: Option<Expression<'a>>,
  pub rvalue: Expression<'a>,
  pub span: Span<'a>,
}

impl<'a> FromPest<'a> for Assignment<'a> {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'a, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let pair = pairs.next().expect("no assignment found");
    let span = pair.as_span();
    let mut inner = pair.into_inner();

    let identifier = Identifier::from_pest(&mut inner)?;

    let (index_expression, rvalue) = match (inner.next(), inner.next()) {
      (Some(index), Some(rvalue)) => {
        (Some(Expression::from_pest(&mut Pairs::single(index))?), Expression::from_pest(&mut Pairs::single(rvalue))?)
      }
      (Some(rvalue), None) => (None, Expression::from_pest(&mut Pairs::single(rvalue))?),
      _ => unreachable!(),
    };

    Ok(Self { identifier, index_expression, rvalue, span })
  }
}

#[derive(PartialEq, Debug)]
pub struct Declaration<'a> {
  pub ty: Ty,
  pub count: Option<usize>,
  pub identifier: Identifier,
  pub span: Span<'a>,
}

impl<'a> FromPest<'a> for Declaration<'a> {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'a, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let pair = pairs.next().expect("no declaration found");
    let span = pair.as_span();
    let mut inner = pair.into_inner();

    let mut dec_type = inner.next().expect("no declaration type found").into_inner();
    let (ty, count) = match (dec_type.next(), dec_type.next()) {
      (Some(ty), Some(int)) => (Ty::from_pest(&mut Pairs::single(ty))?, Some(int.as_str().parse::<usize>().unwrap())),
      (Some(ty), None) => (Ty::from_pest(&mut Pairs::single(ty))?, None),
      _ => unreachable!(),
    };

    let identifier = Identifier::from_pest(&mut inner)?;

    Ok(Self { ty, count, identifier, span })
  }
}

#[derive(PartialEq, Debug)]
pub struct IfStatement<'a> {
  pub condition: Expression<'a>,
  pub block: Statement<'a>,
  pub else_block: Option<Statement<'a>>,
  pub span: Span<'a>,
}

impl<'a> FromPest<'a> for IfStatement<'a> {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'a, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let pair = pairs.next().expect("no if statement found");
    let span = pair.as_span();
    let mut inner = pair.into_inner();

    Ok(Self {
      condition: Expression::from_pest(&mut inner)?,
      block: Statement::from_pest(&mut inner)?,
      else_block: match inner.next() {
        Some(statement) => Some(Statement::from_pest(&mut Pairs::single(statement))?),
        None => None,
      },
      span,
    })
  }
}

#[derive(PartialEq, Debug)]
pub struct WhileStatement<'a> {
  pub condition: Expression<'a>,
  pub block: Statement<'a>,
  pub span: Span<'a>,
}

impl<'a> FromPest<'a> for WhileStatement<'a> {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'a, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let pair = pairs.next().expect("no while statement found");
    let span = pair.as_span();
    let mut inner = pair.into_inner();

    Ok(Self { condition: Expression::from_pest(&mut inner)?, block: Statement::from_pest(&mut inner)?, span })
  }
}

#[derive(PartialEq, Debug)]
pub struct ReturnStatement<'a> {
  pub expression: Option<Expression<'a>>,
  pub span: Span<'a>,
}

impl<'a> FromPest<'a> for ReturnStatement<'a> {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'a, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let pair = pairs.next().expect("no return statement found");
    let span = pair.as_span();
    let mut inner = pair.into_inner();

    let expression = if inner.peek().is_some() { Some(Expression::from_pest(&mut inner)?) } else { None };

    Ok(Self { expression, span })
  }
}

#[derive(PartialEq, Debug)]
pub struct CompoundStatement<'a> {
  pub statements: Vec<Statement<'a>>,
  pub span: Span<'a>,
}

impl<'a> FromPest<'a> for CompoundStatement<'a> {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'a, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let pair = pairs.next().expect("no compound statement found");
    let span = pair.as_span();

    Ok(Self {
      statements: pair
        .into_inner()
        .map(|stmt| Statement::from_pest(&mut Pairs::single(stmt)))
        .collect::<Result<Vec<_>, _>>()?,
      span,
    })
  }
}

#[derive(PartialEq, Debug)]
pub enum Statement<'a> {
  If(Box<IfStatement<'a>>),
  While(Box<WhileStatement<'a>>),
  Ret(ReturnStatement<'a>),
  Decl(Declaration<'a>),
  Assignment(Box<Assignment<'a>>),
  Expression(Expression<'a>),
  Compound(CompoundStatement<'a>),
}

impl<'a> FromPest<'a> for Statement<'a> {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'a, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let mut inner = pairs.next().expect("no statement found").into_inner();

    Ok(match inner.peek().unwrap().as_rule() {
      Rule::if_stmt => Self::If(Box::new(IfStatement::from_pest(&mut inner)?)),
      Rule::while_stmt => Self::While(Box::new(WhileStatement::from_pest(&mut inner)?)),
      Rule::ret_stmt => Self::Ret(ReturnStatement::from_pest(&mut inner)?),
      Rule::declaration => Self::Decl(Declaration::from_pest(&mut inner)?),
      Rule::assignment => Self::Assignment(Box::new(Assignment::from_pest(&mut inner)?)),
      Rule::expression => Self::Expression(Expression::from_pest(&mut inner)?),
      Rule::compound_stmt => Self::Compound(CompoundStatement::from_pest(&mut inner)?),
      rule => return Err(ConversionError::Malformed(format!("unknown statement: {:?}", rule))),
    })
  }
}

#[derive(PartialEq, Debug)]
pub struct FunctionDeclaration<'a> {
  pub ty: Option<Ty>,
  pub identifier: Identifier,
  pub parameters: Vec<Parameter>,
  pub body: CompoundStatement<'a>,
  pub span: Span<'a>,
}

impl<'a> FromPest<'a> for FunctionDeclaration<'a> {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'a, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let pair = pairs.next().expect("no function declaration found");
    let span = pair.as_span();
    let mut inner = pair.into_inner();

    let ty = if inner.peek().map(|p| p.as_rule()) == Some(Rule::ty) { Some(Ty::from_pest(&mut inner)?) } else { None };

    let identifier = Identifier::from_pest(&mut inner)?;

    let parameters = if inner.peek().map(|p| p.as_rule()) == Some(Rule::parameters) {
      let params = inner.next().unwrap().into_inner();
      params.map(|p| Parameter::from_pest(&mut Pairs::single(p))).collect::<Result<Vec<_>, _>>()?
    } else {
      vec![]
    };

    let body = CompoundStatement::from_pest(&mut inner)?;

    Ok(Self { ty, identifier, parameters, body, span })
  }
}

#[derive(PartialEq, Debug)]
pub struct Program<'a> {
  pub function_declarations: Vec<FunctionDeclaration<'a>>,
}

impl<'a> FromPest<'a> for Program<'a> {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'a, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let inner = pairs.next().expect("no program found").into_inner();

    Ok(Self {
      function_declarations: inner
        .take_while(|p| p.as_rule() != Rule::EOI)
        .map(|dec| {
          FunctionDeclaration::from_pest(&mut Pairs::single(dec)).expect("failed to parse function declaration")
        })
        .collect(),
    })
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{McParser, Rule};
  use pest::Parser;
  use pretty_assertions::assert_eq;

  #[test]
  fn return_statement_from_pest() {
    let expr = "return;";
    let mut pairs = McParser::parse(Rule::ret_stmt, &expr).unwrap();
    ReturnStatement::from_pest(&mut pairs).unwrap();
  }

  #[test]
  fn expression_from_pest() {
    let expr = "2 * 2 + 4 / (-4.9 - pi(true, nested()))";
    let mut pairs = McParser::parse(Rule::expression, &expr).unwrap();

    assert_eq!(
      Expression::from_pest(&mut pairs).unwrap(),
      Expression::Binary {
        op: BinaryOp::Plus,
        lhs: Box::new(Expression::Binary {
          op: BinaryOp::Times,
          lhs: Box::new(Expression::Literal { literal: Literal::Int(2), span: Span::new(&expr, 0, 1).unwrap() }),
          rhs: Box::new(Expression::Literal { literal: Literal::Int(2), span: Span::new(&expr, 4, 5).unwrap() }),
          span: Span::new(&expr, 0, 5).unwrap(),
        }),
        rhs: Box::new(Expression::Binary {
          op: BinaryOp::Divide,
          lhs: Box::new(Expression::Literal { literal: Literal::Int(4), span: Span::new(&expr, 8, 9).unwrap() }),
          rhs: Box::new(Expression::Binary {
            op: BinaryOp::Minus,
            lhs: Box::new(Expression::Unary {
              op: UnaryOp::Minus,
              expression: Box::new(Expression::Literal {
                literal: Literal::Float(4.9),
                span: Span::new(&expr, 14, 17).unwrap(),
              }),
              span: Span::new(&expr, 13, 17).unwrap(),
            }),
            rhs: Box::new(Expression::FunctionCall {
              identifier: Identifier::from("pi"),
              arguments: vec![
                Expression::Literal { literal: Literal::Bool(true), span: Span::new(&expr, 23, 27).unwrap() },
                Expression::FunctionCall {
                  identifier: Identifier::from("nested"),
                  arguments: vec![],
                  span: Span::new(&expr, 29, 37).unwrap()
                },
              ],
              span: Span::new(&expr, 20, 38).unwrap(),
            }),
            span: Span::new(&expr, 13, 38).unwrap(),
          }),
          span: Span::new(&expr, 8, 39).unwrap(),
        }),
        span: Span::new(&expr, 0, 39).unwrap(),
      }
    );
  }

  #[test]
  fn assignment_from_pest() {
    let assignment_with_index = "numbers[10] = 12.4";
    let mut pairs = McParser::parse(Rule::assignment, &assignment_with_index).unwrap();

    assert_eq!(
      Assignment::from_pest(&mut pairs).unwrap(),
      Assignment {
        identifier: Identifier::from("numbers"),
        index_expression: Some(Expression::Literal {
          literal: Literal::Int(10),
          span: Span::new(&assignment_with_index, 8, 10).unwrap()
        }),
        rvalue: Expression::Literal {
          literal: Literal::Float(12.4),
          span: Span::new(&assignment_with_index, 14, 18).unwrap()
        },
        span: Span::new(&assignment_with_index, 0, 18).unwrap(),
      }
    );

    let assignment_no_index = "number = 12.4";
    pairs = McParser::parse(Rule::assignment, &assignment_no_index).unwrap();

    assert_eq!(
      Assignment::from_pest(&mut pairs).unwrap(),
      Assignment {
        identifier: Identifier::from("number"),
        index_expression: None,
        rvalue: Expression::Literal {
          literal: Literal::Float(12.4),
          span: Span::new(&assignment_no_index, 9, 13).unwrap()
        },
        span: Span::new(&assignment_no_index, 0, 13).unwrap(),
      }
    )
  }

  #[test]
  fn declaration_from_pest() {
    let declaration_with_index = "int[5] numbers";
    let mut pairs = McParser::parse(Rule::declaration, &declaration_with_index).unwrap();

    assert_eq!(
      Declaration::from_pest(&mut pairs).unwrap(),
      Declaration {
        ty: Ty::Int,
        count: Some("5".to_string().parse::<usize>().unwrap()),
        identifier: Identifier::from("numbers"),
        span: Span::new(&declaration_with_index, 0, 14).unwrap(),
      }
    );

    let declaration_no_index = "float x";
    pairs = McParser::parse(Rule::declaration, &declaration_no_index).unwrap();

    assert_eq!(
      Declaration::from_pest(&mut pairs).unwrap(),
      Declaration {
        ty: Ty::Float,
        count: None,
        identifier: Identifier::from("x"),
        span: Span::new(&declaration_no_index, 0, 7).unwrap()
      }
    )
  }

  #[test]
  fn if_stmt_from_pest() {
    let if_stmt = "if (lol == true) { i = 1; } else { return i; }";
    let mut pairs = McParser::parse(Rule::if_stmt, &if_stmt).unwrap();

    assert_eq!(
      IfStatement::from_pest(&mut pairs).unwrap(),
      IfStatement {
        condition: Expression::Binary {
          op: BinaryOp::Eq,
          lhs: Box::new(Expression::Variable {
            identifier: Identifier::from("lol"),
            index_expression: None,
            span: Span::new(&if_stmt, 4, 7).unwrap(),
          }),
          rhs: Box::new(Expression::Literal {
            literal: Literal::Bool(true),
            span: Span::new(&if_stmt, 11, 15).unwrap(),
          }),
          span: Span::new(&if_stmt, 4, 15).unwrap(),
        },
        block: Statement::Compound(CompoundStatement {
          statements: vec![Statement::Assignment(Box::new(Assignment {
            identifier: Identifier::from("i"),
            index_expression: None,
            rvalue: Expression::Literal { literal: Literal::Int(1), span: Span::new(&if_stmt, 23, 24).unwrap() },
            span: Span::new(&if_stmt, 19, 24).unwrap(),
          }))],
          span: Span::new(&if_stmt, 17, 27).unwrap(),
        }),
        else_block: Some(Statement::Compound(CompoundStatement {
          statements: vec![Statement::Ret(ReturnStatement {
            expression: Some(Expression::Variable {
              identifier: Identifier::from("i"),
              index_expression: None,
              span: Span::new(&if_stmt, 42, 43).unwrap(),
            }),
            span: Span::new(&if_stmt, 35, 44).unwrap(),
          })],
          span: Span::new(&if_stmt, 33, 46).unwrap(),
        })),
        span: Span::new(&if_stmt, 0, 46).unwrap(),
      }
    )
  }

  #[test]
  fn function_declaration_from_pest() {
    let if_stmt = "int sum(int[16] n) { }";
    let mut pairs = McParser::parse(Rule::function_def, &if_stmt).unwrap();

    assert_eq!(
      FunctionDeclaration::from_pest(&mut pairs).unwrap(),
      FunctionDeclaration {
        ty: Some(Ty::Int),
        identifier: Identifier::from("sum"),
        parameters: vec![Parameter { ty: Ty::Int, count: Some(16), identifier: Identifier::from("n") }],
        body: CompoundStatement { statements: vec![], span: Span::new(&if_stmt, 19, 22).unwrap() },
        span: Span::new(&if_stmt, 0, 22).unwrap(),
      }
    )
  }

  #[test]
  fn dangling_else() {
    let dangling_else = r#"
      if (c1)
        if (c2)
          f2();
        else
          f3();
    "#;

    assert_eq!(
      IfStatement::from_pest(&mut McParser::parse(Rule::if_stmt, &dangling_else).unwrap()).unwrap(),
      IfStatement {
        condition: Expression::Variable {
          identifier: Identifier::from("c1"),
          index_expression: None,
          span: Span::new(&dangling_else, 11, 13).unwrap(),
        },
        block: Statement::If(Box::new(IfStatement {
          condition: Expression::Variable {
            identifier: Identifier::from("c2"),
            index_expression: None,
            span: Span::new(&dangling_else, 27, 29).unwrap(),
          },
          block: Statement::Expression(Expression::FunctionCall {
            identifier: Identifier::from("f2"),
            arguments: vec![],
            span: Span::new(&dangling_else, 41, 45).unwrap(),
          }),
          else_block: Some(Statement::Expression(Expression::FunctionCall {
            identifier: Identifier::from("f3"),
            arguments: vec![],
            span: Span::new(&dangling_else, 70, 74).unwrap(),
          })),
          span: Span::new(&dangling_else, 23, 75).unwrap(),
        })),
        else_block: None,
        span: Span::new(&dangling_else, 0, 80).unwrap(),
      }
    )
  }
}
