use std::fmt;

use from_pest::{ConversionError, FromPest};
use pest::{
  iterators::{Pair, Pairs},
  prec_climber::{Assoc, Operator, PrecClimber},
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

pub fn consume<'i>(pair: Pair<'i, Rule>, climber: &PrecClimber<Rule>) -> Expression {
  let primary = |pair| consume(pair, climber);

  let infix = |lhs: Expression, op: Pair<'_, Rule>, rhs: Expression| Expression::Binary {
    op: BinaryOp::from_pest(&mut Pairs::single(op)).unwrap(),
    lhs: Box::new(lhs),
    rhs: Box::new(rhs),
  };

  match pair.as_rule() {
    Rule::unary_expression => {
      let mut pairs = pair.into_inner();

      Expression::Unary {
        op: UnaryOp::from_pest(&mut pairs).unwrap(),
        expression: Box::new(climber.climb(pairs, primary, infix)),
      }
    }
    Rule::expression => climber.climb(pair.into_inner(), primary, infix),
    Rule::call_expr => {
      let mut pairs = pair.into_inner();

      let identifier = Identifier(pairs.next().expect("no identifier in call expression").as_str().to_string());
      let arguments = pairs
        .next()
        .map(|args| args.into_inner().map(|p| climber.climb(p.into_inner(), primary, infix)).collect())
        .unwrap_or_else(Vec::new);

      Expression::FunctionCall { identifier, arguments }
    }
    Rule::literal => Expression::Literal(Literal::from_pest(&mut pair.into_inner()).unwrap()),
    Rule::identifier => {
      let mut pairs = Pairs::single(pair);
      Expression::Variable {
        identifier: Identifier::from_pest(&mut pairs).unwrap(),
        index_expression: pairs.next().map(|index| Box::new(Expression::from_pest(&mut Pairs::single(index)).unwrap())),
      }
    }
    _ => unreachable!("pair {:?}", pair),
  }
}

#[derive(PartialEq, Debug)]
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

  fn from_pest(pest: &mut Pairs<'_, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let pair = pest.next().unwrap();
    assert!(pest.next().is_none());

    Ok(match pair.as_str() {
      "bool" => Self::Bool,
      "int" => Self::Int,
      "float" => Self::Float,
      "string" => Self::String,
      rule => return Err(ConversionError::Malformed(format!("unknown type: {:?}", rule))),
    })
  }
}

#[derive(PartialEq, Debug)]
pub enum Literal {
  Bool(bool),
  Int(i64),
  Float(f64),
  String(String),
}

impl FromPest<'_> for Literal {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pest: &mut Pairs<'_, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let pair = pest.next().unwrap();
    assert!(pest.next().is_none());

    Ok(match pair.as_rule() {
      Rule::float => Self::Float(pair.as_str().parse::<f64>().unwrap()),
      Rule::int => Self::Int(pair.as_str().parse::<i64>().unwrap()),
      Rule::boolean => Self::Bool(pair.as_str().parse::<bool>().unwrap()),
      Rule::string => Self::String(pair.as_str().to_owned()),
      rule => return Err(ConversionError::Malformed(format!("unknown literal: {:?}", rule))),
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

impl FromPest<'_> for UnaryOp {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pest: &mut Pairs<'_, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
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

impl FromPest<'_> for BinaryOp {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pest: &mut Pairs<'_, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
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
      rule => return Err(ConversionError::Malformed(format!("unknown binary operation: {:?}", rule))),
    })
  }
}

#[derive(PartialEq, Debug)]
pub enum Expression {
  Literal(Literal),
  Variable { identifier: Identifier, index_expression: Option<Box<Expression>> },
  FunctionCall { identifier: Identifier, arguments: Vec<Expression> },
  Unary { op: UnaryOp, expression: Box<Expression> },
  Binary { op: BinaryOp, lhs: Box<Expression>, rhs: Box<Expression> },
}

impl FromPest<'_> for Expression {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pest: &mut Pairs<'_, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let pair = pest.next().expect("no pair found");
    let climber = climber();
    Ok(consume(pair, &climber))
  }
}

#[derive(PartialEq, Debug)]
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
    let identifier = pairs.next().unwrap().as_str();
    Ok(Self(identifier.to_owned()))
  }
}

#[derive(PartialEq, Debug)]
pub struct Parameter {
  pub ty: String,
  pub identifier: Identifier,
}

impl FromPest<'_> for Parameter {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'_, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let mut inner = pairs.next().expect("no pair found").into_inner();
    let typ = inner.next().unwrap().as_str();
    assert!(!inner.next().is_none());
    Ok(Self { ty: typ.to_owned(), identifier: Identifier::from_pest(&mut inner).unwrap() })
  }
}

#[derive(PartialEq, Debug)]
pub struct Assignment {
  pub identifier: Identifier,
  pub index_expression: Option<Expression>,
  pub rvalue: Expression,
}

impl FromPest<'_> for Assignment {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'_, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let mut inner = pairs.next().expect("no pair found").into_inner();

    let identifier = Identifier::from_pest(&mut inner).unwrap();

    let (index_expression, rvalue) = match (inner.next(), inner.next()) {
      (Some(index), Some(rvalue)) => (
        Some(Expression::from_pest(&mut Pairs::single(index)).unwrap()),
        Expression::from_pest(&mut Pairs::single(rvalue)).unwrap(),
      ),
      (Some(rvalue), None) => (None, Expression::from_pest(&mut Pairs::single(rvalue)).unwrap()),
      _ => unreachable!(),
    };

    Ok(Self { identifier, index_expression, rvalue })
  }
}

#[derive(PartialEq, Debug)]
pub struct Declaration {
  pub ty: Ty,
  pub count: Option<usize>,
  pub identifier: Identifier,
}

impl FromPest<'_> for Declaration {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'_, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let mut inner = pairs.next().expect("no pair found").into_inner();

    let mut dec_type = inner.next().expect("no declaration type").into_inner();
    let (ty, count) = match (dec_type.next(), dec_type.next()) {
      (Some(ty), Some(int)) => {
        (Ty::from_pest(&mut Pairs::single(ty)).unwrap(), Some(int.as_str().parse::<usize>().unwrap()))
      }
      (Some(ty), None) => (Ty::from_pest(&mut Pairs::single(ty)).unwrap(), None),
      _ => unreachable!(),
    };

    let identifier = Identifier::from_pest(&mut inner).unwrap();

    Ok(Self { ty, count, identifier })
  }
}

#[derive(PartialEq, Debug)]
pub struct IfStatement {
  pub condition: Expression,
  pub block: Statement,
  pub else_block: Option<Statement>,
}

impl FromPest<'_> for IfStatement {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'_, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let mut inner = pairs.next().expect("no pair found").into_inner();

    Ok(Self {
      condition: Expression::from_pest(&mut inner).unwrap(),
      block: Statement::from_pest(&mut inner).unwrap(),
      else_block: match inner.next() {
        Some(statement) => Some(Statement::from_pest(&mut Pairs::single(statement)).unwrap()),
        None => None,
      },
    })
  }
}

#[derive(PartialEq, Debug)]
pub struct WhileStatement {
  pub condition: Expression,
  pub block: Statement,
}

impl FromPest<'_> for WhileStatement {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'_, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let mut inner = pairs.next().expect("no pair found").into_inner();

    Ok(Self { condition: Expression::from_pest(&mut inner).unwrap(), block: Statement::from_pest(&mut inner).unwrap() })
  }
}

#[derive(PartialEq, Debug)]
pub struct ReturnStatement {
  pub expression: Expression,
}

impl FromPest<'_> for ReturnStatement {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'_, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let mut inner = pairs.next().expect("no pair found").into_inner();

    Ok(Self { expression: Expression::from_pest(&mut inner).unwrap() })
  }
}

#[derive(PartialEq, Debug)]
pub struct CompoundStatement {
  pub statements: Vec<Statement>,
}

impl FromPest<'_> for CompoundStatement {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'_, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    Ok(Self {
      statements: pairs
        .next()
        .expect("no pair found")
        .into_inner()
        .map(|stmt| Statement::from_pest(&mut Pairs::single(stmt)).unwrap())
        .collect(),
    })
  }
}

#[derive(PartialEq, Debug)]
pub enum Statement {
  If(Box<IfStatement>),
  While(Box<WhileStatement>),
  Ret(ReturnStatement),
  Decl(Declaration),
  Assignment(Assignment),
  Expression(Expression),
  Compound(CompoundStatement),
}

impl FromPest<'_> for Statement {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'_, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let mut inner = pairs.next().expect("no pair found").into_inner();
    let stmt = inner.next().unwrap();

    Ok(match stmt.as_rule() {
      Rule::if_stmt => Self::If(Box::new(IfStatement::from_pest(&mut Pairs::single(stmt)).unwrap())),
      Rule::while_stmt => Self::While(Box::new(WhileStatement::from_pest(&mut Pairs::single(stmt)).unwrap())),
      Rule::ret_stmt => Self::Ret(ReturnStatement::from_pest(&mut Pairs::single(stmt)).unwrap()),
      Rule::declaration => Self::Decl(Declaration::from_pest(&mut Pairs::single(stmt)).unwrap()),
      Rule::assignment => Self::Assignment(Assignment::from_pest(&mut Pairs::single(stmt)).unwrap()),
      Rule::expression => Self::Expression(Expression::from_pest(&mut Pairs::single(stmt)).unwrap()),
      Rule::compound_stmt => Self::Compound(CompoundStatement::from_pest(&mut Pairs::single(stmt)).unwrap()),
      rule => return Err(ConversionError::Malformed(format!("unknown statement: {:?}", rule))),
    })
  }
}

#[derive(PartialEq, Debug)]
pub struct FunctionDeclaration {
  pub ty: Option<Ty>,
  pub identifier: Identifier,
  pub parameters: Vec<Parameter>,
  pub body: CompoundStatement,
}

impl FromPest<'_> for FunctionDeclaration {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'_, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let mut inner = pairs.next().expect("no pair found").into_inner();

    let (ty, identifier, parameters, body) = match (inner.next(), inner.next(), inner.next(), inner.next()) {
      (Some(ty), Some(name), Some(params), Some(body)) => (
        Option::Some(Ty::from_pest(&mut Pairs::single(ty)).unwrap()),
        Identifier::from_pest(&mut Pairs::single(name)).unwrap(),
        params.into_inner().map(|param| Parameter::from_pest(&mut Pairs::single(param)).unwrap()).collect(),
        CompoundStatement::from_pest(&mut Pairs::single(body)).unwrap(),
      ),
      (Some(name), Some(params), Some(body), None) => (
        Option::None,
        Identifier::from_pest(&mut Pairs::single(name)).unwrap(),
        params.into_inner().map(|param| Parameter::from_pest(&mut Pairs::single(param)).unwrap()).collect(),
        CompoundStatement::from_pest(&mut Pairs::single(body)).unwrap(),
      ),
      _ => unreachable!(),
    };

    Ok(Self { ty, identifier, parameters, body })
  }
}

#[derive(PartialEq, Debug)]
pub struct Program {
  pub function_declarations: Vec<FunctionDeclaration>,
}

impl FromPest<'_> for Program {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'_, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let mut inner = pairs.next().expect("no pair found").into_inner();

    Ok(Self {
      function_declarations: inner
        .next()
        .unwrap()
        .into_inner()
        .map(|dec| FunctionDeclaration::from_pest(&mut Pairs::single(dec)).unwrap())
        .collect(),
    })
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{McParser, Rule};
  use pest::Parser;

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
          lhs: Box::new(Expression::Literal(Literal::Int(2))),
          rhs: Box::new(Expression::Literal(Literal::Int(2)))
        }),
        rhs: Box::new(Expression::Binary {
          op: BinaryOp::Divide,
          lhs: Box::new(Expression::Literal(Literal::Int(4))),
          rhs: Box::new(Expression::Binary {
            op: BinaryOp::Minus,
            lhs: Box::new(Expression::Unary {
              op: UnaryOp::Minus,
              expression: Box::new(Expression::Literal(Literal::Float(4.9)))
            }),
            rhs: Box::new(Expression::FunctionCall {
              identifier: Identifier("pi".to_string()),
              arguments: vec![
                Expression::Literal(Literal::Bool(true)),
                Expression::FunctionCall { identifier: Identifier("nested".to_string()), arguments: vec![] },
              ],
            }),
          }),
        }),
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
        identifier: Identifier("numbers".to_string()),
        index_expression: Option::Some(Expression::Literal(Literal::Int(10))),
        rvalue: Expression::Literal(Literal::Float(12.4))
      }
    );

    let assignment_no_index = "number = 12.4";
    pairs = McParser::parse(Rule::assignment, &assignment_no_index).unwrap();

    assert_eq!(
      Assignment::from_pest(&mut pairs).unwrap(),
      Assignment {
        identifier: Identifier("number".to_string()),
        index_expression: Option::None,
        rvalue: Expression::Literal(Literal::Float(12.4))
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
        count: Option::Some("5".to_string().parse::<usize>().unwrap()),
        identifier: Identifier("numbers".to_string())
      }
    );

    let declaration_no_index = "float x";
    pairs = McParser::parse(Rule::declaration, &declaration_no_index).unwrap();

    assert_eq!(
      Declaration::from_pest(&mut pairs).unwrap(),
      Declaration { ty: Ty::Float, count: Option::None, identifier: Identifier("x".to_string()) }
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
            identifier: Identifier("lol".to_string()),
            index_expression: Option::None
          }),
          rhs: Box::new(Expression::Literal(Literal::Bool(true)))
        },
        block: Statement::Compound(CompoundStatement {
          statements: vec![Statement::Assignment(Assignment {
            identifier: Identifier("i".to_string()),
            index_expression: Option::None,
            rvalue: Expression::Literal(Literal::Int(1))
          })]
        }),
        else_block: Option::Some(Statement::Compound(CompoundStatement {
          statements: vec![Statement::Ret(ReturnStatement {
            expression: Expression::Variable {
              identifier: Identifier("i".to_string()),
              index_expression: Option::None
            }
          })]
        }))
      }
    )
  }
}
