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

impl FromPest<'_> for Ty {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pest: &mut Pairs<'_, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
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

#[derive(PartialEq, Debug)]
pub struct Span {
  pub string: String,
  pub start: usize,
  pub end: usize,
}

impl From<pest::Span<'_>> for Span {
  fn from(pest_span: pest::Span<'_>) -> Span {
    Self { string: pest_span.as_str().to_owned(), start: pest_span.start(), end: pest_span.end() }
  }
}

impl Span {
  pub fn new(string: &str, start: usize, end: usize) -> Span {
    Self { string: string.to_owned(), start, end }
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
pub enum Expression {
  Literal(Literal),
  Variable { identifier: Identifier, index_expression: Option<Box<Expression>> },
  FunctionCall { identifier: Identifier, arguments: Vec<Expression> },
  Unary { op: UnaryOp, expression: Box<Expression> },
  Binary { op: BinaryOp, lhs: Box<Expression>, rhs: Box<Expression> },
}

impl Expression {
  fn consume<'i>(
    pair: Pair<'i, Rule>,
    climber: &PrecClimber<Rule>,
  ) -> Result<Self, ConversionError<<Self as FromPest<'i>>::FatalError>> {
    let primary = |pair| Self::consume(pair, climber);

    let infix = |lhs: Result<Expression, ConversionError<<Self as FromPest<'i>>::FatalError>>,
                 op: Pair<'_, Rule>,
                 rhs: Result<Expression, ConversionError<<Self as FromPest<'i>>::FatalError>>| {
      Ok(Expression::Binary {
        op: BinaryOp::from_pest(&mut Pairs::single(op))?,
        lhs: Box::new(lhs?),
        rhs: Box::new(rhs?),
      })
    };

    Ok(match pair.as_rule() {
      Rule::unary_expression => {
        let mut pairs = pair.into_inner();

        Expression::Unary {
          op: UnaryOp::from_pest(&mut pairs)?,
          expression: Box::new(climber.climb(pairs, primary, infix)?),
        }
      }
      Rule::expression => climber.climb(pair.into_inner(), primary, infix)?,
      Rule::call_expr => {
        let mut pairs = pair.into_inner();

        let identifier = Identifier::from_pest(&mut pairs)?;
        let arguments = pairs
          .next()
          .map(|args| {
            args.into_inner().map(|p| climber.climb(p.into_inner(), primary, infix)).collect::<Result<Vec<_>, _>>()
          })
          .unwrap_or_else(|| Ok(Vec::new()))?;

        Expression::FunctionCall { identifier, arguments }
      }
      Rule::literal => Expression::Literal(Literal::from_pest(&mut pair.into_inner())?),
      Rule::identifier => {
        let mut pairs = Pairs::single(pair);

        let identifier = Identifier::from_pest(&mut pairs)?;

        Expression::Variable {
          identifier,
          index_expression: pairs
            .next()
            .map(|index| Expression::from_pest(&mut Pairs::single(index)))
            .transpose()?
            .map(Box::new),
        }
      }
      _ => unreachable!(),
    })
  }
}

impl From<Exp> for Expression {
  fn from(exp: Exp) -> Self {
    exp.expression
  }
}

impl FromPest<'_> for Expression {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pest: &mut Pairs<'_, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let pair = pest.next().expect("no expression found");
    let climber = climber();
    Self::consume(pair, &climber)
  }
}

#[derive(PartialEq, Debug)]
pub struct Exp {
  pub expression: Expression,
  pub span: Span,
}

impl FromPest<'_> for Exp {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pest: &mut Pairs<'_, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let pair = pest.next().expect("no expression found");
    let span = pair.as_span();

    Ok(Self { expression: Expression::from_pest(&mut Pairs::single(pair)).unwrap(), span: Span::from(span) })
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
pub struct Assignment {
  pub identifier: Identifier,
  pub index_expression: Option<Exp>,
  pub rvalue: Exp,
}

impl FromPest<'_> for Assignment {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'_, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let mut inner = pairs.next().expect("no assignment found").into_inner();

    let identifier = Identifier::from_pest(&mut inner)?;

    let (index_expression, rvalue) = match (inner.next(), inner.next()) {
      (Some(index), Some(rvalue)) => {
        (Some(Exp::from_pest(&mut Pairs::single(index))?), Exp::from_pest(&mut Pairs::single(rvalue))?)
      }
      (Some(rvalue), None) => (None, Exp::from_pest(&mut Pairs::single(rvalue))?),
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
    let mut inner = pairs.next().expect("no declaration found").into_inner();

    let mut dec_type = inner.next().expect("no declaration type").into_inner();
    let (ty, count) = match (dec_type.next(), dec_type.next()) {
      (Some(ty), Some(int)) => (Ty::from_pest(&mut Pairs::single(ty))?, Some(int.as_str().parse::<usize>().unwrap())),
      (Some(ty), None) => (Ty::from_pest(&mut Pairs::single(ty))?, None),
      _ => unreachable!(),
    };

    let identifier = Identifier::from_pest(&mut inner)?;

    Ok(Self { ty, count, identifier })
  }
}

#[derive(PartialEq, Debug)]
pub struct IfStatement {
  pub condition: Exp,
  pub block: Statement,
  pub else_block: Option<Statement>,
}

impl FromPest<'_> for IfStatement {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'_, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let mut inner = pairs.next().expect("no if statement found").into_inner();

    Ok(Self {
      condition: Exp::from_pest(&mut inner)?,
      block: Statement::from_pest(&mut inner)?,
      else_block: match inner.next() {
        Some(statement) => Some(Statement::from_pest(&mut Pairs::single(statement))?),
        None => None,
      },
    })
  }
}

#[derive(PartialEq, Debug)]
pub struct WhileStatement {
  pub condition: Exp,
  pub block: Statement,
}

impl FromPest<'_> for WhileStatement {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'_, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let mut inner = pairs.next().expect("no while statement found").into_inner();

    Ok(Self { condition: Exp::from_pest(&mut inner)?, block: Statement::from_pest(&mut inner)? })
  }
}

#[derive(PartialEq, Debug)]
pub struct ReturnStatement {
  pub expression: Option<Exp>,
}

impl FromPest<'_> for ReturnStatement {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'_, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let mut inner = pairs.next().expect("no return statement found").into_inner();

    let expression = if inner.peek().is_some() { Some(Exp::from_pest(&mut inner)?) } else { None };

    Ok(Self { expression })
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
        .expect("no compound statement found")
        .into_inner()
        .map(|stmt| Statement::from_pest(&mut Pairs::single(stmt)))
        .collect::<Result<Vec<_>, _>>()?,
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
  Expression(Exp),
  Compound(CompoundStatement),
}

impl FromPest<'_> for Statement {
  type Rule = Rule;
  type FatalError = String;

  fn from_pest(pairs: &mut Pairs<'_, Self::Rule>) -> Result<Self, ConversionError<Self::FatalError>> {
    let mut inner = pairs.next().expect("no statement found").into_inner();

    Ok(match inner.peek().unwrap().as_rule() {
      Rule::if_stmt => Self::If(Box::new(IfStatement::from_pest(&mut inner)?)),
      Rule::while_stmt => Self::While(Box::new(WhileStatement::from_pest(&mut inner)?)),
      Rule::ret_stmt => Self::Ret(ReturnStatement::from_pest(&mut inner)?),
      Rule::declaration => Self::Decl(Declaration::from_pest(&mut inner)?),
      Rule::assignment => Self::Assignment(Assignment::from_pest(&mut inner)?),
      Rule::expression => Self::Expression(Exp::from_pest(&mut inner)?),
      Rule::compound_stmt => {
        let mut statement = CompoundStatement::from_pest(&mut inner)?;

        if statement.statements.len() == 1 {
          statement.statements.pop().unwrap()
        } else {
          Self::Compound(statement)
        }
      }
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
    let mut inner = pairs.next().expect("no function declaration found").into_inner();

    let ty = if inner.peek().map(|p| p.as_rule()) == Some(Rule::ty) { Some(Ty::from_pest(&mut inner)?) } else { None };

    let identifier = Identifier::from_pest(&mut inner)?;

    let parameters = if inner.peek().map(|p| p.as_rule()) == Some(Rule::parameters) {
      let params = inner.next().unwrap().into_inner();
      params.map(|p| Parameter::from_pest(&mut Pairs::single(p))).collect::<Result<Vec<_>, _>>()?
    } else {
      vec![]
    };

    let body = CompoundStatement::from_pest(&mut inner)?;

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
              identifier: Identifier::from("pi"),
              arguments: vec![
                Expression::Literal(Literal::Bool(true)),
                Expression::FunctionCall { identifier: Identifier::from("nested"), arguments: vec![] },
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
        identifier: Identifier::from("numbers"),
        index_expression: Some(Exp { expression: Expression::Literal(Literal::Int(10)), span: Span::new("10", 8, 10) }),
        rvalue: Exp { expression: Expression::Literal(Literal::Float(12.4)), span: Span::new("12.4", 14, 18) }
      }
    );

    let assignment_no_index = "number = 12.4";
    pairs = McParser::parse(Rule::assignment, &assignment_no_index).unwrap();

    assert_eq!(
      Assignment::from_pest(&mut pairs).unwrap(),
      Assignment {
        identifier: Identifier::from("number"),
        index_expression: None,
        rvalue: Exp { expression: Expression::Literal(Literal::Float(12.4)), span: Span::new("12.4", 9, 13) }
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
        identifier: Identifier::from("numbers")
      }
    );

    let declaration_no_index = "float x";
    pairs = McParser::parse(Rule::declaration, &declaration_no_index).unwrap();

    assert_eq!(
      Declaration::from_pest(&mut pairs).unwrap(),
      Declaration { ty: Ty::Float, count: None, identifier: Identifier::from("x") }
    )
  }

  #[test]
  fn if_stmt_from_pest() {
    let if_stmt = "if (lol == true) { i = 1; } else { return i; }";
    let mut pairs = McParser::parse(Rule::if_stmt, &if_stmt).unwrap();

    assert_eq!(
      IfStatement::from_pest(&mut pairs).unwrap(),
      IfStatement {
        condition: Exp {
          expression: Expression::Binary {
            op: BinaryOp::Eq,
            lhs: Box::new(Expression::Variable { identifier: Identifier::from("lol"), index_expression: None }),
            rhs: Box::new(Expression::Literal(Literal::Bool(true)))
          },
          span: Span::new("lol == true", 4, 15),
        },
        block: Statement::Assignment(Assignment {
          identifier: Identifier::from("i"),
          index_expression: None,
          rvalue: Exp { expression: Expression::Literal(Literal::Int(1)), span: Span::new("1", 23, 24) }
        }),
        else_block: Some(Statement::Ret(ReturnStatement {
          expression: Some(Exp {
            expression: Expression::Variable { identifier: Identifier::from("i"), index_expression: None },
            span: Span::new("i", 42, 43),
          })
        }))
      }
    )
  }

  #[test]
  fn function_declaration_from_pest() {
    let if_stmt = "int sum(int[16] n) { }";
    let mut pairs = McParser::parse(Rule::function_def, &if_stmt).unwrap();

    eprintln!("Pairs:\n{:#?}", pairs);
    assert_eq!(
      FunctionDeclaration::from_pest(&mut pairs).unwrap(),
      FunctionDeclaration {
        ty: Some(Ty::Int),
        identifier: Identifier::from("sum"),
        parameters: vec![Parameter { ty: Ty::Int, count: Some(16), identifier: Identifier::from("n") }],
        body: CompoundStatement { statements: vec![] },
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

    let dangling_else = IfStatement::from_pest(&mut McParser::parse(Rule::if_stmt, &dangling_else).unwrap()).unwrap();

    assert_eq!(
      dangling_else,
      IfStatement {
        condition: Exp {
          expression: Expression::Variable { identifier: Identifier::from("c1"), index_expression: None },
          span: Span::new("c1", 11, 13),
        },
        block: Statement::If(Box::new(IfStatement {
          condition: Exp {
            expression: Expression::Variable { identifier: Identifier::from("c2"), index_expression: None },
            span: Span::new("c2", 27, 29),
          },
          block: Statement::Expression(Exp {
            expression: Expression::FunctionCall { identifier: Identifier::from("f2"), arguments: vec![] },
            span: Span::new("f2()", 41, 45),
          }),
          else_block: Some(Statement::Expression(Exp {
            expression: Expression::FunctionCall { identifier: Identifier::from("f3"), arguments: vec![] },
            span: Span::new("f3()", 70, 74),
          }))
        })),
        else_block: None,
      }
    )
  }
}
