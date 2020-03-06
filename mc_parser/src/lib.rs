#![deny(missing_debug_implementations, rust_2018_idioms)]

use from_pest::{ConversionError, FromPest};
use pest::{
  error::Error,
  iterators::{Pair, Pairs},
  prec_climber::{Assoc, Operator, PrecClimber},
  Parser,
};
use pest_derive::Parser;

pub mod ast;

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct McParser;

pub fn parse(program: &str) -> Result<Pairs<'_, Rule>, Error<Rule>> {
  McParser::parse(Rule::program, program)
}

impl FromPest<'_> for ast::BinaryOp {
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

pub fn consume<'i>(pair: Pair<'i, Rule>, climber: &PrecClimber<Rule>) -> ast::Expression {
  let primary = |pair| consume(pair, climber);

  let infix =
    |lhs: ast::Expression, op: Pair<'_, Rule>, rhs: ast::Expression| ast::Expression::Binary {
      op: ast::BinaryOp::from_pest(&mut Pairs::single(op)).unwrap(),
      lhs: Box::new(lhs),
      rhs: Box::new(rhs),
    };

  eprintln!("PAIR: {:?}", pair);

  match pair.as_rule() {
    Rule::unary_expression => {
      let mut pairs = pair.into_inner();

      let op = match pairs
        .next()
        .expect("no unary operator inside unary expression")
        .as_rule()
      {
        Rule::unary_minus => ast::UnaryOp::Minus,
        Rule::not => ast::UnaryOp::Not,
        _ => unreachable!(),
      };

      ast::Expression::Unary {
        op,
        expression: Box::new(climber.climb(pairs, primary, infix)),
      }
    }
    Rule::expression => climber.climb(pair.into_inner(), primary, infix),
    Rule::call_expr => {
      let mut pairs = pair.into_inner();

      let identifier = pairs
        .next()
        .expect("no identifier in call expression")
        .as_str()
        .to_string();
      let arguments = pairs
        .next()
        .map(|args| {
          args
            .into_inner()
            .map(|p| climber.climb(p.into_inner(), primary, infix))
            .collect()
        })
        .unwrap_or_else(Vec::new);

      ast::Expression::FunctionCall {
        identifier,
        arguments,
      }
    }
    Rule::literal => {
      let pair = pair.into_inner().next().unwrap();
      match pair.as_rule() {
        Rule::float => {
          ast::Expression::Literal(ast::Literal::Float(pair.as_str().parse::<f64>().unwrap()))
        }
        Rule::int => {
          ast::Expression::Literal(ast::Literal::Int(pair.as_str().parse::<i64>().unwrap()))
        }
        Rule::boolean => {
          ast::Expression::Literal(ast::Literal::Bool(pair.as_str().parse::<bool>().unwrap()))
        }
        Rule::string => ast::Expression::Literal(ast::Literal::String(pair.as_str().to_owned())),
        _ => unreachable!("binary rule"),
      }
    }
    _ => unreachable!("pair: {:?}", pair),
  }
}

#[cfg(test)]
mod tests {
  use pest::{consumes_to, fails_with, parses_to};

  use super::*;

  #[test]
  fn climb() {
    let expr = "2 * 2 + 4 / (-4.9 - pi(true, nested()))";
    let mut pairs = McParser::parse(Rule::expression, &expr).unwrap();

    let climber = climber();

    let ps = pairs.next().expect("no pair found");

    eprintln!("{:#?}", ps);

    let result = consume(ps, &climber);

    eprintln!("RESULT:\n{:#?}", result);
  }

  #[test]
  fn parse_int() {
    parses_to! {
      parser: McParser,
      input:  "42",
      rule:   Rule::int,
      tokens: [int(0, 2)]
    };
  }

  #[test]
  fn parse_float() {
    parses_to! {
      parser: McParser,
      input:  "4.2",
      rule:   Rule::float,
      tokens: [float(0, 3)]
    };
  }

  #[test]
  fn parse_bool() {
    parses_to! {
      parser: McParser,
      input:  "false",
      rule:   Rule::boolean,
      tokens: [boolean(0, 5)]
    }
  }

  #[test]
  fn parse_string() {
    parses_to! {
      parser: McParser,
      input:  "\"Str!?\"",
      rule:   Rule::string,
      tokens: [
                string(0, 7, [
                  inner(1, 6)
                ])
              ]
    }

    parses_to! {
      parser: McParser,
      input:  "\"\twith whitespace\n\"",
      rule:   Rule::string,
      tokens: [
                string(0, 19, [
                  inner(1, 18)
                ])
              ]
    }
  }

  #[test]
  fn parse_identifier() {
    parses_to! {
      parser: McParser,
      input:  "var_Nam3",
      rule:   Rule::identifier,
      tokens: [identifier(0, 8)]
    }

    fails_with! {
      parser: McParser,
      input:  "3var_Nam",
      rule:   Rule::identifier,
      positives: vec![Rule::identifier],
      negatives: vec![],
      pos: 0
    }
  }

  #[test]
  fn parse_declaration_type() {
    parses_to! {
      parser: McParser,
      input:  "float[10]",
      rule:   Rule::declaration_type,
      tokens: [
                declaration_type(0, 9, [
                  ty(0, 5),
                  int(6, 8)
                ]),
              ]
    }
  }

  #[test]
  fn parse_declaration() {
    parses_to! {
      parser: McParser,
      input:  "float[10] array",
      rule:   Rule::declaration,
      tokens: [
                declaration(0, 15, [
                  declaration_type(0, 9, [
                    ty(0, 5),
                    int(6, 8)
                  ]),
                  identifier(10, 15)
                ])
              ]
    }
  }

  #[test]
  fn parse_expression() {
    parses_to! {
      parser: McParser,
      input:  "192 + 3.14",
      rule:   Rule::expression,
      tokens: [
                expression(0, 10, [
                  literal(0, 3, [
                    int(0, 3)
                  ]),
                  plus(4, 5),
                  literal(6, 10, [
                    float(6, 10)
                  ])
                ])
              ]
    }

    parses_to! {
      parser: McParser,
      input:  "42 * (192 + 3.14)",
      rule:   Rule::expression,
      tokens: [
                expression(0, 17, [
                  literal(0, 2, [
                    int(0, 2)
                  ]),
                  times(3, 4),
                  expression(6, 16, [
                    literal(6, 9, [
                      int(6, 9)
                    ]),
                    plus(10, 11),
                    literal(12, 16, [
                      float(12, 16)
                    ])
                  ])
                ])
              ]
    }

    parses_to! {
      parser: McParser,
      input:  "1 <= 2",
      rule:   Rule::expression,
      tokens: [
                expression(0, 6, [
                  literal(0, 1, [
                    int(0, 1)
                  ]),
                  lte(2, 4),
                  literal(5, 6, [
                    int(5, 6)
                  ])
                ])
              ]
    }

    parses_to! {
      parser: McParser,
      input:  "47.1",
      rule:   Rule::expression,
      tokens: [
                expression(0, 4, [
                  literal(0, 4, [
                    float(0, 4)
                  ]),
                ])
              ]
    }

    parses_to! {
      parser: McParser,
      input:  r#"("")"#,
      rule:   Rule::expression,
      tokens: [
                expression(0, 4, [
                  expression(1, 3, [
                    literal(1, 3, [
                      string(1, 3, [
                        inner(2, 2)
                      ]),
                    ]),
                  ]),
                ]),
              ]
    }

    fails_with! {
      parser: McParser,
      input:  "(42",
      rule:   Rule::expression,
      positives: vec![Rule::plus, Rule::minus, Rule::times, Rule::divide, Rule::lte, Rule::lt, Rule::gte, Rule::gt, Rule::land, Rule::lor, Rule::eq, Rule::neq],
      negatives: vec![],
      pos: 3
    }
  }

  #[test]
  fn parse_call_expr() {
    parses_to! {
      parser: McParser,
      input:  "main()",
      rule:   Rule::call_expr,
      tokens: [
                call_expr(0, 6, [
                  identifier(0, 4),
                ])
              ]
    }
  }

  #[test]
  fn parse_function_def() {
    parses_to! {
      parser: McParser,
      input:  "void main() { }",
      rule:   Rule::function_def,
      tokens: [
                function_def(0, 15, [
                  identifier(5, 9),
                  compound_stmt(12, 15)
                ])
              ]
    }
  }
}
