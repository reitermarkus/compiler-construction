#![deny(missing_debug_implementations, rust_2018_idioms)]

use from_pest::{ConversionError, FromPest};
use pest::Parser;
use pest_derive::Parser;

pub mod ast;
use ast::Program;

#[derive(Parser, Debug)]
#[grammar = "grammar.pest"]
pub struct McParser;

pub fn parse(program: &str) -> Result<Program<'_>, ConversionError<String>> {
  let mut parse_tree =
    McParser::parse(Rule::program, program).map_err(|err| ConversionError::Malformed(err.to_string()))?;
  Program::from_pest(&mut parse_tree)
}

#[cfg(test)]
mod tests {
  use pest::{consumes_to, fails_with, parses_to};

  use super::*;

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
                  par_expression(5, 17, [
                    expression(6, 16, [
                      literal(6, 9, [
                        int(6, 9)
                      ]),
                      plus(10, 11),
                      literal(12, 16, [
                        float(12, 16)
                      ]),
                    ]),
                  ]),
                ]),
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
      input:  "path_cost[i * 4 + j]",
      rule:   Rule::expression,
      tokens: [
                expression(0, 20, [
                  variable_expression(0, 20, [
                    identifier(0, 9),
                    expression(10, 19, [
                      variable_expression(10, 11, [
                        identifier(10, 11),
                      ]),
                      times(12, 13),
                      literal(14, 15, [
                        int(14, 15),
                      ]),
                      plus(16, 17),
                      variable_expression(18, 19, [
                        identifier(18, 19),
                      ]),
                    ])
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
                  par_expression(0, 4, [
                    expression(1, 3, [
                      literal(1, 3, [
                        string(1, 3, [
                          inner(2, 2)
                        ]),
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
      positives: vec![
        Rule::plus, Rule::minus,
        Rule::times, Rule::divide,
        Rule::lte, Rule::lt, Rule::gte, Rule::gt,
        Rule::land, Rule::lor, Rule::eq, Rule::neq,
      ],
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

  #[test]
  fn parse_assignment() {
    parses_to! {
      parser: McParser,
      input:  "numbers[10] = 12.4",
      rule:   Rule::assignment,
      tokens: [
                assignment(0, 18, [
                  identifier(0, 7),
                  expression(8, 10, [
                    literal(8, 10, [
                      int(8, 10)
                    ])
                  ]),
                  expression(14, 18, [
                    literal(14, 18, [
                      float(14, 18)
                    ])
                  ])
                ])
              ]
    }
  }

  #[test]
  fn parse_if_stmt() {
    parses_to! {
      parser: McParser,
      input:  "if (i > 0) { j = 1; } else { j = 0; }",
      rule:   Rule::if_stmt,
      tokens: [
                if_stmt(0, 37, [
                  expression(4, 9, [
                    variable_expression(4, 5, [
                      identifier(4, 5),
                    ]),
                    gt(6, 7),
                    literal(8, 9, [
                      int(8, 9)
                    ]),
                  ]),
                  statement(11, 21, [
                    compound_stmt(11, 21, [
                      statement(13, 19, [
                        assignment(13, 18, [
                          identifier(13, 14),
                          expression(17, 18, [
                            literal(17, 18, [
                              int(17, 18)
                            ])
                          ])
                        ])
                      ])
                    ])
                  ]),
                  statement(27, 37, [
                    compound_stmt(27, 37, [
                      statement(29, 35, [
                        assignment(29, 34, [
                          identifier(29, 30),
                          expression(33, 34, [
                            literal(33, 34, [
                              int(33, 34)
                            ])
                          ])
                        ])
                      ])
                    ])
                  ])
                ])
              ]
    }
  }
}
