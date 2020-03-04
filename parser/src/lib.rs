use pest_derive::Parser;

#[macro_use]
extern crate pest;

#[derive(Parser)]
#[grammar = "grammar.pest"]
pub struct McParser;

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
                  binary_operator(4, 5),
                  literal(6, 10, [
                    float(6, 10)
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
  }
}
