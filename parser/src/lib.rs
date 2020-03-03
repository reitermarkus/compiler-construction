use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "grammar.pest"]
pub struct McParser;

#[cfg(test)]
mod tests {
  use pest::{parses_to, consumes_to};

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
}
