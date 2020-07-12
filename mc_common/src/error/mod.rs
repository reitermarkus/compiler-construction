use std::fmt;

use colored::*;
use from_pest::ConversionError;

use mc_parser::Rule;

mod semantic_error;
pub use semantic_error::SemanticError;

#[derive(Debug)]
pub enum SuperWauError2000<'a> {
  ParseError(ConversionError<pest::error::Error<Rule>>),
  SemanticError(Vec<SemanticError<'a>>),
}

impl fmt::Display for SuperWauError2000<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::ParseError(err) => {
        writeln!(f, "{}", "Syntax error encountered:".bold().red())?;

        match err {
          ConversionError::NoMatch => unreachable!(),
          ConversionError::Malformed(err) => {
            writeln!(f, "{}", err)?;
          }
        }

        Ok(())
      }
      Self::SemanticError(errors) => {
        writeln!(f, "{}", "Semantic error(s) encountered:".bold().red())?;
        for e in errors.iter() {
          writeln!(f)?;
          writeln!(f, "{}", e)?;
        }
        writeln!(f)
      }
    }
  }
}

impl From<ConversionError<pest::error::Error<Rule>>> for SuperWauError2000<'_> {
  fn from(error: ConversionError<pest::error::Error<Rule>>) -> Self {
    Self::ParseError(error)
  }
}

impl<'a> From<Vec<SemanticError<'a>>> for SuperWauError2000<'a> {
  fn from(errors: Vec<SemanticError<'a>>) -> Self {
    Self::SemanticError(errors)
  }
}
