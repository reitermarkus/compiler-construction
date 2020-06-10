use ordered_float::OrderedFloat;
use std::collections::BTreeMap;
use std::collections::HashSet;
use std::fmt;

use mc_parser::ast::*;

#[derive(Debug)]
pub struct Asm {
  pub lines: Vec<String>,
  pub labels: BTreeMap<usize, String>,
  pub strings: BTreeMap<String, String>,
  pub floats: BTreeMap<OrderedFloat<f64>, String>,
  pub builtin_functions: HashSet<Identifier>,
}

impl fmt::Display for Asm {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    for line in &self.lines {
      line.fmt(f)?;
      writeln!(f)?;
    }

    Ok(())
  }
}
