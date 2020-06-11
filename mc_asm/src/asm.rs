use ordered_float::OrderedFloat;
use std::collections::BTreeMap;
use std::collections::HashSet;
use std::fmt;

use mc_parser::ast::*;

use crate::storage::*;

#[macro_export]
macro_rules! l {
  { $label:expr } => (
    format!("{}:", $label)
  );
}

#[macro_export]
macro_rules! i {
  { $instruction:expr } => (
    format!("  {}", $instruction)
  );
  { $instruction:expr; $arg:expr } => (
    format!("  {:6} {}", $instruction, $arg)
  );
  { "movzx"; $lhs:expr, $rhs:expr } => (
    format!("  {:6} {}, {:#}", "movzx", $lhs, $rhs)
  );
  { $instruction:expr; $lhs:expr, $rhs:expr } => (
    format!("  {:6} {}, {}", $instruction, $lhs, $rhs)
  );
}

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

    for (float, label) in self.floats.iter() {
      writeln!(f, "{}", l! { label })?;
      writeln!(f, "{}", i! { ".float"; float })?;
    }

    for (string, label) in self.strings.iter() {
      writeln!(f, "{}", l! { label })?;
      writeln!(f, "{}", i! { ".string"; format!("{:?}", string) })?;
    }

    Ok(())
  }
}

impl Asm {
  pub fn add_float(&mut self, float: f64) -> Storage {
    let float = OrderedFloat::from(float);

    let float_number = self.floats.len();
    let label = self.floats.entry(float).or_insert_with(|| format!(".LC{}", float_number));
    Storage::Label(StorageType::Dword, label.to_owned(), false)
  }

  pub fn add_string(&mut self, s: &str) -> Storage {
    let string_number = self.strings.len();
    let label = self.strings.entry(s.to_owned()).or_insert_with(|| format!(".LS{}", string_number));
    Storage::Label(StorageType::Dword, label.to_owned(), true)
  }

  pub fn load_float(&mut self, storage: &Storage) {
    if matches!(storage, Storage::Fpu(..)) {
      self.lines.push(i! { "nop" });
    } else {
      self.lines.push(i! { "fld"; storage });
    }
  }
}
