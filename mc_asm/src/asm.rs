use ordered_float::OrderedFloat;
use std::collections::BTreeMap;
use std::collections::HashSet;
use std::fmt;

use crate::storage::*;

/// Returns a string formatted as a label.
///
/// # Arguments
///
/// * `label` - A string to be formatted as a label.
///
#[macro_export]
macro_rules! l {
  { $label:expr } => (
    format!("{}:", $label)
  );
}

/// Returns a string formatted as an assembly instruction.
///
/// # Arguments
///
/// * `instruction` - A string representing an instruction.
///
/// * `instruction` - A string representing an instruction.
/// * `arg` - An Argument used with the instruction
///
/// * `lhs` - An Argument used with the `movzx` instruction.
/// * `rhs` - An Argument used with the `movzx` instruction.
///
/// * `instruction` - A string representing an instruction.
/// * `lhs` - An Argument used with the `movzx` instruction.
/// * `rhs` - An Argument used with the `movzx` instruction.
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

/// `Asm` repreents a global struct for all components of the assembly output.
#[derive(Debug)]
pub struct Asm {
  /// All assembly lines, that will be in the output of the assembly file.
  pub lines: Vec<String>,
  /// All *labels*, that will be in the output of the assembly file.
  pub labels: BTreeMap<usize, String>,
  /// All *strings*, that will be in the output of the assembly file.
  pub strings: BTreeMap<String, String>,
  /// All *floats*, that will be in the output of the assembly file.
  pub floats: BTreeMap<OrderedFloat<f64>, String>,
  /// All built-in functions, that will be in the output of the assembly file like `read_int`, `read_float` or `print_nl`.
  pub builtin_functions: HashSet<&'static str>,
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
  /// Returns a [`Label`](crate::storage::Storage::Label) containing a [`Dword`](crate::storage::StorageType::Dword), the actual label and a boolean, that specifies that *OFFSET FLAT* is not required in the output.
  ///
  /// # Arguments
  ///
  /// * `float` - The floating point number to be repsented in a label.
  ///
  pub fn add_float(&mut self, float: f64) -> Storage {
    let float = OrderedFloat::from(float);

    let float_number = self.floats.len();
    let label = self.floats.entry(float).or_insert_with(|| format!(".LC{}", float_number));
    Storage::Label(StorageType::Dword, label.to_owned(), false)
  }

  /// Returns a [`Label`](storage::Storage::Label) containing a [`Dword`](storage::StorageType::Dword), the actual label and a boolean, that specifies that *OFFSET FLAT* is required in the output.
  ///
  /// # Arguments
  ///
  /// * `s` - The string to be repsented in a label.
  ///
  pub fn add_string(&mut self, s: &str) -> Storage {
    let string_number = self.strings.len();
    let label = self.strings.entry(s.to_owned()).or_insert_with(|| format!(".LS{}", string_number));
    Storage::Label(StorageType::Dword, label.to_owned(), true)
  }

  /// Loads a float.
  ///
  /// # Arguments
  ///
  /// * `storage` - The [`Storage`](storage::Storage) enum representing the float to be loaded.
  ///
  pub fn load_float(&mut self, storage: &Storage) {
    if matches!(storage, Storage::Fpu(..)) {
      self.lines.push(i! { "nop" });
    } else {
      self.lines.push(i! { "fld"; storage });
    }
  }
}
