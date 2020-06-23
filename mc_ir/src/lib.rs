#![deny(missing_debug_implementations, rust_2018_idioms)]

use std::convert::TryFrom;
use std::io::{Read, Write};

use mc_common::input_to_string;

mod ir;
pub use ir::{Arg, IntermediateRepresentation, Op};

mod add_to_ir;
pub use add_to_ir::AddToIr;

mod format_ir;

pub fn cli(input: impl Read, mut output: impl Write) -> Result<(), i32> {
  let contents = input_to_string(input)?;

  let ir = match IntermediateRepresentation::try_from(&*contents) {
    Ok(ir) => ir,
    Err(err) => {
      eprintln!("{}", err);
      return Err(1);
    }
  };

  match write!(output, "{}", ir) {
    Ok(_) => Ok(()),
    Err(err) => {
      eprintln!("Error writing intermediate representation: {}", err);
      Err(1)
    }
  }
}
