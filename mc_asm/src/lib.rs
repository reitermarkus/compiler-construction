#![deny(missing_debug_implementations, rust_2018_idioms)]

use std::convert::TryFrom;
use std::io::{Read, Write};

use mc_common::input_to_string;
use mc_ir::IntermediateRepresentation;

mod asm;
mod register;
mod stack;
mod storage;

mod to_asm;
pub use to_asm::ToAsm;

pub fn cli(input: impl Read, mut output: impl Write) -> Result<(), i32> {
  let contents = input_to_string(input)?;

  let ir = match IntermediateRepresentation::try_from(&*contents) {
    Ok(ir) => ir,
    Err(err) => {
      eprintln!("{}", err);
      return Err(1);
    }
  };

  let asm = ir.to_asm();

  match write!(output, "{}", asm) {
    Ok(_) => Ok(()),
    Err(err) => {
      eprintln!("Error writing assembly: {}", err);
      Err(1)
    }
  }
}
