#![deny(missing_debug_implementations, rust_2018_idioms)]

use std::io::{Read, Write};

use mc_ir::AddToIr;
use mc_ir::IntermediateRepresentation;
use mc_common::input_to_string;

mod asm;
mod register;
mod stack;
mod storage;

mod to_asm;
pub use to_asm::ToAsm;

pub fn cli(input: impl Read, mut output: impl Write) -> Result<(), i32> {
  let contents = input_to_string(input)?;

  let ast = mc_parser::parse(&contents).expect("failed to parse program");

  if let Err(err) = mc_symbol_table::check_semantics(&ast) {
    eprintln!("{}", err);
    return Err(1);
  }

  let mut ir = IntermediateRepresentation::default();
  ast.add_to_ir(&mut ir);

  let asm = ir.to_asm();

  match write!(output, "{}", asm) {
    Ok(_) => Ok(()),
    Err(err) => {
      eprintln!("Error writing assembly: {}", err);
      Err(1)
    }
  }
}
