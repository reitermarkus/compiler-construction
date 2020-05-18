#![deny(missing_debug_implementations, rust_2018_idioms)]

use std::fs::File;
use std::io::{prelude::*, stdin};
use std::path::Path;

mod ir;
use ir::IntermediateRepresentation;

mod add_to_ir;
use add_to_ir::AddToIr;

mod format_ir;

pub fn mc_ir(in_file: impl AsRef<Path>, mut out_stream: impl Write) -> std::io::Result<()> {
  let mut contents = String::new();

  if in_file.as_ref() == Path::new("-") {
    stdin().read_to_string(&mut contents)?;
  } else {
    File::open(in_file)?.read_to_string(&mut contents)?;
  }

  let ast = mc_parser::parse(&contents).expect("failed to parse program");

  let mut ir = IntermediateRepresentation::default();
  ast.add_to_ir(&mut ir);

  write!(out_stream, "{}", ir)
}
