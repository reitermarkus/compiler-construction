#![deny(missing_debug_implementations, rust_2018_idioms)]

use std::env::current_dir;
use std::fs::File;
use std::io::{prelude::*, stdin};
use std::path::Path;
use std::process::{exit, Command, Stdio};

use mc_asm::ToAsm;

use mc_ir::AddToIr;
use mc_ir::IntermediateRepresentation;

pub fn mcc(in_file: impl AsRef<Path>, out_file: impl AsRef<Path>, backend: String, quiet: bool) -> std::io::Result<()> {
  let mut contents = String::new();

  if in_file.as_ref() == Path::new("-") {
    stdin().read_to_string(&mut contents)?;
  } else {
    let in_file = in_file.as_ref().canonicalize()?;
    File::open(&in_file)?.read_to_string(&mut contents)?;
  };

  let ast = mc_parser::parse(&contents).expect("failed to parse program");

  mc_symbol_table::mc_check_semantics(&ast).expect("semantic checks failed");

  let mut ir = IntermediateRepresentation::default();
  ast.add_to_ir(&mut ir);

  let asm = ir.to_asm();

  let stderr = if quiet {
    Stdio::null()
  } else {
    Stdio::inherit()
  };

  let mut command = Command::new(&backend);

  if backend == "docker" {
    command.arg("run");
    command.arg("-i");

    command.arg("-v");
    command.arg(format!("{}:/root", current_dir().unwrap().display()));

    command.arg("gcc");
    command.arg("gcc");
  }

  command.arg("-m32");
  command.arg("-o");
  command.arg(out_file.as_ref());
  command.arg("-x");
  command.arg("assembler");
  command.arg("-");

  command.stdin(Stdio::piped());
  command.stderr(stderr);

  let mut child = command.spawn()?;

  let mut stdin = child.stdin.take().unwrap();
  write!(&mut stdin, "{}", asm)?;

  drop(stdin);

  let status = child.wait()?;

  if !status.success() {
    match status.code() {
      Some(exit_code) => exit(exit_code),
      None => panic!("'{:?}' failed.", command)
    }
  }

  Ok(())
}
