#![deny(missing_debug_implementations, rust_2018_idioms)]

use std::ffi::OsString;
use std::fs::File;
use std::io::{prelude::*, stdin};
use std::path::Path;
use std::process::{exit, Command, Stdio};

use mc_asm::ToAsm;

use mc_ir::AddToIr;
use mc_ir::IntermediateRepresentation;

use tempfile::tempdir;

pub fn mcc(in_file: impl AsRef<Path>, out_file: impl AsRef<Path>, backend: String, quiet: bool) -> std::io::Result<()> {
  let mut contents = String::new();

  let asm_file_name = if in_file.as_ref() == Path::new("-") {
    stdin().read_to_string(&mut contents)?;
    OsString::from("a.s")
  } else {
    let in_file = in_file.as_ref().canonicalize()?;
    File::open(&in_file)?.read_to_string(&mut contents)?;
    in_file.with_extension("s").file_name().unwrap().to_os_string()
  };

  let ast = mc_parser::parse(&contents).expect("failed to parse program");

  mc_symbol_table::mc_check_semantics(&ast).expect("semantic checks failed");

  let mut ir = IntermediateRepresentation::default();
  ast.add_to_ir(&mut ir);

  let asm = ir.to_asm();

  let temp_dir = tempdir()?;

  let asm_file = temp_dir.path().join(asm_file_name);
  let mut asm_stream = File::create(&asm_file)?;
  write!(&mut asm_stream, "{}", asm)?;

  let stderr = if quiet {
    Stdio::null()
  } else {
    Stdio::inherit()
  };

  let mut command = Command::new(backend)
    .arg("-m32")
    .arg(asm_file)
    .arg("-o")
    .arg(out_file.as_ref())
    .stderr(stderr)
    .spawn()?;

  let status = command.wait()?;

  temp_dir.close()?;

  if !status.success() {
    match status.code() {
      Some(exit_code) => exit(exit_code),
      None => panic!("'{:?}' failed.", command)
    }
  }

  Ok(())
}
