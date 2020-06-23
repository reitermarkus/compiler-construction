#![deny(missing_debug_implementations, rust_2018_idioms)]

use std::io::{Read, Write};
use std::path::Path;
use std::process::{exit, Command, Stdio};

use mc_asm::ToAsm;

use mc_ir::AddToIr;
use mc_ir::IntermediateRepresentation;

pub fn cli(
  mut input: impl Read,
  out_file: impl AsRef<Path>,
  backend: String,
  docker_image: Option<String>,
  quiet: bool,
) -> std::io::Result<()> {
  let mut contents = String::new();
  input.read_to_string(&mut contents)?;

  let ast = mc_parser::parse(&contents).expect("failed to parse program");

  mc_symbol_table::check_semantics(&ast).expect("semantic checks failed");

  let mut ir = IntermediateRepresentation::default();
  ast.add_to_ir(&mut ir);

  let asm = ir.to_asm();

  let stderr = if quiet { Stdio::null() } else { Stdio::inherit() };

  let mut command;

  let common_flags = ["-m32", "-x", "assembler", "-"];

  if let Some(docker_image) = docker_image {
    command = Command::new("docker");

    command.arg("run");
    command.arg("--rm");
    command.arg("-i");

    command.arg("-v");

    let out_file = out_file.as_ref();
    let out_dir = out_file.parent().unwrap_or(&out_file).canonicalize()?;
    command.arg(format!("{}:/project", out_dir.display()));
    let out_file = out_file.file_name().map(|n| Path::new(n)).unwrap_or(out_file);

    command.arg("-w");
    command.arg("/project");

    command.arg(docker_image);
    command.arg(backend);
    command.args(&common_flags);
    command.arg("-o");
    command.args(out_file);
  } else {
    command = Command::new(backend);
    command.args(&common_flags);
    command.arg("-o");
    command.arg(out_file.as_ref());
  }

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
      None => panic!("'{:?}' failed.", command),
    }
  }

  Ok(())
}
