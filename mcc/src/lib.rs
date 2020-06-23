#![deny(missing_debug_implementations, rust_2018_idioms)]

use std::io::{Read, Write};
use std::path::Path;
use std::process::{Command, Stdio};

use mc_asm::ToAsm;

use mc_ir::AddToIr;
use mc_ir::IntermediateRepresentation;
use mc_common::input_to_string;

pub fn cli(
  input: impl Read,
  out_file: impl AsRef<Path>,
  backend: String,
  docker_image: Option<String>,
  quiet: bool,
) -> Result<(), i32> {
  let contents = input_to_string(input)?;

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
    let out_dir = out_file.parent().unwrap_or(&out_file);
    let out_dir = match out_dir.canonicalize() {
      Ok(child) => child,
      Err(err) => {
        eprintln!("Failed resolving path {:?}: {}", out_dir, err);
        return Err(1);
      }
    };
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

  let mut child = match command.spawn() {
    Ok(child) => child,
    Err(err) => {
      eprintln!("Failed starting command {:?}: {}", command, err);
      return Err(1);
    }
  };

  let mut stdin = child.stdin.take().unwrap();
  if let Err(err) =  write!(&mut stdin, "{}", asm) {
    eprintln!("Failed writing stdin to command {:?}: {}", command, err);
    return Err(1);
  }
  drop(stdin);

  let status = match child.wait() {
    Ok(child) => child,
    Err(err) => {
      eprintln!("Failed waiting for command {:?}: {}", command, err);
      return Err(1);
    }
  };

  if !status.success() {
    return match status.code() {
      Some(exit_code) => Err(exit_code),
      None => {
        eprintln!("Command {:?} failed.", command);
        Err(1)
      },
    };
  }

  Ok(())
}
