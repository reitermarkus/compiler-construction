#![deny(missing_debug_implementations, rust_2018_idioms)]

use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use mc_asm::ToAsm;

use mc_common::{error::*, input_to_string};
use mc_ir::AddToIr;
use mc_ir::IntermediateRepresentation;

pub fn cli(
  input: impl Read,
  out_file: impl AsRef<Path>,
  backend: String,
  docker_image: Option<String>,
  quiet: bool,
) -> Result<(), i32> {
  let contents = input_to_string(input)?;

  let ast = match mc_parser::parse(&contents) {
    Ok(program) => program,
    Err(err) => {
      eprintln!("{}", SuperWauError2000::from(err));
      return Err(1);
    }
  };

  if let Err(err) = mc_symbol_table::check_semantics(&ast) {
    eprintln!("{}", err);
    return Err(1);
  }

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
    let out_dir = match canonicalize_path(out_dir) {
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
  if let Err(err) = write!(&mut stdin, "{}", asm) {
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
      }
    };
  }

  Ok(())
}

#[cfg(target_os = "windows")]
fn canonicalize_path(path: &Path) -> std::io::Result<PathBuf> {
  Ok(path.to_path_buf())
}

#[cfg(not(target_os = "windows"))]
fn canonicalize_path(path: &Path) -> std::io::Result<PathBuf> {
  path.canonicalize()
}
