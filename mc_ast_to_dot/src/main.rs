use std::fs::File;
use std::io::{prelude::*, stdin, stdout};

use clap::{value_t, App, Arg};

fn main() -> std::io::Result<()> {
  let matches = App::new("mC AST to DOT Converter")
    .set_term_width(0)
    .max_term_width(0)
    .about(
      "Utility for printing an abstract syntax tree in the DOT format. The output can be visualised using Graphviz. Errors are reported on invalid inputs."
    )
    .arg(
      Arg::from_usage("-o, --output <out-file> 'output file (defaults to stdout)'").required(false),
    )
    .arg(Arg::from_usage(
      "<file> 'input file (use '-' to read from stdin)'",
    ))
    .get_matches();

  let out_file = value_t!(matches, "out-file", String).ok();
  let in_file = value_t!(matches, "file", String).unwrap();

  let mut contents = String::new();

  match in_file.as_str() {
    "-" => {
      stdin().read_to_string(&mut contents)?;
    }
    in_file => {
      File::open(in_file)?.read_to_string(&mut contents)?;
    }
  }

  let ast = format!("{:#?}", mc_parser::parse(&contents));

  if let Some(out_file) = out_file.map(File::create) {
    out_file?.write_all(ast.as_bytes())?;
  } else {
    stdout().write_all(ast.as_bytes())?;
  }

  Ok(())
}
