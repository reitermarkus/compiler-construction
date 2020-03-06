#![deny(missing_debug_implementations, rust_2018_idioms)]

use std::fs::File;
use std::io::{prelude::*, stdin, stdout};
use std::string::ToString;

use clap::{value_t, App, Arg};
use petgraph::dot::Dot;

use mc_parser::ast::*;

mod add_to_graph;
use add_to_graph::{AddToGraph, *};

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

  let ast = Program {
    function_declarations: vec![FunctionDeclaration {
      ty: Some("int".to_string()),
      identifier: String::from("main"),
      parameters: vec![
        Parameter {
          ty: "float".into(),
          identifier: "n".to_owned(),
        },
        Parameter {
          ty: "string".into(),
          identifier: "message".to_owned(),
        },
      ],
      body: CompoundStatement {
        statements: vec![Statement::If(Box::new(IfStatement {
          condition: Expression::Literal(Literal::Bool(false)),
          block: Statement::Compound(CompoundStatement { statements: vec![] }),
          else_block: None,
        }))],
      },
    }],
  };

  let mut deps = AstGraph::new();
  ast.add_to_graph(&mut deps);

  let output = Dot::new(&deps).to_string();

  if let Some(out_file) = out_file.map(File::create) {
    out_file?.write_all(output.as_bytes())?;
  } else {
    stdout().write_all(output.as_bytes())?;
  }

  Ok(())
}
