#![deny(missing_debug_implementations, rust_2018_idioms)]

use std::fs::File;
use std::io::{prelude::*, stdin, stdout};
use std::string::ToString;

use clap::{value_t, App, Arg};
use petgraph::dot::{Config, Dot};

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
      ty: Some(Ty::Int),
      identifier: Identifier(String::from("fib")),
      parameters: vec![Parameter { ty: "int".into(), identifier: Identifier("n".to_string()) }],
      body: CompoundStatement {
        statements: vec![
          Statement::If(Box::new(IfStatement {
            condition: Expression::Binary {
              op: BinaryOp::Lt,
              lhs: Box::new(Expression::Variable { identifier: Identifier("n".to_string()), index_expression: None }),
              rhs: Box::new(Expression::Literal(Literal::Int(2))),
            },
            block: Statement::Ret(ReturnStatement {
              expression: Expression::Variable { identifier: Identifier("n".to_string()), index_expression: None },
            }),
            else_block: None,
          })),
          Statement::Ret(ReturnStatement {
            expression: Expression::Binary {
              op: BinaryOp::Plus,
              lhs: Box::new(Expression::FunctionCall {
                identifier: Identifier("fib".to_string()),
                arguments: vec![Expression::Binary {
                  op: BinaryOp::Minus,
                  lhs: Box::new(Expression::Variable {
                    identifier: Identifier("n".to_string()),
                    index_expression: None,
                  }),
                  rhs: Box::new(Expression::Literal(Literal::Int(1))),
                }],
              }),
              rhs: Box::new(Expression::FunctionCall {
                identifier: Identifier("fib".to_string()),
                arguments: vec![Expression::Binary {
                  op: BinaryOp::Minus,
                  lhs: Box::new(Expression::Variable {
                    identifier: Identifier("n".to_string()),
                    index_expression: None,
                  }),
                  rhs: Box::new(Expression::Literal(Literal::Int(2))),
                }],
              }),
            },
          }),
        ],
      },
    }],
  };

  let mut graph = AstGraph::new();
  ast.add_to_graph(&mut graph);

  fn output(mut writer: impl Write, graph: &AstGraph) -> std::io::Result<()> {
    writeln!(writer, "digraph {{")?;

    writeln!(writer, r##"    node [fontname="sans-serif", color="#c8e6ff", style=filled]"##)?;
    writeln!(writer, r##"    edge [fontname="sans-serif"]"##)?;

    write!(writer, "{}", Dot::with_config(&graph, &[Config::GraphContentOnly]))?;

    writeln!(writer, "}}")
  };

  if let Some(out_file) = out_file.map(File::create) {
    output(out_file?, &graph)
  } else {
    output(stdout(), &graph)
  }
}
