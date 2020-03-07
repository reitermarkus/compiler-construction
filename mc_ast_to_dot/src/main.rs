#![deny(missing_debug_implementations, rust_2018_idioms)]

use std::fs::File;
use std::io::{prelude::*, stdin, stdout};

use clap::{value_t, App, Arg};
use from_pest::FromPest;
use pest::Parser;
use petgraph::dot::{Config, Dot};

use mc_parser::{ast::*, McParser, Rule};

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

  let mut parse_tree = McParser::parse(Rule::expression, &contents).unwrap();

  let ast = Expression::from_pest(&mut parse_tree).unwrap();

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
