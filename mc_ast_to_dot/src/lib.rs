#![deny(missing_debug_implementations, rust_2018_idioms)]

use std::fs::File;
use std::io::{prelude::*, stdin};
use std::path::Path;

use from_pest::FromPest;
use petgraph::dot::{Config, Dot};

use mc_parser::ast::*;

mod add_to_graph;
use add_to_graph::{AddToGraph, *};

pub fn mc_ast_to_dot(in_file: impl AsRef<Path>, mut out_stream: impl Write) -> std::io::Result<()> {
  let mut contents = String::new();

  if in_file.as_ref() == Path::new("-") {
    stdin().read_to_string(&mut contents)?;
  } else {
    File::open(in_file)?.read_to_string(&mut contents)?;
  }

  let mut parse_tree = mc_parser::parse(&contents).expect("failed to parse program");
  let ast = Program::from_pest(&mut parse_tree).expect("failed to convert parse tree to AST");

  let mut graph = AstGraph::new();
  ast.add_to_graph(&mut graph);

  writeln!(out_stream, "digraph {{")?;

  writeln!(out_stream, r##"    graph [bgcolor="transparent", colorsheme=svg]"##)?;
  writeln!(out_stream, r##"    node [fontname="sans-serif", color="#c8e6ff", style=filled]"##)?;
  writeln!(out_stream, r##"    edge [fontname="sans-serif"]"##)?;

  write!(out_stream, "{}", Dot::with_config(&graph, &[Config::GraphContentOnly]))?;

  writeln!(out_stream, "}}")
}
