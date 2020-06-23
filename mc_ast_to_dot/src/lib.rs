#![deny(missing_debug_implementations, rust_2018_idioms)]

use std::io::{self, Read, Write};

use petgraph::dot::{Config, Dot};

use mc_common::input_to_string;

mod add_to_graph;
use add_to_graph::{AddToGraph, *};

fn write_graph(mut output: impl Write, graph: AstGraph) -> io::Result<()> {
  writeln!(output, "digraph {{")?;

  writeln!(output, r##"    graph [bgcolor="transparent", colorsheme=svg]"##)?;
  writeln!(output, r##"    node [fontname="sans-serif", color="#c8e6ff", style=filled]"##)?;
  writeln!(output, r##"    edge [fontname="sans-serif"]"##)?;

  write!(output, "{}", Dot::with_config(&graph, &[Config::GraphContentOnly]))?;

  writeln!(output, "}}")
}

pub fn cli(input: impl Read, output: impl Write) -> Result<(), i32> {
  let contents = input_to_string(input)?;

  let ast = mc_parser::parse(&contents).expect("failed to parse program");

  let mut graph = AstGraph::new();
  ast.add_to_graph(&mut graph);

  match write_graph(output, graph) {
    Ok(()) => Ok(()),
    Err(err) => {
      eprintln!("Error printing graph: {}", err);
      Err(1)
    }
  }
}
