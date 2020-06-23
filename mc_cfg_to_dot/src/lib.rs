#![deny(missing_debug_implementations, rust_2018_idioms)]

use std::convert::TryFrom;
use std::io::{self, Read, Write};

use petgraph::dot::{Config, Dot};

use mc_common::input_to_string;
use mc_ir::*;

mod cfg;
use cfg::*;

fn write_graph(mut output: impl Write, graph: CfgGraph) -> io::Result<()> {
  writeln!(output, "digraph {{")?;

  writeln!(output, r##"    graph [bgcolor="transparent", colorsheme=svg]"##)?;
  writeln!(output, r##"    node [fontname="Menlo, monospace", color="#c8e6ff", style=filled, shape=rect]"##)?;
  writeln!(output, r##"    edge [fontname="sans-serif"]"##)?;

  write!(output, "{}", Dot::with_config(&graph, &[Config::GraphContentOnly]))?;

  writeln!(output, "}}")
}

pub fn cli(input: impl Read, output: impl Write) -> Result<(), i32> {
  let contents = input_to_string(input)?;

  let ir = match IntermediateRepresentation::try_from(&*contents) {
    Ok(ir) => ir,
    Err(err) => {
      eprintln!("{}", err);
      return Err(1);
    }
  };

  let mut graph = CfgGraph::new();
  ir.add_to_graph(&mut graph);

  match write_graph(output, graph) {
    Ok(()) => Ok(()),
    Err(err) => {
      eprintln!("Error printing graph: {}", err);
      Err(1)
    }
  }
}
