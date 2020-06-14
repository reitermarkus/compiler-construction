#![deny(missing_debug_implementations, rust_2018_idioms)]

use std::fs::File;
use std::io::{prelude::*, stdin};
use std::path::Path;

use petgraph::dot::{Config, Dot};

use mc_ir::*;

mod cfg;
use cfg::*;

pub fn mc_cfg_to_dot(in_file: impl AsRef<Path>, mut out_stream: impl Write) -> std::io::Result<()> {
  let mut contents = String::new();

  if in_file.as_ref() == Path::new("-") {
    stdin().read_to_string(&mut contents)?;
  } else {
    File::open(in_file)?.read_to_string(&mut contents)?;
  }

  let ast = mc_parser::parse(&contents).expect("failed to parse program");

  mc_symbol_table::mc_check_semantics(&ast).expect("semantic checks failed");

  let mut ir = IntermediateRepresentation::default();
  ast.add_to_ir(&mut ir);

  let mut graph = CfgGraph::new();
  ir.add_to_graph(&mut graph);
  let dot = Dot::with_config(&graph, &[Config::GraphContentOnly]);

  writeln!(out_stream, "digraph {{")?;

  writeln!(out_stream, r##"    graph [bgcolor="transparent", colorsheme=svg]"##)?;
  writeln!(out_stream, r##"    node [fontname="Menlo, monospace", color="#c8e6ff", style=filled, shape=rect]"##)?;
  writeln!(out_stream, r##"    edge [fontname="sans-serif"]"##)?;

  write!(out_stream, "{}", dot)?;

  writeln!(out_stream, "}}")
}
