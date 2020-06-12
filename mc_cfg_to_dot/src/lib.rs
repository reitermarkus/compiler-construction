#![deny(missing_debug_implementations, rust_2018_idioms)]

use std::fs::File;
use std::io::{prelude::*, stdin};
use std::path::Path;

use petgraph::dot::{Config, Dot};

//mod cfg;

pub fn mc_cfg_to_dot(in_file: impl AsRef<Path>, mut out_stream: impl Write) -> std::io::Result<()> {
  let mut contents = String::new();

  if in_file.as_ref() == Path::new("-") {
    stdin().read_to_string(&mut contents)?;
  } else {
    File::open(in_file)?.read_to_string(&mut contents)?;
  }

  let ast = mc_parser::parse(&contents).expect("failed to parse program");

  writeln!(out_stream, "digraph {{")?;

  writeln!(out_stream, r##"    graph [bgcolor="transparent", colorsheme=svg]"##)?;
  writeln!(out_stream, r##"    node [fontname="sans-serif", color="#c8e6ff", style=filled]"##)?;
  writeln!(out_stream, r##"    edge [fontname="sans-serif"]"##)?;

  writeln!(out_stream, "}}")
}
