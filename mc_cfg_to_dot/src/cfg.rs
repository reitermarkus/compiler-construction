use std::mem;
use std::ops::Range;

use petgraph::{graph::NodeIndex, Directed, Graph};

use mc_ir::*;

pub trait AddToGraph {
  fn add_to_graph(&self, graph: &mut CfgGraph);
}

pub type CfgGraph = Graph<String, String, Directed>;

fn format_range(statements: &[Op<'_>], range: Range<usize>) -> String {
  statements[range].iter().map(|s| format!("{}\n", s)).collect::<Vec<_>>().join("")
}

fn add_statements(
  previous_nodes: &mut Vec<(NodeIndex, String)>,
  graph: &mut CfgGraph,
  statements: &[Op<'_>],
  range: Range<usize>,
) -> NodeIndex {
  let mut start = range.start;
  let mut i = start;

  while i < range.end {
    match statements[i] {
      Op::Jumpfalse(_, Arg::Reference(_, reference)) => match statements[reference - 1] {
        Op::Jump(Arg::Reference(_, back_reference)) if back_reference < reference => {
          let block_before = graph.add_node(format_range(statements, start..back_reference));

          for (previous_node, label) in mem::replace(previous_nodes, vec![]) {
            graph.add_edge(previous_node, block_before, label);
          }

          let while_condition = graph.add_node(format_range(statements, back_reference..(i + 1)));
          graph.add_edge(block_before, while_condition, "".into());

          previous_nodes.push((while_condition, "true".into()));
          let while_block = add_statements(previous_nodes, graph, statements, (i + 1)..reference);

          graph.add_edge(while_block, while_condition, "".into());

          previous_nodes.push((while_condition, "false".into()));

          start = reference;
          i = start;
        }
        _ => {
          let if_condition = graph.add_node(format_range(statements, start..(i + 1)));

          for (previous_node, label) in mem::replace(previous_nodes, vec![]) {
            graph.add_edge(previous_node, if_condition, label);
          }

          previous_nodes.push((if_condition, "true".into()));
          let if_block = add_statements(previous_nodes, graph, statements, (i + 1)..reference);

          match statements[reference - 1] {
            Op::Return(_) => {
              previous_nodes.push((if_condition, "false".into()));

              start = reference;
              i = start;
            }
            Op::Jump(Arg::Reference(_, back_reference)) if back_reference > reference => {
              previous_nodes.push((if_condition, "false".into()));
              let else_block = add_statements(previous_nodes, graph, statements, reference..back_reference);

              previous_nodes.extend(vec![(if_block, "".into()), (else_block, "".into())]);

              start = back_reference;
              i = start;
            }
            _ => {
              previous_nodes.extend(vec![(if_condition, "false".into()), (if_block, "".into())]);

              start = reference;
              i = start;
            }
          }
        }
      },
      _ => {
        i += 1;
      }
    }
  }

  let last_block = graph.add_node(format_range(statements, start..range.end));

  for (previous_node, label) in mem::replace(previous_nodes, vec![]) {
    graph.add_edge(previous_node, last_block, label);
  }

  last_block
}

impl AddToGraph for IntermediateRepresentation<'_> {
  fn add_to_graph(&self, graph: &mut CfgGraph) {
    for (function, (range, _)) in &self.functions {
      let function_name = graph.add_node(format!("{}:", function));
      let mut previous_nodes = vec![(function_name, "".into())];

      add_statements(&mut previous_nodes, graph, &self.statements, range.clone());
    }
  }
}
