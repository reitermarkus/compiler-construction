use std::ops::Range;

use petgraph::{Directed, Graph};

use mc_ir::*;

pub trait AddToGraph {
  fn add_to_graph(&self, graph: &mut CfgGraph);
}

pub type CfgGraph = Graph<String, String, Directed>;

fn format_range(statements: &[Op<'_>], range: Range<usize>) -> String {
  statements[range].iter().map(|s| format!("{}\n", s)).collect::<Vec<_>>().join("")
}

impl AddToGraph for IntermediateRepresentation<'_> {
  fn add_to_graph(&self, graph: &mut CfgGraph) {
    for (function, (range, _)) in &self.functions {
      let mut start = range.start;

      let mut i = start;

      let function_name = graph.add_node(format!("{}:", function));

      let mut previous_nodes = vec![(function_name, "".into())];

      while i < range.end {
        match self.statements[i] {
          Op::Jumpfalse(_, Arg::Reference(_, reference)) => {
            if let Op::Jump(Arg::Reference(_, back_reference)) = self.statements[reference - 1] {
              let is_if = back_reference > reference;
              let is_while = back_reference < reference;

              if is_if {
                let if_condition = graph.add_node(format_range(&self.statements, start..(i + 1)));

                for (previous_node, label) in previous_nodes {
                  graph.add_edge(previous_node, if_condition, label);
                }

                let if_block = graph.add_node(format_range(&self.statements, (i + 1)..(reference)));
                let else_block = graph.add_node(format_range(&self.statements, reference..back_reference));

                graph.add_edge(if_condition, if_block, "true".into());
                graph.add_edge(if_condition, else_block, "false".into());

                previous_nodes = vec![(if_block, "".into()), (else_block, "".into())];

                start = back_reference;
              }

              if is_while {
                let block_before = graph.add_node(format_range(&self.statements, start..back_reference));

                for (previous_node, label) in previous_nodes {
                  graph.add_edge(previous_node, block_before, label);
                }

                let while_condition = graph.add_node(format_range(&self.statements, back_reference..(i + 1)));

                graph.add_edge(block_before, while_condition, "".into());

                let while_block = graph.add_node(format_range(&self.statements, (i + 1)..reference));

                graph.add_edge(while_condition, while_block, "true".into());
                graph.add_edge(while_block, while_condition, "".into());

                previous_nodes = vec![(while_condition, "false".into())];

                start = reference;
              }
            };

            i = start;
          }
          _ => {
            i += 1;
          }
        }
      }

      let last_block = graph.add_node(format_range(&self.statements, start..range.end));

      for (previous_node, label) in previous_nodes {
        graph.add_edge(previous_node, last_block, label);
      }
    }
  }
}
