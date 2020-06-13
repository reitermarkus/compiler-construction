use std::collections::HashMap;

use mc_ir::*;
use mc_parser::ast::Identifier;

#[derive(Debug, Default)]
pub struct Cfg {
  pub blocks: Vec<CfgBlock>,
  pub edges: HashMap<usize, (usize, String)>,
}

pub type CfgBlock = Vec<String>;

impl Cfg {
  fn push_line(&mut self, line: String) {
    if let Some(block) = self.blocks.last_mut() {
      block.push(line);
    } else {
      self.blocks.push(vec![line]);
    }
  }

  fn push_block(&mut self) {
    self.blocks.push(Vec::new());
  }
}

pub trait ToCfg {
  fn to_cfg(&self) -> Cfg;
}

impl ToCfg for IntermediateRepresentation<'_> {
  fn to_cfg(&self) -> Cfg {
    let mut cfg = Cfg::default();

    let labels = self
      .statements
      .iter()
      .filter_map(|statement| match statement {
        Op::Jumpfalse(_, Arg::Reference(_, reference)) | Op::Jump(Arg::Reference(_, reference)) => Some(reference),
        _ => None,
      })
      .collect::<Vec<_>>();

    let (main_range, _) = self.functions.get(&Identifier::from("main")).expect("no main function found");

    for i in main_range.clone() {
      if labels.contains(&&i) {
        cfg.push_block();
      }
      cfg.push_line(self.statements[i].to_string());
    }

    cfg
  }
}
