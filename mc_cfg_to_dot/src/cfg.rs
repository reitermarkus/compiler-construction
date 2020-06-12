use std::collections::HashMap;

use mc_parser::ast::Identifier;
use mc_ir::*;

#[derive(Debug, Default)]
pub struct Cfg {
  pub blocks: Vec<CfgBlock>,
  pub edges: HashMap<usize, (usize, String)>,
}

pub type CfgBlock = Vec<String>;

pub trait ToCfg {
  fn to_cfg(&self) -> Cfg;
}

impl ToCfg for IntermediateRepresentation<'_> {
  fn to_cfg(&self) -> Cfg {
    let mut cfg = Cfg::default();

    let labels = self.statements.iter().filter_map(|statement| match statement {
        Op::Jumpfalse(_, Arg::Reference(_, reference)) | Op::Jump(Arg::Reference(_, reference)) => {
          Some(reference)
        }
        _ => None
      }).collect::<Vec<_>>();

    let (main_range, _) = self.functions.get(&Identifier::from("main")).expect("no main function found");

    let mut block = CfgBlock::new();

    for i in main_range.clone() {
      block.push(self.statements[i].to_string());
    }

    cfg.blocks.push(block);

    cfg
  }
}