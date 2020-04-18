use mc_parser::ast::*;

#[allow(dead_code)]
#[derive(Default)]
pub struct IntermediateRepresentation {
  instructions: Vec<Instruction>,
  stack: Vec<String>,
}

#[allow(dead_code)]
pub enum Object {
  Variable(Identifier),
  Literal(Literal),
  FunctionCall(),
}

#[allow(dead_code)]
pub enum Instruction {
  Assignment { des: Identifier, obj: Object },
  BinaryAssignment { des: Identifier, obj1: Object, op: BinaryOp, obj2: Object },
  UnaryAssignment { des: Identifier, op: UnaryOp, obj: Object },
}

pub trait AddToIr {
  fn add_to_ir(&self, _ir: &IntermediateRepresentation) {}
}

impl AddToIr for Assignment<'_> {
  fn add_to_ir(&self, _ir: &IntermediateRepresentation) {}
}

#[cfg(test)]
mod tests {
  use std::convert::TryFrom;

  use super::*;

  #[test]
  fn expression_to_ir() {
    let e = Assignment::try_from("x = a + b * c").unwrap();

    let mut ir = IntermediateRepresentation::default();
    e.add_to_ir(&mut ir);
  }
}
