use std::sync::atomic::{AtomicUsize, Ordering};

use mc_parser::ast::*;

pub trait AddToIr<'a> {
  fn add_to_ir(&'a self, ir: &mut IntermediateRepresentation<'a>) -> Arg<'a>;
}

impl<'a> AddToIr<'a> for Assignment<'a> {
  fn add_to_ir(&'a self, ir: &mut IntermediateRepresentation<'a>) -> Arg<'a> {
    let arg = self.rvalue.add_to_ir(ir);
    ir.push(Op::Assign(arg, Arg::Variable(&self.identifier)));

    ir.last_ref()
  }
}

impl<'a> AddToIr<'a> for Expression<'a> {
  fn add_to_ir(&'a self, ir: &mut IntermediateRepresentation<'a>) -> Arg<'a> {
    match self {
      Self::Literal { literal, .. } => Arg::Literal(literal),
      Self::Variable { identifier, .. } => Arg::Variable(identifier),
      Self::Binary { op, lhs, rhs, .. } => {
        let arg1 = lhs.add_to_ir(ir);
        let arg2 = rhs.add_to_ir(ir);

        ir.push(match op {
          BinaryOp::Gt => Op::Gt(arg1, arg2),
          BinaryOp::Gte => Op::Gte(arg1, arg2),
          BinaryOp::Lt => Op::Lt(arg1, arg2),
          BinaryOp::Lte => Op::Lte(arg1, arg2),
          BinaryOp::Plus => Op::Plus(arg1, arg2),
          BinaryOp::Minus => Op::Minus(arg1, arg2),
          BinaryOp::Divide => Op::Divide(arg1, arg2),
          BinaryOp::Times => Op::Times(arg1, arg2),
          BinaryOp::Eq => Op::Eq(arg1, arg2),
          BinaryOp::Neq => Op::Neq(arg1, arg2),
          BinaryOp::Land => Op::Land(arg1, arg2),
          BinaryOp::Lor => Op::Lor(arg1, arg2),
        });

        Arg::Reference(AtomicUsize::new(ir.statements.len() - 1))
      }
      Self::Unary { op, expression, .. } => {
        let arg = expression.add_to_ir(ir);

        ir.push(match op {
          UnaryOp::Not => Op::Not(arg),
          UnaryOp::Minus => Op::UnaryMinus(arg),
        });

        Arg::Reference(AtomicUsize::new(ir.statements.len() - 1))
      }
      Self::FunctionCall { .. } => todo!(),
    }
  }
}

impl<'a> AddToIr<'a> for Statement<'a> {
  fn add_to_ir(&'a self, ir: &mut IntermediateRepresentation<'a>) -> Arg<'a> {
    match self {
      Self::Assignment(assignment) => assignment.add_to_ir(ir),
      Self::Expression(expression) => expression.add_to_ir(ir),
      Self::If(if_stmt) => if_stmt.add_to_ir(ir),
      Self::Compound(comp_stmt) => comp_stmt.add_to_ir(ir),
      _ => todo!(),
    }
  }
}

impl<'a> AddToIr<'a> for IfStatement<'a> {
  fn add_to_ir(&'a self, ir: &mut IntermediateRepresentation<'a>) -> Arg<'a> {
    let condition = self.condition.add_to_ir(ir);

    let jumpfalse_index = ir.statements.len();
    ir.push(Op::Jumpfalse(condition, Arg::Reference(AtomicUsize::default())));

    self.block.add_to_ir(ir);

    if let Some(else_block) = &self.else_block {
      let jump_index = ir.statements.len();
      ir.push(Op::Jump(Arg::Reference(AtomicUsize::default())));

      ir.update_reference(jumpfalse_index, ir.statements.len());

      else_block.add_to_ir(ir);

      ir.update_reference(jump_index, ir.statements.len());
    } else {
      ir.update_reference(jumpfalse_index, ir.statements.len());
    }

    ir.last_ref()
  }
}

impl<'a> AddToIr<'a> for CompoundStatement<'a> {
  fn add_to_ir(&'a self, ir: &mut IntermediateRepresentation<'a>) -> Arg<'a> {
    for stmt in &self.statements {
      stmt.add_to_ir(ir);
    }

    ir.last_ref()
  }
}

#[cfg(test)]
mod tests {
  use std::convert::TryFrom;

  use super::*;

  #[test]
  fn assignment_to_ir() {
    let assignment = Assignment::try_from("x = 1 + 2 * 3").unwrap();

    let mut ir = IntermediateRepresentation::default();
    assignment.add_to_ir(&mut ir);

    assert_eq!(
      ir.statements,
      vec![
        Op::Times(Arg::Literal(&Literal::Int(2)), Arg::Literal(&Literal::Int(3))),
        Op::Plus(Arg::Literal(&Literal::Int(1)), Arg::Reference(AtomicUsize::new(0))),
        Op::Assign(Arg::Reference(AtomicUsize::new(1)), Arg::Variable(&Identifier::from("x"))),
      ]
    );
  }

  #[test]
  fn expression_to_ir() {
    let expression = Expression::try_from("1 + 2 * 3").unwrap();

    let mut ir = IntermediateRepresentation::default();

    let arg = expression.add_to_ir(&mut ir);

    assert_eq!(
      ir.statements,
      vec![
        Op::Times(Arg::Literal(&Literal::Int(2)), Arg::Literal(&Literal::Int(3))),
        Op::Plus(Arg::Literal(&Literal::Int(1)), Arg::Reference(AtomicUsize::new(0))),
      ]
    );
    assert_eq!(arg, Arg::Reference(AtomicUsize::new(1)));
  }

  #[test]
  fn if_stmt_to_ir() {
    let if_stmt = IfStatement::try_from(
      "if (a > b) {
      max = a;
    } else {
      max = b;
    }",
    )
    .unwrap();

    let mut ir = IntermediateRepresentation::default();
    if_stmt.add_to_ir(&mut ir);

    assert_eq!(
      ir.statements,
      vec![
        Op::Gt(Arg::Variable(&Identifier::from("a")), Arg::Variable(&Identifier::from("b"))),
        Op::Jumpfalse(Arg::Reference(AtomicUsize::new(0)), Arg::Reference(AtomicUsize::new(4))),
        Op::Assign(Arg::Variable(&Identifier::from("a")), Arg::Variable(&Identifier::from("max"))),
        Op::Jump(Arg::Reference(AtomicUsize::new(5))),
        Op::Assign(Arg::Variable(&Identifier::from("b")), Arg::Variable(&Identifier::from("max"))),
      ]
    )
  }
}

#[derive(Debug)]
pub enum Arg<'a> {
  Literal(&'a Literal),
  Variable(&'a Identifier),
  Reference(AtomicUsize),
}

impl<'a> PartialEq for Arg<'a> {
  fn eq(&self, other: &Self) -> bool {
    match (self, other) {
      (Self::Literal(l1), Self::Literal(l2)) => l1 == l2,
      (Self::Variable(v1), Self::Variable(v2)) => v1 == v2,
      (Self::Reference(au1), Self::Reference(au2)) => au1.load(Ordering::SeqCst) == au2.load(Ordering::SeqCst),
      _ => false,
    }
  }
}

#[derive(Default)]
pub struct IntermediateRepresentation<'a> {
  statements: Vec<Op<'a>>,
}

impl<'a> IntermediateRepresentation<'a> {
  fn push(&mut self, op: Op<'a>) {
    self.statements.push(op)
  }

  fn last_ref(&self) -> Arg<'a> {
    Arg::Reference(AtomicUsize::new(self.statements.len() - 1))
  }

  fn update_reference(&mut self, index: usize, value: usize) {
    match self.statements.get(index) {
      Some(Op::Jumpfalse(_, Arg::Reference(i))) | Some(Op::Jump(Arg::Reference(i))) => {
        i.store(value, Ordering::SeqCst);
      }
      _ => unreachable!(),
    }
  }
}

#[derive(Debug, PartialEq)]
pub enum Op<'a> {
  Gt(Arg<'a>, Arg<'a>),
  Gte(Arg<'a>, Arg<'a>),
  Lt(Arg<'a>, Arg<'a>),
  Lte(Arg<'a>, Arg<'a>),
  Plus(Arg<'a>, Arg<'a>),
  Minus(Arg<'a>, Arg<'a>),
  Divide(Arg<'a>, Arg<'a>),
  Times(Arg<'a>, Arg<'a>),
  Assign(Arg<'a>, Arg<'a>),
  UnaryMinus(Arg<'a>),
  Not(Arg<'a>),
  Eq(Arg<'a>, Arg<'a>),
  Neq(Arg<'a>, Arg<'a>),
  Land(Arg<'a>, Arg<'a>),
  Lor(Arg<'a>, Arg<'a>),
  Jumpfalse(Arg<'a>, Arg<'a>),
  Jump(Arg<'a>),
}
