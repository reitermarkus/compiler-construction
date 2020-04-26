use mc_parser::ast::*;

pub trait AddToIr<'a> {
  fn add_to_ir(&'a self, ir: &mut IntermediateRepresentation<'a>) -> Arg<'a>;
}

impl<'a> AddToIr<'a> for Assignment<'a> {
  fn add_to_ir(&'a self, ir: &mut IntermediateRepresentation<'a>) -> Arg<'a> {
    let arg = self.rvalue.add_to_ir(ir);
    ir.push(Op::Assign(arg, Arg::Variable(&self.identifier)));

    Arg::Reference(ir.len() - 1)
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

        Arg::Reference(ir.len() - 1)
      }
      Self::Unary { op, expression, .. } => {
        let arg = expression.add_to_ir(ir);

        ir.push(match op {
          UnaryOp::Not => Op::Not(arg),
          UnaryOp::Minus => Op::UnaryMinus(arg),
        });

        Arg::Reference(ir.len() - 1)
      }
      Self::FunctionCall { .. } => todo!(),
    }
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
      ir,
      vec![
        Op::Times(Arg::Literal(&Literal::Int(2)), Arg::Literal(&Literal::Int(3))),
        Op::Plus(Arg::Literal(&Literal::Int(1)), Arg::Reference(0)),
        Op::Assign(Arg::Reference(1), Arg::Variable(&Identifier::from("x"))),
      ]
    );
  }

  #[test]
  fn expression_to_ir() {
    let expression = Expression::try_from("1 + 2 * 3").unwrap();

    let mut ir = IntermediateRepresentation::new();

    let arg = expression.add_to_ir(&mut ir);

    assert_eq!(
      ir,
      vec![
        Op::Times(Arg::Literal(&Literal::Int(2)), Arg::Literal(&Literal::Int(3))),
        Op::Plus(Arg::Literal(&Literal::Int(1)), Arg::Reference(0)),
      ]
    );
    assert_eq!(arg, Arg::Reference(1));
  }
}

#[derive(Debug, PartialEq)]
pub enum Arg<'a> {
  Literal(&'a Literal),
  Variable(&'a Identifier),
  Reference(usize),
}

type IntermediateRepresentation<'a> = Vec<Op<'a>>;

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
  // Jumpfalse(Arg<'a>, Arg<'a>),
  // Jump(Arg<'a>),
}
