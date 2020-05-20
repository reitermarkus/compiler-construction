use mc_parser::ast::*;

use crate::ir::*;

pub trait AddToIr<'a> {
  fn add_to_ir(&'a self, ir: &mut IntermediateRepresentation<'a>) -> Arg<'a>;
}

impl<'a> AddToIr<'a> for Assignment<'a> {
  fn add_to_ir(&'a self, ir: &mut IntermediateRepresentation<'a>) -> Arg<'a> {
    let arg = self.rvalue.add_to_ir(ir);
    ir.push(Op::Assign(arg, Arg::Variable(&self.identifier)));

    let reference = ir.statements.len() - 1;
    *ir.stack.lookup_mut(&self.identifier).unwrap() = reference;
    Arg::Reference(reference)
  }
}

impl<'a> AddToIr<'a> for Declaration<'a> {
  fn add_to_ir(&'a self, ir: &mut IntermediateRepresentation<'a>) -> Arg<'a> {
    let reference = 0;
    ir.stack.push(self.identifier.clone(), reference);
    Arg::Reference(reference)
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

        Arg::Reference(ir.statements.len() - 1)
      }
      Self::Unary { op, expression, .. } => {
        let arg = expression.add_to_ir(ir);

        ir.push(match op {
          UnaryOp::Not => Op::Not(arg),
          UnaryOp::Minus => Op::UnaryMinus(arg),
        });

        Arg::Reference(ir.statements.len() - 1)
      }
      Self::FunctionCall { identifier, arguments, .. } => {
        let args = arguments.iter().map(|a| a.add_to_ir(ir)).collect::<Vec<Arg<'_>>>();
        Arg::FunctionCall(identifier, args)
      }
    }
  }
}

impl<'a> AddToIr<'a> for Statement<'a> {
  fn add_to_ir(&'a self, ir: &mut IntermediateRepresentation<'a>) -> Arg<'a> {
    match self {
      Self::Assignment(assignment) => assignment.add_to_ir(ir),
      Self::Decl(declaration) => declaration.add_to_ir(ir),
      Self::Expression(expression) => {
        if let Expression::FunctionCall { .. } = expression {
          let arg = expression.add_to_ir(ir);
          ir.push(Op::Call(arg));
          ir.last_ref()
        } else {
          expression.add_to_ir(ir)
        }
      }
      Self::If(if_stmt) => if_stmt.add_to_ir(ir),
      Self::While(while_stmt) => while_stmt.add_to_ir(ir),
      Self::Ret(ret_stmt) => ret_stmt.add_to_ir(ir),
      Self::Compound(comp_stmt) => comp_stmt.add_to_ir(ir),
    }
  }
}

impl<'a> AddToIr<'a> for IfStatement<'a> {
  fn add_to_ir(&'a self, ir: &mut IntermediateRepresentation<'a>) -> Arg<'a> {
    let condition = self.condition.add_to_ir(ir);

    let jumpfalse_index = ir.statements.len();
    ir.push(Op::Jumpfalse(condition, Arg::Reference(0)));

    self.block.add_to_ir(ir);

    if let Some(else_block) = &self.else_block {
      let jump_index = ir.statements.len();
      ir.push(Op::Jump(Arg::Reference(0)));

      ir.update_reference(jumpfalse_index, ir.statements.len());

      else_block.add_to_ir(ir);

      ir.update_reference(jump_index, ir.statements.len());
    } else {
      ir.update_reference(jumpfalse_index, ir.statements.len());
    }

    ir.last_ref()
  }
}

impl<'a> AddToIr<'a> for WhileStatement<'a> {
  fn add_to_ir(&'a self, ir: &mut IntermediateRepresentation<'a>) -> Arg<'a> {
    let condition = self.condition.add_to_ir(ir);

    let jumpfalse_index = ir.statements.len();
    ir.push(Op::Jumpfalse(condition, Arg::Reference(0)));

    self.block.add_to_ir(ir);
    ir.update_reference(jumpfalse_index, ir.statements.len());

    ir.last_ref()
  }
}

impl<'a> AddToIr<'a> for ReturnStatement<'a> {
  fn add_to_ir(&'a self, ir: &mut IntermediateRepresentation<'a>) -> Arg<'a> {
    if let Some(expression) = &self.expression {
      let to_return = expression.add_to_ir(ir);
      ir.push(Op::Return(Some(to_return)));
    } else {
      ir.push(Op::Return(None))
    }

    ir.last_ref()
  }
}

impl<'a> AddToIr<'a> for CompoundStatement<'a> {
  fn add_to_ir(&'a self, ir: &mut IntermediateRepresentation<'a>) -> Arg<'a> {
    let ptr = ir.stack.ptr();

    for stmt in &self.statements {
      stmt.add_to_ir(ir);
    }

    ir.stack.reset(ptr);
    ir.last_ref()
  }
}

impl<'a> AddToIr<'a> for FunctionDeclaration<'a> {
  fn add_to_ir(&'a self, ir: &mut IntermediateRepresentation<'a>) -> Arg<'a> {
    let ptr = ir.stack.ptr();

    let start_index = ir.statements.len();

    for parameter in &self.parameters {
      parameter.add_to_ir(ir);
    }

    self.body.add_to_ir(ir);
    let end_index = ir.statements.len();

    ir.add_function(&self.identifier, IrFunction::from((start_index, end_index)));

    ir.stack.reset(ptr);
    ir.last_ref()
  }
}

impl<'a> AddToIr<'a> for Program<'a> {
  fn add_to_ir(&'a self, ir: &mut IntermediateRepresentation<'a>) -> Arg<'a> {
    for function in &self.function_declarations {
      function.add_to_ir(ir);
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
    let assignment = CompoundStatement::try_from(
      "{
      int x;
      x = 1 + 2 * 3;
      }
      ",
    )
    .unwrap();

    let mut ir = IntermediateRepresentation::default();
    assignment.add_to_ir(&mut ir);

    assert_eq!(
      ir.statements,
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

    let mut ir = IntermediateRepresentation::default();

    let arg = expression.add_to_ir(&mut ir);

    assert_eq!(
      ir.statements,
      vec![
        Op::Times(Arg::Literal(&Literal::Int(2)), Arg::Literal(&Literal::Int(3))),
        Op::Plus(Arg::Literal(&Literal::Int(1)), Arg::Reference(0)),
      ]
    );
    assert_eq!(arg, Arg::Reference(1));
  }

  #[test]
  fn if_stmt_to_ir() {
    let if_stmt = CompoundStatement::try_from(
      "{
        int a;
        int b;
        int max;
        if (a > b) {
          max = a;
        } else {
          max = b;
        }
      }",
    )
    .unwrap();

    let mut ir = IntermediateRepresentation::default();
    if_stmt.add_to_ir(&mut ir);

    assert_eq!(
      ir.statements,
      vec![
        Op::Gt(Arg::Variable(&Identifier::from("a")), Arg::Variable(&Identifier::from("b"))),
        Op::Jumpfalse(Arg::Reference(0), Arg::Reference(4)),
        Op::Assign(Arg::Variable(&Identifier::from("a")), Arg::Variable(&Identifier::from("max"))),
        Op::Jump(Arg::Reference(5)),
        Op::Assign(Arg::Variable(&Identifier::from("b")), Arg::Variable(&Identifier::from("max"))),
      ]
    )
  }

  #[test]
  fn comp_stmt_to_ir() {
    let comp_stmt = CompoundStatement::try_from(
      "{
      int a;
      int b;
      while (a > b) {
        a = a + 1;
      }
      return a;
    }",
    )
    .unwrap();

    let mut ir = IntermediateRepresentation::default();
    comp_stmt.add_to_ir(&mut ir);

    assert_eq!(
      ir.statements,
      vec![
        Op::Gt(Arg::Variable(&Identifier::from("a")), Arg::Variable(&Identifier::from("b"))),
        Op::Jumpfalse(Arg::Reference(0), Arg::Reference(4)),
        Op::Plus(Arg::Variable(&Identifier::from("a")), Arg::Literal(&Literal::Int(1))),
        Op::Assign(Arg::Reference(2), Arg::Variable(&Identifier::from("a"))),
        Op::Return(Some(Arg::Variable(&Identifier::from("a")))),
      ]
    )
  }

  #[test]
  fn function_to_ir() {
    let function = FunctionDeclaration::try_from(
      "void main() {
        int x;
        x = 1 + 1;
        int y;
        y = x;
        return;
      }",
    )
    .unwrap();

    let mut ir = IntermediateRepresentation::default();
    function.add_to_ir(&mut ir);

    assert_eq!(
      ir.statements,
      vec![
        Op::Plus(Arg::Literal(&Literal::Int(1)), Arg::Literal(&Literal::Int(1))),
        Op::Assign(Arg::Reference(0), Arg::Variable(&Identifier::from("x"))),
        Op::Assign(Arg::Variable(&Identifier::from("x")), Arg::Variable(&Identifier::from("y"))),
        Op::Return(None),
      ]
    );

    assert_eq!(ir.functions.get(&Identifier::from("main")), Some(&IrFunction { start: 0, end: 4 }),)
  }
}
