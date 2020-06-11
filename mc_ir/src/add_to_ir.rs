use mc_parser::ast::*;

use crate::ir::*;
use mc_symbol_table::semantic_checks::FindReturnStatement;

pub trait AddToIr<'a> {
  fn add_to_ir(&'a self, ir: &mut IntermediateRepresentation<'a>) -> Arg<'a>;
}

impl<'a> AddToIr<'a> for Assignment<'a> {
  fn add_to_ir(&'a self, ir: &mut IntermediateRepresentation<'a>) -> Arg<'a> {
    let (reference, ty) = ir.stack.lookup(&self.identifier).unwrap();

    let variable = if let Some(index_expression) = &self.index_expression {
      Arg::Variable(ty, reference, Box::new(Some(index_expression.add_to_ir(ir))))
    } else {
      Arg::Variable(ty, reference, Box::default())
    };

    let arg = self.rvalue.add_to_ir(ir);

    ir.push(Op::Assign(arg, variable));

    ir.last_ref()
  }
}

impl<'a> AddToIr<'a> for Declaration<'a> {
  fn add_to_ir(&'a self, ir: &mut IntermediateRepresentation<'a>) -> Arg<'a> {
    ir.push(Op::Decl(&self.identifier, self.ty, self.count));

    let reference = ir.statements.len() - 1;
    ir.stack.push(self.identifier.clone(), reference, self.ty);
    Arg::Reference(Some(self.ty), reference)
  }
}

impl<'a> AddToIr<'a> for Expression<'a> {
  fn add_to_ir(&'a self, ir: &mut IntermediateRepresentation<'a>) -> Arg<'a> {
    match self {
      Self::Literal { literal, .. } => Arg::Literal(literal.clone()),
      Self::Variable { identifier, index_expression, .. } => {
        let (reference, ty) = ir.stack.lookup(identifier).unwrap();

        if let Some(index_expression) = index_expression {
          let index_expression = index_expression.add_to_ir(ir);
          Arg::Variable(ty, reference, Box::new(Some(index_expression)))
        } else {
          Arg::Variable(ty, reference, Box::default())
        }
      }
      Self::Binary { op, lhs, rhs, .. } => {
        let lhs = lhs.add_to_ir(ir);
        let rhs = rhs.add_to_ir(ir);

        match (lhs, rhs) {
          (Arg::Literal(lhs), Arg::Literal(rhs)) => {
            macro_rules! literal_op {
              ($ty:path, $op:expr, $l:expr, $r:expr) => {
                match $op {
                  BinaryOp::Plus => $ty($l + $r),
                  BinaryOp::Minus => $ty($l - $r),
                  BinaryOp::Times => $ty($l * $r),
                  BinaryOp::Divide => $ty($l / $r),
                  BinaryOp::Gt => Literal::Bool($l > $r),
                  BinaryOp::Gte => Literal::Bool($l >= $r),
                  BinaryOp::Lt => Literal::Bool($l < $r),
                  BinaryOp::Lte => Literal::Bool($l <= $r),
                  BinaryOp::Eq => Literal::Bool($l == $r),
                  BinaryOp::Neq => Literal::Bool($l != $r),
                  _ => unreachable!(),
                }
              };
            };

            let literal = match (lhs, rhs) {
              (Literal::Int(l), Literal::Int(r)) => literal_op!(Literal::Int, op, l, r),
              (Literal::Float(l), Literal::Float(r)) => literal_op!(Literal::Float, op, l, r),
              (Literal::Bool(l), Literal::Bool(r)) => match op {
                BinaryOp::Land => Literal::Bool(l && r),
                BinaryOp::Lor => Literal::Bool(l || r),
                _ => unreachable!(),
              },
              _ => unreachable!(),
            };

            Arg::Literal(literal)
          }
          (lhs, rhs) => {
            ir.push(match op {
              BinaryOp::Gt => Op::Gt(lhs, rhs),
              BinaryOp::Gte => Op::Gte(lhs, rhs),
              BinaryOp::Lt => Op::Lt(lhs, rhs),
              BinaryOp::Lte => Op::Lte(lhs, rhs),
              BinaryOp::Plus => Op::Plus(lhs, rhs),
              BinaryOp::Minus => Op::Minus(lhs, rhs),
              BinaryOp::Divide => Op::Divide(lhs, rhs),
              BinaryOp::Times => Op::Times(lhs, rhs),
              BinaryOp::Eq => Op::Eq(lhs, rhs),
              BinaryOp::Neq => Op::Neq(lhs, rhs),
              BinaryOp::Land => Op::Land(lhs, rhs),
              BinaryOp::Lor => Op::Lor(lhs, rhs),
            });

            ir.last_ref()
          }
        }
      }
      Self::Unary { op, expression, .. } => {
        let arg = expression.add_to_ir(ir);

        ir.push(match op {
          UnaryOp::Not => Op::Not(arg),
          UnaryOp::Minus => Op::UnaryMinus(arg),
        });

        ir.last_ref()
      }
      Self::FunctionCall { identifier, arguments, .. } => {
        let args = arguments.iter().map(|a| a.add_to_ir(ir)).collect::<Vec<Arg<'_>>>();

        let ty = match identifier.as_ref() {
          "read_int" => Some(Ty::Int),
          "read_float" => Some(Ty::Float),
          _ => ir.functions.get(identifier).and_then(|&(_, ty)| ty),
        };

        let arg = Arg::FunctionCall(ty, identifier, args);
        ir.push(Op::Call(arg));
        ir.last_ref()
      }
    }
  }
}

impl<'a> AddToIr<'a> for Statement<'a> {
  fn add_to_ir(&'a self, ir: &mut IntermediateRepresentation<'a>) -> Arg<'a> {
    match self {
      Self::Assignment(assignment) => assignment.add_to_ir(ir),
      Self::Decl(declaration) => declaration.add_to_ir(ir),
      Self::Expression(expression) => expression.add_to_ir(ir),
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
    ir.push(Op::Jumpfalse(condition, Arg::Reference(None, 0)));

    let block_always_returns = self.block.find_return_statement();
    self.block.add_to_ir(ir);

    if let Some(else_block) = &self.else_block {
      let jump_index = ir.statements.len();

      if !block_always_returns {
        ir.push(Op::Jump(Arg::Reference(None, 0)));
      }

      ir.update_reference(jumpfalse_index, ir.statements.len());

      else_block.add_to_ir(ir);

      if !block_always_returns {
        ir.update_reference(jump_index, ir.statements.len());
      }
    } else {
      ir.update_reference(jumpfalse_index, ir.statements.len());
    }

    ir.push(Op::Nope);
    ir.last_ref()
  }
}

impl<'a> AddToIr<'a> for WhileStatement<'a> {
  fn add_to_ir(&'a self, ir: &mut IntermediateRepresentation<'a>) -> Arg<'a> {
    let condition_ref = Arg::Reference(None, ir.statements.len());
    let condition = self.condition.add_to_ir(ir);

    let jumpfalse_index = ir.statements.len();
    ir.push(Op::Jumpfalse(condition, Arg::Reference(None, 0)));

    self.block.add_to_ir(ir);
    ir.push(Op::Jump(condition_ref));

    ir.update_reference(jumpfalse_index, ir.statements.len());

    ir.push(Op::Nope);
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

      if stmt.find_return_statement() {
        break;
      }
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
      ir.push(Op::Param(&parameter.identifier, parameter.ty, parameter.count));

      let reference = ir.statements.len() - 1;
      ir.stack.push(parameter.identifier.clone(), reference, parameter.ty);
    }

    self.body.add_to_ir(ir);
    let end_index = ir.statements.len();

    ir.add_function(&self.identifier, start_index..end_index, self.ty);

    ir.stack.reset(ptr);
    ir.last_ref()
  }
}

impl<'a> AddToIr<'a> for Program<'a> {
  fn add_to_ir(&'a self, ir: &mut IntermediateRepresentation<'a>) -> Arg<'a> {
    for function in &self.function_declarations {
      ir.add_function(&function.identifier, 0..0, function.ty);
    }

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

   use Arg::{
     Reference,
     Variable
   };

   use Op::*;

   use Ty::*;

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
         Op::Decl(&Identifier("x".to_owned()), Ty::Int, None),
         Op::Assign(Arg::Literal(Literal::Int(7)), Arg::Variable(Ty::Int, 0, Box::new(None)))
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
       vec![]
     );
     assert_eq!(arg, Arg::Literal(Literal::Int(7)));
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
         Decl(&Identifier("a".to_owned()), Int, None),
         Decl(&Identifier("b".to_owned()), Int, None),
         Decl(&Identifier("max".to_owned()), Int, None),
         Gt(Variable(Ty::Int, 0, Box::default()), Variable(Int, 1, Box::default())),
         Jumpfalse(Reference(Some(Bool), 3), Reference(None, 7)),
         Assign(Variable(Int, 0, Box::default()), Variable(Int, 2, Box::default())),
         Jump(Reference(None, 8)),
         Assign(Variable(Int, 1, Box::default()),
         Variable(Int, 2, Box::default())),
         Nope
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
       Decl(&Identifier("a".to_owned()), Int, None),
       Decl(&Identifier("b".to_owned()), Int, None),
       Gt(Variable(Int, 0, Box::default()),
       Variable(Int, 1, Box::default())),
       Jumpfalse(Reference(Some(Bool), 2),
       Reference(None, 7)),
       Plus(Variable(Int, 0, Box::default()), Arg::Literal(Literal::Int(1))),
       Assign(Reference(Some(Int), 4), Variable(Int, 0, Box::default())),
       Jump(Reference(None, 2)),
       Nope,
       Return(Some(Variable(Int, 0, Box::default())))
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
        Decl(&Identifier("x".to_owned()), Int, None),
        Assign(Arg::Literal(Literal::Int(2)), Variable(Int, 0, Box::default())),
        Decl(&Identifier("y".to_owned()), Int, None),
        Assign(Variable(Int, 0, Box::default()), Variable(Int, 2, Box::default())),
        Return(None)
      ]
    );

    assert_eq!(ir.functions.get(&Identifier::from("main")), Some(&(0..5, None)))
  }
}
