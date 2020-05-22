use std::collections::HashMap;
use std::fmt;

use mc_ir::{Arg, IntermediateRepresentation, Op};
use mc_parser::ast::*;

#[derive(Debug)]
pub struct Asm {
  lines: Vec<String>,
}

impl fmt::Display for Asm {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    for line in &self.lines {
      line.fmt(f)?;
      writeln!(f)?;
    }

    Ok(())
  }
}

pub trait ToAsm {
  fn to_asm(&self) -> Asm;
}

#[derive(Default, Debug)]
pub struct Stack {
  lookup_table: HashMap<usize, usize>,
  variables: Vec<(Ty, usize, usize)>,
  size: usize,
}

impl Stack {
  pub fn lookup(&self, index: usize) -> (Ty, usize, usize) {
    let i = self.lookup_table.get(&index).unwrap();
    self.variables[*i]
  }

  pub fn push(&mut self, index: usize, ty: Ty, count: usize) {
    self.variables.push((ty, count, self.size));
    self.lookup_table.insert(index, self.variables.len() - 1);
    self.size += count * ty.size();
  }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Temporaries {
  EAX,
  EBX,
  ECX,
  EDX,
}

impl fmt::Display for Temporaries {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::EAX => write!(f, "eax"),
      Self::EBX => write!(f, "ebx"),
      Self::ECX => write!(f, "ecx"),
      Self::EDX => write!(f, "edx"),
    }
  }
}

pub struct Float {
  long1: i32,
  long2: i32,
}

impl From<f64> for Float {
  fn from(f: f64) -> Self {
    let fb = f.to_le_bytes();
    let long1 = i32::from_le_bytes([fb[0], fb[1], fb[2], fb[3]]);
    let long2 = i32::from_le_bytes([fb[4], fb[5], fb[6], fb[7]]);
    Self { long1, long2 }
  }
}

impl Float {
  pub fn to_asm(&self) -> Vec<String> {
    vec![format!(".long {}", self.long1), format!(".long {}", self.long2)]
  }
}

pub fn add_expression(statements: &[Op<'_>], stack: &Stack, asm: &mut Asm, reg: Temporaries, arg: &Arg<'_>) -> String {
  match arg {
    Arg::Variable(decl_index, index_offset) => {
      let (ty, count, mut offset) = stack.lookup(*decl_index);
      offset += count * ty.size();

      let index_reg = if let Arg::Literal(Literal::Int(index_offset)) = &**index_offset {
        offset -= *index_offset as usize * ty.size();
        None
      } else {
        add_expression(statements, stack, asm, reg, &*index_offset);
        Some(reg)
      };

      let index_offset = if let Some(reg) = index_reg { format!("+{}*{}", reg, ty.size()) } else { "".into() };

      match ty {
        Ty::Int => format!("DWORD PTR [ebp-{}{}]", offset, index_offset),
        ty => unimplemented!("{:?}", ty),
      }
    }
    Arg::Reference(reference) => {
      let temporary = &statements[*reference];

      match temporary {
        Op::Plus(lhs, rhs) => match (lhs, rhs) {
          (Arg::Literal(Literal::Int(l)), Arg::Literal(Literal::Int(r))) => {
            add_expression(statements, stack, asm, reg, &Arg::Literal(&Literal::Int(l + r)))
          }
          (lhs, Arg::Literal(Literal::Int(rhs))) | (Arg::Literal(Literal::Int(rhs)), lhs) => {
            let lhs = add_expression(statements, stack, asm, reg, lhs);

            asm.lines.push(format!("  add    {}, {}", lhs, rhs));

            lhs
          }
          (lhs, rhs) => {
            add_expression(statements, stack, asm, Temporaries::EDX, lhs);
            add_expression(statements, stack, asm, Temporaries::EAX, rhs);

            if reg == Temporaries::EAX {
              asm.lines.push(format!("  add    {}, {}", reg, Temporaries::EDX));
            } else {
              asm.lines.push(format!("  add    {}, {}", reg, Temporaries::EAX));
            }

            reg.to_string()
          }
        },
        Op::Load(variable) => {
          let variable = add_expression(statements, stack, asm, reg, variable);

          asm.lines.push(format!("  mov    {}, {}", reg, variable));

          reg.to_string()
        }
        op => unimplemented!("{:?}", op),
      }
    }
    Arg::Literal(literal) => match literal {
      Literal::Int(integer) => integer.to_string(),
      literal => unimplemented!("{:?}", literal),
    },
    arg => unimplemented!("{:?}", arg),
  }
}

impl<'a> ToAsm for IntermediateRepresentation<'a> {
  fn to_asm(&self) -> Asm {
    let mut asm = Asm { lines: vec![] };

    asm.lines.push("  .intel_syntax noprefix".to_string());
    asm.lines.push("  .global main".to_string());

    for (&name, range) in &self.functions {
      let is_main = name == &Identifier::from("main");

      let mut stack = Stack::default();

      asm.lines.push(format!("{}:", name));

      asm.lines.push("  push   ebp".to_string());
      asm.lines.push("  mov    ebp, esp".to_string());

      let stack_size_index = asm.lines.len();

      for (i, statement) in self.statements.iter().enumerate().skip(range.start).take(range.end) {
        match statement {
          Op::Decl(_, ty, count) => {
            stack.push(i, *ty, *count);
          }
          Op::Assign(arg, variable) => {
            let variable = add_expression(&self.statements, &stack, &mut asm, Temporaries::EAX, variable);
            let value = add_expression(&self.statements, &stack, &mut asm, Temporaries::EDX, arg);
            asm.lines.push(format!("  mov    {}, {}", variable, value));
          }
          Op::Return(arg) => match arg {
            Some(arg) => {
              let value = add_expression(&self.statements, &stack, &mut asm, Temporaries::EAX, arg);

              if value != Temporaries::EAX.to_string() {
                asm.lines.push(format!("  mov    {}, {}", Temporaries::EAX, value));
              }
            }
            _ => todo!(),
          },
          _ => {}
        }
      }

      if is_main {
        asm.lines.push("  leave".to_string());
      } else {
        asm.lines.push("  pop    ebp".to_string());
      }

      asm.lines.push("  ret".to_string());

      asm.lines.insert(stack_size_index, format!("  sub    esp, {}", ((stack.size + 15) / 16) * 16));
    }

    asm
  }
}
