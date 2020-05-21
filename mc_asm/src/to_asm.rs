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

fn index_expression_to_asm(
  stack: &Stack,
  lines: &mut Vec<String>,
  decl_index: usize,
  index_expression: &Arg<'_>,
) -> (usize, String) {
  let (ty, count, mut offset) = stack.lookup(decl_index);

  offset += count * ty.size();

  let index = match index_expression {
    Arg::Literal(Literal::Int(index)) => {
      offset -= *index as usize * ty.size();
      "".into()
    }
    Arg::Variable(decl_index, index_expression) => {
      {
        let (offset, index) = index_expression_to_asm(&stack, lines, *decl_index, &**index_expression);
        lines.push(format!("  mov    eax, DWORD PTR [ebp-{}{}]", offset, index));
      }

      format!("+eax*{}", ty.size())
    }
    _ => unimplemented!(),
  };

  (offset, index)
}

impl<'a> ToAsm for IntermediateRepresentation<'a> {
  fn to_asm(&self) -> Asm {
    let mut lines = vec![];

    lines.push("  .intel_syntax noprefix".to_string());
    lines.push("  .global main".to_string());

    for (&name, range) in &self.functions {
      let is_main = name == &Identifier::from("main");

      let mut stack = Stack::default();

      lines.push(format!("{}:", name));

      lines.push("  push   ebp".to_string());
      lines.push("  mov    ebp, esp".to_string());

      let stack_size_index = lines.len();

      for (i, statement) in self.statements.iter().enumerate().skip(range.start).take(range.end) {
        match statement {
          Op::Decl(_, ty, count) => {
            stack.push(i, *ty, *count);
          }
          Op::Assign(arg, variable) => {
            if let Arg::Variable(decl_index, index_expression) = variable {
              let value = if let Arg::Literal(Literal::Int(v)) = arg { format!("{}", v) } else { "".into() };

              let (offset, index) = index_expression_to_asm(&stack, &mut lines, *decl_index, &**index_expression);
              lines.push(format!("  mov    DWORD PTR [ebp-{}{}], {}", offset, index, value));
            } else {
              unimplemented!()
            }
          }
          Op::Return(arg) => match arg {
            Some(Arg::Literal(Literal::Int(v))) => {
              lines.push(format!("  mov    eax, {}", v));
            }
            Some(_) => {}
            _ => {}
          },
          Op::Plus(_lhs, _rhs) => {}
          _ => {}
        }
      }

      if is_main {
        lines.push("  leave".to_string());
      } else {
        lines.push("  pop    ebp".to_string());
      }

      lines.push("  ret".to_string());

      lines.insert(stack_size_index, format!("  sub    esp, {}", ((stack.size + 15) / 16) * 16));
    }

    Asm { lines }
  }
}
