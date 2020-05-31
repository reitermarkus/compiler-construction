use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::collections::BTreeMap;
use std::fmt;

use mc_ir::{Arg, IntermediateRepresentation, Op};
use mc_parser::ast::*;

#[derive(Debug)]
pub struct Asm {
  lines: Vec<String>,
  temporary_register: BTreeMap<usize, Reg32>,
  temporaries: VecDeque<Reg32>,
  labels: BTreeMap<usize, String>,
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
pub enum Reg32 {
  EAX,
  ECX,
  EDX,
  EBX,
  ESP,
  EBP,
  ESI,
  EDI,
}

impl fmt::Display for Reg32 {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::EAX => "eax",
      Self::EBX => "ebx",
      Self::ECX => "ecx",
      Self::EDX => "edx",
      Self::ESP => "ebp",
      Self::EBP => "ebp",
      Self::EDI => "edi",
      Self::ESI => "esi",
    }.fmt(f)
  }
}

impl Reg32 {
  pub fn as_reg8(&self) -> (Reg8, Reg8) {
    match self {
      Self::EAX => (Reg8::AL, Reg8::AH),
      Self::ECX => (Reg8::CL, Reg8::CH),
      Self::EDX => (Reg8::DL, Reg8::DH),
      Self::EBX => (Reg8::BL, Reg8::BH),
      _ => unreachable!(),
    }
  }

  pub fn as_reg16(&self) -> Reg16 {
    match self {
      Self::EAX => Reg16::AX,
      Self::ECX => Reg16::CX,
      Self::EDX => Reg16::DX,
      Self::EBX => Reg16::BX,
      Self::ESP => Reg16::SP,
      Self::EBP => Reg16::BP,
      Self::ESI => Reg16::SI,
      Self::EDI => Reg16::DI,
    }
  }
}

pub enum Reg16 {
  AX,
  CX,
  DX,
  BX,
  SP,
  BP,
  SI,
  DI,
}

impl fmt::Display for Reg16 {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::AX => "ax",
      Self::CX => "cx",
      Self::DX => "dx",
      Self::BX => "bx",
      Self::SP => "sp",
      Self::BP => "bp",
      Self::SI => "si",
      Self::DI => "di",
    }.fmt(f)
  }
}

pub enum Reg8 {
  AL,
  CL,
  DL,
  BL,
  AH,
  CH,
  DH,
  BH,
}

impl fmt::Display for Reg8 {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::AL => "al",
      Self::CL => "cl",
      Self::DL => "dl",
      Self::BL => "bl",
      Self::AH => "ah",
      Self::CH => "ch",
      Self::DH => "dh",
      Self::BH => "bh",
    }.fmt(f)
  }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ConditionalJump {
  JL,
  JLE,
  JG,
  JGE,
  JE,
  JNE
}

impl fmt::Display for ConditionalJump {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::JL => write!(f, "jl"),
      Self::JLE => write!(f, "jle"),
      Self::JG => write!(f, "jg"),
      Self::JGE => write!(f, "jge"),
      Self::JE => write!(f, "je"),
      Self::JNE => write!(f, "jne"),
    }
  }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ConditionalSet {
  SETL,
  SETLE,
  SETG,
  SETGE,
  SETE,
  SETNE
}

impl fmt::Display for ConditionalSet {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::SETL => write!(f, "setl"),
      Self::SETLE => write!(f, "setle"),
      Self::SETG => write!(f, "setg"),
      Self::SETGE => write!(f, "setge"),
      Self::SETE => write!(f, "sete"),
      Self::SETNE => write!(f, "setne"),
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

fn push_temporary(temporary: Reg32, temporaries: &mut VecDeque<Reg32>) {
  if temporary == Reg32::EAX || temporary == Reg32::EDX || temporary == Reg32::ECX {
    temporaries.push_front(temporary);
  } else {
    temporaries.push_back(temporary);
  }
}

macro_rules! stack_hygiene {
  ($asm:expr, $closure:expr) => (
    let temp_var = $asm.temporaries.pop_front().unwrap();
    $closure(temp_var)
  );
  ($ref_l:expr, $i:expr, $asm:expr, $closure:expr) => {
    let temp_l = *$asm.temporary_register.get($ref_l).unwrap();

    $closure(temp_l);

    $asm.temporary_register.insert($i, temp_l);
    $asm.temporary_register.remove($ref_l);
  };
  ($ref_l:expr, $ref_r:expr, $i:expr, $asm:expr, $closure:expr) => {
    let temp_l = *$asm.temporary_register.get($ref_l).unwrap();
    let temp_r = *$asm.temporary_register.get($ref_r).unwrap();

    $closure(temp_l, temp_r);

    push_temporary(temp_r, &mut $asm.temporaries);
    $asm.temporary_register.insert($i, temp_l);
    $asm.temporary_register.remove($ref_r);
    $asm.temporary_register.remove($ref_l);
  }
}

macro_rules! condition_to_asm {
  ($asm:expr, $lhs:expr, $rhs:expr, $op:expr, $index:expr) => {
    $asm.lines.push(format!("  cmp    {}, {}", $lhs, $rhs));
    $asm.lines.push(format!("  {}    {}", $op, $lhs.as_reg8().0));
    $asm.temporary_register.insert($index, $lhs);
  };
}

macro_rules! match_args {
  ($stack:expr, $asm:expr, $args:expr, $op:tt, $index:expr, $instruction:expr) => {
    match $args {
      (Arg::Literal(Literal::Int(l)), Arg::Literal(Literal::Int(r))) => {
        calc_index_offset($stack, $asm, Reg32::EAX, &Arg::Literal(&Literal::Bool(l $op r)));
      }
      (Arg::Reference(ref_l), Arg::Literal(Literal::Int(rhs))) | (Arg::Literal(Literal::Int(rhs)), Arg::Reference(ref_l)) => {
        stack_hygiene!(ref_l, $index, $asm, |temp_l: Reg32| {
          condition_to_asm!($asm, temp_l, rhs, $instruction, $index);
        });
      }
      (Arg::Reference(ref_l), Arg::Reference(ref_r)) => {
        stack_hygiene!(ref_l, ref_r, $index, $asm, |temp_l: Reg32, temp_r: Reg32| $asm.lines.push(format!("  cmp   {}, {}", temp_l, temp_r)));
      },
      _ => unimplemented!()
    }
  };
}

macro_rules! generate_label {
  ($asm:expr, $reference:expr) => {
    if let Some(label) = $asm.labels.get($reference) {
      label
    } else {
      let label_number = $asm.labels.len();
      let label = format!(".L{}", label_number);
      $asm.labels.insert(*$reference, label);
      $asm.labels.get($reference).unwrap()
    }
  };
}

fn calc_index_offset(stack: &Stack,asm: &mut Asm, reg: Reg32, arg: &Arg<'_>) -> String {
    match arg {
      Arg::Variable(decl_index, index_offset) => {
        let (ty, count, mut offset) = stack.lookup(*decl_index);
        offset += count * ty.size();

        let index_reg = match &**index_offset {
          Arg::Literal(Literal::Int(index_offset)) => {
            offset -= *index_offset as usize * ty.size();
            None
          },
          Arg::Reference(decl_index) => {
            let temp = asm.temporary_register.remove(decl_index).unwrap();
            push_temporary(temp, &mut asm.temporaries);
            Some(temp)
          },
          _ => None
        };

        let index_offset = if let Some(reg) = index_reg { format!("+{}*{}", reg, ty.size()) } else { "".into() };

        match ty {
          Ty::Int => format!("DWORD PTR [ebp-{}{}]", offset, index_offset),
          ty => unimplemented!("{:?}", ty),
        }
      },
      Arg::Literal(literal) => {
        push_temporary(reg, &mut asm.temporaries);

        match literal {
          Literal::Int(integer) => integer.to_string(),
          Literal::Bool(boolean) => if *boolean { 1 } else { 0 }.to_string(),
          literal => unimplemented!("{:?}", literal),
        }
      },
      _ => unimplemented!("{:?}", arg)
    }
}

impl<'a> ToAsm for IntermediateRepresentation<'a> {
  fn to_asm(&self) -> Asm {
    let mut asm = Asm {
        lines: vec![],
        temporary_register: BTreeMap::new(),
        temporaries: VecDeque::from(vec![
          Reg32::EAX,
          Reg32::EDX,
          Reg32::ECX,
          Reg32::EBX,
          Reg32::EDI,
          Reg32::ESI,
        ]),
        labels: Default::default(),
     };

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
        if let Some(label) = asm.labels.get(&i) {
          asm.lines.push(format!("{}:", label));
        }

        match statement {
          Op::Decl(_, ty, count) => {
            stack.push(i, *ty, *count);
          }
          Op::Assign(arg, variable) => {
            stack_hygiene!(&mut asm, |temp: Reg32| {
              let variable = calc_index_offset(&stack, &mut asm, temp, variable);
              let value = calc_index_offset(&stack, &mut asm, temp, arg);
              asm.lines.push(format!("  mov    {}, {}", variable, value));
            });
          }
          Op::Return(arg) => {
            if let Some(arg) = arg {
              match arg {
                Arg::Literal(literal) => asm.lines.push(format!("  mov    eax, {}", literal)),
                Arg::Reference(reference) => {
                  let result_register = asm.temporary_register.get(reference).unwrap();

                  if result_register != &Reg32::EAX {
                    asm.lines.push(format!("  mov    {}, {}", Reg32::EAX, result_register));
                  }
                }
                _ => unimplemented!()
              }
            }

            asm.lines.push(format!("  jmp    .AWAY_{}", name));
          }
          Op::Plus(lhs, rhs) => match (lhs, rhs) {
            (Arg::Literal(Literal::Int(l)), Arg::Literal(Literal::Int(r))) => {
              calc_index_offset(&stack, &mut asm, Reg32::EAX, &Arg::Literal(&Literal::Int(l + r)));
            }
            (Arg::Reference(ref_l), Arg::Literal(Literal::Int(rhs))) | (Arg::Literal(Literal::Int(rhs)), Arg::Reference(ref_l)) => {
              stack_hygiene!(ref_l, i, &mut asm, |temp_l: Reg32| asm.lines.push(format!("  add    {}, {}", temp_l, rhs)));
            }
            (Arg::Reference(ref_l), Arg::Reference(ref_r)) => {
              stack_hygiene!(ref_l, ref_r, i, &mut asm, |temp_l: Reg32, temp_r: Reg32| asm.lines.push(format!("  add    {}, {}", temp_l, temp_r)));
            },
            _ => unimplemented!()
          },
          Op::Minus(lhs, rhs) => match (lhs, rhs) {
            (Arg::Literal(Literal::Int(l)), Arg::Literal(Literal::Int(r))) => {
              calc_index_offset(&stack, &mut asm, Reg32::EAX, &Arg::Literal(&Literal::Int(l - r)));
            }
            (Arg::Reference(ref_l), Arg::Literal(Literal::Int(rhs))) => {
              stack_hygiene!(ref_l, i, &mut asm, |temp_l: Reg32| asm.lines.push(format!("  sub    {}, {}", temp_l, rhs)));
            }
            (Arg::Literal(Literal::Int(lhs)), Arg::Reference(ref_r)) => {
              let front_reg = asm.temporaries.pop_front().unwrap();
              let temp_r = *asm.temporary_register.get(ref_r).unwrap();

              asm.lines.push(format!("  mov    {}, {}", front_reg, lhs));
              asm.lines.push(format!("  sub    {}, {}", temp_r, front_reg));

              push_temporary(front_reg, &mut asm.temporaries);
              asm.temporary_register.remove(ref_r);
              asm.temporary_register.insert(i, temp_r);
            }
            (Arg::Reference(ref_l), Arg::Reference(ref_r)) => {
              stack_hygiene!(ref_l, ref_r, i, &mut asm, |temp_l: Reg32, temp_r: Reg32|asm.lines.push(format!("  sub    {}, {}", temp_l, temp_r)));
            },
            _ => unimplemented!()
          },
          Op::Times(lhs, rhs) => match (lhs, rhs) {
            (Arg::Literal(Literal::Int(l)), Arg::Literal(Literal::Int(r))) => {
              calc_index_offset(&stack, &mut asm, Reg32::EAX, &Arg::Literal(&Literal::Int(l * r)));
            }
            (Arg::Reference(ref_l), Arg::Literal(Literal::Int(rhs))) | (Arg::Literal(Literal::Int(rhs)), Arg::Reference(ref_l)) => {
              stack_hygiene!(ref_l, i, &mut asm, |temp_l: Reg32| asm.lines.push(format!("  imul   {}, {}, {}", temp_l, temp_l, rhs)));
            }
            (Arg::Reference(ref_l), Arg::Reference(ref_r)) => {
              stack_hygiene!(ref_l, ref_r, i, &mut asm, |temp_l: Reg32, temp_r: Reg32| asm.lines.push(format!("  imul   {}, {}", temp_l, temp_r)));
            },
            _ => unimplemented!()
          },
          Op::Load(variable) => {
            stack_hygiene!(&mut asm, |temp: Reg32| {
              asm.temporary_register.insert(i, temp);
              let var = calc_index_offset(&stack, &mut asm, temp, variable);
              asm.lines.push(format!("  mov    {}, {}", temp, var));
            });
          }
          Op::Gt(lhs, rhs) | Op::Lte(rhs, lhs) => {
            match_args!(&stack, &mut asm, (lhs, rhs), >, i, ConditionalSet::SETG);
          },
          Op::Lt(lhs, rhs) | Op::Gte(rhs, lhs) => {
            match_args!(&stack, &mut asm, (lhs, rhs), <, i, ConditionalSet::SETL);
          },
          Op::Eq(lhs, rhs) => {
            match_args!(&stack, &mut asm, (lhs, rhs), ==, i, ConditionalSet::SETE);
          },
          Op::Neq(lhs, rhs) => {
            match_args!(&stack, &mut asm, (lhs, rhs), !=, i, ConditionalSet::SETNE);
          },
          Op::Land(lhs, rhs) => match (lhs, rhs) {
            (Arg::Literal(Literal::Bool(l)), Arg::Literal(Literal::Bool(r))) => {
              calc_index_offset(&stack, &mut asm, Reg32::EAX, &Arg::Literal(&Literal::Bool(*l && *r)));
            }
            (Arg::Reference(ref_l), Arg::Literal(Literal::Bool(rhs))) | (Arg::Literal(Literal::Bool(rhs)), Arg::Reference(ref_l)) => {
              stack_hygiene!(ref_l, i, &mut asm, |temp_l: Reg32| asm.lines.push(format!("  and   {}, {}, {}", temp_l, temp_l, rhs)));
            }
            (Arg::Reference(ref_l), Arg::Reference(ref_r)) => {
              stack_hygiene!(ref_l, ref_r, i, &mut asm, |temp_l: Reg32, temp_r: Reg32| asm.lines.push(format!("  and   {}, {}", temp_l, temp_r)));
            },
            _ => unimplemented!()
          },
          Op::Lor(lhs, rhs) => match (lhs, rhs) {
            (Arg::Literal(Literal::Bool(l)), Arg::Literal(Literal::Bool(r))) => {
              calc_index_offset(&stack, &mut asm, Reg32::EAX, &Arg::Literal(&Literal::Bool(*l || *r)));
            }
            (Arg::Reference(ref_l), Arg::Literal(Literal::Bool(rhs))) | (Arg::Literal(Literal::Bool(rhs)), Arg::Reference(ref_l)) => {
              stack_hygiene!(ref_l, i, &mut asm, |temp_l: Reg32| asm.lines.push(format!("  or   {}, {}, {}", temp_l, temp_l, rhs)));
            }
            (Arg::Reference(ref_l), Arg::Reference(ref_r)) => {
              stack_hygiene!(ref_l, ref_r, i, &mut asm, |temp_l: Reg32, temp_r: Reg32| asm.lines.push(format!("  or   {}, {}", temp_l, temp_r)));
            },
            _ => unimplemented!()
          }
          Op::Jumpfalse(Arg::Reference(cond), Arg::Reference(reference)) => {
            let label = generate_label!(asm, reference);

            let register = asm.temporary_register.get(cond).unwrap();

            asm.lines.push(format!("  cmp    {}, 0", register.as_reg8().0));
            asm.lines.push(format!("  je     {}", label));
          },
          Op::Jump(Arg::Reference(reference)) => {
            let label = generate_label!(asm, reference);

            asm.lines.push(format!("  jmp    {}", label));
          },
          op => unimplemented!("{:?}", op),
        }
      }

      let pop_lines = asm.lines.iter().filter_map(|line| {
        if line.contains("ebx") {
          return Some("  pop    ebx".into());
        }

        if line.contains("edi") {
          return Some("  pop    edi".into());
        }

        if line.contains("esi") {
          return Some("  pop    esi".into());
        }

        None
      }).collect::<HashSet<_>>();

      asm.lines.extend(pop_lines);

      asm.lines.push(format!(".AWAY_{}:", name));

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
