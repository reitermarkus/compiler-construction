use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::collections::BTreeMap;
use std::fmt;
use std::fmt::Display;
use std::cmp::Ordering;

use mc_ir::{Arg, IntermediateRepresentation, Op};
use mc_parser::ast::*;

#[derive(Debug)]
pub struct Asm {
  lines: Vec<String>,
  temporary_register: BTreeMap<usize, Reg32>,
  temporaries: VecDeque<Reg32>,
  labels: BTreeMap<usize, String>,
  floats: BTreeMap<Float, String>,
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

#[derive(Clone, PartialEq, Debug, Eq, PartialOrd, Copy)]
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

impl Ord for Float {
  fn cmp(&self, other: &Self) -> Ordering {
      self.long1.cmp(&other.long1).then(self.long2.cmp(&other.long2))
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

    $asm.temporary_register.remove($ref_l);

    if !$asm.temporary_register.contains_key(&$i) {
      $asm.temporary_register.insert($i, temp_l);
    }
  };
  ($ref_l:expr, $ref_r:expr, $i:expr, $asm:expr, $closure:expr) => {
    let temp_l = *$asm.temporary_register.get($ref_l).unwrap();
    let temp_r = *$asm.temporary_register.get($ref_r).unwrap();

    $closure(temp_l, temp_r);

    push_temporary(temp_r, &mut $asm.temporaries);

    $asm.temporary_register.remove($ref_r);
    $asm.temporary_register.remove($ref_l);

    if !$asm.temporary_register.contains_key(&$i) {
      $asm.temporary_register.insert($i, temp_l);
    }
  }
}

macro_rules! operation_to_asm {
  ($index:expr, $stack:expr, $asm:expr, $args:expr, $op:tt: $from:ident -> $to:ident, $reflit_closure:expr, $reference_closure:expr) => {
    operation_to_asm!($index, $stack, $asm, $args, $op: $from -> $to, $reflit_closure, $reflit_closure, $reference_closure)
  };
  ($index:expr, $stack:expr, $asm:expr, $args:expr, $op:tt: $from:ident -> $to:ident, $reflit_closure:expr, $litref_closure:expr, $reference_closure:expr) => {
    match $args {
      (Arg::Literal(Literal::$from(l)), Arg::Literal(Literal::$from(r))) => {
        calc_index_offset($stack, $asm, Reg32::EAX, &Arg::Literal(&Literal::$to(*l $op *r)));
      }
      (Arg::Reference(Some(ty), ref_l), Arg::Literal(Literal::$from(rhs))) if ty == &Ty::$from => {
        stack_hygiene!(ref_l, $index, $asm, |temp_l: Reg32| {
          $reflit_closure($index, $asm, temp_l, rhs)
        });
      }
      (Arg::Literal(Literal::$from(lhs)), Arg::Reference(Some(ty), ref_r)) if ty == &Ty::$from => {
        stack_hygiene!(ref_r, $index, $asm, |temp_r: Reg32| {
          $litref_closure($index, $asm, temp_r, lhs)
        });
      }
      (Arg::Reference(Some(ty_l), ref_l), Arg::Reference(Some(ty_r), ref_r)) if ty_l == &Ty::$from && ty_r == &Ty::$from => {
        stack_hygiene!(ref_l, ref_r, $index, $asm, |temp_l: Reg32, temp_r: Reg32| {
          $reference_closure($index, $asm, temp_l, temp_r)
        });
      },
      (lhs, rhs) => unreachable!("LHS = {:?}, RHS = {:?}", lhs, rhs)
    }
  };
}

macro_rules! comparison_to_asm {
  ($op:expr) => {
    fn comparison_to_asm<T: Display>(index: usize, asm: &mut Asm, lhs: Reg32, rhs: T) {
      asm.lines.push(format!("  cmp    {}, {}", lhs, rhs));
      asm.lines.push(format!("  {}   {}", $op, lhs.as_reg8().0));
    }
  };
}

pub enum Pointer {
  Qword { offset: usize, index_offset: Option<Reg32> },
  Dword { offset: usize, index_offset: Option<Reg32> },
  Byte { offset: usize, index_offset: Option<Reg32> },
}

impl Pointer {
  fn name(&self) -> &'static str {
    match self {
      Self::Qword { .. } => "QWORD PTR",
      Self::Dword { .. } => "DWORD PTR",
      Self::Byte { .. } => "BYTE PTR",
    }
  }

  fn size(&self) -> usize {
    match self {
      Self::Qword { .. } => 8,
      Self::Dword { .. } => 4,
      Self::Byte { .. } => 1,
    }
  }
}

impl fmt::Display for Pointer {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Qword { offset, index_offset } | Self::Dword { offset, index_offset } | Self::Byte { offset, index_offset } => {
        write!(f, "{} [ebp-{}", self.name(), offset)?;

        if let Some(index_offset) = index_offset {
          write!(f, "+{}*{}", index_offset, self.size())?;
        }

        write!(f, "]")
      }
    }
  }
}

pub enum Storage {
  Pointer(Pointer),
  Register(Reg32),
  Literal(String),
}

impl fmt::Display for Storage {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Pointer(pointer) => write!(f, "{}", pointer),
      Self::Register(reg) => write!(f, "{}", reg),
      Self::Literal(string) => write!(f, "{}", string)
    }
  }
}

impl Storage {
  fn map_register(&self, reg: &Reg32) -> String {
    match self {
      Self::Pointer(Pointer::Dword { .. }) => reg.to_string(),
      Self::Pointer(Pointer::Byte { .. }) => reg.as_reg8().0.to_string(),
      Self::Register(_) => reg.to_string(),
      _ => unreachable!(),
    }
  }
}

fn calc_index_offset(stack: &Stack,asm: &mut Asm, reg: Reg32, arg: &Arg<'_>) -> Storage {
    match arg {
      Arg::Variable(ty, decl_index, index_offset) => {
        let (ty, count, mut offset) = stack.lookup(*decl_index);
        offset += count * ty.size();

        let index_reg = match &**index_offset {
          Arg::Literal(Literal::Int(index_offset)) => {
            offset -= *index_offset as usize * ty.size();
            None
          },
          Arg::Reference(ty, decl_index) => {
            let temp = asm.temporary_register.remove(decl_index).unwrap();
            push_temporary(temp, &mut asm.temporaries);
            Some(temp)
          },
          _ => None
        };

        Storage::Pointer(match ty {
          Ty::Int => Pointer::Dword { offset, index_offset: index_reg },
          Ty::Bool => Pointer::Byte { offset, index_offset: index_reg },
          Ty::Float => Pointer::Qword { offset, index_offset: index_reg },
          ty => unimplemented!("{:?}", ty),
        })
      },
      Arg::Reference(_, reference) => {
        Storage::Register(*asm.temporary_register.get(reference).unwrap())
      },
      Arg::Literal(literal) => {
        push_temporary(reg, &mut asm.temporaries);

        Storage::Literal(match literal {
          Literal::Int(integer) => integer.to_string(),
          Literal::Bool(boolean) => if *boolean { 1 } else { 0 }.to_string(),
          literal => unimplemented!("{:?}", literal),
        })
      },
      _ => unimplemented!("{:?}", arg)
    }
}

fn add_float(asm: &mut Asm, float: f64) -> String {
  let float = Float::from(float);

  if let Some(label) = asm.floats.get(&float) {
    label
  } else {
    let float_number = asm.floats.len();
    asm.floats.insert(float, format!(".LC{}", float_number));
    asm.floats.get(&float).unwrap()
  }.to_owned()
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
        floats: BTreeMap::new(),
     };

    asm.lines.push("  .intel_syntax noprefix".to_string());
    asm.lines.push("  .global main".to_string());

    for (i, statement) in self.statements.iter().enumerate() {
      match statement {
        Op::Jumpfalse(_, Arg::Reference(_, reference)) | Op::Jump(Arg::Reference(_, reference)) => {
          let label_number = asm.labels.len();
          let label = format!(".L{}", label_number);
          asm.labels.insert(*reference, label);
        },
        _ => {}
      }
    }

    for (&name, (range, _)) in &self.functions {
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
            match variable {
              Arg::Variable(Ty::Float, ..) => {
                match arg {
                  Arg::Literal(Literal::Float(float)) => {
                    stack_hygiene!(&mut asm, |temp: Reg32| {
                      let variable = calc_index_offset(&stack, &mut asm, temp, variable);
                      let label = add_float(&mut asm, *float);

                      match variable {
                        Storage::Pointer(pointer) => {
                          asm.lines.push(format!("  fld    {} {}", pointer.name(), label));
                          asm.lines.push(format!("  fstp   {}", pointer));
                        },
                        _ => unreachable!(),
                      }
                    });
                  },
                  Arg::Reference(_, reference) => {
                    stack_hygiene!(&mut asm, |temp: Reg32| {
                      let variable = calc_index_offset(&stack, &mut asm, temp, variable);
                      asm.lines.push(format!("  fstp   {}", variable));
                    });
                  },
                  _ => unreachable!(),
                }
              },
              variable => {
                stack_hygiene!(&mut asm, |temp: Reg32| {
                  let variable = calc_index_offset(&stack, &mut asm, temp, variable);
                  let value = calc_index_offset(&stack, &mut asm, temp, arg);
                  asm.lines.push(format!("  mov    {}, {}", variable, value));
                });
              }
            }
          }
          Op::Load(variable) => {
            match variable {
              Arg::Variable(Ty::Float, ..) => {
                stack_hygiene!(&mut asm, |temp: Reg32| {
                  let var = calc_index_offset(&stack, &mut asm, temp, variable);
                  asm.lines.push(format!("  fld    {}", var));
                });
              },
              variable => {
                stack_hygiene!(&mut asm, |temp: Reg32| {
                  asm.temporary_register.insert(i, temp);
                  let var = calc_index_offset(&stack, &mut asm, temp, variable);
                  let reg = var.map_register(&temp);
                  asm.lines.push(format!("  mov    {}, {}", reg, var));
                });
              }
            }
          }
          Op::Return(arg) => {
            if let Some(arg) = arg {
              match arg {
                Arg::Literal(literal) => asm.lines.push(format!("  mov    eax, {}", literal)),
                Arg::Reference(ty, reference) => {
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
          Op::Plus(lhs, rhs) => match lhs.ty() {
            Some(Ty::Int) => {
              fn add_reflit_to_asm<T: Display>(index: usize, asm: &mut Asm, lhs: Reg32, rhs: T) {
                asm.lines.push(format!("  add    {}, {}", lhs, rhs));
              }

              fn add_reference_to_asm<T: Display>(index: usize, asm: &mut Asm, lhs: Reg32, rhs: T) {
                asm.lines.push(format!("  add    {}, {}", lhs, rhs));
              }

              operation_to_asm!(i, &stack, &mut asm, (lhs, rhs), +: Int -> Int, add_reflit_to_asm, add_reference_to_asm);
            },
            Some(Ty::Float) => {
              match (lhs, rhs) {
                (Arg::Literal(Literal::Float(lhs)), Arg::Literal(Literal::Float(rhs))) => {
                  let pointer = add_float(&mut asm, lhs + rhs);
                  asm.lines.push(format!("  fld    QWORD PTR {}", pointer));
                },
                (Arg::Reference(Some(ty), ref_l), Arg::Literal(Literal::Float(rhs))) | (Arg::Literal(Literal::Float(rhs)), Arg::Reference(Some(ty), ref_l)) if ty == &Ty::Float => {
                  let pointer = add_float(&mut asm, *rhs);
                  asm.lines.push(format!("  fld    QWORD PTR {}", pointer));
                  asm.lines.push(format!("  faddp  st(1), st"));
                }
                (Arg::Reference(Some(ty_l), ref_l), Arg::Reference(Some(ty_r), ref_r)) if ty_l == &Ty::Float && ty_r == &Ty::Float => {
                  asm.lines.push(format!("  faddp  st(1), st"));
                },
                (lhs, rhs) => unreachable!("LHS = {:?}, RHS = {:?}", lhs, rhs)
              }
            },
            _ => unimplemented!(),
          },
          Op::Minus(lhs, rhs) => match lhs.ty() {
            Some(Ty::Int) => {
              fn sub_reflit_to_asm<T: Display>(index: usize, asm: &mut Asm, lhs: Reg32, rhs: T) {
                asm.lines.push(format!("  sub    {}, {}", lhs, rhs));
              }

              fn sub_litref_to_asm<T: Display>(index: usize, asm: &mut Asm, rhs: Reg32, lhs: T) {
                let temp_l = asm.temporaries.pop_front().unwrap();

                asm.lines.push(format!("  mov    {}, {}", temp_l, lhs));
                asm.lines.push(format!("  sub    {}, {}", temp_l, rhs));

                asm.temporary_register.insert(index, temp_l);
              }

              fn sub_reference_to_asm<T: Display>(index: usize, asm: &mut Asm, lhs: Reg32, rhs: T) {
                asm.lines.push(format!("  sub    {}, {}", lhs, rhs));
              }

              operation_to_asm!(i, &stack, &mut asm, (lhs, rhs), -: Int -> Int, sub_reflit_to_asm, sub_litref_to_asm, sub_reference_to_asm);
            },
            Some(Ty::Float) => {
              match (lhs, rhs) {
                (Arg::Literal(Literal::Float(lhs)), Arg::Literal(Literal::Float(rhs))) => {
                  let pointer = add_float(&mut asm, lhs - rhs);
                  asm.lines.push(format!("  fld    QWORD PTR {}", pointer));
                },
                (Arg::Reference(Some(ty), ref_l), Arg::Literal(Literal::Float(rhs))) if ty == &Ty::Float => {
                  let pointer = add_float(&mut asm, *rhs);
                  asm.lines.push(format!("  fld    QWORD PTR {}", pointer));
                  asm.lines.push(format!("  fsubp  st(1), st"));
                },
                (Arg::Literal(Literal::Float(lhs)), Arg::Reference(Some(ty), ref_r)) if ty == &Ty::Float => {
                  let pointer = add_float(&mut asm, *lhs);
                  asm.lines.push(format!("  fld    QWORD PTR {}", pointer));
                  asm.lines.push(format!("  fsubp  st, st(1)"));
                }
                (Arg::Reference(Some(ty_l), ref_l), Arg::Reference(Some(ty_r), ref_r)) if ty_l == &Ty::Float && ty_r == &Ty::Float => {
                  asm.lines.push(format!("  fsubp  st(1), st"));
                },
                (lhs, rhs) => unreachable!("LHS = {:?}, RHS = {:?}", lhs, rhs)
              }
            },
            _ => unimplemented!(),
          },
          Op::Times(lhs, rhs) => {
            match lhs.ty() {
              Some(Ty::Int) => {
                fn imul_reflit_to_asm<T: Display>(index: usize, asm: &mut Asm, lhs: Reg32, rhs: T) {
                  asm.lines.push(format!("  imul   {}, {}, {}", lhs, lhs, rhs));
                }

                fn imul_reference_to_asm<T: Display>(index: usize, asm: &mut Asm, lhs: Reg32, rhs: T) {
                  asm.lines.push(format!("  imul   {}, {}", lhs, rhs));
                }

                operation_to_asm!(i, &stack, &mut asm, (lhs, rhs), *: Int -> Int, imul_reflit_to_asm, imul_reference_to_asm);
              },
              _ => unimplemented!(),
            }
          },
          Op::Divide(lhs, rhs) => match lhs.ty() {
            Some(Ty::Int) => {
              fn div_reflit_to_asm<T: Display>(index: usize, asm: &mut Asm, lhs: Reg32, rhs: T) {
                if lhs != Reg32::EAX {
                  asm.lines.push(format!("  mov    eax, {}", lhs));
                }

                let temp_r = asm.temporaries.pop_front().unwrap();

                asm.lines.push(format!("  mov    {}, {}", temp_r, rhs));

                asm.lines.push(format!("  cdq"));
                asm.lines.push(format!("  idiv   {}", temp_r));
                asm.lines.push(format!("  mov    {}, eax", lhs));

                push_temporary(temp_r, &mut asm.temporaries);
              }

              fn div_litref_to_asm<T: Display>(index: usize, asm: &mut Asm, rhs: Reg32, lhs: T) {
                let temp_l = asm.temporaries.pop_front().unwrap();

                if temp_l != Reg32::EAX {
                  asm.lines.push(format!("  mov    eax, {}", lhs));
                }

                asm.lines.push(format!("  cdq"));
                asm.lines.push(format!("  idiv   {}", rhs));

                if temp_l != Reg32::EAX {
                  asm.lines.push(format!("  mov    {}, eax", temp_l));
                }

                asm.temporary_register.insert(index, temp_l);
              }

              fn div_reference_to_asm<T: Display>(index: usize, asm: &mut Asm, lhs: Reg32, rhs: T) {
                if lhs != Reg32::EAX {
                  asm.lines.push(format!("  mov    eax, {}", lhs));
                }

                asm.lines.push(format!("  cdq"));
                asm.lines.push(format!("  idiv   {}", rhs));

                if lhs != Reg32::EAX {
                  asm.lines.push(format!("  mov    {}, eax", lhs));
                }
              }

              operation_to_asm!(i, &stack, &mut asm, (lhs, rhs), -: Int -> Int, div_reflit_to_asm, div_litref_to_asm, div_reference_to_asm);
            },
            _ => unimplemented!(),
          },
          Op::Gt(lhs, rhs) | Op::Lte(rhs, lhs) => {
            comparison_to_asm!(ConditionalSet::SETG);

            match lhs.ty() {
              Some(Ty::Int) => operation_to_asm!(i, &stack, &mut asm, (lhs, rhs), >: Int -> Bool, comparison_to_asm, comparison_to_asm),
              _ => unimplemented!(),
            }
          },
          Op::Lt(lhs, rhs) | Op::Gte(rhs, lhs) => {
            comparison_to_asm!(ConditionalSet::SETL);

            match lhs.ty() {
              Some(Ty::Int) => operation_to_asm!(i, &stack, &mut asm, (lhs, rhs), <: Int -> Bool, comparison_to_asm, comparison_to_asm),
              _ => unimplemented!(),
            }
          },
          Op::Eq(lhs, rhs) => {
            comparison_to_asm!(ConditionalSet::SETE);

            match lhs.ty() {
              Some(Ty::Int) => operation_to_asm!(i, &stack, &mut asm, (lhs, rhs), ==: Int -> Bool, comparison_to_asm, comparison_to_asm),
              _ => unimplemented!(),
            }
          },
          Op::Neq(lhs, rhs) => {
            comparison_to_asm!(ConditionalSet::SETNE);

            match lhs.ty() {
              Some(Ty::Int) => operation_to_asm!(i, &stack, &mut asm, (lhs, rhs), !=: Int -> Bool, comparison_to_asm, comparison_to_asm),
              _ => unimplemented!(),
            }
          },
          Op::Land(lhs, rhs) => {
            fn and_to_asm<T: Display>(index: usize, asm: &mut Asm, lhs: Reg32, rhs: T) {
              asm.lines.push(format!("  and    {}, {}", lhs, rhs));
            }

            operation_to_asm!(i, &stack, &mut asm, (lhs, rhs), &&: Bool -> Bool, and_to_asm, and_to_asm)
          },
          Op::Lor(lhs, rhs) => {
            fn or_to_asm<T: Display>(index: usize, asm: &mut Asm, lhs: Reg32, rhs: T) {
              asm.lines.push(format!("  or    {}, {}", lhs, rhs));
            }

            operation_to_asm!(i, &stack, &mut asm, (lhs, rhs), ||: Bool -> Bool, or_to_asm, or_to_asm)
          }
          Op::Jumpfalse(cond, Arg::Reference(ty_r, reference)) => match cond {
            Arg::Reference(ty_l, cond) => {
              let register = asm.temporary_register.get(cond).unwrap();

              asm.lines.push(format!("  cmp    {}, 0", register.as_reg8().0));
              asm.lines.push(format!("  je     {}", asm.labels.get(reference).unwrap()));
            },
            Arg::Literal(Literal::Bool(true)) => (),
            Arg::Literal(Literal::Bool(false)) => {
              asm.lines.push(format!("  jmp    {}", asm.labels.get(reference).unwrap()));
            },
            _ => unimplemented!(),
          },
          Op::Jump(Arg::Reference(ty, reference)) => {
            asm.lines.push(format!("  jmp    {}", asm.labels.get(reference).unwrap()));
          },
          op => unimplemented!("{:?}", op),
        }
      }

      asm.lines.push(format!(".AWAY_{}:", name));

      if is_main {
        asm.lines.push("  leave".to_string());
      } else {
        asm.lines.push("  pop    ebp".to_string());
      }

      asm.lines.push("  ret".to_string());

      asm.lines.insert(stack_size_index, format!("  sub    esp, {}", ((stack.size + 15) / 16) * 16));
    }

    for (float, label) in asm.floats.iter() {
      asm.lines.push(format!("{}:", label));
      asm.lines.push(format!("  .long {}", float.long1));
      asm.lines.push(format!("  .long {}", float.long2));
    }

    asm
  }
}
