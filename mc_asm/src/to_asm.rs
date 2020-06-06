use ordered_float::OrderedFloat;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::fmt;
use std::fmt::Display;

use mc_ir::{Arg, IntermediateRepresentation, Op};
use mc_parser::ast::*;

#[derive(Debug)]
pub struct Asm {
  lines: Vec<String>,
  labels: BTreeMap<usize, String>,
  strings: BTreeMap<String, String>,
  floats: BTreeMap<OrderedFloat<f64>, String>,
  builtin_functions: HashSet<Identifier>,
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

#[derive(Debug)]
pub struct Stack {
  temporary_register: BTreeMap<usize, Reg32>,
  temporaries: VecDeque<Reg32>,
  lookup_table: HashMap<usize, (usize, bool)>,
  parameters: Vec<(Ty, usize, usize)>,
  parameters_size: usize,
  stack_size_index: usize,
  variables: Vec<(Ty, usize, usize)>,
  variables_size: usize,
}

impl Default for Stack {
  fn default() -> Stack {
    Stack {
      temporary_register: Default::default(),
      temporaries: VecDeque::from(vec![Reg32::EAX, Reg32::EDX, Reg32::ECX, Reg32::EBX, Reg32::EDI, Reg32::ESI]),
      lookup_table: Default::default(),
      parameters: Default::default(),
      parameters_size: 8,
      stack_size_index: Default::default(),
      variables: Default::default(),
      variables_size: Default::default(),
    }
  }
}

impl Stack {
  pub fn lookup(&self, index: usize) -> (Ty, usize, usize, bool) {
    let &(i, parameter) = self.lookup_table.get(&index).unwrap();

    let (ty, count, offset) = if parameter { self.parameters[i] } else { self.variables[i] };

    (ty, count, offset, parameter)
  }

  pub fn push(&mut self, index: usize, ty: Ty, count: usize, parameter: bool) -> Pointer {
    if parameter {
      let offset = self.parameters_size;
      self.parameters.push((ty, count, self.parameters_size));
      self.lookup_table.insert(index, (self.parameters.len() - 1, true));
      self.parameters_size += count * ty.size();
      Pointer { storage_type: StorageType::Dword, offset, index_offset: None, parameter }
    } else {
      self.variables_size += count * ty.size();
      self.variables.push((ty, count, self.variables_size));
      self.lookup_table.insert(index, (self.variables.len() - 1, false));
      Pointer { storage_type: (&ty).into(), offset: self.variables_size, index_offset: None, parameter }
    }
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
    }
    .fmt(f)
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
    }
    .fmt(f)
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
    }
    .fmt(f)
  }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ConditionalJump {
  JL,
  JLE,
  JG,
  JGE,
  JE,
  JNE,
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
  SETNE,
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

fn push_temporary(temporary: Reg32, temporaries: &mut VecDeque<Reg32>) {
  if temporary == Reg32::EAX || temporary == Reg32::EDX || temporary == Reg32::ECX {
    temporaries.push_front(temporary);
  } else {
    temporaries.push_back(temporary);
  }
}

macro_rules! stack_hygiene {
  ($i:expr, $stack:expr, $closure:expr) => {
    let temp_var = $stack.temporaries.pop_front().unwrap();
    $stack.temporary_register.insert($i, temp_var);
    $closure(temp_var)
  };
  ($stack:expr, $closure:expr) => {
    let temp_var = $stack.temporaries.pop_front().unwrap();
    $closure(temp_var);
    push_temporary(temp_var, &mut $stack.temporaries);
  };
  ($ref_l:expr, $i:expr, $stack:expr, $closure:expr) => {
    let temp_l = *$stack.temporary_register.get($ref_l).unwrap();

    $closure(temp_l);

    $stack.temporary_register.remove($ref_l);

    if !$stack.temporary_register.contains_key(&$i) {
      $stack.temporary_register.insert($i, temp_l);
    }
  };
  ($ref_l:expr, $ref_r:expr, $i:expr, $stack:expr, $closure:expr) => {
    let temp_l = *$stack.temporary_register.get($ref_l).unwrap();
    let temp_r = *$stack.temporary_register.get($ref_r).unwrap();

    $closure(temp_l, temp_r);

    push_temporary(temp_r, &mut $stack.temporaries);

    $stack.temporary_register.remove($ref_r);
    $stack.temporary_register.remove($ref_l);

    if !$stack.temporary_register.contains_key(&$i) {
      $stack.temporary_register.insert($i, temp_l);
    }
  };
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
        stack_hygiene!(ref_l, $index, $stack, |temp_l: Reg32| {
          $reflit_closure($index, $stack, $asm, temp_l, rhs)
        });
      }
      (Arg::Literal(Literal::$from(lhs)), Arg::Reference(Some(ty), ref_r)) if ty == &Ty::$from => {
        stack_hygiene!(ref_r, $index, $stack, |temp_r: Reg32| {
          $litref_closure($index, $stack, $asm, temp_r, lhs)
        });
      }
      (Arg::Reference(Some(ty_l), ref_l), Arg::Reference(Some(ty_r), ref_r)) if ty_l == &Ty::$from && ty_r == &Ty::$from => {
        stack_hygiene!(ref_l, ref_r, $index, $stack, |temp_l: Reg32, temp_r: Reg32| {
          $reference_closure($index, $stack, $asm, temp_l, temp_r)
        });
      },
      (lhs, rhs) => unreachable!("LHS = {:?}, RHS = {:?}", lhs, rhs)
    }
  };
}

macro_rules! comparison_to_asm {
  ($op:expr) => {
    fn comparison_to_asm<T: Display>(_index: usize, mut _stack: &mut Stack, asm: &mut Asm, lhs: Reg32, rhs: T) {
      asm.lines.push(format!("  cmp    {}, {}", lhs, rhs));
      asm.lines.push(format!("  {}   {}", $op, lhs.as_reg8().0));
    }
  };
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum StorageType {
  Qword,
  Dword,
  Byte,
}

impl From<&Ty> for StorageType {
  fn from(ty: &Ty) -> Self {
    match ty {
      Ty::Float => Self::Dword,
      Ty::Int => Self::Dword,
      Ty::Bool => Self::Byte,
      Ty::String => Self::Dword,
    }
  }
}

impl fmt::Display for StorageType {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Qword => "QWORD PTR",
      Self::Dword => "DWORD PTR",
      Self::Byte => "BYTE PTR",
    }
    .fmt(f)
  }
}

impl StorageType {
  fn size(&self) -> usize {
    match self {
      Self::Qword => 8,
      Self::Dword => 4,
      Self::Byte => 1,
    }
  }

  fn map_register(&self, reg: &Reg32) -> String {
    match self {
      Self::Dword => reg.to_string(),
      Self::Byte => reg.as_reg8().0.to_string(),
      _ => unreachable!(),
    }
  }
}

#[derive(Debug)]
pub struct Pointer {
  storage_type: StorageType,
  offset: usize,
  index_offset: Option<Reg32>,
  parameter: bool,
}

impl fmt::Display for Pointer {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{} [ebp", self.storage_type)?;

    if self.parameter { "+" } else { "-" }.fmt(f)?;

    write!(f, "{}", self.offset)?;

    if let Some(index_offset) = self.index_offset {
      write!(f, "+{}*{}", index_offset, self.storage_type.size())?;
    }

    write!(f, "]")
  }
}

#[derive(Debug)]
pub enum Storage {
  Pointer(Pointer),
  Register(StorageType, Reg32),
  Literal(StorageType, String),
  Label(StorageType, String, bool),
}

impl fmt::Display for Storage {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Pointer(pointer) => write!(f, "{}", pointer),
      Self::Register(storage_type, reg) => write!(f, "{}", storage_type.map_register(reg)),
      Self::Literal(_, string) => write!(f, "{}", string),
      Self::Label(ty, label, flat) => {
        if *flat {
          write!(f, "OFFSET FLAT:{}", label)
        } else {
          write!(f, "{} {}", ty, label)
        }

      },
    }
  }
}

impl Storage {
  fn storage_type(&self) -> StorageType {
    match *self {
      Self::Pointer(Pointer { storage_type, .. }) => storage_type,
      Self::Register(storage_type, _) => storage_type,
      Self::Literal(storage_type, _) => storage_type,
      Self::Label(storage_type, ..) => storage_type,
    }
  }

  fn map_register(&self, reg: &Reg32) -> String {
    self.storage_type().map_register(reg)
  }
}

fn calc_index_offset(stack: &mut Stack, asm: &mut Asm, reg: Reg32, arg: &Arg<'_>) -> Storage {
  match arg {
    Arg::Variable(_, decl_index, index_offset) => {
      let (ty, _, mut offset, parameter) = stack.lookup(*decl_index);

      let index_reg = match index_offset.as_ref() {
        Arg::Literal(Literal::Int(index_offset)) => {
          if parameter {
            offset += *index_offset as usize * ty.size();
          } else {
            offset -= *index_offset as usize * ty.size();
          }

          None
        }
        arg => match calc_index_offset(stack, asm, reg, arg) {
          Storage::Register(_, temp) => Some(temp),
          _ => unreachable!(),
        },
      };

      Storage::Pointer(match ty {
        Ty::Int => Pointer { storage_type: StorageType::Dword, offset, index_offset: index_reg, parameter },
        Ty::Bool => Pointer { storage_type: StorageType::Byte, offset, index_offset: index_reg, parameter },
        Ty::Float => Pointer { storage_type: StorageType::Dword, offset, index_offset: index_reg, parameter },
        Ty::String => Pointer { storage_type: StorageType::Dword, offset, index_offset: index_reg, parameter },
      })
    }
    Arg::Reference(Some(ty), reference) => {
      if *ty == Ty::Float {
        Storage::Pointer(Pointer { storage_type: StorageType::Dword, offset: 0, index_offset: None, parameter: false })
      } else {
        let temp = *stack.temporary_register.get(reference).unwrap();
        push_temporary(temp, &mut stack.temporaries);
        Storage::Register(ty.into(), temp)
      }
    }
    Arg::Literal(literal) => match literal {
      Literal::Int(integer) => Storage::Literal(StorageType::Dword, integer.to_string()),
      Literal::Bool(boolean) => Storage::Literal(StorageType::Byte, if *boolean { 1 } else { 0 }.to_string()),
      Literal::Float(float) => {
        let label = add_float(asm, *float);
        Storage::Label(StorageType::Dword, label, false)
      }
      Literal::String(string) => {
        add_string(asm, string)
      }
    },
    Arg::FunctionCall(ty, identifier, args) => {
      let mut args_size = 0;

      let alignment_index = asm.lines.len();

      for arg in args.iter().rev() {
        let argument = calc_index_offset(stack, asm, reg, arg);

        args_size += argument.storage_type().size();

        if arg.ty() == Some(Ty::Float) {
          if matches!(arg, Arg::Reference(..)) {
            asm.lines.push("  nop".to_string());
          } else {
            asm.lines.push(format!("  fld   {}", argument));
          }
        } else {
          match argument {
            Storage::Register(_, reg) => {
              asm.lines.push(format!("  push   {}", reg));
            }
            argument => {
              asm.lines.push(format!("  push   {}", argument));
            }
          }
        }
      }

      if *identifier == &Identifier::from("print_int") {
        args_size += StorageType::Dword.size();
        let format_string = add_string(asm, "%d");
        asm.lines.push(format!("  push   {}", format_string));
        asm.lines.push("  call   printf".to_string());
      } else if *identifier == &Identifier::from("print_nl") {
        args_size += StorageType::Dword.size();
        asm.lines.push("  push   10".to_string());
        asm.lines.push("  call   putchar".to_string());
      } else if *identifier == &Identifier::from("print_float") {
        asm.lines.push("  lea    esp, [esp-8]".to_string());
        asm.lines.push("  fstp   QWORD PTR [esp]".to_string());

        let format_string = add_string(asm, "%f");
        asm.lines.push(format!("  push   {}", format_string));
        args_size += 8;

        asm.lines.push("  call   printf".to_string());
      } else if *identifier == &Identifier::from("print") {
        asm.lines.push("  call   printf".to_string());
      } else if *identifier == &Identifier::from("read_int") || *identifier == &Identifier::from("read_float") {
        asm.builtin_functions.insert((**identifier).clone());
        asm.lines.push(format!("  call   {}", identifier));
      } else {
        asm.lines.push(format!("  call   {}", identifier));
      }

      let alignment = (16 - args_size % 16) % 16;

      if alignment > 0 {
        asm.lines.insert(alignment_index, format!("  sub    esp, {}", alignment));
      }

      args_size = (args_size + 15) / 16 * 16;

      if args_size > 0 {
        asm.lines.push(format!("  add    esp, {}", args_size));
      }

      if let Some(ty) = ty {
        Storage::Register(ty.into(), Reg32::EAX)
      } else {
        Storage::Register(StorageType::Dword, Reg32::EAX)
      }
    }
    _ => unimplemented!("{:?}", arg),
  }
}

fn add_float(asm: &mut Asm, float: f64) -> String {
  let float = OrderedFloat::from(float);

  if let Some(label) = asm.floats.get(&float) {
    label
  } else {
    let float_number = asm.floats.len();
    asm.floats.insert(float, format!(".LC{}", float_number));
    asm.floats.get(&float).unwrap()
  }
  .to_owned()
}

fn add_string(asm: &mut Asm, s: &str) -> Storage {
  let label = if let Some(label) = asm.strings.get(s) {
    label
  } else {
    let string_number = asm.strings.len();
    asm.strings.insert(s.to_owned(), format!(".LS{}", string_number));
    asm.strings.get(s).unwrap()
  };

  Storage::Label(StorageType::Dword, label.to_owned(), true)
}

impl<'a> ToAsm for IntermediateRepresentation<'a> {
  fn to_asm(&self) -> Asm {
    let mut asm = Asm {
      lines: vec![],
      labels: Default::default(),
      strings: Default::default(),
      floats: Default::default(),
      builtin_functions: Default::default(),
    };

    asm.lines.push("  .intel_syntax noprefix".to_string());
    asm.lines.push("  .global main".to_string());

    for statement in self.statements.iter() {
      match statement {
        Op::Jumpfalse(_, Arg::Reference(_, reference)) | Op::Jump(Arg::Reference(_, reference)) => {
          let label_number = asm.labels.len();
          let label = format!(".L{}", label_number);
          asm.labels.insert(*reference, label);
        }
        _ => {}
      }
    }

    for (&name, (range, _)) in &self.functions {
      let mut stack = Stack::default();

      asm.lines.push(format!("{}:", name));

      asm.lines.push("  push   ebp".to_string());
      asm.lines.push("  mov    ebp, esp".to_string());

      stack.stack_size_index = asm.lines.len();

      for (i, statement) in self.statements.iter().enumerate().skip(range.start).take(range.end) {
        if let Some(label) = asm.labels.get(&i) {
          asm.lines.push(format!("{}:", label));
        }

        match statement {
          Op::Param(_, ty, count) => match StorageType::from(ty) {
            StorageType::Dword => {
              stack.push(i, *ty, *count, true);
            }
            StorageType::Byte => {
              stack_hygiene!(&mut stack, |temp: Reg32| {
                let arg = stack.push(i, Ty::Int, 1, true);

                let pointer = stack.push(i, *ty, *count, false);

                asm.lines.push(format!("  mov    {}, {}", temp, arg));
                asm.lines.push(format!("  mov    {}, {}", pointer, pointer.storage_type.map_register(&temp)));
              });
            }
            _ => unreachable!(),
          },
          Op::Decl(_, ty, count) => {
            stack.push(i, *ty, *count, false);
          }
          Op::Assign(arg, variable) => match variable {
            Arg::Variable(Ty::Float, ..) => match arg {
              Arg::Literal(Literal::Float(float)) => {
                stack_hygiene!(&mut stack, |temp: Reg32| {
                  let variable = calc_index_offset(&mut stack, &mut asm, temp, variable);
                  let label = add_float(&mut asm, *float);

                  match variable {
                    Storage::Pointer(pointer) => {
                      asm.lines.push(format!("  fld    {} {}", pointer.storage_type, label));
                      asm.lines.push(format!("  fstp   {}", pointer));
                    }
                    _ => unreachable!(),
                  }
                });
              }
              _ => {
                stack_hygiene!(&mut stack, |temp: Reg32| {
                  let variable = calc_index_offset(&mut stack, &mut asm, temp, variable);
                  calc_index_offset(&mut stack, &mut asm, temp, arg);
                  asm.lines.push(format!("  fstp   {}", variable));
                });
              }
            },
            variable => {
              stack_hygiene!(&mut stack, |temp: Reg32| {
                let variable = calc_index_offset(&mut stack, &mut asm, temp, variable);
                let value = calc_index_offset(&mut stack, &mut asm, temp, arg);
                asm.lines.push(format!("  mov    {}, {}", variable, value));
              });
            }
          },
          Op::Load(variable) => match variable {
            Arg::Variable(Ty::Float, ..) => {
              stack_hygiene!(i, &mut stack, |temp: Reg32| {
                let var = calc_index_offset(&mut stack, &mut asm, temp, variable);
                asm.lines.push(format!("  fld    {}", var));
              });
            }
            variable => {
              stack_hygiene!(i, &mut stack, |temp: Reg32| {
                let var = calc_index_offset(&mut stack, &mut asm, temp, variable);
                let reg = var.map_register(&temp);
                asm.lines.push(format!("  mov    {}, {}", reg, var));
              });
            }
          },
          Op::Return(arg) => {
            if let Some(arg) = arg {
              stack_hygiene!(&mut stack, |temp: Reg32| {
                let result = calc_index_offset(&mut stack, &mut asm, temp, arg);

                if !matches!(result, Storage::Register(_, Reg32::EAX)) {
                  if result.storage_type() == StorageType::Byte && !matches!(result, Storage::Literal(..)) {
                    asm.lines.push(format!("  movzx  {}, {}", Reg32::EAX, result));
                  } else if arg.ty() == Some(Ty::Float) {
                    asm.lines.push(format!("  fld    {}", result));
                  } else {
                    asm.lines.push(format!("  mov    {}, {}", Reg32::EAX, result));
                  };
                } else {
                  asm.lines.push("  nop".to_string());
                }
              });
            }

            asm.lines.push(format!("  jmp    .AWAY_{}", name));
          }
          Op::UnaryMinus(arg) => {
            stack_hygiene!(&mut stack, |temp: Reg32| {
              let register = calc_index_offset(&mut stack, &mut asm, temp, arg);

              dbg!(&register);

              match (arg.ty(), register) {
                (Some(Ty::Int), Storage::Register(_, reg)) => {
                  asm.lines.push(format!("  neg    {}", reg));
                  assert_eq!(reg, stack.temporaries.pop_front().unwrap());
                  stack.temporary_register.insert(i, reg);
                }
                (Some(Ty::Float), _) => {
                  asm.lines.push("  fchs".to_string());
                }
                _ => unreachable!(),
              }
            });
          }
          Op::Plus(lhs, rhs) => match lhs.ty() {
            Some(Ty::Int) => {
              fn add_reflit_to_asm<T: Display>(index: usize, stack: &mut Stack, asm: &mut Asm, lhs: Reg32, rhs: T) {
                asm.lines.push(format!("  add    {}, {}", lhs, rhs));
              }

              fn add_reference_to_asm<T: Display>(index: usize, stack: &mut Stack, asm: &mut Asm, lhs: Reg32, rhs: T) {
                asm.lines.push(format!("  add    {}, {}", lhs, rhs));
              }

              operation_to_asm!(i, &mut stack, &mut asm, (lhs, rhs), +: Int -> Int, add_reflit_to_asm, add_reference_to_asm);
            }
            Some(Ty::Float) => match (lhs, rhs) {
              (Arg::Literal(Literal::Float(lhs)), Arg::Literal(Literal::Float(rhs))) => {
                let pointer = add_float(&mut asm, lhs + rhs);
                asm.lines.push(format!("  fld    DWORD PTR {}", pointer));
              }
              (Arg::Reference(Some(ty), _), Arg::Literal(Literal::Float(rhs)))
              | (Arg::Literal(Literal::Float(rhs)), Arg::Reference(Some(ty), _))
                if ty == &Ty::Float =>
              {
                let pointer = add_float(&mut asm, *rhs);
                asm.lines.push(format!("  fld    DWORD PTR {}", pointer));
                asm.lines.push(format!("  faddp  st(1), st"));
              }
              (arg_l, arg_r) if arg_l.ty() == Some(Ty::Float) && arg_r.ty() == Some(Ty::Float) => {
                stack_hygiene!(&mut stack, |temp: Reg32| {
                  // TODO: Move left hand side onto stack if right hand side is a function call.
                  calc_index_offset(&mut stack, &mut asm, temp, arg_l);
                  calc_index_offset(&mut stack, &mut asm, temp, arg_r);
                  asm.lines.push(format!("  faddp  st(1), st"));
                });
              }
              (lhs, rhs) => unreachable!("LHS = {:?}, RHS = {:?}", lhs, rhs),
            },
            _ => unimplemented!(),
          },
          Op::Minus(lhs, rhs) => match lhs.ty() {
            Some(Ty::Int) => {
              fn sub_reflit_to_asm<T: Display>(index: usize, stack: &mut Stack, asm: &mut Asm, lhs: Reg32, rhs: T) {
                asm.lines.push(format!("  sub    {}, {}", lhs, rhs));
              }

              fn sub_litref_to_asm<T: Display>(index: usize, stack: &mut Stack, asm: &mut Asm, rhs: Reg32, lhs: T) {
                let temp_l = stack.temporaries.pop_front().unwrap();

                asm.lines.push(format!("  mov    {}, {}", temp_l, lhs));
                asm.lines.push(format!("  sub    {}, {}", temp_l, rhs));

                stack.temporary_register.insert(index, temp_l);
              }

              fn sub_reference_to_asm<T: Display>(index: usize, stack: &mut Stack, asm: &mut Asm, lhs: Reg32, rhs: T) {
                asm.lines.push(format!("  sub    {}, {}", lhs, rhs));
              }

              operation_to_asm!(i, &mut stack, &mut asm, (lhs, rhs), -: Int -> Int, sub_reflit_to_asm, sub_litref_to_asm, sub_reference_to_asm);
            }
            Some(Ty::Float) => match (lhs, rhs) {
              (Arg::Literal(Literal::Float(lhs)), Arg::Literal(Literal::Float(rhs))) => {
                let pointer = add_float(&mut asm, lhs - rhs);
                asm.lines.push(format!("  fld    DWORD PTR {}", pointer));
              }
              (Arg::Reference(Some(ty), _), Arg::Literal(Literal::Float(rhs))) if ty == &Ty::Float => {
                let pointer = add_float(&mut asm, *rhs);
                asm.lines.push(format!("  fld    DWORD PTR {}", pointer));
                asm.lines.push(format!("  fsubp  st(1), st"));
              }
              (Arg::Literal(Literal::Float(lhs)), Arg::Reference(Some(ty), _)) if ty == &Ty::Float => {
                let pointer = add_float(&mut asm, *lhs);
                asm.lines.push(format!("  fld    DWORD PTR {}", pointer));
                asm.lines.push(format!("  fsubp  st, st(1)"));
              }
              (arg_l, arg_r) if arg_l.ty() == Some(Ty::Float) && arg_r.ty() == Some(Ty::Float) => {
                stack_hygiene!(&mut stack, |temp: Reg32| {
                  // TODO: Move left hand side onto stack if right hand side is a function call.
                  calc_index_offset(&mut stack, &mut asm, temp, arg_l);
                  calc_index_offset(&mut stack, &mut asm, temp, arg_r);
                  asm.lines.push(format!("  fsubp  st(1), st"));
                });
              }
              (lhs, rhs) => unreachable!("LHS = {:?}, RHS = {:?}", lhs, rhs),
            },
            _ => unimplemented!(),
          },
          Op::Times(lhs, rhs) => match lhs.ty() {
            Some(Ty::Int) => {
              fn imul_reflit_to_asm<T: Display>(index: usize, stack: &mut Stack, asm: &mut Asm, lhs: Reg32, rhs: T) {
                asm.lines.push(format!("  imul   {}, {}, {}", lhs, lhs, rhs));
              }

              fn imul_reference_to_asm<T: Display>(index: usize, stack: &mut Stack, asm: &mut Asm, lhs: Reg32, rhs: T) {
                asm.lines.push(format!("  imul   {}, {}", lhs, rhs));
              }

              operation_to_asm!(i, &mut stack, &mut asm, (lhs, rhs), *: Int -> Int, imul_reflit_to_asm, imul_reference_to_asm);
            }
            _ => unimplemented!(),
          },
          Op::Divide(lhs, rhs) => match lhs.ty() {
            Some(Ty::Int) => {
              fn div_reflit_to_asm<T: Display>(index: usize, stack: &mut Stack, asm: &mut Asm, lhs: Reg32, rhs: T) {
                if lhs != Reg32::EAX {
                  asm.lines.push(format!("  mov    eax, {}", lhs));
                }

                let temp_r = stack.temporaries.pop_front().unwrap();

                asm.lines.push(format!("  mov    {}, {}", temp_r, rhs));

                asm.lines.push(format!("  cdq"));
                asm.lines.push(format!("  idiv   {}", temp_r));
                asm.lines.push(format!("  mov    {}, eax", lhs));

                push_temporary(temp_r, &mut stack.temporaries);
              }

              fn div_litref_to_asm<T: Display>(index: usize, stack: &mut Stack, asm: &mut Asm, rhs: Reg32, lhs: T) {
                let temp_l = stack.temporaries.pop_front().unwrap();

                if temp_l != Reg32::EAX {
                  asm.lines.push(format!("  mov    eax, {}", lhs));
                }

                asm.lines.push(format!("  cdq"));
                asm.lines.push(format!("  idiv   {}", rhs));

                if temp_l != Reg32::EAX {
                  asm.lines.push(format!("  mov    {}, eax", temp_l));
                }

                stack.temporary_register.insert(index, temp_l);
              }

              fn div_reference_to_asm<T: Display>(index: usize, stack: &mut Stack, asm: &mut Asm, lhs: Reg32, rhs: T) {
                if lhs != Reg32::EAX {
                  asm.lines.push(format!("  mov    eax, {}", lhs));
                }

                asm.lines.push(format!("  cdq"));
                asm.lines.push(format!("  idiv   {}", rhs));

                if lhs != Reg32::EAX {
                  asm.lines.push(format!("  mov    {}, eax", lhs));
                }
              }

              operation_to_asm!(i, &mut stack, &mut asm, (lhs, rhs), -: Int -> Int, div_reflit_to_asm, div_litref_to_asm, div_reference_to_asm);
            }
            _ => unimplemented!(),
          },
          Op::Lte(lhs, rhs) => {
            comparison_to_asm!(ConditionalSet::SETLE);

            match lhs.ty() {
              Some(Ty::Int) => {
                operation_to_asm!(i, &mut stack, &mut asm, (lhs, rhs), >: Int -> Bool, comparison_to_asm, comparison_to_asm)
              }
              _ => unimplemented!(),
            }
          }
          Op::Gt(lhs, rhs) => {
            comparison_to_asm!(ConditionalSet::SETG);

            match lhs.ty() {
              Some(Ty::Int) => {
                operation_to_asm!(i, &mut stack, &mut asm, (lhs, rhs), >: Int -> Bool, comparison_to_asm, comparison_to_asm)
              }
              _ => unimplemented!(),
            }
          }
          Op::Gte(lhs, rhs) => {
            comparison_to_asm!(ConditionalSet::SETGE);

            match lhs.ty() {
              Some(Ty::Int) => {
                operation_to_asm!(i, &mut stack, &mut asm, (lhs, rhs), <: Int -> Bool, comparison_to_asm, comparison_to_asm)
              }
              _ => unimplemented!(),
            }
          }
          Op::Lt(lhs, rhs) => {
            comparison_to_asm!(ConditionalSet::SETL);

            match lhs.ty() {
              Some(Ty::Int) => {
                operation_to_asm!(i, &mut stack, &mut asm, (lhs, rhs), <: Int -> Bool, comparison_to_asm, comparison_to_asm)
              }
              _ => unimplemented!(),
            }
          }
          Op::Eq(lhs, rhs) => {
            comparison_to_asm!(ConditionalSet::SETE);

            match lhs.ty() {
              Some(Ty::Int) => {
                operation_to_asm!(i, &mut stack, &mut asm, (lhs, rhs), ==: Int -> Bool, comparison_to_asm, comparison_to_asm)
              }
              _ => unimplemented!(),
            }
          }
          Op::Neq(lhs, rhs) => {
            comparison_to_asm!(ConditionalSet::SETNE);

            match lhs.ty() {
              Some(Ty::Int) => {
                operation_to_asm!(i, &mut stack, &mut asm, (lhs, rhs), !=: Int -> Bool, comparison_to_asm, comparison_to_asm)
              }
              _ => unimplemented!(),
            }
          }
          Op::Land(lhs, rhs) => {
            fn and_to_asm<T: Display>(index: usize, stack: &mut Stack, asm: &mut Asm, lhs: Reg32, rhs: T) {
              asm.lines.push(format!("  and    {}, {}", lhs, rhs));
            }

            operation_to_asm!(i, &mut stack, &mut asm, (lhs, rhs), &&: Bool -> Bool, and_to_asm, and_to_asm)
          }
          Op::Lor(lhs, rhs) => {
            fn or_to_asm<T: Display>(index: usize, stack: &mut Stack, asm: &mut Asm, lhs: Reg32, rhs: T) {
              asm.lines.push(format!("  or    {}, {}", lhs, rhs));
            }

            operation_to_asm!(i, &mut stack, &mut asm, (lhs, rhs), ||: Bool -> Bool, or_to_asm, or_to_asm)
          }
          Op::Jumpfalse(cond, Arg::Reference(ty_r, reference)) => match cond {
            Arg::Literal(Literal::Bool(true)) => (),
            Arg::Literal(Literal::Bool(false)) => {
              asm.lines.push(format!("  jmp    {}", asm.labels.get(reference).unwrap()));
            }
            arg => {
              stack_hygiene!(&mut stack, |temp: Reg32| {
                let result_register = calc_index_offset(&mut stack, &mut asm, temp, arg);

                asm.lines.push(format!("  cmp    {}, 0", result_register));
                asm.lines.push(format!("  je     {}", asm.labels.get(reference).unwrap()));
              });
            }
          },
          Op::Jump(Arg::Reference(_, reference)) => {
            asm.lines.push(format!("  jmp    {}", asm.labels.get(reference).unwrap()));
          }
          Op::Call(arg) => {
            stack_hygiene!(&mut stack, |temp: Reg32| {
              calc_index_offset(&mut stack, &mut asm, temp, arg);
            });
          }
          op => unimplemented!("{:?}", op),
        }
      }

      asm.lines.push(format!(".AWAY_{}:", name));

      if stack.variables.is_empty() {
        asm.lines.push("  pop    ebp".to_string());
      } else {
        asm.lines.insert(stack.stack_size_index, format!("  sub    esp, {}", ((stack.variables_size + 15) / 16) * 16));
        asm.lines.push("  leave".to_string());
      }

      asm.lines.push("  ret".to_string());
    }

    for builtin_function in asm.builtin_functions.clone().iter() {
      asm.lines.push(format!("{}:", builtin_function));

      if builtin_function == &Identifier::from("read_int") {
        asm.lines.push("  push   ebp".to_string());
        asm.lines.push("  mov    ebp, esp".to_string());
        asm.lines.push("  sub    esp, 32".to_string());
        asm.lines.push("  lea    eax, [ebp-12]".to_string());
        asm.lines.push("  push   eax".to_string());
        let format_string = add_string(&mut asm, "%d");
        asm.lines.push(format!("  push   {}", format_string));
        asm.lines.push("  call   __isoc99_scanf".to_string());
        asm.lines.push("  add    esp, 16".to_string());
        asm.lines.push("  mov    eax, DWORD PTR [ebp-12]".to_string());
        asm.lines.push("  leave".to_string());
        asm.lines.push("  ret".to_string());
      } else if builtin_function == &Identifier::from("read_float") {
        asm.lines.push("  push    ebp".to_string());
        asm.lines.push("  mov     ebp, esp".to_string());
        asm.lines.push("  sub     esp, 32".to_string());
        asm.lines.push("  lea     eax, [ebp-12]".to_string());
        asm.lines.push("  push    eax".to_string());
        let format_string = add_string(&mut asm, "%f");
        asm.lines.push(format!("  push   {}", format_string));
        asm.lines.push("  call    __isoc99_scanf".to_string());
        asm.lines.push("  add     esp, 16".to_string());
        asm.lines.push("  fld     DWORD PTR [ebp-12]".to_string());
        asm.lines.push("  leave".to_string());
        asm.lines.push("  ret".to_string());
      }
    }

    for (float, label) in asm.floats.iter() {
      asm.lines.push(format!("{}:", label));
      asm.lines.push(format!("  .float {}", float));
    }

    for (string, label) in asm.strings.iter() {
      asm.lines.push(format!("{}:", label));
      asm.lines.push(format!("  .string {:?}", string));
    }

    asm
  }
}
