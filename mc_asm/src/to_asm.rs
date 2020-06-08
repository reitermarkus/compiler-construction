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
  used_registers: BTreeMap<Reg32, usize>,
}

impl Default for Stack {
  fn default() -> Stack {
    Stack {
      temporary_register: Default::default(),
      temporaries: VecDeque::from(vec![Reg32::EAX, Reg32::EDX, Reg32::ECX, Reg32::EDI, Reg32::ESI]),
      lookup_table: Default::default(),
      parameters: Default::default(),
      parameters_size: 8,
      stack_size_index: Default::default(),
      variables: Default::default(),
      variables_size: Default::default(),
      used_registers: Default::default(),
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
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

fn push_storage_temporary(storage: Storage, temporaries: &mut VecDeque<Reg32>) {
  if let Storage::Register(_, reg) = storage {
    push_temporary(reg, temporaries);
  }
}

fn push_temporary(temporary: Reg32, temporaries: &mut VecDeque<Reg32>) {
  if temporary == Reg32::EAX || temporary == Reg32::EDX || temporary == Reg32::ECX || temporary == Reg32::EBX {
    temporaries.push_front(temporary);
  } else {
    temporaries.push_back(temporary);
  }
}

macro_rules! stack_hygiene {
  ($i:expr, $stack:expr, $closure:expr) => {
    let temp_var = $stack.temporaries.pop_front().unwrap();
    $closure(temp_var);
    $stack.temporary_register.insert($i, temp_var);
    $stack.used_registers.insert(temp_var, $i);
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

#[derive(Debug, Clone)]
pub struct Pointer {
  storage_type: StorageType,
  offset: usize,
  index_offset: Option<Reg32>,
  parameter: bool,
}

impl fmt::Display for Pointer {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{} [ebp", self.storage_type)?;

    if self.offset != 0 {
      if self.parameter { "+" } else { "-" }.fmt(f)?;

      write!(f, "{}", self.offset)?;
    }
    if let Some(index_offset) = self.index_offset {
      write!(f, "+{}*{}", index_offset, self.storage_type.size())?;
    }

    write!(f, "]")
  }
}

#[derive(Debug, Clone)]
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
      Self::Register(storage_type, reg) => {
        if f.alternate() {
          write!(f, "{}", storage_type.map_register(reg))
        } else {
          write!(f, "{}", reg)
        }
      }
      Self::Literal(_, string) => write!(f, "{}", string),
      Self::Label(ty, label, flat) => {
        if *flat {
          write!(f, "OFFSET FLAT:{}", label)
        } else {
          write!(f, "{} {}", ty, label)
        }
      }
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
          pointer @ Storage::Pointer(..) => {
            asm.lines.push(format!("  mov    {}, {}", reg, pointer));
            Some(reg)
          }
          u => unreachable!("{:?}", u),
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
        let (ty, _, offset, parameter) = stack.lookup(*reference);
        Storage::Pointer(Pointer { storage_type: StorageType::Dword, offset, index_offset: None, parameter })
      } else {
        let temp = *stack.temporary_register.get(reference).unwrap();
        Storage::Register(ty.into(), temp)
      }
    }
    Arg::Literal(literal) => match literal {
      Literal::Int(integer) => Storage::Literal(StorageType::Dword, integer.to_string()),
      Literal::Bool(boolean) => Storage::Literal(StorageType::Byte, if *boolean { 1 } else { 0 }.to_string()),
      Literal::Float(float) => add_float(asm, *float),
      Literal::String(string) => add_string(asm, string),
    },
    Arg::FunctionCall(ty, identifier, args) => {
      if let Some(eax_index) = stack.used_registers.remove(&Reg32::EAX) {
        asm.lines.push(format!("  mov    ebx, eax"));
        stack.temporary_register.insert(eax_index, Reg32::EBX);
        stack.used_registers.insert(Reg32::EBX, eax_index);
      }

      let mut args_size = 0;

      let alignment_index = asm.lines.len();

      for arg in args.iter().rev() {
        let argument = calc_index_offset(stack, asm, reg, arg);

        args_size += argument.storage_type().size();

        if arg.ty() == Some(Ty::Float) {
          asm.lines.push(format!("  fld    {}", argument));
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
        asm.lines.insert(alignment_index, format!("  sub    esp, {}   # alignment", alignment));
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

fn add_float(asm: &mut Asm, float: f64) -> Storage {
  let float = OrderedFloat::from(float);

  let label = if let Some(label) = asm.floats.get(&float) {
    label
  } else {
    let float_number = asm.floats.len();
    asm.floats.insert(float, format!(".LC{}", float_number));
    asm.floats.get(&float).unwrap()
  };

  Storage::Label(StorageType::Dword, label.to_owned(), false)
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

      let mut push_ebx = false;

      for (i, statement) in self.statements.iter().enumerate().skip(range.start).take(range.end - range.start) {
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
          Op::Assign(value, variable) => {
            stack_hygiene!(&mut stack, |temp: Reg32| {
              let var = calc_index_offset(&mut stack, &mut asm, temp, variable);
              let val = calc_index_offset(&mut stack, &mut asm, temp, value);

              match variable.ty() {
                Some(Ty::Float) => {
                  asm.lines.push(format!("  fld    {}", val));
                  asm.lines.push(format!("  fstp   {}", var));
                }
                _ => match val {
                  Storage::Pointer(..) => {
                    stack_hygiene!(&mut stack, |temp: Reg32| {
                      asm.lines.push(format!("  mov    {}, {}", temp, val));
                      asm.lines.push(format!("  mov    {}, {:#}", var, temp));
                    });
                  }
                  _ => {
                    asm.lines.push(format!("  mov    {}, {:#}", var, val));
                  }
                },
              }

              push_storage_temporary(var, &mut stack.temporaries);
              push_storage_temporary(val, &mut stack.temporaries);
            });
          }
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
                    asm.lines.push(format!("  movzx  {}, {:#}", Reg32::EAX, result));
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
          Op::UnaryMinus(arg) => match arg.ty() {
            Some(Ty::Int) => {
              stack_hygiene!(i, &mut stack, |temp: Reg32| {
                let register = calc_index_offset(&mut stack, &mut asm, temp, arg);
                asm.lines.push(format!("  mov    {}, {}", temp, register));
                asm.lines.push(format!("  neg    {}", temp));
              });
            }
            Some(Ty::Float) => {
              stack_hygiene!(i, &mut stack, |temp: Reg32| {
                let register = calc_index_offset(&mut stack, &mut asm, temp, arg);
                let temp_float = stack.push(i, Ty::Float, 1, false);
                asm.lines.push(format!("  fld    {}", register));
                asm.lines.push("  fchs".to_string());
                asm.lines.push(format!("  fstp   {}", temp_float));
              });
            }
            _ => unreachable!(),
          },
          Op::Plus(lhs, rhs) => match lhs.ty() {
            Some(Ty::Int) => {
              stack_hygiene!(i, &mut stack, |temp_l: Reg32| {
                stack_hygiene!(&mut stack, |temp_r: Reg32| {
                  let lhs = calc_index_offset(&mut stack, &mut asm, temp_l, lhs);
                  asm.lines.push(format!("  mov    {}, {}", temp_l, lhs));
                  push_storage_temporary(lhs, &mut stack.temporaries);

                  let rhs = calc_index_offset(&mut stack, &mut asm, temp_r, rhs);
                  asm.lines.push(format!("  add    {}, {}", temp_l, rhs));
                  push_storage_temporary(rhs, &mut stack.temporaries);
                });
              });
            }
            Some(Ty::Float) => {
              stack_hygiene!(&mut stack, |temp: Reg32| {
                let lhs = calc_index_offset(&mut stack, &mut asm, temp, lhs);
                asm.lines.push(format!("  fld    {}", lhs));
                push_storage_temporary(lhs, &mut stack.temporaries);

                let rhs = calc_index_offset(&mut stack, &mut asm, temp, rhs);
                asm.lines.push(format!("  fadd   {}", rhs));

                let temp_float = stack.push(i, Ty::Float, 1, false);
                asm.lines.push(format!("  fstp   {}", temp_float));

                push_storage_temporary(rhs, &mut stack.temporaries);
              });
            }
            _ => unimplemented!(),
          },
          Op::Minus(lhs, rhs) => match lhs.ty() {
            Some(Ty::Int) => {
              stack_hygiene!(i, &mut stack, |temp_l: Reg32| {
                stack_hygiene!(&mut stack, |temp_r: Reg32| {
                  let lhs = calc_index_offset(&mut stack, &mut asm, temp_l, lhs);
                  asm.lines.push(format!("  mov    {}, {}", temp_l, lhs));
                  push_storage_temporary(lhs, &mut stack.temporaries);

                  let rhs = calc_index_offset(&mut stack, &mut asm, temp_r, rhs);
                  asm.lines.push(format!("  sub    {}, {}", temp_l, rhs));
                  push_storage_temporary(rhs, &mut stack.temporaries);
                });
              });
            }
            Some(Ty::Float) => {
              stack_hygiene!(&mut stack, |temp: Reg32| {
                let lhs = calc_index_offset(&mut stack, &mut asm, temp, lhs);
                asm.lines.push(format!("  fld    {}", lhs));
                push_storage_temporary(lhs, &mut stack.temporaries);

                let rhs = calc_index_offset(&mut stack, &mut asm, temp, rhs);
                asm.lines.push(format!("  fsub   {}", rhs));

                let temp_float = stack.push(i, Ty::Float, 1, false);
                asm.lines.push(format!("  fstp   {}", temp_float));

                push_storage_temporary(rhs, &mut stack.temporaries);
              });
            }
            _ => unimplemented!(),
          },
          Op::Times(lhs, rhs) => match lhs.ty() {
            Some(Ty::Int) => {
              stack_hygiene!(i, &mut stack, |temp_l: Reg32| {
                stack_hygiene!(&mut stack, |temp_r: Reg32| {
                  let lhs = calc_index_offset(&mut stack, &mut asm, temp_l, lhs);
                  asm.lines.push(format!("  mov    {}, {}", temp_l, lhs));
                  push_storage_temporary(lhs, &mut stack.temporaries);

                  let rhs = calc_index_offset(&mut stack, &mut asm, temp_r, rhs);
                  asm.lines.push(format!("  imul   {}, {}", temp_l, rhs));
                  push_storage_temporary(rhs, &mut stack.temporaries);
                });
              });
            }
            Some(Ty::Float) => {
              stack_hygiene!(&mut stack, |temp: Reg32| {
                let lhs = calc_index_offset(&mut stack, &mut asm, temp, lhs);
                asm.lines.push(format!("  fld    {}", lhs));
                push_storage_temporary(lhs, &mut stack.temporaries);

                let rhs = calc_index_offset(&mut stack, &mut asm, temp, rhs);
                asm.lines.push(format!("  fmul   {}", rhs));

                let temp_float = stack.push(i, Ty::Float, 1, false);
                asm.lines.push(format!("  fstp   {}", temp_float));

                push_storage_temporary(rhs, &mut stack.temporaries);
              });
            }
            _ => unimplemented!(),
          },
          Op::Divide(lhs, rhs) => match lhs.ty() {
            Some(Ty::Int) => {
              let eax_free = stack.temporaries.contains(&Reg32::EAX);
              let edx_free = stack.temporaries.contains(&Reg32::EDX);

              let find_non_eax_edx = |temporaries: &mut VecDeque<Reg32>| {
                let position = temporaries.iter().position(|&reg| reg != Reg32::EAX && reg != Reg32::EDX).unwrap();
                temporaries.remove(position).unwrap()
              };

              stack_hygiene!(i, &mut stack, |temp_l: Reg32| {
                stack_hygiene!(&mut stack, |temp_r: Reg32| {
                  let eax_backup = if !eax_free {
                    let eax_backup = find_non_eax_edx(&mut stack.temporaries);
                    asm.lines.push(format!("  mov    {}, eax", eax_backup));
                    Some(eax_backup)
                  } else {
                    None
                  };

                  let edx_backup = if !edx_free {
                    let edx_backup = find_non_eax_edx(&mut stack.temporaries);
                    asm.lines.push(format!("  mov    {}, edx", edx_backup));
                    Some(edx_backup)
                  } else {
                    None
                  };

                  let lhs = calc_index_offset(&mut stack, &mut asm, temp_l, lhs);
                  let rhs = calc_index_offset(&mut stack, &mut asm, temp_r, rhs);

                  let temp_r_backup = match temp_r {
                    Reg32::EAX | Reg32::EDX => Some(find_non_eax_edx(&mut stack.temporaries)),
                    _ => None,
                  };

                  let rhs_backup = match rhs {
                    Storage::Register(_, Reg32::EAX) | Storage::Register(_, Reg32::EDX) | Storage::Literal(..) => {
                      let temp = temp_r_backup.unwrap_or(temp_r);
                      asm.lines.push(format!("  mov    {}, {}", temp, rhs));
                      Some(temp)
                    }
                    _ => None,
                  };

                  if !matches!(lhs, Storage::Register(_, Reg32::EAX)) {
                    asm.lines.push(format!("  mov    eax, {}", lhs));
                  }

                  asm.lines.push(format!("  cdq"));

                  if let Some(rhs_backup) = rhs_backup {
                    asm.lines.push(format!("  idiv   {}", rhs_backup));
                  } else {
                    asm.lines.push(format!("  idiv   {}", rhs));
                  }

                  if temp_l != Reg32::EAX {
                    asm.lines.push(format!("  mov    {}, eax", temp_l));
                  }

                  if let Some(temp_r_backup) = temp_r_backup {
                    push_temporary(temp_r_backup, &mut stack.temporaries);
                  }

                  if let Some(eax_backup) = eax_backup {
                    asm.lines.push(format!("  mov    eax, {}", eax_backup));
                    push_temporary(eax_backup, &mut stack.temporaries);
                  }

                  if let Some(edx_backup) = edx_backup {
                    asm.lines.push(format!("  mov    edx, {}", edx_backup));
                    push_temporary(edx_backup, &mut stack.temporaries);
                  }

                  push_storage_temporary(lhs, &mut stack.temporaries);
                  push_storage_temporary(rhs, &mut stack.temporaries);
                });
              });
            }
            Some(Ty::Float) => {
              stack_hygiene!(&mut stack, |temp: Reg32| {
                let lhs = calc_index_offset(&mut stack, &mut asm, temp, lhs);
                asm.lines.push(format!("  fld    {}", lhs));
                push_storage_temporary(lhs, &mut stack.temporaries);

                let rhs = calc_index_offset(&mut stack, &mut asm, temp, rhs);
                asm.lines.push(format!("  fdiv   {}", rhs));

                let temp_float = stack.push(i, Ty::Float, 1, false);
                asm.lines.push(format!("  fstp   {}", temp_float));

                push_storage_temporary(rhs, &mut stack.temporaries);
              });
            }
            _ => unimplemented!(),
          },
          op @ Op::Eq(..)
          | op @ Op::Neq(..)
          | op @ Op::Lte(..)
          | op @ Op::Gt(..)
          | op @ Op::Gte(..)
          | op @ Op::Lt(..) => {
            let (lhs, rhs, set_instruction) = match op {
              Op::Lte(lhs, rhs) => (lhs, rhs, ConditionalSet::SETLE),
              Op::Lt(lhs, rhs) => (lhs, rhs, ConditionalSet::SETL),
              Op::Gte(lhs, rhs) => (lhs, rhs, ConditionalSet::SETGE),
              Op::Gt(lhs, rhs) => (lhs, rhs, ConditionalSet::SETG),
              Op::Eq(lhs, rhs) => (lhs, rhs, ConditionalSet::SETE),
              Op::Neq(lhs, rhs) => (lhs, rhs, ConditionalSet::SETNE),
              _ => unreachable!(),
            };

            match lhs.ty() {
              Some(Ty::Int) => {
                stack_hygiene!(i, &mut stack, |temp_l: Reg32| {
                  stack_hygiene!(&mut stack, |temp_r: Reg32| {
                    let lhs = calc_index_offset(&mut stack, &mut asm, temp_l, lhs);
                    asm.lines.push(format!("  mov    {}, {} # cmp", temp_l, lhs));

                    let rhs = calc_index_offset(&mut stack, &mut asm, temp_r, rhs);
                    asm.lines.push(format!("  cmp    {}, {}", temp_l, rhs));

                    push_storage_temporary(lhs, &mut stack.temporaries);
                    push_storage_temporary(rhs, &mut stack.temporaries);

                    asm.lines.push(format!("  {}   {}", set_instruction, temp_l.as_reg8().0));
                  });
                });
              }
              _ => unimplemented!(),
            }
          }
          op @ Op::Land(..) | op @ Op::Lor(..) => {
            let (lhs, rhs, set_instruction) = match op {
              Op::Land(lhs, rhs) => (lhs, rhs, "and"),
              Op::Lor(lhs, rhs) => (lhs, rhs, "or "),
              _ => unreachable!(),
            };

            match lhs.ty() {
              Some(Ty::Bool) => {
                stack_hygiene!(i, &mut stack, |temp: Reg32| {
                  let mut lhs = calc_index_offset(&mut stack, &mut asm, temp, lhs);

                  let lhs_reg = if let Storage::Register(ty, reg) = lhs {
                    stack.temporary_register.insert(i, reg);
                    stack.used_registers.insert(reg, i);
                    Some((ty, reg))
                  } else {
                    None
                  };

                  let rhs = calc_index_offset(&mut stack, &mut asm, temp, rhs);

                  if let Some((ty, lhs_reg)) = lhs_reg {
                    if let Some(lhs_reg) = stack.temporary_register.get(&i) {
                      if lhs_reg == &Reg32::EBX {
                        push_ebx = true;
                      }

                      lhs = Storage::Register(ty, *lhs_reg);
                    }

                    stack.used_registers.remove(&lhs_reg);
                  }

                  asm.lines.push(format!("  {}    {:#}, {:#}", set_instruction, lhs, rhs));

                  asm.lines.push(format!("  movzx  {:#}, {:#} # ebx", temp, lhs));

                  push_storage_temporary(lhs, &mut stack.temporaries);
                  push_storage_temporary(rhs, &mut stack.temporaries);
                });
              }
              _ => unreachable!(),
            }
          }
          Op::Jumpfalse(cond, Arg::Reference(ty_r, reference)) => match cond {
            Arg::Literal(Literal::Bool(true)) => (),
            Arg::Literal(Literal::Bool(false)) => {
              asm.lines.push(format!("  jmp    {}", asm.labels.get(reference).unwrap()));
            }
            arg => {
              stack_hygiene!(&mut stack, |temp: Reg32| {
                let result_register = calc_index_offset(&mut stack, &mut asm, temp, arg);

                asm.lines.push(format!("  cmp    {:#}, 0", result_register));
                asm.lines.push(format!("  je     {}", asm.labels.get(reference).unwrap()));

                push_storage_temporary(result_register, &mut stack.temporaries);
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

      if push_ebx {
        asm.lines.insert(stack.stack_size_index, format!("  push   ebx"));
        asm.lines.push("  pop    ebx".to_string());
      }

      if stack.variables.is_empty() {
        asm.lines.push("  pop    ebp".to_string());
      } else {
        asm.lines.insert(
          stack.stack_size_index,
          format!("  sub    esp, {}   # stack variables size", ((stack.variables_size + 15) / 16) * 16),
        );
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
