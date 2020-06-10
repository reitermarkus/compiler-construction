use ordered_float::OrderedFloat;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::fmt;
use std::mem;

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
  lookup_table: HashMap<usize, (usize, bool, bool)>,
  parameters: Vec<(StorageType, usize, usize)>,
  parameters_size: usize,
  stack_size_index: usize,
  variables: Vec<(StorageType, usize, usize)>,
  variables_size: usize,
  used_registers: BTreeMap<Reg32, usize>,
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
      used_registers: Default::default(),
    }
  }
}

impl Stack {
  pub fn lookup(&self, index: usize) -> (StorageType, usize, usize, bool, bool) {
    let &(i, parameter, array) = self.lookup_table.get(&index).unwrap();

    let (ty, count, offset) = if parameter { self.parameters[i] } else { self.variables[i] };

    (ty, count, offset, parameter, array)
  }

  pub fn push(
    &mut self,
    index: usize,
    storage_type: StorageType,
    count: usize,
    parameter: bool,
    array: bool,
  ) -> Pointer {
    if parameter {
      let offset = self.parameters_size;
      self.parameters.push((storage_type, count, self.parameters_size));
      self.lookup_table.insert(index, (self.parameters.len() - 1, true, array));

      if array {
        self.parameters_size += StorageType::Dword.size();
      } else {
        self.parameters_size += count * storage_type.size();
      }

      Pointer { base: Reg32::EBP, storage_type: StorageType::Dword, offset, index_offset: None, parameter, array }
    } else {
      self.variables_size += count * storage_type.size();
      self.variables.push((storage_type, count, self.variables_size));
      self.lookup_table.insert(index, (self.variables.len() - 1, false, array));
      Pointer { base: Reg32::EBP, storage_type, offset: self.variables_size, index_offset: None, parameter, array }
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
}

#[derive(Debug)]
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

fn push_storage_temporary(storage: Storage, stack: &mut Stack) {
  if let Storage::Register(_, reg) = storage {
    push_temporary(reg, stack);
  }
}

fn push_temporary(temporary: Reg32, stack: &mut Stack) {
  stack.used_registers.remove(&temporary);

  if temporary == Reg32::EAX || temporary == Reg32::EDX || temporary == Reg32::ECX || temporary == Reg32::EBX {
    stack.temporaries.push_front(temporary);
  } else {
    stack.temporaries.push_back(temporary);
  }
}

macro_rules! stack_hygiene {
  ($i:expr, $stack:expr, $closure:expr) => {
    let temp_var = $stack.temporaries.pop_front().unwrap();
    $stack.used_registers.insert(temp_var, $i);
    $stack.temporary_register.insert($i, temp_var);
    $closure(temp_var);
  };
  ($stack:expr, $closure:expr) => {
    let temp_var = $stack.temporaries.pop_front().unwrap();
    $closure(temp_var);
    push_temporary(temp_var, $stack);
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

    push_temporary(temp_r, &mut $stack);

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
  base: Reg32,
  storage_type: StorageType,
  offset: usize,
  index_offset: Option<Offset>,
  parameter: bool,
  array: bool,
}

impl fmt::Display for Pointer {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{} [{}", self.storage_type, self.base)?;

    if self.offset != 0 {
      if self.parameter { "+" } else { "-" }.fmt(f)?;

      write!(f, "{}", self.offset)?;
    }
    if let Some(index_offset) = &self.index_offset {
      write!(f, "+{}*{}", index_offset, self.storage_type.size())?;
    }

    write!(f, "]")
  }
}

#[derive(Debug, Clone)]
pub enum Storage {
  Pointer(Pointer),
  Register(StorageType, Reg32),
  Fpu(StorageType),
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
      Self::Fpu(_) => unreachable!(),
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

#[derive(Debug, Clone)]
enum Offset {
  Register(Reg32),
  Literal(usize),
}

impl fmt::Display for Offset {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Register(reg) => reg.fmt(f),
      Self::Literal(lit) => lit.fmt(f),
    }
  }
}

impl Storage {
  fn storage_type(&self) -> StorageType {
    match *self {
      Self::Pointer(Pointer { storage_type, .. }) => storage_type,
      Self::Register(storage_type, _) => storage_type,
      Self::Fpu(storage_type) => storage_type,
      Self::Literal(storage_type, _) => storage_type,
      Self::Label(storage_type, ..) => storage_type,
    }
  }
}

fn calc_index_offset(stack: &mut Stack, asm: &mut Asm, reg: Reg32, arg: &Arg<'_>) -> Storage {
  match arg {
    Arg::Variable(_, decl_index, index_offset) => {
      let (storage_type, _, offset, parameter, array) = stack.lookup(*decl_index);

      let index_offset = match index_offset.as_ref() {
        Some(Arg::Literal(Literal::Int(index_offset))) => Some(Offset::Literal(*index_offset as usize)),
        Some(arg) => match calc_index_offset(stack, asm, reg, arg) {
          Storage::Register(_, reg) => {
            push_temporary(reg, stack);
            Some(Offset::Register(reg))
          }
          pointer @ Storage::Pointer(..) => {
            asm.lines.push(format!("  mov    {}, {} # arg", reg, pointer));
            Some(Offset::Register(reg))
          }
          u => unreachable!("{:?}", u),
        },
        None => None,
      };

      let mut pointer = Pointer { base: Reg32::EBP, storage_type, offset, index_offset, parameter, array };

      if parameter && array {
        stack_hygiene!(stack, |temp: Reg32| {
          if let Some(Offset::Register(index_reg)) = pointer.index_offset {
            asm.lines.push(format!("  lea    {}, [0+{}]", temp, index_reg));
            pointer.index_offset = Some(Offset::Register(temp))
          }

          let index_offset = pointer.index_offset.take();
          asm.lines.push(format!("  mov    {}, {}", reg, pointer));
          pointer.base = reg;
          pointer.offset = 0;
          pointer.index_offset = index_offset;
        });
      }

      Storage::Pointer(pointer)
    }
    Arg::Reference(ty, reference) => {
      if *ty == Some(Ty::Float) {
        let (_, _, offset, parameter, array) = stack.lookup(*reference);
        Storage::Pointer(Pointer {
          base: Reg32::EBP,
          storage_type: StorageType::Dword,
          offset,
          index_offset: None,
          parameter,
          array,
        })
      } else {
        let temp = *stack.temporary_register.get(reference).unwrap();
        Storage::Register(ty.as_ref().unwrap().into(), temp)
      }
    }
    Arg::Literal(literal) => match literal {
      Literal::Int(integer) => Storage::Literal(StorageType::Dword, integer.to_string()),
      Literal::Bool(boolean) => Storage::Literal(StorageType::Byte, if *boolean { 1 } else { 0 }.to_string()),
      Literal::Float(float) => add_float(asm, *float),
      Literal::String(string) => add_string(asm, string),
    },
    Arg::FunctionCall(mut ty, identifier, args) => {
      let mut args_size = 0;

      let alignment_index = asm.lines.len();

      for arg in args.iter().rev() {
        let argument = calc_index_offset(stack, asm, reg, arg);

        args_size += argument.storage_type().size();

        if arg.ty() == Some(Ty::Float) {
          load_float(asm, &argument, "push function argument");

          if identifier.as_ref() != "print_float" {
            asm.lines.push("  lea    esp, [esp-4]".to_string());
            asm.lines.push("  fstp    DWORD PTR [esp]".to_string());
          }
        } else {
          match &argument {
            Storage::Pointer(Pointer { array, ref index_offset, .. }) if *array && index_offset.is_none() => {
              stack_hygiene!(stack, |temp: Reg32| {
                asm.lines.push(format!("  lea    {}, {}", temp, argument));
                asm.lines.push(format!("  push   {} # ptr", temp));
              });
            }
            Storage::Register(_, reg) => {
              asm.lines.push(format!("  push   {} # reg", reg));
            }
            argument => {
              asm.lines.push(format!("  push   {} # arg", argument));
            }
          }

          push_storage_temporary(argument, stack);
        }
      }

      match identifier.as_ref() {
        "print_int" => {
          args_size += StorageType::Dword.size();
          let format_string = add_string(asm, "%d");
          asm.lines.push(format!("  push   {}", format_string));
          asm.lines.push("  call   printf".to_string());
        }
        "print_nl" => {
          args_size += StorageType::Dword.size();
          asm.lines.push("  push   10".to_string());
          asm.lines.push("  call   putchar".to_string());
        }
        "print_float" => {
          args_size += 4;
          asm.lines.push("  lea    esp, [esp-8]".to_string());
          asm.lines.push("  fstp   QWORD PTR [esp]".to_string());

          let format_string = add_string(asm, "%f");
          asm.lines.push(format!("  push   {}", format_string));

          asm.lines.push("  call   printf".to_string());
        }
        "print" => {
          asm.lines.push("  call   printf".to_string());
        }
        "read_int" | "read_float" => {
          asm.builtin_functions.insert((**identifier).clone());
          asm.lines.push(format!("  call   {}", identifier));

          if identifier.as_ref() == "read_float" {
            ty = Some(Ty::Float);
          }
        }
        _ => {
          asm.lines.push(format!("  call   {}", map_function_name(identifier.as_ref())));
        }
      }

      let alignment = (16 - args_size % 16) % 16;

      if alignment > 0 {
        asm.lines.insert(alignment_index, format!("  sub    esp, {}   # alignment", alignment));
      }

      args_size = (args_size + 15) / 16 * 16;

      if args_size > 0 {
        asm.lines.push(format!("  add    esp, {}", args_size));
      }

      match &ty {
        Some(ty @ Ty::Float) => Storage::Fpu(ty.into()),
        Some(ty) => Storage::Register(ty.into(), Reg32::EAX),
        _ => Storage::Register(StorageType::Dword, Reg32::EAX),
      }
    }
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

fn map_function_name(name: &str) -> String {
  if name == "main" {
    return name.to_owned();
  }

  format!("mc_{}", name)
}

fn load_float(asm: &mut Asm, storage: &Storage, comment: &str) {
  if matches!(storage, Storage::Fpu(..)) {
    asm.lines.push(format!("  nop # {}", comment));
  } else {
    asm.lines.push(format!("  fld    {} # {}", storage, comment));
  }
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
          asm.labels.entry(*reference).or_insert_with(|| format!(".L{}", label_number));
        }
        _ => {}
      }
    }

    for (&name, (range, _)) in &self.functions {
      let mut stack = Stack::default();

      asm.lines.push(format!("{}:", map_function_name(name.as_ref())));

      asm.lines.push("  push   ebp".to_string());
      asm.lines.push("  mov    ebp, esp".to_string());

      stack.stack_size_index = asm.lines.len();

      for (i, statement) in self.statements.iter().enumerate().skip(range.start).take(range.end - range.start) {
        if let Some(label) = asm.labels.get(&i) {
          asm.lines.push(format!("{}:", label));
        }

        match statement {
          Op::Param(_, ty, count) => match StorageType::from(ty) {
            storage_type @ StorageType::Byte => {
              stack_hygiene!(&mut stack, |temp: Reg32| {
                let arg = stack.push(i, StorageType::Dword, 1, true, false);

                let pointer = stack.push(i, storage_type, count.clone().unwrap_or(1), false, count.is_some());

                asm.lines.push(format!("  mov    {}, {}", temp, arg));
                asm.lines.push(format!("  mov    {}, {}", pointer, pointer.storage_type.map_register(&temp)));
              });
            }
            storage_type => {
              stack.push(i, storage_type, count.clone().unwrap_or(1), true, count.is_some());
            }
          },
          Op::Decl(_, ty, count) => {
            stack.push(i, ty.into(), count.clone().unwrap_or(1), false, count.is_some());
          }
          Op::Assign(value, variable) => {
            stack_hygiene!(&mut stack, |temp: Reg32| {
              let var = calc_index_offset(&mut stack, &mut asm, temp, variable);

              let val = calc_index_offset(&mut stack, &mut asm, temp, value);

              match variable.ty() {
                Some(Ty::Float) => {
                  load_float(&mut asm, &val, "assign FPU");
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

              push_storage_temporary(var, &mut stack);
              push_storage_temporary(val, &mut stack);
            });
          }
          Op::Return(arg) => {
            if let Some(arg) = arg {
              stack_hygiene!(&mut stack, |temp: Reg32| {
                let result = calc_index_offset(&mut stack, &mut asm, temp, arg);

                if arg.ty() == Some(Ty::Float) {
                  load_float(&mut asm, &result, "return FPU");
                } else if !matches!(result, Storage::Register(_, Reg32::EAX)) {
                  if result.storage_type() == StorageType::Byte && !matches!(result, Storage::Literal(..)) {
                    asm.lines.push(format!("  movzx  {}, {:#}", Reg32::EAX, result));
                  } else {
                    asm.lines.push(format!("  mov    {}, {}", Reg32::EAX, result));
                  };
                } else {
                  asm.lines.push("  nop".to_string());
                }

                push_storage_temporary(result, &mut stack);
              });
            }

            asm.lines.push(format!("  jmp    .AWAY_{}", name));
          }
          Op::Not(arg) => {
            stack_hygiene!(i, &mut stack, |temp: Reg32| {
              let result = calc_index_offset(&mut stack, &mut asm, temp, arg);
              asm.lines.push(format!("  movzx  {}, {:#}", temp, result));
              asm.lines.push(format!("  xor    {}, 1", temp))
            });
          }
          Op::UnaryMinus(arg) => match &arg.ty() {
            Some(Ty::Int) => {
              stack_hygiene!(i, &mut stack, |temp: Reg32| {
                let register = calc_index_offset(&mut stack, &mut asm, temp, arg);
                asm.lines.push(format!("  mov    {}, {}", temp, register));
                asm.lines.push(format!("  neg    {}", temp));
              });
            }
            Some(ty @ Ty::Float) => {
              stack_hygiene!(&mut stack, |temp: Reg32| {
                let register = calc_index_offset(&mut stack, &mut asm, temp, arg);

                load_float(&mut asm, &register, "unary minus FPU");

                let temp_float = stack.push(i, ty.into(), 1, false, false);
                asm.lines.push("  fchs".to_string());
                asm.lines.push(format!("  fstp   {}", temp_float));
              });
            }
            _ => unreachable!(),
          },
          Op::Divide(lhs, rhs) if lhs.ty() == Some(Ty::Int) => {
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

                asm.lines.push("  cdq".to_string());

                if let Some(rhs_backup) = rhs_backup {
                  asm.lines.push(format!("  idiv   {}", rhs_backup));
                } else {
                  asm.lines.push(format!("  idiv   {}", rhs));
                }

                if temp_l != Reg32::EAX {
                  asm.lines.push(format!("  mov    {}, eax", temp_l));
                }

                if let Some(temp_r_backup) = temp_r_backup {
                  push_temporary(temp_r_backup, &mut stack);
                }

                if let Some(eax_backup) = eax_backup {
                  asm.lines.push(format!("  mov    eax, {}", eax_backup));
                  push_temporary(eax_backup, &mut stack);
                }

                if let Some(edx_backup) = edx_backup {
                  asm.lines.push(format!("  mov    edx, {}", edx_backup));
                  push_temporary(edx_backup, &mut stack);
                }

                push_storage_temporary(lhs, &mut stack);
                push_storage_temporary(rhs, &mut stack);
              });
            });
          }
          op @ Op::Plus(..) | op @ Op::Minus(..) | op @ Op::Times(..) | op @ Op::Divide(..) => {
            let (lhs, rhs, int_instruction, float_instruction) = match op {
              Op::Plus(lhs, rhs) => (lhs, rhs, "add", "fadd"),
              Op::Minus(lhs, rhs) => (lhs, rhs, "sub", "fsub"),
              Op::Times(lhs, rhs) => (lhs, rhs, "imul", "fmul"),
              Op::Divide(lhs, rhs) => (lhs, rhs, "idiv", "fdiv"),
              _ => unreachable!(),
            };

            match &lhs.ty() {
              Some(Ty::Int) => {
                stack_hygiene!(i, &mut stack, |temp_l: Reg32| {
                  stack_hygiene!(&mut stack, |temp_r: Reg32| {
                    let lhs = calc_index_offset(&mut stack, &mut asm, temp_l, lhs);
                    asm.lines.push(format!("  mov    {}, {}", temp_l, lhs));
                    push_storage_temporary(lhs, &mut stack);

                    let rhs = calc_index_offset(&mut stack, &mut asm, temp_r, rhs);
                    asm.lines.push(format!("  {}    {}, {}", int_instruction, temp_l, rhs));

                    push_storage_temporary(rhs, &mut stack);
                  });
                });
              }
              Some(ty @ Ty::Float) => {
                stack_hygiene!(&mut stack, |temp: Reg32| {
                  let lhs = calc_index_offset(&mut stack, &mut asm, temp, lhs);

                  load_float(&mut asm, &lhs, "calc FPU");
                  push_storage_temporary(lhs, &mut stack);

                  let rhs = calc_index_offset(&mut stack, &mut asm, temp, rhs);
                  asm.lines.push(format!("  {}   {}", float_instruction, rhs));

                  let temp_float = stack.push(i, ty.into(), 1, false, false);
                  asm.lines.push(format!("  fstp   {}", temp_float));

                  push_storage_temporary(rhs, &mut stack);
                });
              }
              _ => unimplemented!(),
            }
          }
          op @ Op::Eq(..)
          | op @ Op::Neq(..)
          | op @ Op::Lte(..)
          | op @ Op::Gt(..)
          | op @ Op::Gte(..)
          | op @ Op::Lt(..) => {
            let (lhs, rhs, int_instruction, float_instruction) = match op {
              Op::Lte(lhs, rhs) => (lhs, rhs, "setle", "setae"),
              Op::Lt(lhs, rhs) => (lhs, rhs, "setl", "seta"),
              Op::Gte(lhs, rhs) => (lhs, rhs, "setge", "setbe"),
              Op::Gt(lhs, rhs) => (lhs, rhs, "setg", "setb"),
              Op::Eq(lhs, rhs) => (lhs, rhs, "sete", "sete"),
              Op::Neq(lhs, rhs) => (lhs, rhs, "setne", "setne"),
              _ => unreachable!(),
            };

            match lhs.ty() {
              Some(Ty::Int) | Some(Ty::Bool) => {
                stack_hygiene!(i, &mut stack, |temp_l: Reg32| {
                  stack_hygiene!(&mut stack, |temp_r: Reg32| {
                    let lhs = calc_index_offset(&mut stack, &mut asm, temp_l, lhs);

                    if lhs.storage_type() == StorageType::Byte {
                      asm.lines.push(format!("  movzx  {}, {:#} # cmp", temp_l, lhs));
                    } else {
                      asm.lines.push(format!("  mov    {}, {} # cmp", temp_l, lhs));
                    }

                    let rhs = calc_index_offset(&mut stack, &mut asm, temp_r, rhs);
                    asm.lines.push(format!("  cmp    {}, {}", temp_l, rhs));

                    asm.lines.push(format!("  {}   {}", int_instruction, temp_l.as_reg8().0));

                    push_storage_temporary(lhs, &mut stack);
                    push_storage_temporary(rhs, &mut stack);
                  });
                });
              }
              Some(Ty::Float) => {
                stack_hygiene!(i, &mut stack, |temp_l: Reg32| {
                  let lhs = calc_index_offset(&mut stack, &mut asm, temp_l, lhs);
                  let rhs = calc_index_offset(&mut stack, &mut asm, temp_l, rhs);

                  load_float(&mut asm, &lhs, "cmp FPU lhs");
                  asm.lines.push(format!("  fld    {} # cmp rhs", rhs));

                  asm.lines.push("  fcomip  st, st(1)".to_string());
                  asm.lines.push("  fstp    st(0)".to_string());

                  asm.lines.push(format!("  {}   {}", float_instruction, temp_l.as_reg8().0));

                  push_storage_temporary(lhs, &mut stack);
                  push_storage_temporary(rhs, &mut stack);
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
                  let lhs = calc_index_offset(&mut stack, &mut asm, temp, lhs);
                  let rhs = calc_index_offset(&mut stack, &mut asm, temp, rhs);

                  if lhs.storage_type() == StorageType::Byte {
                    asm.lines.push(format!("  movzx  {}, {:#}", temp, lhs));
                  } else {
                    asm.lines.push(format!("  mov    {}, {}", temp, lhs));
                  }

                  asm.lines.push(format!("  {}    {:#}, {:#}", set_instruction, temp.as_reg8().0, rhs));

                  push_storage_temporary(lhs, &mut stack);
                  push_storage_temporary(rhs, &mut stack);
                });
              }
              _ => unreachable!(),
            }
          }
          Op::Jumpfalse(cond, Arg::Reference(_, reference)) => match cond {
            Arg::Literal(Literal::Bool(true)) => (),
            Arg::Literal(Literal::Bool(false)) => {
              asm.lines.push(format!("  jmp    {}", asm.labels.get(reference).unwrap()));
            }
            arg => {
              stack_hygiene!(&mut stack, |temp: Reg32| {
                let result_register = calc_index_offset(&mut stack, &mut asm, temp, arg);

                asm.lines.push(format!("  cmp    {:#}, 0", result_register));
                asm.lines.push(format!("  je     {}", asm.labels.get(reference).unwrap()));

                push_storage_temporary(result_register, &mut stack);
              });
            }
          },
          Op::Jump(Arg::Reference(_, reference)) => {
            asm.lines.push(format!("  jmp    {}", asm.labels.get(reference).unwrap()));
          }
          Op::Call(arg) => {
            let saved_registers = stack.used_registers.iter().map(|(&reg, _)| reg).collect::<Vec<_>>();

            for reg in saved_registers.iter() {
              asm.lines.push(format!("  push    {}", reg));
            }

            match &arg.ty() {
              Some(ty @ Ty::Float) => {
                stack_hygiene!(&mut stack, |temp: Reg32| {
                  calc_index_offset(&mut stack, &mut asm, temp, arg);
                  let temp_float = stack.push(i, ty.into(), 1, false, false);
                  asm.lines.push(format!("  fstp   {}", temp_float));
                });
              }
              ty => {
                stack_hygiene!(i, &mut stack, |temp: Reg32| {
                  let result = calc_index_offset(&mut stack, &mut asm, temp, arg);

                  if matches!(result, Storage::Register(_, reg) if reg != temp) {
                    asm.lines.push(format!("  mov    {}, {}", temp, result));
                  }

                  if ty.is_none() {
                    push_temporary(temp, &mut stack);
                  }
                });
              }
            }

            for reg in saved_registers.iter().rev() {
              asm.lines.push(format!("  pop    {}", reg));
            }
          },
          Op::Nope => asm.lines.push("  nop".to_string()),
          _ => unreachable!(),
        }
      }

      asm.lines.push(format!(".AWAY_{}:", name));

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

    for builtin_function in mem::take(&mut asm.builtin_functions).iter() {
      asm.lines.push(format!("{}:", builtin_function));

      match builtin_function.as_ref() {
        "read_int" => {
          asm.lines.push("  push   ebp".to_string());
          asm.lines.push("  mov    ebp, esp".to_string());
          asm.lines.push("  sub    esp, 32".to_string());
          asm.lines.push("  lea    eax, [ebp-12]".to_string());
          asm.lines.push("  push   eax".to_string());
          let format_string = add_string(&mut asm, "%d");
          asm.lines.push(format!("  push   {}", format_string));
          asm.lines.push("  call   __isoc99_scanf".to_string());
          asm.lines.push("  add    esp, 16".to_string());
          asm.lines.push("  cmp    eax, 1".to_string());
          asm.lines.push("  je    .READ_INT_SUCCEEDED".to_string());
          asm.lines.push("  push   101".to_string());
          asm.lines.push("  call   exit".to_string());
          asm.lines.push(".READ_INT_SUCCEEDED:".to_string());
          asm.lines.push("  mov    eax, DWORD PTR [ebp-12]".to_string());
          asm.lines.push("  leave".to_string());
          asm.lines.push("  ret".to_string());
        }
        "read_float" => {
          asm.lines.push("  push    ebp".to_string());
          asm.lines.push("  mov     ebp, esp".to_string());
          asm.lines.push("  sub     esp, 32".to_string());
          asm.lines.push("  lea     eax, [ebp-12]".to_string());
          asm.lines.push("  push    eax".to_string());
          let format_string = add_string(&mut asm, "%f");
          asm.lines.push(format!("  push   {}", format_string));
          asm.lines.push("  call    __isoc99_scanf".to_string());
          asm.lines.push("  add     esp, 16".to_string());
          asm.lines.push("  cmp    eax, 1".to_string());
          asm.lines.push("  je    .READ_FLOAT_SUCCEEDED".to_string());
          asm.lines.push("  push   101".to_string());
          asm.lines.push("  call   exit".to_string());
          asm.lines.push(".READ_FLOAT_SUCCEEDED:".to_string());
          asm.lines.push("  fld     DWORD PTR [ebp-12]".to_string());
          asm.lines.push("  leave".to_string());
          asm.lines.push("  ret".to_string());
        }
        _ => unreachable!(),
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
