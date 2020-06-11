use ordered_float::OrderedFloat;
use std::collections::VecDeque;
use std::mem;

use mc_ir::{Arg, IntermediateRepresentation, Op};
use mc_parser::ast::*;

use crate::asm::Asm;
use crate::register::*;
use crate::stack::*;
use crate::storage::*;

pub trait ToAsm {
  fn to_asm(&self) -> Asm;
}

const fn extend_to_multiple(number: usize, n: usize) -> usize {
  ((number + n - 1) / n) * n
}

const fn calculate_alignment(number: usize, n: usize) -> (usize, usize) {
  let multiple = extend_to_multiple(number, n);
  (multiple - number, multiple)
}

fn calc_index_offset(stack: &mut Stack, asm: &mut Asm, reg: Reg32, arg: &Arg<'_>) -> Storage {
  match arg {
    Arg::Variable(_, decl_index, index_offset) => {
      let (storage_type, offset, parameter, array) = stack.lookup(*decl_index);

      let index_offset = match index_offset.as_ref() {
        Some(Arg::Literal(Literal::Int(index_offset))) => Some(Offset::Literal(*index_offset as usize)),
        Some(arg) => match calc_index_offset(stack, asm, reg, arg) {
          Storage::Register(_, reg) => {
            stack.push_temporary(reg);
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
        stack.with_temporary(|_, temp| {
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
        let (_, offset, parameter, array) = stack.lookup(*reference);
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

        let storage_type = match (identifier.as_ref(), arg.ty()) {
          ("print_float", Some(Ty::Float)) => StorageType::Qword,
          _ => argument.storage_type(),
        };

        args_size += storage_type.size();

        match &argument {
          Storage::Pointer(Pointer { array, ref index_offset, .. }) if *array && index_offset.is_none() => {
            stack.with_temporary(|_, temp| {
              asm.lines.push(format!("  lea    {}, {}", temp, argument));
              asm.lines.push(format!("  push   {} # ptr", temp));
            });
          }
          argument if arg.ty() == Some(Ty::Float) => {
            load_float(asm, &argument, "push function argument");

            asm.lines.push(format!("  lea    esp, [esp-{}]", storage_type.size()));
            asm.lines.push(format!("  fstp   {} [esp]", storage_type));
          }
          Storage::Register(_, reg) => {
            asm.lines.push(format!("  push   {} # reg", reg));
          }
          argument => {
            asm.lines.push(format!("  push   {} # arg", argument));
          }
        }

        stack.push_storage_temporary(argument);
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
          let format_string = add_string(asm, "%.2f");
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

      let (stack_alignment, stack_size) = calculate_alignment(args_size, 16);

      if stack_size > 0 {
        if stack_alignment > 0 {
          asm.lines.insert(alignment_index, format!("  sub    esp, {} # stack alignment", stack_alignment));
        }

        asm.lines.push(format!("  add    esp, {}", stack_size));
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
              stack.with_temporary(|stack, temp| {
                let arg = stack.push(i, StorageType::Dword, 1, true, false);

                let pointer = stack.push(i, storage_type, count.clone().unwrap_or(1), false, count.is_some());

                asm.lines.push(format!("  mov    {}, {}", temp, arg));
                asm.lines.push(format!("  mov    {}, {}", pointer, pointer.storage_type.map_register(temp)));
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
            stack.with_temporary(|stack, temp| {
              let val = calc_index_offset(stack, &mut asm, temp, value);

              match variable.ty() {
                Some(Ty::Float) => {
                  load_float(&mut asm, &val, "assign FPU");

                  let var = calc_index_offset(stack, &mut asm, temp, variable);
                  asm.lines.push(format!("  fstp   {}", var));
                  stack.push_storage_temporary(var);
                }
                _ => match val {
                  Storage::Pointer(..) => {
                    stack.with_temporary(|stack, temp_val| {
                      asm.lines.push(format!("  mov    {}, {}", temp_val, val));

                      let var = calc_index_offset(stack, &mut asm, temp, variable);
                      asm.lines.push(format!("  mov    {}, {:#}", var, temp_val));
                      stack.push_storage_temporary(var);
                    });
                  }
                  _ => {
                    let var = calc_index_offset(stack, &mut asm, temp, variable);
                    asm.lines.push(format!("  mov    {}, {:#}", var, val));
                    stack.push_storage_temporary(var);
                  }
                },
              }

              stack.push_storage_temporary(val);
            });
          }
          Op::Return(arg) => {
            if let Some(arg) = arg {
              stack.with_temporary(|stack, temp| {
                let result = calc_index_offset(stack, &mut asm, temp, arg);

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

                stack.push_storage_temporary(result);
              });
            }

            asm.lines.push(format!("  jmp    .AWAY_{}", name));
          }
          Op::Not(arg) => {
            stack.with_indexed_temporary(i, |stack, temp: Reg32| {
              let result = calc_index_offset(stack, &mut asm, temp, arg);
              asm.lines.push(format!("  movzx  {}, {:#}", temp, result));
              asm.lines.push(format!("  xor    {}, 1", temp))
            });
          }
          Op::UnaryMinus(arg) => match &arg.ty() {
            Some(Ty::Int) => {
              stack.with_indexed_temporary(i, |stack, temp: Reg32| {
                let register = calc_index_offset(stack, &mut asm, temp, arg);
                asm.lines.push(format!("  mov    {}, {}", temp, register));
                asm.lines.push(format!("  neg    {}", temp));
              });
            }
            Some(ty @ Ty::Float) => {
              stack.with_temporary(|stack, temp| {
                let register = calc_index_offset(stack, &mut asm, temp, arg);

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

            stack.with_indexed_temporary(i, |stack, temp_l: Reg32| {
              stack.with_temporary(|stack, temp_r| {
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

                let lhs = calc_index_offset(stack, &mut asm, temp_l, lhs);
                let rhs = calc_index_offset(stack, &mut asm, temp_r, rhs);

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
                  stack.push_temporary(temp_r_backup);
                }

                if let Some(eax_backup) = eax_backup {
                  asm.lines.push(format!("  mov    eax, {}", eax_backup));
                  stack.push_temporary(eax_backup);
                }

                if let Some(edx_backup) = edx_backup {
                  asm.lines.push(format!("  mov    edx, {}", edx_backup));
                  stack.push_temporary(edx_backup);
                }

                stack.push_storage_temporary(lhs);
                stack.push_storage_temporary(rhs);
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
                stack.with_indexed_temporary(i, |stack, temp_l: Reg32| {
                  stack.with_temporary(|stack, temp_r| {
                    let lhs = calc_index_offset(stack, &mut asm, temp_l, lhs);
                    asm.lines.push(format!("  mov    {}, {}", temp_l, lhs));
                    stack.push_storage_temporary(lhs);

                    let rhs = calc_index_offset(stack, &mut asm, temp_r, rhs);
                    asm.lines.push(format!("  {}    {}, {}", int_instruction, temp_l, rhs));

                    stack.push_storage_temporary(rhs);
                  });
                });
              }
              Some(ty @ Ty::Float) => {
                stack.with_temporary(|stack, temp| {
                  let lhs = calc_index_offset(stack, &mut asm, temp, lhs);

                  load_float(&mut asm, &lhs, "calc FPU");
                  stack.push_storage_temporary(lhs);

                  let rhs = calc_index_offset(stack, &mut asm, temp, rhs);
                  asm.lines.push(format!("  {}   {}", float_instruction, rhs));

                  let temp_float = stack.push(i, ty.into(), 1, false, false);
                  asm.lines.push(format!("  fstp   {}", temp_float));

                  stack.push_storage_temporary(rhs);
                });
              }
              _ => unreachable!(),
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
                stack.with_indexed_temporary(i, |stack, temp_l: Reg32| {
                  stack.with_temporary(|stack, temp_r| {
                    let lhs = calc_index_offset(stack, &mut asm, temp_l, lhs);

                    if lhs.storage_type() == StorageType::Byte {
                      asm.lines.push(format!("  movzx  {}, {:#} # cmp", temp_l, lhs));
                    } else {
                      asm.lines.push(format!("  mov    {}, {} # cmp", temp_l, lhs));
                    }

                    let rhs = calc_index_offset(stack, &mut asm, temp_r, rhs);
                    asm.lines.push(format!("  cmp    {}, {}", temp_l, rhs));

                    asm.lines.push(format!("  {}   {}", int_instruction, temp_l.as_reg8().0));

                    stack.push_storage_temporary(lhs);
                    stack.push_storage_temporary(rhs);
                  });
                });
              }
              Some(Ty::Float) => {
                stack.with_indexed_temporary(i, |stack, temp_l: Reg32| {
                  let lhs = calc_index_offset(stack, &mut asm, temp_l, lhs);
                  load_float(&mut asm, &lhs, "cmp FPU lhs");

                  let rhs = calc_index_offset(stack, &mut asm, temp_l, rhs);
                  asm.lines.push(format!("  fld    {} # cmp rhs", rhs));

                  asm.lines.push("  fcomip  st, st(1)".to_string());
                  asm.lines.push("  fstp    st(0)".to_string());

                  asm.lines.push(format!("  {}   {}", float_instruction, temp_l.as_reg8().0));

                  stack.push_storage_temporary(lhs);
                  stack.push_storage_temporary(rhs);
                });
              }
              _ => unreachable!(),
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
                stack.with_indexed_temporary(i, |stack, temp: Reg32| {
                  let lhs = calc_index_offset(stack, &mut asm, temp, lhs);
                  let rhs = calc_index_offset(stack, &mut asm, temp, rhs);

                  if lhs.storage_type() == StorageType::Byte {
                    asm.lines.push(format!("  movzx  {}, {:#}", temp, lhs));
                  } else {
                    asm.lines.push(format!("  mov    {}, {}", temp, lhs));
                  }

                  asm.lines.push(format!("  {}    {:#}, {:#}", set_instruction, temp.as_reg8().0, rhs));

                  stack.push_storage_temporary(lhs);
                  stack.push_storage_temporary(rhs);
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
              stack.with_temporary(|stack, temp| {
                let result_register = calc_index_offset(stack, &mut asm, temp, arg);

                asm.lines.push(format!("  cmp    {:#}, 0", result_register));
                asm.lines.push(format!("  je     {}", asm.labels.get(reference).unwrap()));

                stack.push_storage_temporary(result_register);
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
                stack.with_temporary(|stack, temp| {
                  calc_index_offset(stack, &mut asm, temp, arg);
                  let temp_float = stack.push(i, ty.into(), 1, false, false);
                  asm.lines.push(format!("  fstp   {}", temp_float));
                });
              }
              ty => {
                stack.with_indexed_temporary(i, |stack, temp: Reg32| {
                  let result = calc_index_offset(stack, &mut asm, temp, arg);

                  if ty.is_none() {
                    stack.push_temporary(temp);
                  } else if matches!(result, Storage::Register(_, reg) if reg != temp) {
                    asm.lines.push(format!("  mov    {}, {}", temp, result));
                  }
                });
              }
            }

            for reg in saved_registers.iter().rev() {
              asm.lines.push(format!("  pop    {}", reg));
            }
          }
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
          format!("  sub    esp, {}   # stack variables size", extend_to_multiple(stack.variables_size, 16)),
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
