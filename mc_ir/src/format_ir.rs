use std::fmt;

use crate::ir::*;

impl fmt::Display for Arg<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Literal(literal) => literal.to_string().fmt(f),
      Self::Variable(_, reference, offset) => write!(
        f,
        "(&{}, {})",
        reference,
        offset.as_ref().as_ref().map(|o| format!("[{}]", o)).unwrap_or_else(|| "lel".to_string())
      ),
      Self::Reference(_, reference) => write!(f, "t{}", reference),
      Self::FunctionCall(_, identifier, arguments) => {
        write!(f, "{}({})", identifier, arguments.iter().map(|a| a.to_string()).collect::<Vec<_>>().join(", "))
      }
    }
  }
}

impl fmt::Display for Op<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Param(arg, ty, size) => {
        write!(f, "param {} {} {}", arg, ty, size.map(|s| format!("[{}]", s)).unwrap_or_else(|| "lel".to_string()))
      }
      Self::Decl(arg, ty, size) => {
        write!(f, "decl {} {} {}", arg, ty, size.map(|s| format!("[{}]", s)).unwrap_or_else(|| "lel".to_string()))
      }
      Self::Gt(arg1, arg2) => write!(f, "{} > {}", arg1, arg2),
      Self::Gte(arg1, arg2) => write!(f, "{} >= {}", arg1, arg2),
      Self::Lt(arg1, arg2) => write!(f, "{} < {}", arg1, arg2),
      Self::Lte(arg1, arg2) => write!(f, "{} <= {}", arg1, arg2),
      Self::Plus(arg1, arg2) => write!(f, "{} + {}", arg1, arg2),
      Self::Minus(arg1, arg2) => write!(f, "{} - {}", arg1, arg2),
      Self::Divide(arg1, arg2) => write!(f, "{} / {}", arg1, arg2),
      Self::Times(arg1, arg2) => write!(f, "{} * {}", arg1, arg2),
      Self::Eq(arg1, arg2) => write!(f, "{} == {}", arg1, arg2),
      Self::Neq(arg1, arg2) => write!(f, "{} != {}", arg1, arg2),
      Self::Land(arg1, arg2) => write!(f, "{} && {}", arg1, arg2),
      Self::Lor(arg1, arg2) => write!(f, "{} || {}", arg1, arg2),
      Self::Not(arg) => write!(f, "!{}", arg),
      Self::UnaryMinus(arg) => write!(f, "-{}", arg),
      Self::Assign(arg1, arg2) => write!(f, "{} = {}", arg2, arg1),
      Self::Jumpfalse(arg1, arg2) => write!(f, "jumpfalse {} {}", arg1, arg2),
      Self::Jump(arg) => write!(f, "jump {}", arg),
      Self::Call(arg) => write!(f, "{}", arg),
      Self::Return(arg) => {
        if let Some(ret_arg) = arg {
          write!(f, "return {}", ret_arg)
        } else {
          write!(f, "return;")
        }
      }
      Self::Nope => write!(f, "nope"),
    }
  }
}

impl fmt::Display for IntermediateRepresentation<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    for (identifier, (range, _)) in &self.functions {
      writeln!(f, "\t {}:", identifier)?;
      for (i, stmt) in self.statements[range.start..range.end].iter().enumerate() {
        match stmt {
          Op::Param(..)
          | Op::Decl(..)
          | Op::Assign(..)
          | Op::Jump(..)
          | Op::Jumpfalse(..)
          | Op::Call(..)
          | Op::Return(..)
          | Op::Nope => {
            writeln!(f, "{}:\t \t {}", range.start + i, stmt)?;
          }
          _ => writeln!(f, "{}:\t \t t{} = {}", range.start + i, range.start + i, stmt)?,
        }
      }

      writeln!(f)?;
    }

    writeln!(f)
  }
}
