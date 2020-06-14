use std::fmt;

use crate::ir::*;

impl fmt::Display for Arg<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Literal(literal) => literal.fmt(f),
      Self::Variable(_, reference, offset) => {
        write!(f, "&{}{}", reference, offset.as_ref().as_ref().map(|o| format!("[{}]", o)).unwrap_or_else(String::new))
      }
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
        write!(f, "param {} {}{}", arg, ty, size.map(|s| format!("[{}]", s)).unwrap_or_else(String::new))
      }
      Self::Decl(arg, ty, size) => {
        write!(f, "decl {} {}{}", arg, ty, size.map(|s| format!("[{}]", s)).unwrap_or_else(String::new))
      }
      Self::Gt(lhs, rhs) => write!(f, "{} > {}", lhs, rhs),
      Self::Gte(lhs, rhs) => write!(f, "{} >= {}", lhs, rhs),
      Self::Lt(lhs, rhs) => write!(f, "{} < {}", lhs, rhs),
      Self::Lte(lhs, rhs) => write!(f, "{} <= {}", lhs, rhs),
      Self::Plus(lhs, rhs) => write!(f, "{} + {}", lhs, rhs),
      Self::Minus(lhs, rhs) => write!(f, "{} - {}", lhs, rhs),
      Self::Divide(lhs, rhs) => write!(f, "{} / {}", lhs, rhs),
      Self::Times(lhs, rhs) => write!(f, "{} * {}", lhs, rhs),
      Self::Eq(lhs, rhs) => write!(f, "{} == {}", lhs, rhs),
      Self::Neq(lhs, rhs) => write!(f, "{} != {}", lhs, rhs),
      Self::Land(lhs, rhs) => write!(f, "{} && {}", lhs, rhs),
      Self::Lor(lhs, rhs) => write!(f, "{} || {}", lhs, rhs),
      Self::Not(arg) => write!(f, "!{}", arg),
      Self::UnaryMinus(arg) => write!(f, "-{}", arg),
      Self::Assign(lhs, rhs) => write!(f, "{} = {}", rhs, lhs),
      Self::Jumpfalse(lhs, rhs) => write!(f, "jumpfalse {} {}", lhs, rhs),
      Self::Jump(arg) => write!(f, "jump {}", arg),
      Self::Call(arg) => write!(f, "{}", arg),
      Self::Return(arg) => {
        if let Some(ret_arg) = arg {
          write!(f, "return {}", ret_arg)
        } else {
          write!(f, "return;")
        }
      }
      Self::Nope => write!(f, "nop"),
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
