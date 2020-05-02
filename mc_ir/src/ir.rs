use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};

use mc_parser::ast::*;

#[derive(Debug)]
pub enum Arg<'a> {
  Literal(&'a Literal),
  Variable(&'a Identifier),
  FunctionCall(&'a Identifier, &'a Vec<Expression<'a>>),
  Reference(AtomicUsize),
}

impl<'a> PartialEq for Arg<'a> {
  fn eq(&self, other: &Self) -> bool {
    match (self, other) {
      (Self::Literal(l1), Self::Literal(l2)) => l1 == l2,
      (Self::Variable(v1), Self::Variable(v2)) => v1 == v2,
      (Self::Reference(au1), Self::Reference(au2)) => au1.load(Ordering::SeqCst) == au2.load(Ordering::SeqCst),
      _ => false,
    }
  }
}

#[derive(Default, Debug, PartialEq)]
pub struct IrFunction {
  pub start: usize,
  pub end: usize,
}

impl From<(usize, usize)> for IrFunction {
  fn from(tuple: (usize, usize)) -> IrFunction {
    Self { start: tuple.0, end: tuple.1 }
  }
}

#[derive(Default, Debug)]
pub struct IntermediateRepresentation<'a> {
  pub statements: Vec<Op<'a>>,
  pub functions: HashMap<&'a Identifier, IrFunction>,
}

impl<'a> IntermediateRepresentation<'a> {
  pub fn push(&mut self, op: Op<'a>) {
    self.statements.push(op)
  }

  pub fn last_ref(&self) -> Arg<'a> {
    Arg::Reference(AtomicUsize::new(self.statements.len() - 1))
  }

  pub fn update_reference(&mut self, index: usize, value: usize) {
    match self.statements.get(index) {
      Some(Op::Jumpfalse(_, Arg::Reference(i))) | Some(Op::Jump(Arg::Reference(i))) => {
        i.store(value, Ordering::SeqCst);
      }
      _ => unreachable!(),
    }
  }

  pub fn add_function(&mut self, identifier: &'a Identifier, irf: IrFunction) {
    self.functions.insert(identifier, irf);
  }
}

#[derive(Debug, PartialEq)]
pub enum Op<'a> {
  Gt(Arg<'a>, Arg<'a>),
  Gte(Arg<'a>, Arg<'a>),
  Lt(Arg<'a>, Arg<'a>),
  Lte(Arg<'a>, Arg<'a>),
  Plus(Arg<'a>, Arg<'a>),
  Minus(Arg<'a>, Arg<'a>),
  Divide(Arg<'a>, Arg<'a>),
  Times(Arg<'a>, Arg<'a>),
  Assign(Arg<'a>, Arg<'a>),
  UnaryMinus(Arg<'a>),
  Not(Arg<'a>),
  Eq(Arg<'a>, Arg<'a>),
  Neq(Arg<'a>, Arg<'a>),
  Land(Arg<'a>, Arg<'a>),
  Lor(Arg<'a>, Arg<'a>),
  Jumpfalse(Arg<'a>, Arg<'a>),
  Jump(Arg<'a>),
  Return(Option<Arg<'a>>),
}
