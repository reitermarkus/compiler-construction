use std::collections::HashMap;

use mc_parser::ast::*;

#[derive(Debug, Default)]
pub struct HashStack {
  pub stack: Vec<(Identifier, usize)>,
}

impl HashStack {
  pub fn push(&mut self, identifier: Identifier, reference: usize) {
    self.stack.push((identifier, reference));
  }

  pub fn lookup(&self, identifier: &Identifier) -> Option<usize> {
    self.stack.iter().rev().find(|i| &i.0 == identifier).map(|e| e.1)
  }

  pub fn lookup_mut(&mut self, identifier: &Identifier) -> Option<&mut usize> {
    self.stack.iter_mut().rev().find(|i| &i.0 == identifier).map(|e| &mut e.1)
  }

  pub fn ptr(&self) -> usize {
    self.stack.len()
  }

  pub fn reset(&mut self, ptr: usize) {
    self.stack.truncate(ptr);
  }
}

#[derive(Debug)]
pub enum Arg<'a> {
  Literal(&'a Literal),
  Variable(&'a Identifier),
  FunctionCall(&'a Identifier, Vec<Arg<'a>>),
  Reference(usize),
}

impl<'a> PartialEq for Arg<'a> {
  fn eq(&self, other: &Self) -> bool {
    match (self, other) {
      (Self::Literal(l1), Self::Literal(l2)) => l1 == l2,
      (Self::Variable(v1), Self::Variable(v2)) => v1 == v2,
      (Self::Reference(au1), Self::Reference(au2)) => au1 == au2,
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
  pub stack: HashStack,
  pub statements: Vec<Op<'a>>,
  pub functions: HashMap<&'a Identifier, IrFunction>,
}

impl<'a> IntermediateRepresentation<'a> {
  pub fn push(&mut self, op: Op<'a>) {
    self.statements.push(op)
  }

  pub fn last_ref(&self) -> Arg<'a> {
    Arg::Reference(self.statements.len() - 1)
  }

  pub fn update_reference(&mut self, index: usize, value: usize) {
    match self.statements.get_mut(index) {
      Some(Op::Jumpfalse(_, Arg::Reference(ref mut i))) | Some(Op::Jump(Arg::Reference(ref mut i))) => {
        *i = value;
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
  Decl(Arg<'a>),
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
  Call(Arg<'a>),
  Return(Option<Arg<'a>>),
}
