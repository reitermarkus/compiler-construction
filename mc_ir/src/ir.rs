use std::collections::HashMap;
use std::ops::Range;

use mc_parser::ast::*;

#[derive(Debug, Default)]
pub struct HashStack {
  pub stack: Vec<(Identifier, usize, Ty)>,
}

impl HashStack {
  pub fn push(&mut self, identifier: Identifier, reference: usize, ty: Ty) {
    self.stack.push((identifier, reference, ty));
  }

  pub fn lookup(&self, identifier: &Identifier) -> Option<(usize, Ty)> {
    self.stack.iter().rev().find(|(id, _, _)| id == identifier).map(|&(_, reference, ty)| (reference, ty))
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
  Variable(Ty, usize, Box<Arg<'a>>),
  FunctionCall(Option<Ty>, &'a Identifier, Vec<Arg<'a>>),
  Reference(Option<Ty>, usize),
}

impl<'a> Arg<'a> {
  pub fn ty(&self) -> Option<Ty> {
    match self {
      Self::Literal(literal) => Some(Ty::from(*literal)),
      Self::Variable(ty, ..) => Some(*ty),
      Self::FunctionCall(ty, ..) => *ty,
      Self::Reference(ty, ..) => *ty,
    }
  }
}

impl<'a> PartialEq for Arg<'a> {
  fn eq(&self, other: &Self) -> bool {
    match (self, other) {
      (Self::Literal(l1), Self::Literal(l2)) => l1 == l2,
      (Self::Variable(ty1, v1, o1), Self::Variable(ty2, v2, o2)) => ty1 == ty2 && v1 == v2 && o1 == o2,
      (Self::Reference(ty1, au1), Self::Reference(ty2, au2)) => ty1 == ty2 && au1 == au2,
      _ => false,
    }
  }
}

#[derive(Default, Debug)]
pub struct IntermediateRepresentation<'a> {
  pub stack: HashStack,
  pub statements: Vec<Op<'a>>,
  pub functions: HashMap<&'a Identifier, (Range<usize>, Option<Ty>)>,
}

impl<'a> IntermediateRepresentation<'a> {
  pub fn push(&mut self, op: Op<'a>) {
    self.statements.push(op)
  }

  pub fn last_ref(&self) -> Arg<'a> {
    let reference = self.statements.len() - 1;
    let ty = self.statements[reference].ty();
    Arg::Reference(ty, reference)
  }

  pub fn update_reference(&mut self, index: usize, value: usize) {
    match self.statements.get_mut(index) {
      Some(Op::Jumpfalse(_, Arg::Reference(_, ref mut i))) | Some(Op::Jump(Arg::Reference(_, ref mut i))) => {
        *i = value;
      }
      _ => unreachable!(),
    }
  }

  pub fn add_function(&mut self, identifier: &'a Identifier, range: Range<usize>, ty: Option<Ty>) {
    self.functions.insert(identifier, (range, ty));
  }
}

#[derive(Debug, PartialEq)]
pub enum Op<'a> {
  Load(Arg<'a>),
  Param(&'a Identifier, Ty, usize),
  Decl(&'a Identifier, Ty, usize),
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

impl<'a> Op<'a> {
  pub fn ty(&self) -> Option<Ty> {
    match self {
      Self::Load(arg) => arg.ty(),
      Self::Param(_, ty, _) => Some(*ty),
      Self::Decl(_, ty, _) => Some(*ty),
      Self::Gt(..) => Some(Ty::Bool),
      Self::Gte(..) => Some(Ty::Bool),
      Self::Lt(..) => Some(Ty::Bool),
      Self::Lte(..) => Some(Ty::Bool),
      Self::Plus(arg, _) => arg.ty(),
      Self::Minus(arg, _) => arg.ty(),
      Self::Divide(arg, _) => arg.ty(),
      Self::Times(arg, _) => arg.ty(),
      Self::Assign(arg, _) => arg.ty(),
      Self::UnaryMinus(arg) => arg.ty(),
      Self::Not(..) => Some(Ty::Bool),
      Self::Eq(..) => Some(Ty::Bool),
      Self::Neq(..) => Some(Ty::Bool),
      Self::Land(..) => Some(Ty::Bool),
      Self::Lor(..) => Some(Ty::Bool),
      Self::Jumpfalse(arg, _) => arg.ty(),
      Self::Jump(_) => None,
      Self::Call(arg) => arg.ty(),
      Self::Return(arg) => arg.as_ref().and_then(|a| a.ty()),
    }
  }
}