use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;

use std::collections::HashMap;
use std::ops::{Deref, DerefMut};

use mc_parser::ast::*;

#[derive(Default)]
pub struct Scope {
  pub name: Option<String>,
  pub parent: Option<Rc<RefCell<Scope>>>,
  pub symbols: SymbolTable,
  pub return_type: Option<Ty>,
  pub children: Vec<Rc<RefCell<Scope>>>,
}

impl fmt::Debug for Scope {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("Scope")
      .field("name", &self.name)
      .field("has_parent", &self.parent.is_some())
      .field("symbols", &self.symbols)
      .field("return_type", &self.return_type)
      .field("children", &self.children)
      .finish()
  }
}

impl fmt::Display for Scope {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if let Some(parent) = &self.parent {
      let parent = parent.borrow();

      if let Some(name) = &self.name {
        write!(f, "{}.{}", parent, name)
      } else {
        parent.fmt(f)
      }
    } else if let Some(name) = &self.name {
      name.fmt(f)
    } else {
      "root".fmt(f)
    }
  }
}

impl Scope {
  pub fn new() -> Rc<RefCell<Self>> {
    let mut scope = Scope::default();

    scope.insert(Identifier::from("print"), Symbol::Function(None, vec![(Ty::String, None)]));
    scope.insert(Identifier::from("print_nl"), Symbol::Function(None, vec![]));
    scope.insert(Identifier::from("print_int"), Symbol::Function(None, vec![(Ty::Int, None)]));
    scope.insert(Identifier::from("print_float"), Symbol::Function(None, vec![(Ty::Float, None)]));
    scope.insert(Identifier::from("read_int"), Symbol::Function(Some(Ty::Int), vec![]));
    scope.insert(Identifier::from("read_float"), Symbol::Function(Some(Ty::Float), vec![]));

    Rc::new(RefCell::new(scope))
  }

  pub fn new_child(parent: &Rc<RefCell<Self>>, name: &str) -> Rc<RefCell<Self>> {
    let mut child = Self::default();
    child.parent = Some(Rc::clone(&parent));

    let mut parent = parent.borrow_mut();
    let id = parent.children.len();
    child.name = Some(format!("{}[{}]", name, id));
    parent.children.push(Rc::new(RefCell::new(child)));

    Rc::clone(parent.children.last().unwrap())
  }

  pub fn insert(&mut self, identifier: Identifier, symbol: Symbol) {
    self.symbols.insert(identifier, symbol);
  }

  pub fn lookup(scope: &Rc<RefCell<Self>>, identifier: &Identifier) -> Option<Symbol> {
    let scope = scope.borrow();

    if let Some(symbol) = scope.symbols.get(identifier) {
      return Some(symbol.clone());
    }

    if let Some(parent) = &scope.parent {
      Self::lookup(parent, identifier)
    } else {
      None
    }
  }

  pub fn lookup_in_scope(scope: &Rc<RefCell<Self>>, identifier: &Identifier) -> Option<Symbol> {
    let scope = scope.borrow();

    if let Some(symbol) = scope.symbols.get(identifier) {
      Some(symbol.clone())
    } else {
      None
    }
  }

  pub fn return_type(scope: &Rc<RefCell<Self>>) -> Option<Ty> {
    let scope = scope.borrow();

    if let Some(ty) = &scope.return_type {
      Some(ty.clone())
    } else if let Some(parent) = &scope.parent {
      Self::return_type(parent)
    } else {
      None
    }
  }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Symbol {
  Function(Option<Ty>, Vec<(Ty, Option<usize>)>),
  Variable(Ty, Option<usize>),
}

impl fmt::Display for Symbol {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    use Symbol::*;

    match self {
      Function(ty, args) => {
        write!(f, "function (")?;

        for (ty, index) in args {
          write!(f, " {}", ty)?;
          if let Some(i) = index {
            write!(f, "[{}]", i)?;
          }
        }
        write!(f, " )")?;

        if let Some(ty) = ty {
          write!(f, " -> {}", ty)?;
        }
      }
      Variable(ty, size) => {
        write!(f, "variable = {}", ty)?;

        if let Some(size) = size {
          write!(f, "[{}]", size)?;
        }
      }
    }

    Ok(())
  }
}

#[derive(Default, Debug)]
pub struct SymbolTable {
  pub table: HashMap<Identifier, Symbol>,
}

impl Deref for SymbolTable {
  type Target = HashMap<Identifier, Symbol>;

  fn deref(&self) -> &Self::Target {
    &self.table
  }
}

impl DerefMut for SymbolTable {
  fn deref_mut(&mut self) -> &mut Self::Target {
    &mut self.table
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn insert_and_lookup() {
    let root_scope = Scope::new();

    let fib_id = Identifier::from("fib");
    let fib_symbol = Symbol::Function(Some(Ty::Int), Vec::new());
    Scope::insert(&mut root_scope.borrow_mut(), fib_id.clone(), fib_symbol.clone());

    let main_id = Identifier::from("main");
    let main_symbol = Symbol::Function(None, Vec::new());
    Scope::insert(&mut root_scope.borrow_mut(), main_id.clone(), main_symbol.clone());

    let function_scope = Scope::new_child(&root_scope, "function");
    let param_id = Identifier::from("x");
    let param_symbol = Symbol::Variable(Ty::Float, None);
    Scope::insert(&mut function_scope.borrow_mut(), param_id.clone(), param_symbol.clone());

    let block_scope = Scope::new_child(&function_scope, "block");
    let var_id = Identifier::from("y");
    let var_symbol = Symbol::Variable(Ty::String, None);
    Scope::insert(&mut block_scope.borrow_mut(), var_id.clone(), var_symbol.clone());

    assert_eq!(Scope::lookup(&root_scope, &fib_id), Some(fib_symbol.clone()));
    assert_eq!(Scope::lookup(&function_scope, &fib_id), Some(fib_symbol.clone()));
    assert_eq!(Scope::lookup(&block_scope, &fib_id), Some(fib_symbol.clone()));

    assert_eq!(Scope::lookup(&root_scope, &main_id), Some(main_symbol.clone()));
    assert_eq!(Scope::lookup(&function_scope, &main_id), Some(main_symbol.clone()));
    assert_eq!(Scope::lookup(&block_scope, &main_id), Some(main_symbol.clone()));

    assert_eq!(Scope::lookup(&root_scope, &param_id), None);
    assert_eq!(Scope::lookup(&function_scope, &param_id), Some(param_symbol.clone()));
    assert_eq!(Scope::lookup(&block_scope, &param_id), Some(param_symbol.clone()));

    assert_eq!(Scope::lookup(&root_scope, &var_id), None);
    assert_eq!(Scope::lookup(&function_scope, &var_id), None);
    assert_eq!(Scope::lookup(&block_scope, &var_id), Some(var_symbol.clone()));
  }
}
