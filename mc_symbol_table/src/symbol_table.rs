use std::collections::HashMap;
use std::ops::{Deref, DerefMut};

use mc_parser::ast::*;

#[derive(Default, PartialEq, Eq, Hash, Clone)]
pub struct Scope {
  path: Vec<String>,
}

impl Scope {
  pub fn child(&self, child: String) -> Scope {
    let mut path = self.path.clone();
    path.push(child);
    Self { path }
  }

  pub fn parent(&self) -> Option<Scope> {
    if self.path.len() == 0 {
      None
    } else {
      Some(Self { path: self.path.iter().take(self.path.len() - 1).map(Clone::clone).collect::<Vec<String>>() })
    }
  }
}

struct ScopeIterator {
  scope: Option<Scope>,
}

impl Iterator for ScopeIterator {
  type Item = Scope;

  fn next(&mut self) -> Option<Self::Item> {
    self.scope.replace(self.scope.as_ref()?.parent()?)
  }
}

#[derive(Debug, PartialEq)]
pub enum Symbol {
  Function(Option<Ty>),
  Variable(Ty, Option<usize>),
}

#[derive(Default)]
pub struct SymbolTable {
  table: HashMap<Identifier, Symbol>,
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

#[derive(Default)]
pub struct ScopeTable {
  table: HashMap<Scope, SymbolTable>,
}

impl ScopeTable {
  pub fn insert(&mut self, scope: Scope, identifier: Identifier, symbol: Symbol) {
    match self.table.get_mut(&scope) {
      Some(ref mut symbol_table) => {
        symbol_table.insert(identifier, symbol);
      }
      None => {
        let mut symbol_table = SymbolTable::default();
        symbol_table.insert(identifier, symbol);
        self.table.insert(scope.clone(), symbol_table);
      }
    };
  }

  pub fn lookup(&self, scope: Scope, identifier: &Identifier) -> Option<&Symbol> {
    let mut it = ScopeIterator { scope: Some(scope) };

    while let Some(scope) = it.next() {
      let symbol_table = match self.table.get(&scope) {
        Some(st) => st,
        None => continue,
      };

      if let Some(symbol) = symbol_table.get(identifier) {
        return Some(symbol);
      }
    }

    None
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn insert_and_lookup() {
    let root = Scope::default();

    let mut scope_table = ScopeTable::default();

    let fib_scope = root.child("fib".into());
    let fib_id = Identifier::from("fib");
    let fib_symbol = Symbol::Function(Some(Ty::Int));
    scope_table.insert(fib_scope.clone(), fib_id.clone(), fib_symbol);

    let param_scope = fib_scope.child("in_fib".to_owned());
    let param_id = Identifier::from("x");
    let param_symbol = Symbol::Variable(Ty::Float, None);
    scope_table.insert(param_scope.clone(), param_id.clone(), param_symbol);

    let looked_up_fib = scope_table.lookup(fib_scope, &fib_id);
    let looked_up_x = scope_table.lookup(param_scope, &param_id);

    assert_eq!(looked_up_fib, Some(&Symbol::Function(Some(Ty::Int))));
    assert_eq!(looked_up_x, Some(&Symbol::Variable(Ty::Float, None)));
  }
}
