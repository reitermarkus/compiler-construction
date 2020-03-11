use std::collections::HashMap;

use mc_parser::ast::*;

#[derive(Debug)]
pub enum SymbolType {
  Function(Option<Ty>),
}

#[derive(Debug)]
pub struct SymbolTable(HashMap<Identifier, (SymbolType, Option<Box<SymbolTable>>)>);

pub trait ToSymbolTable {
  fn to_symbol_table(&self) -> SymbolTable;
}

impl ToSymbolTable for Program {
  fn to_symbol_table(&self) -> SymbolTable {
    let mut table = HashMap::new();

    for function in &self.function_declarations {
      table.insert(function.identifier.clone(), (SymbolType::Function(function.ty.clone()), None));
    }

    SymbolTable(table)
  }
}
