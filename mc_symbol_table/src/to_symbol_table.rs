use std::collections::HashMap;

use mc_parser::ast::*;

#[derive(Debug)]
pub enum SymbolType {
  Function(Option<Ty>),
  Variable(Ty, Option<usize>),
  CompoundStatement(),
  Statement(),
}

#[derive(Debug)]
pub struct SymbolTable(HashMap<Identifier, (SymbolType, Option<Box<SymbolTable>>)>);

pub trait ToSymbolTable {
  fn to_symbol_table(&self) -> SymbolTable;
}

impl ToSymbolTable for IfStatement<'_> {
  fn to_symbol_table(&self) -> SymbolTable {
    let mut table = HashMap::new();

    table
      .insert(Identifier(String::from("if")), (SymbolType::Statement(), Some(Box::new(self.block.to_symbol_table()))));

    match &self.else_block {
      Some(statement) => {
        table.insert(
          Identifier(String::from("else")),
          (SymbolType::Statement(), Some(Box::new(statement.to_symbol_table()))),
        );
      }
      None => {}
    }

    SymbolTable(table)
  }
}

impl ToSymbolTable for WhileStatement<'_> {
  fn to_symbol_table(&self) -> SymbolTable {
    let mut table = HashMap::new();

    table.insert(
      Identifier(String::from("while")),
      (SymbolType::Statement(), Some(Box::new(self.block.to_symbol_table()))),
    );

    SymbolTable(table)
  }
}

impl ToSymbolTable for ReturnStatement<'_> {
  fn to_symbol_table(&self) -> SymbolTable {
    SymbolTable(HashMap::new())
  }
}

impl ToSymbolTable for Declaration {
  fn to_symbol_table(&self) -> SymbolTable {
    let mut table = HashMap::new();

    table.insert(self.identifier.clone(), (SymbolType::Variable(self.ty.clone(), self.count.clone()), None));

    SymbolTable(table)
  }
}

impl ToSymbolTable for Assignment<'_> {
  fn to_symbol_table(&self) -> SymbolTable {
    SymbolTable(HashMap::new())
  }
}

impl ToSymbolTable for Expression<'_> {
  fn to_symbol_table(&self) -> SymbolTable {
    SymbolTable(HashMap::new())
  }
}

impl ToSymbolTable for Statement<'_> {
  fn to_symbol_table(&self) -> SymbolTable {
    match self {
      Self::If(statement) => statement.to_symbol_table(),
      Self::While(statement) => statement.to_symbol_table(),
      Self::Ret(statement) => statement.to_symbol_table(),
      Self::Decl(statement) => statement.to_symbol_table(),
      Self::Assignment(statement) => statement.to_symbol_table(),
      Self::Expression(statement) => statement.to_symbol_table(),
      Self::Compound(statement) => statement.to_symbol_table(),
    }
  }
}

impl ToSymbolTable for CompoundStatement<'_> {
  fn to_symbol_table(&self) -> SymbolTable {
    let mut table = HashMap::new();

    for (i, statement) in self.statements.iter().enumerate() {
      let statement_table = statement.to_symbol_table();
      let mut id = String::from("statement");
      id.push_str(&i.to_string());
      table.insert(Identifier(id), (SymbolType::Statement(), Some(Box::new(statement_table))));
    }

    SymbolTable(table)
  }
}

impl ToSymbolTable for FunctionDeclaration<'_> {
  fn to_symbol_table(&self) -> SymbolTable {
    let mut table = HashMap::new();

    for param in &self.parameters {
      table.insert(param.identifier.clone(), (SymbolType::Variable(param.ty.clone(), param.count.clone()), None));
    }

    let comp_stmt_table = self.body.to_symbol_table();
    table
      .insert(Identifier(String::from("compound")), (SymbolType::CompoundStatement(), Some(Box::new(comp_stmt_table))));

    SymbolTable(table)
  }
}

impl ToSymbolTable for Program<'_> {
  fn to_symbol_table(&self) -> SymbolTable {
    let mut table = HashMap::new();

    for function in &self.function_declarations {
      let function_table = function.to_symbol_table();
      table.insert(
        function.identifier.clone(),
        (SymbolType::Function(function.ty.clone()), Some(Box::new(function_table))),
      );
    }

    SymbolTable(table)
  }
}
