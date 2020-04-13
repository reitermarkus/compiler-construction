use format::consts::FORMAT_BOX_CHARS;
use prettytable::{format, Table};

use crate::symbol_table::Scope;

impl Scope {
  pub fn to_pretty_table(&self, table: &mut Table) {
    table.set_format(*FORMAT_BOX_CHARS);
    table.set_titles(row!["scope", "symbol", "type"]);

    for (identifier, symbol) in self.symbols.iter() {
      table.add_row(row![self, identifier, symbol]);
    }

    for child in &self.children {
      (*child.borrow()).to_pretty_table(table);
    }
  }
}

#[cfg(test)]
mod tests {
  use pest::Span;

  use mc_parser::ast::*;

  use crate::add_to_scope::*;
  use crate::symbol_table::Scope;

  use super::*;

  #[test]
  fn format_symbol_table() {
    let ast = Program {
      function_declarations: vec![FunctionDeclaration {
        ty: Some(Ty::Int),
        identifier: Identifier::from("fib"),
        parameters: vec![
          Parameter { ty: Ty::Int, count: None, identifier: Identifier::from("n") },
          Parameter { ty: Ty::Bool, count: None, identifier: Identifier::from("debug") },
        ],
        body: CompoundStatement {
          statements: vec![Statement::Decl(Declaration {
            identifier: Identifier::from("y"),
            count: None,
            ty: Ty::String,
            span: Span::new("", 0, 0).unwrap(),
          })],
          span: Span::new("", 0, 0).unwrap(),
        },
        span: Span::new("", 0, 0).unwrap(),
      }],
      span: Span::new("", 0, 0).unwrap(),
    };

    let scope = Scope::new();
    let _ = ast.add_to_scope(&scope);

    let mut table = Table::new();
    scope.borrow().to_pretty_table(&mut table);
    table.printstd();
  }
}
