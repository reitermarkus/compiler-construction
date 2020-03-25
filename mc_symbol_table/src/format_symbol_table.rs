use format::consts::FORMAT_BOX_CHARS;
use prettytable::{format, Cell, Row, Table};

use crate::symbol_table::ScopeTable;

impl ScopeTable {
  pub fn to_pretty_tables(&self) -> Vec<Table> {
    let root = self.table.iter().find(|(sc, _)| sc.to_string() == "root").unwrap();

    let mut tables = Vec::new();

    let mut table = Table::new();
    table.set_format(*FORMAT_BOX_CHARS);
    table.set_titles(Row::new(vec![Cell::new("root"), Cell::new(" ")]));

    for (identifier, symbol) in root.1.iter() {
      table.add_row(row![identifier, symbol]);
    }

    tables.push(table);

    tables.extend(
      root
        .1
        .iter()
        .flat_map(|(identifier, _)| {
          let mut childs = self
            .table
            .iter()
            .filter(move |(sc, _)| sc.to_string().contains(&["root", &identifier.to_string()].join(".")))
            .collect::<Vec<_>>();
          childs.sort_by(|(sc_a, _), (sc_b, _)| sc_a.to_string().partial_cmp(&sc_b.to_string()).unwrap());

          childs.into_iter().map(|(scope, sym_table)| {
            let mut table = Table::new();
            table.set_format(*FORMAT_BOX_CHARS);
            table.set_titles(Row::new(vec![Cell::new(&scope.to_string()), Cell::new(" ")]));

            for (identifier, symbol) in sym_table.iter() {
              table.add_row(row![identifier, symbol]);
            }

            table
          })
        })
        .collect::<Vec<_>>(),
    );

    tables
  }
}

#[cfg(test)]
mod tests {
  use mc_parser::ast::*;

  use crate::symbol_table::Scope;
  use crate::to_symbol_table::*;

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
          })],
        },
      }],
    };

    let mut table = ScopeTable::default();
    let root = Scope::default().child("root".to_owned());

    ast.to_symbol_table(&mut table, root);

    let formatted_tables = table.to_pretty_tables();
    for t in formatted_tables {
      t.printstd();
    }
  }
}
