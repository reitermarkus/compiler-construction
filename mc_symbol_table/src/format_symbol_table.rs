use prettytable::{format, Cell, Row, Table};
use format::consts::FORMAT_NO_LINESEP_WITH_TITLE;

use crate::symbol_table::*;

impl ScopeTable {
  pub fn to_pretty_tables(&self) -> Vec<Table> {
    self.table.iter().map(|(scope, sym_table)| sym_table.to_pretty_table(scope.clone())).collect()
  }
}

impl SymbolTable {
  pub fn to_pretty_table(&self, scope: Scope) -> Table {
    let mut table = Table::new();
    table.set_format(*FORMAT_NO_LINESEP_WITH_TITLE);

    table.set_titles(Row::new(vec![Cell::new(&scope.to_string()), Cell::new(" ")]));

    for (identifier, symbol) in self.table.iter() {
      table.add_row(row![identifier, symbol]);
    }

    table
  }
}

#[cfg(test)]
mod tests {
  use crate::to_symbol_table::*;
  use mc_parser::ast::*;
  use pest::Span;

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
          statements: vec![
            Statement::If(Box::new(IfStatement {
              condition: Expression::Binary {
                op: BinaryOp::Lt,
                lhs: Box::new(Expression::Variable {
                  identifier: Identifier::from("n"),
                  index_expression: None,
                  span: Span::new("", 0, 0).unwrap(),
                }),
                rhs: Box::new(Expression::Literal { literal: Literal::Int(2), span: Span::new("", 0, 0).unwrap() }),
                span: Span::new("", 0, 0).unwrap(),
              },
              block: Statement::Compound(CompoundStatement {
                statements: vec![Statement::Decl(Declaration {
                  identifier: Identifier::from("x"),
                  count: None,
                  ty: Ty::Float,
                })],
              }),
              else_block: Some(Statement::Compound(CompoundStatement {
                statements: vec![Statement::Decl(Declaration {
                  identifier: Identifier::from("x"),
                  count: None,
                  ty: Ty::Int,
                })],
              })),
            })),
            Statement::Decl(Declaration { identifier: Identifier::from("y"), count: None, ty: Ty::String }),
          ],
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
