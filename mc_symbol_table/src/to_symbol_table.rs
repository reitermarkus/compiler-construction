use mc_parser::ast::*;

use crate::symbol_table::*;

pub trait ToSymbolTable {
  fn to_symbol_table(&self, table: &mut ScopeTable, scope: Scope);
}

impl ToSymbolTable for IfStatement<'_> {
  fn to_symbol_table(&self, table: &mut ScopeTable, scope: Scope) {
    self.block.to_symbol_table(table, scope.append_to_scope("if"));

    match &self.else_block {
      Some(statement) => {
        statement.to_symbol_table(table, scope.append_to_scope("else"));
      }
      None => {}
    }
  }
}

impl ToSymbolTable for WhileStatement<'_> {
  fn to_symbol_table(&self, table: &mut ScopeTable, scope: Scope) {
    self.block.to_symbol_table(table, scope.append_to_scope("while"));
  }
}

#[allow(unused_variables)]
impl ToSymbolTable for ReturnStatement<'_> {
  fn to_symbol_table(&self, table: &mut ScopeTable, scope: Scope) {}
}

impl ToSymbolTable for Declaration {
  fn to_symbol_table(&self, table: &mut ScopeTable, scope: Scope) {
    table.insert(scope.parent().unwrap(), self.identifier.clone(), Symbol::Variable(self.ty.clone(), None));
  }
}

#[allow(unused_variables)]
impl ToSymbolTable for Assignment<'_> {
  fn to_symbol_table(&self, table: &mut ScopeTable, scope: Scope) {}
}

#[allow(unused_variables)]
impl ToSymbolTable for Expression<'_> {
  fn to_symbol_table(&self, table: &mut ScopeTable, scope: Scope) {}
}

impl ToSymbolTable for Statement<'_> {
  fn to_symbol_table(&self, table: &mut ScopeTable, scope: Scope) {
    match self {
      Self::If(statement) => {
        statement.to_symbol_table(table, scope);
      }
      Self::While(statement) => {
        statement.to_symbol_table(table, scope);
      }
      Self::Ret(statement) => {
        statement.to_symbol_table(table, scope);
      }
      Self::Decl(statement) => {
        statement.to_symbol_table(table, scope);
      }
      Self::Assignment(statement) => {
        statement.to_symbol_table(table, scope);
      }
      Self::Expression(statement) => {
        statement.to_symbol_table(table, scope);
      }
      Self::Compound(statement) => {
        statement.to_symbol_table(table, scope);
      }
    }
  }
}

impl ToSymbolTable for CompoundStatement<'_> {
  fn to_symbol_table(&self, table: &mut ScopeTable, scope: Scope) {
    for (i, statement) in self.statements.iter().enumerate() {
      statement.to_symbol_table(table, scope.child(i.to_string()));
    }
  }
}

impl ToSymbolTable for FunctionDeclaration<'_> {
  fn to_symbol_table(&self, table: &mut ScopeTable, scope: Scope) {
    for param in &self.parameters {
      table.insert(scope.clone(), param.identifier.clone(), Symbol::Variable(param.ty.clone(), param.count));
    }
    self.body.to_symbol_table(table, scope);
  }
}

impl ToSymbolTable for Program<'_> {
  fn to_symbol_table(&self, table: &mut ScopeTable, scope: Scope) {
    for function in &self.function_declarations {
      table.insert(scope.clone(), function.identifier.clone(), Symbol::Function(function.ty.clone()));
      function.to_symbol_table(table, scope.child(function.identifier.0.clone()));
    }
  }
}

#[cfg(test)]
mod tests {
  use pest::Span;

  use super::*;

  #[test]
  fn ast_to_symbol_table() {
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

    ast.to_symbol_table(&mut table, root.clone());

    assert_eq!(
      table.lookup(root.clone().child("fib".to_owned()).child("0if".to_owned()), &Identifier::from("x")),
      Some(&Symbol::Variable(Ty::Float, None))
    );
    assert_eq!(
      table.lookup(root.clone().child("fib".to_owned()).child("0else".to_owned()), &Identifier::from("x")),
      Some(&Symbol::Variable(Ty::Int, None))
    );
    assert_eq!(
      table.lookup(root.clone().child("fib".to_owned()).child("0else".to_owned()), &Identifier::from("n")),
      Some(&Symbol::Variable(Ty::Int, None))
    );

    assert_eq!(
      table.lookup(root.clone().child("fib".to_owned()), &Identifier::from("y")),
      Some(&Symbol::Variable(Ty::String, None))
    );
    assert_eq!(table.lookup(root.clone().child("fib".to_owned()), &Identifier::from("x")), None);
  }
}
