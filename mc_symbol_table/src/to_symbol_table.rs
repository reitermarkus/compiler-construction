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
      .insert(Identifier::from("if"), (SymbolType::Statement(), Some(Box::new(self.block.to_symbol_table()))));

    match &self.else_block {
      Some(statement) => {
        table.insert(
          Identifier::from("else"),
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
      Identifier::from("while"),
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

    for statement in &self.statements {
      let statement_map = statement.to_symbol_table().0;
      table.extend(statement_map);
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
      .insert(Identifier::from("compound"), (SymbolType::CompoundStatement(), Some(Box::new(comp_stmt_table))));

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
        parameters: vec![Parameter { ty: Ty::Int, count: None, identifier: Identifier::from("n") }],
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
              block: Statement::Ret(ReturnStatement {
                expression: Some(Expression::Variable {
                  identifier: Identifier::from("n"),
                  index_expression: None,
                  span: Span::new("", 0, 0).unwrap(),
                }),
              }),
              else_block: None,
            })),
            Statement::Ret(ReturnStatement {
              expression: Some(Expression::Binary {
                op: BinaryOp::Plus,
                lhs: Box::new(Expression::FunctionCall {
                  identifier: Identifier::from("fib"),
                  arguments: vec![Expression::Binary {
                    op: BinaryOp::Minus,
                    lhs: Box::new(Expression::Variable {
                      identifier: Identifier::from("n"),
                      index_expression: None,
                      span: Span::new("", 0, 0).unwrap(),
                    }),
                    rhs: Box::new(Expression::Literal { literal: Literal::Int(1), span: Span::new("", 0, 0).unwrap() }),
                    span: Span::new("", 0, 0).unwrap(),
                  }],
                  span: Span::new("", 0, 0).unwrap(),
                }),
                rhs: Box::new(Expression::FunctionCall {
                  identifier: Identifier::from("fib"),
                  arguments: vec![Expression::Binary {
                    op: BinaryOp::Minus,
                    lhs: Box::new(Expression::Variable {
                      identifier: Identifier::from("n"),
                      index_expression: None,
                      span: Span::new("", 0, 0).unwrap(),
                    }),
                    rhs: Box::new(Expression::Literal { literal: Literal::Int(2), span: Span::new("", 0, 0).unwrap() }),
                    span: Span::new("", 0, 0).unwrap(),
                  }],
                  span: Span::new("", 0, 0).unwrap(),
                }),
                span: Span::new("", 0, 0).unwrap(),
              }),
            }),
          ],
        },
      }],
    };

    let symbol_table = ast.to_symbol_table();

    eprintln!("Table:\n{:#?}", symbol_table);
  }
}