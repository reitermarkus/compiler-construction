use std::cell::RefCell;
use std::rc::Rc;

use mc_parser::ast::*;

use crate::*;

use super::extend_errors;
use crate::semantic_checks::*;

pub trait AddToScope {
  fn add_to_scope(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>>;
}

impl AddToScope for IfStatement<'_> {
  fn add_to_scope(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    let then_scope = Scope::new_child(scope, "if_then");
    let mut res = self.block.add_to_scope(&then_scope);

    if let Some(statement) = &self.else_block {
      let else_scope = Scope::new_child(scope, "if_else");
      extend_errors!(res, statement.add_to_scope(&else_scope));
    }

    res
  }
}

impl AddToScope for WhileStatement<'_> {
  fn add_to_scope(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    let child_scope = Scope::new_child(scope, "while");
    self.block.add_to_scope(&child_scope)
  }
}

#[allow(unused_variables)]
impl AddToScope for ReturnStatement<'_> {
  fn add_to_scope(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    Ok(())
  }
}

impl AddToScope for Declaration<'_> {
  fn add_to_scope(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    let res = self.check_semantics(scope);
    (*scope.borrow_mut()).insert(self.identifier.clone(), Symbol::Variable(self.ty.clone(), self.count));
    res
  }
}

impl AddToScope for Assignment<'_> {
  fn add_to_scope(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    self.check_semantics(scope)
  }
}

impl AddToScope for Expression<'_> {
  fn add_to_scope(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    self.check_semantics(scope)
  }
}

impl AddToScope for Statement<'_> {
  fn add_to_scope(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    match self {
      Self::If(statement) => statement.add_to_scope(scope),
      Self::While(statement) => statement.add_to_scope(scope),
      Self::Ret(statement) => statement.add_to_scope(scope),
      Self::Decl(statement) => statement.add_to_scope(scope),
      Self::Assignment(statement) => statement.add_to_scope(scope),
      Self::Expression(statement) => statement.add_to_scope(scope),
      Self::Compound(statement) => statement.add_to_scope(scope),
    }
  }
}

impl AddToScope for CompoundStatement<'_> {
  fn add_to_scope(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    let child_scope = Scope::new_child(scope, "block");

    let mut res = Ok(());

    for statement in self.statements.iter() {
      extend_errors!(res, statement.add_to_scope(&child_scope));
    }

    res
  }
}

impl AddToScope for FunctionDeclaration<'_> {
  fn add_to_scope(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    let mut res = Ok(());

    for param in &self.parameters {
      extend_errors!(res, param.check_semantics(scope));
      (*scope.borrow_mut()).insert(param.identifier.clone(), Symbol::Variable(param.ty.clone(), param.count));
    }

    extend_errors!(res, self.body.add_to_scope(scope));
    res
  }
}

impl AddToScope for Program<'_> {
  fn add_to_scope(&self, scope: &Rc<RefCell<Scope>>) -> Result<(), Vec<SemanticError<'_>>> {
    let mut res = Ok(());

    for function in &self.function_declarations {
      extend_errors!(res, function.check_semantics(scope));

      (*scope.borrow_mut()).insert(
        function.identifier.clone(),
        Symbol::Function(
          function.ty.clone(),
          function.parameters.iter().map(|p| (p.ty.clone(), p.count)).collect::<Vec<(Ty, Option<usize>)>>(),
        ),
      );
      let child_scope = Scope::new_child(scope, "function");

      extend_errors!(res, function.add_to_scope(&child_scope));
    }

    extend_errors!(res, self.check_semantics(scope));

    res
  }
}

#[cfg(test)]
mod tests {
  use pest::Span;

  use super::*;

  #[test]
  fn ast_add_to_scope() {
    let ast = Program {
      function_declarations: vec![FunctionDeclaration {
        ty: Some(Ty::Int),
        identifier: Identifier::from("fib"),
        parameters: vec![
          Parameter { ty: Ty::Int, count: None, identifier: Identifier::from("n"), span: Span::new("", 0, 0).unwrap() },
          Parameter {
            ty: Ty::Bool,
            count: None,
            identifier: Identifier::from("debug"),
            span: Span::new("", 0, 0).unwrap(),
          },
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
                  span: Span::new("", 0, 0).unwrap(),
                })],
                span: Span::new("", 0, 0).unwrap(),
              }),
              else_block: Some(Statement::Compound(CompoundStatement {
                statements: vec![Statement::Decl(Declaration {
                  identifier: Identifier::from("x"),
                  count: None,
                  ty: Ty::Int,
                  span: Span::new("", 0, 0).unwrap(),
                })],
                span: Span::new("", 0, 0).unwrap(),
              })),
              span: Span::new("", 0, 0).unwrap(),
            })),
            Statement::Decl(Declaration {
              identifier: Identifier::from("y"),
              count: None,
              ty: Ty::String,
              span: Span::new("", 0, 0).unwrap(),
            }),
          ],
          span: Span::new("", 0, 0).unwrap(),
        },
        span: Span::new("", 0, 0).unwrap(),
      }],
      span: Span::new("", 0, 0).unwrap(),
    };

    let scope = Scope::new();
    let _ = ast.add_to_scope(&scope);

    assert_eq!(
      Scope::lookup(&scope.borrow().children[0], &Identifier::from("n")),
      Some(Symbol::Variable(Ty::Int, None))
    );
    assert_eq!(
      Scope::lookup(
        &scope.borrow().children[0].borrow().children[0].borrow().children[0].borrow().children[0],
        &Identifier::from("x")
      ),
      Some(Symbol::Variable(Ty::Float, None))
    );
    assert_eq!(
      Scope::lookup(
        &scope.borrow().children[0].borrow().children[0].borrow().children[1].borrow().children[0],
        &Identifier::from("x")
      ),
      Some(Symbol::Variable(Ty::Int, None))
    );

    assert_eq!(
      Scope::lookup(&scope.borrow().children[0].borrow().children[0], &Identifier::from("y")),
      Some(Symbol::Variable(Ty::String, None))
    );
    assert_eq!(Scope::lookup(&scope, &Identifier::from("x")), None);
    assert_eq!(Scope::lookup(&scope.borrow().children[0].borrow().children[0], &Identifier::from("x")), None);
  }
}
