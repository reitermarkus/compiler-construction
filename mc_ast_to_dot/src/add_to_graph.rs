use std::string::ToString;

use petgraph::{graph::NodeIndex, Directed, Graph};

use mc_parser::ast::*;

pub type AstGraph = Graph<String, String, Directed>;

pub trait AddToGraph {
  fn add_to_graph(&self, g: &mut AstGraph) -> NodeIndex;
}

impl AddToGraph for Literal {
  fn add_to_graph(&self, g: &mut AstGraph) -> NodeIndex {
    g.add_node(match self {
      Self::Bool(value) => value.to_string(),
      Self::Int(value) => value.to_string(),
      Self::Float(value) => value.to_string(),
      Self::String(value) => format!("{:?}", value),
    })
  }
}

impl AddToGraph for Expression {
  fn add_to_graph(&self, g: &mut AstGraph) -> NodeIndex {
    match self {
      Self::Literal(lit) => lit.add_to_graph(g),
      Self::Variable { identifier, index_expression } => {
        let v = g.add_node(identifier.to_string());

        if let Some(index_expression) = index_expression {
          let e = index_expression.add_to_graph(g);
          g.add_edge(v, e, "index".into());
        }

        v
      }
      Self::FunctionCall { identifier, arguments } => {
        let f = g.add_node(format!("{}()", identifier));

        for (i, argument) in arguments.iter().enumerate() {
          let a = argument.add_to_graph(g);
          g.add_edge(f, a, i.to_string());
        }

        f
      }
      Self::Unary { op, expression } => {
        let u = g.add_node(op.to_string());

        let e = expression.add_to_graph(g);
        g.add_edge(u, e, "".into());

        u
      }
      Self::Binary { op, lhs, rhs } => {
        let b = g.add_node(op.to_string());

        let l = lhs.add_to_graph(g);
        g.add_edge(b, l, "left".into());

        let r = rhs.add_to_graph(g);
        g.add_edge(b, r, "right".into());

        b
      }
    }
  }
}

impl AddToGraph for IfStatement {
  fn add_to_graph(&self, g: &mut AstGraph) -> NodeIndex {
    let i = g.add_node("if".into());

    let cond = self.condition.add_to_graph(g);
    g.add_edge(i, cond, "cond".into());

    let on_true = self.block.add_to_graph(g);
    g.add_edge(i, on_true, "on_true".into());

    if let Some(else_block) = &self.else_block {
      let on_false = else_block.add_to_graph(g);
      g.add_edge(i, on_false, "on_false".into());
    }

    i
  }
}

impl AddToGraph for WhileStatement {
  fn add_to_graph(&self, g: &mut AstGraph) -> NodeIndex {
    let w = g.add_node("while".into());

    let cond = self.condition.add_to_graph(g);
    g.add_edge(w, cond, "cond".into());

    let on_true = self.block.add_to_graph(g);
    g.add_edge(w, on_true, "on_true".into());

    w
  }
}

impl AddToGraph for ReturnStatement {
  fn add_to_graph(&self, g: &mut AstGraph) -> NodeIndex {
    let r = g.add_node("return".into());

    let expression = self.expression.add_to_graph(g);
    g.add_edge(r, expression, "expr".into());

    r
  }
}

impl AddToGraph for Declaration {
  fn add_to_graph(&self, g: &mut AstGraph) -> NodeIndex {
    let index = self.count.map(|c| format!("[{}]", c)).unwrap_or_else(|| "".into());
    g.add_node(format!("{}{} {}", self.ty, index, self.identifier))
  }
}

impl AddToGraph for Assignment {
  fn add_to_graph(&self, g: &mut AstGraph) -> NodeIndex {
    let a = if let Some(index_expression) = &self.index_expression {
      let a = g.add_node(format!("{}[] =", self.identifier));

      let i = index_expression.add_to_graph(g);
      g.add_edge(a, i, "index".into());

      a
    } else {
      g.add_node(format!("{} =", self.identifier))
    };

    let e = self.rvalue.add_to_graph(g);
    g.add_edge(a, e, "expr".into());

    a
  }
}

impl AddToGraph for Statement {
  fn add_to_graph(&self, g: &mut AstGraph) -> NodeIndex {
    match self {
      Self::If(statement) => statement.add_to_graph(g),
      Self::While(statement) => statement.add_to_graph(g),
      Self::Ret(statement) => statement.add_to_graph(g),
      Self::Decl(statement) => statement.add_to_graph(g),
      Self::Assignment(statement) => statement.add_to_graph(g),
      Self::Expression(statement) => statement.add_to_graph(g),
      Self::Compound(statement) => statement.add_to_graph(g),
    }
  }
}

impl AddToGraph for CompoundStatement {
  fn add_to_graph(&self, g: &mut AstGraph) -> NodeIndex {
    let b = g.add_node("{ }".into());

    for (i, statement) in self.statements.iter().enumerate() {
      let s = statement.add_to_graph(g);
      g.add_edge(b, s, i.to_string());
    }

    b
  }
}

impl AddToGraph for FunctionDeclaration {
  fn add_to_graph(&self, g: &mut AstGraph) -> NodeIndex {
    let parameters =
      self.parameters.iter().map(|p| format!("{} {}", p.ty, p.identifier)).collect::<Vec<_>>().join(", ");
    let label = format!(
      "{} {}({})",
      self.ty.as_ref().map(ToString::to_string).unwrap_or_else(|| "void".to_string()),
      self.identifier,
      parameters
    );
    let f = g.add_node(label);

    let b = self.body.add_to_graph(g);
    g.add_edge(f, b, "body".into());

    f
  }
}

impl AddToGraph for Program {
  fn add_to_graph(&self, g: &mut AstGraph) -> NodeIndex {
    let p = g.add_node("program".into());

    for function in &self.function_declarations {
      let f = function.add_to_graph(g);
      g.add_edge(p, f, "function".into());
    }

    p
  }
}

#[cfg(test)]
mod tests {
  use indoc::indoc;
  use petgraph::dot::{Config, Dot};
  use pretty_assertions::assert_eq;
  use unindent::unindent;

  use super::*;

  #[test]
  fn ast_to_dot() {
    let ast = Program {
      function_declarations: vec![FunctionDeclaration {
        ty: Some(Ty::Int),
        identifier: Identifier(String::from("fib")),
        parameters: vec![Parameter { ty: Ty::Int, identifier: Identifier("n".to_string()) }],
        body: CompoundStatement {
          statements: vec![
            Statement::If(Box::new(IfStatement {
              condition: Expression::Binary {
                op: BinaryOp::Lt,
                lhs: Box::new(Expression::Variable { identifier: Identifier("n".to_string()), index_expression: None }),
                rhs: Box::new(Expression::Literal(Literal::Int(2))),
              },
              block: Statement::Ret(ReturnStatement {
                expression: Expression::Variable { identifier: Identifier("n".to_string()), index_expression: None },
              }),
              else_block: None,
            })),
            Statement::Ret(ReturnStatement {
              expression: Expression::Binary {
                op: BinaryOp::Plus,
                lhs: Box::new(Expression::FunctionCall {
                  identifier: Identifier("fib".to_string()),
                  arguments: vec![Expression::Binary {
                    op: BinaryOp::Minus,
                    lhs: Box::new(Expression::Variable {
                      identifier: Identifier("n".to_string()),
                      index_expression: None,
                    }),
                    rhs: Box::new(Expression::Literal(Literal::Int(1))),
                  }],
                }),
                rhs: Box::new(Expression::FunctionCall {
                  identifier: Identifier("fib".to_string()),
                  arguments: vec![Expression::Binary {
                    op: BinaryOp::Minus,
                    lhs: Box::new(Expression::Variable {
                      identifier: Identifier("n".to_string()),
                      index_expression: None,
                    }),
                    rhs: Box::new(Expression::Literal(Literal::Int(2))),
                  }],
                }),
              },
            }),
          ],
        },
      }],
    };

    let mut graph = AstGraph::new();
    ast.add_to_graph(&mut graph);

    let dot = Dot::with_config(&graph, &[Config::GraphContentOnly]);

    assert_eq!(
      unindent(&dot.to_string().trim()),
      indoc!(
        r##"
          0 [label="program"]
          1 [label="int fib(int n)"]
          2 [label="{ }"]
          3 [label="if"]
          4 [label="<"]
          5 [label="n"]
          6 [label="2"]
          7 [label="return"]
          8 [label="n"]
          9 [label="return"]
          10 [label="+"]
          11 [label="fib()"]
          12 [label="-"]
          13 [label="n"]
          14 [label="1"]
          15 [label="fib()"]
          16 [label="-"]
          17 [label="n"]
          18 [label="2"]
          4 -> 5 [label="left"]
          4 -> 6 [label="right"]
          3 -> 4 [label="cond"]
          7 -> 8 [label="expr"]
          3 -> 7 [label="on_true"]
          2 -> 3 [label="0"]
          12 -> 13 [label="left"]
          12 -> 14 [label="right"]
          11 -> 12 [label="0"]
          10 -> 11 [label="left"]
          16 -> 17 [label="left"]
          16 -> 18 [label="right"]
          15 -> 16 [label="0"]
          10 -> 15 [label="right"]
          9 -> 10 [label="expr"]
          2 -> 9 [label="1"]
          1 -> 2 [label="body"]
          0 -> 1 [label="function"]
        "##
      )
      .trim(),
    )
  }
}
