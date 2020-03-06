#![deny(missing_debug_implementations, rust_2018_idioms)]

#[derive(Debug)]
pub enum Ty {
  Bool,
  Int,
  Float,
  String,
}

#[derive(Debug)]
pub enum Literal {
  Bool(bool),
  Int(i64),
  Float(f64),
  String(String),
}

#[derive(Debug)]
pub enum UnaryOp {
  Minus,
  Not,
}

#[derive(Debug)]
pub enum BinaryOp {
  Plus,
  Minus,
  Times,
  Divide,
  Eq,
  Neq,
  Lte,
  Lt,
  Gte,
  Gt,
  Land,
  Lor,
}

#[derive(Debug)]
pub enum Expression {
  Literal(Literal),
  Variable {
    identifier: String,
    index: Option<usize>,
  },
  FunctionCall {
    identifier: String,
    arguments: Vec<Expression>,
  },
  Unary {
    op: UnaryOp,
    expression: Box<Expression>,
  },
  Binary {
    op: BinaryOp,
    lhs: Box<Expression>,
    rhs: Box<Expression>,
  },
}

#[derive(Debug)]
pub struct Parameter;

#[derive(Debug)]
pub struct Assignment {
  identifier: String,
  index_expression: Option<Expression>,
  rvalue: Expression,
}

#[derive(Debug)]
pub struct Declaration {
  ty: Ty,
  count: Option<usize>,
  identifier: String,
}

#[derive(Debug)]
pub struct IfStatement {
  condition: Expression,
  block: Statement,
  else_block: Option<Statement>,
}

#[derive(Debug)]
pub struct WhileStatement {
  condition: Expression,
  block: Statement,
}

#[derive(Debug)]
pub struct ReturnStatement {
  expression: Expression,
}

#[derive(Debug)]
pub enum Statement {
  If(Box<IfStatement>),
  While(Box<WhileStatement>),
  Ret(ReturnStatement),
  Decl(Declaration),
  Assignment(Assignment),
  Expression(Expression),
  Compound(CompoundStatement),
}

#[derive(Debug)]
pub struct CompoundStatement {
  statements: Vec<Statement>,
}

#[derive(Debug)]
pub struct FunctionDeclaration {
  ty: Option<String>,
  identifier: String,
  parameters: Vec<Parameter>,
  body: CompoundStatement,
}

#[derive(Debug)]
pub struct Program(Vec<FunctionDeclaration>);
