use std::fmt;

#[derive(Debug)]
pub enum Ty {
  Bool,
  Int,
  Float,
  String,
}

impl fmt::Display for Ty {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Bool => "bool",
      Self::Int => "int",
      Self::Float => "float",
      Self::String => "string",
    }
    .fmt(f)
  }
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

impl fmt::Display for UnaryOp {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Minus => "-",
      Self::Not => "!",
    }
    .fmt(f)
  }
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

impl fmt::Display for BinaryOp {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Plus => "+",
      Self::Minus => "-",
      Self::Times => "*",
      Self::Divide => "/",
      Self::Eq => "==",
      Self::Neq => "!=",
      Self::Lte => "<=",
      Self::Lt => "<",
      Self::Gte => ">=",
      Self::Gt => ">",
      Self::Land => "&&",
      Self::Lor => "||",
    }
    .fmt(f)
  }
}

#[derive(Debug)]
pub enum Expression {
  Literal(Literal),
  Variable {
    identifier: String,
    index_expression: Option<Box<Expression>>,
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
pub struct Parameter {
  pub ty: String,
  pub identifier: String,
}

#[derive(Debug)]
pub struct Assignment {
  pub identifier: String,
  pub index_expression: Option<Expression>,
  pub rvalue: Expression,
}

#[derive(Debug)]
pub struct Declaration {
  pub ty: Ty,
  pub count: Option<usize>,
  pub identifier: String,
}

#[derive(Debug)]
pub struct IfStatement {
  pub condition: Expression,
  pub block: Statement,
  pub else_block: Option<Statement>,
}

#[derive(Debug)]
pub struct WhileStatement {
  pub condition: Expression,
  pub block: Statement,
}

#[derive(Debug)]
pub struct ReturnStatement {
  pub expression: Expression,
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
  pub statements: Vec<Statement>,
}

#[derive(Debug)]
pub struct FunctionDeclaration {
  pub ty: Option<String>,
  pub identifier: String,
  pub parameters: Vec<Parameter>,
  pub body: CompoundStatement,
}

#[derive(Debug)]
pub struct Program {
  pub function_declarations: Vec<FunctionDeclaration>,
}
