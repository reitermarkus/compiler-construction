use std::io::{self, Read, Write};
use std::cell::RefCell;
use std::rc::Rc;

use mc_parser::ast::Program;



pub fn cli(mut input: impl Read, mut output: impl Write) -> Result<(), i32> {
  fn input_to_string(mut input: impl Read) -> Result<String, i32> {
    let mut contents = String::new();
    match input.read_to_string(&mut contents) {
      Ok(_) => Ok(contents),
      Err(err) => {
        eprintln!("Error reading input file: {}", err);
        Err(1)
      }
    }
  }

  fn string_to_ast(contents: &str) -> Result<Program<'_>, i32> {
    match mc_parser::parse(contents) {
      Ok(program) => Ok(program),
      Err(err) => {
        eprintln!("Error parsing input file: {:?}", err);
        Err(1)
      }
    }
  }

  let contents = input_to_string(input)?;
  let ast = string_to_ast(&contents)?;
  match crate::check_semantics(&ast).map(|scope| crate::symbol_table(&scope.borrow())) {
    Ok(table) => {
      match table.print(&mut output) {
        Ok(_) => Ok(()),
        Err(err) => {
          eprintln!("Error printing symbol table: {}", err);
          Err(1)
        }
      }
    },
    Err(err) => {
      eprintln!("{}", err);
      Err(1)
    }
  }
}
