use std::io::{self, Read, Write};

pub fn cli(mut input: impl Read, mut output: impl Write) -> io::Result<()> {
  let mut contents = String::new();
  input.read_to_string(&mut contents)?;

  let ast = mc_parser::parse(&contents).unwrap();
  let scope = crate::check_semantics(&ast).unwrap();
  let table = crate::symbol_table(&scope.borrow());

  table.print(&mut output).map(|_| ())
}
