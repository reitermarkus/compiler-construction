use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use mc_symbol_table::mc_symbol_table;

#[test]
fn integration_test() -> io::Result<()> {
  let examples = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..").join("examples");

  for example in examples.read_dir()? {
    let example_dir = example?.path();
    let example_file_name = Path::new(example_dir.file_name().unwrap()).with_extension("mc");
    let mc_file = example_dir.join(example_file_name);

    if mc_file.exists() {
      eprintln!("{}", mc_file.display());
      let contents = fs::read_to_string(mc_file)?;
      mc_symbol_table(&contents).expect("failed to generate symbol table");
    }
  }

  Ok(())
}
