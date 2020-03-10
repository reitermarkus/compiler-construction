use std::io::{self, stdout};
use std::path::{Path, PathBuf};

use mc_ast_to_dot::mc_ast_to_dot;

#[test]
fn integration_test() -> io::Result<()> {
  let examples = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..").join("examples");

  for example in examples.read_dir()? {
    let example_dir = example?.path();
    let example_file_name = Path::new(example_dir.file_name().unwrap()).with_extension("mc");
    let mc_file = example_dir.join(example_file_name);

    if mc_file.exists() {
      mc_ast_to_dot(mc_file, stdout())?;
    }
  }

  Ok(())
}
