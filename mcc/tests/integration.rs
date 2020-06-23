use std::env;
use std::fs::File;
use std::io;
use std::path::{Path, PathBuf};

#[test]
fn integration_test() -> io::Result<()> {
  let examples = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..").join("examples");

  for example in examples.read_dir()? {
    let example_dir = example?.path();
    let example_file_name = Path::new(example_dir.file_name().unwrap()).with_extension("mc");
    let mc_file = example_dir.join(example_file_name);

    if mc_file.exists() {
      eprintln!("{}", mc_file.display());
      let input = File::open(&mc_file)?;
      let out_file = mc_file.with_extension("bin");
      mcc::cli(input, out_file, "gcc".into(), env::var("MCC_DOCKER_IMAGE").ok(), false)?
    }
  }

  Ok(())
}
