pub fn parse() -> i64 {
  2 + 2
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn it_works() {
    assert_eq!(parse(), 4);
  }
}
