#!/bin/sh

for mc in examples/*/*.mc; do
  cargo run --bin mc_ast_to_dot -- "${mc}"
done
