[![Continous Integration](https://github.com/reitermarkus/compiler-construction/workflows/CI/badge.svg)](https://github.com/reitermarkus/compiler-construction/actions?query=workflow%3ACI)
[![Code Coverage](https://codecov.io/gh/reitermarkus/compiler-construction/branch/master/graph/badge.svg)](https://codecov.io/gh/reitermarkus/compiler-construction)
[![Documentation](https://img.shields.io/badge/docs-master-4d76ae)](https://reitermarkus.github.io/compiler-construction/mc_ast_to_dot/index.html)

# Dependencies

- Rust
- Graphviz
- Ruby & Rake


# Building

```
cargo build
```


# Testing

## Unit/Integration Tests

```
cargo test
```

## Generation of AST Graphs

```
rake graphs
```

## Generation of Symbol Tables

```
rake symbol_tables
```
