[![Continous Integration](https://github.com/reitermarkus/compiler-construction/workflows/CI/badge.svg)](https://github.com/reitermarkus/compiler-construction/actions?query=workflow%3ACI)
[![Code Coverage](https://codecov.io/gh/reitermarkus/compiler-construction/branch/master/graph/badge.svg)](https://codecov.io/gh/reitermarkus/compiler-construction)
[![Documentation](https://img.shields.io/badge/docs-master-4d76ae)](https://reitermarkus.github.io/compiler-construction/mc_ast_to_dot/index.html)

# Dependencies

- Rust (>= 1.44)
- Graphviz
- Ruby (>= 2.6) & Rake


# Building

```
cargo build [--release]
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
rake symbol_table
```

## Generation of Intermediate Representation

```
rake ir
```

## Generation of Context Flow Graphs

```
rake cfg
```

## Generation of Assembly Code

```
rake asm
```

## Example error output

```
rake failures
```


# Known Issues
