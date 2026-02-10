# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build and Test Commands

```bash
# Run all tests
cargo test --all --all-targets

# Run a single test
cargo test <test_name>

# Run tests in a specific module
cargo test type_system::tests::subtyping
```

## Project Overview

dada-model is a formal model for the Dada programming language, implemented using [formality-core](https://rust-lang.github.io/a-mir-formality/formality_core.html) from a-mir-formality. It defines the type system and type checking rules for Dada's permission-based ownership model.

## Architecture

### Core Modules

- **`src/grammar.rs`**: Defines the AST/grammar using formality-core's `#[term]` macro. Contains:
  - `Program`, `ClassDecl`, `MethodDecl` - program structure
  - `Ty`, `Perm` - types and permissions
  - `Expr`, `Statement`, `Place` - expressions and control flow
  - `Predicate` - type predicates for constraints

- **`src/type_system.rs`**: Entry point for type checking. Orchestrates checking of programs and declarations.

- **`src/type_system/env.rs`**: The `Env` struct tracks typing context including:
  - Program reference, universe for universal variables
  - Local variable types, predicate assumptions
  - Methods for managing scope and variable bindings

### Key Concepts

**Permissions**: Dada uses a permission system instead of Rust's borrow checker:
- `given` - owned, unique (like Rust's ownership)
- `shared` - owned, shared (like `Rc`)
- `ref[places]` - borrowed reference
- `mut[places]` - borrowed mutable reference
- `moved[places]` - moved permission

**Class Predicates** (in order):
- `guard class` - affine types with destructors
- `class` (default) - mutable fields, can be shared with `.share`
- `struct` (`shared class`) - value types, always shared/copyable

**Judgment Functions**: The type system uses formality-core's `judgment_fn!` macro to define inference rules. See `src/type_system/subtypes.rs` for subtyping rules.

### Test Organization

Tests are in `src/type_system/tests/` as Rust unit tests using `expect_test` for snapshot testing. Tests use the `term()` macro to parse Dada code strings and `check_program()` to type-check them.

## Documentation

The `book/` directory contains mdBook documentation explaining the type system design. Build with `mdbook build book/`.
