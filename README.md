# dada-model

Formal models for Dada, organized by version.

- [v1](v1/): the original Rust type system, interpreter, tests, and mdBook,
  preserved as an executable reference.
- [v2](v2/md/introduction.md): a draft literate specification of the heap machine.
  Rust book tooling renders anchor shields and fact-based heap diagrams;
  Lean formalization and evidence review will follow.

The published [v1 book](https://dada-lang.github.io/dada-model/v1/) retains its
chapter paths under `v1/` (for example, `v1/intro.html`).

## Working with v1

Run `just test` from this directory, or work directly in `v1/`:

```sh
cd v1
cargo test --all --workspace
mdbook build
```

See [v1 instructions](v1/AGENTS.md) and [work in progress](v1/WIP.md).

## Reading the v2 draft

Run `just book-v2` to build it, or `cd v2 && mdbook serve` for a local preview.
The draft covers the machine state, operations, examples, candidate invariants,
and unresolved design questions. Its examples and claims are not yet verified.

The v2 preprocessor is in `v2/mdbook-dada`. Run `cargo test --workspace` from
`v2/` to test it. See the book’s specification-system chapter for authoring syntax.
