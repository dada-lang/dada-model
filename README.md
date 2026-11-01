# dada-model

Formal models for Dada, organized by version.

- [v1](v1/): the original Rust type system, interpreter, tests, and mdBook,
  preserved as an executable reference.
- [v2](v2/md/dada/introduction.md): a literate specification built in layers,
  starting with unique ownership (Given) and extending it with shared ownership
  (Shared). The book pairs definitions, theorems, and examples with named Lean
  declarations and records reviews of their correspondence.

The [published site](https://dada-lang.github.io/dada-model/) opens the v2 draft.
Its [older versions appendix](v2/md/appendices/older-versions.md) explains the
earlier approach and links to the [v1 book](https://dada-lang.github.io/dada-model/v1/).
Chapter paths stay under their version prefix (for example, `v2/given.html`).

Run `just book-tools` to install the pinned mdBook tools, then `just site` to
build the complete site into `_site/`. See [publishing and local preview](pages/README.md)
for dependencies and GitHub Pages setup.

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
The book groups operational semantics and type-system chapters under Given and
Shared, followed by CFlow. Given's type-system chapter is a draft; Shared's type
system and CFlow are coming. Given has formalized signed views, typing rules,
and an unpacking extension, with checked examples. General normalization
properties and static progress/preservation proofs are still pending.
The existing operational models
have syntax, transitions, examples, and checked heap invariants; a Lean proof
establishes that Shared preserves the behavior of the Given fragment.

Install Lean through `elan`, then run `just test-lean` (or `cd v2/lean && lake build --wfail`)
to check all formalization modules. `v2/lean/lean-toolchain` pins Lean 4.35.0;
`just test` includes this check. The Pages workflow checks the Lean project before
building the published books.

The v2 preprocessor is in `v2/mdbook-dada`. Run `cargo test --workspace` from
`v2/` to test it and validate the review evidence. See the book’s contributor
guides for authoring syntax and the review workflow.
