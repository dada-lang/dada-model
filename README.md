# dada-model

Formal models for Dada, organized by version.

- [v1](v1/): the original Rust type system, interpreter, tests, and mdBook,
  preserved as an executable reference.
- [v2](v2/md/introduction.md): a draft literate specification of the heap machine.
  Rust book tooling renders mathematical notation, anchor shields, and heap
  diagrams alongside the Lean formalization.

The [published site](https://dada-lang.github.io/dada-model/) opens the v2 draft.
Its [older versions appendix](v2/md/appendices/older-versions.md) explains the
earlier approach and links to the [v1 book](https://dada-lang.github.io/dada-model/v1/).
Chapter paths stay under their version prefix (for example, `v2/operations.html`).

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
The draft covers the machine state, allocation and creation, place operations,
examples, invariants, and unresolved design questions. Ownership preservation for
allocation, creation, and the supported path operations has checked Lean proofs.
Consuming moves retarget dependent leases and preserve their resolved targets.
Broader reference-validity and cleanup claims remain explicitly pending.

Install Lean through `elan`, then run `just test-lean` (or `cd v2/lean && lake build --wfail`)
to check all formalization modules. `v2/lean/lean-toolchain` pins Lean 4.35.0;
`just test` includes this check. The Pages workflow checks the Lean project before
building the published books.

The v2 preprocessor is in `v2/mdbook-dada`. Run `cargo test --workspace` from
`v2/` to test it. See the book’s specification-system chapter for authoring syntax.
