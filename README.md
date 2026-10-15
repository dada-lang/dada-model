# dada-model

Formal models for Dada, organized by version.

- [v1](v1/): the original Rust type system, interpreter, tests, and mdBook,
  preserved as an executable reference.
- A new literate specification and Lean model are planned for v2.

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
