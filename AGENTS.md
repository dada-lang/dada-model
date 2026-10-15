# dada-model

The original Rust model and mdBook are preserved in `v1/` as a working reference.
Read `v1/AGENTS.md` before changing that model. Its paths and commands are relative
to `v1/`. A future v2 will develop the literate specification and Lean model;
there is no v2 implementation yet.

## Build and test

- `just test` runs the v1 Cargo tests and mdBook example tests.
- From `v1/`, run `cargo test --all --workspace` and `mdbook build`.
- The Rust and book dependency tools are still required for these commands.

## Publishing

GitHub Actions workflows remain in `.github/workflows/`. Pages builds the v1
book and uploads a site containing `index.html` from `pages/` and the complete
book under `v1/`, preserving chapter paths beneath that prefix. Keep generated
source links pointed at the repository's `v1/` directory.

Keep this file and `v1/AGENTS.md` current when changing the repository layout.
