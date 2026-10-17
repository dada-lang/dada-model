# dada-model

The original Rust model and mdBook are preserved in `v1/` as a working reference.
Read `v1/AGENTS.md` before changing that model. Its paths and commands are relative
to `v1/`. The v2 design draft is an mdBook in `v2/md/`, configured by `v2/book.toml`.
The book separates repository methods and specification-system requirements
(`v2/md/repo/`), Dada language goals (`v2/md/dada/`), and the heap model.
`v2/mdbook-dada` is a Rust mdBook preprocessor in the v2 Cargo workspace.
It indexes MyST-style `{anchor}` and `{anchor-ref}` roles and renders `{heap}`
fenced directives as SVG from declarative facts, with a Rendered/Facts selector. It parses `{grammar}` directives as descriptive
algebraic data types with named constructor fields, validates their syntax, and renders compact grammar equations. The parser
and renderer live in `v2/mdbook-dada/src/grammar.rs`; this is not a Lean type checker. The syntax is documented in
`v2/md/repo/spec-system.md`; theme CSS lives in `v2/theme/dada.css`.
`{informational}` at the start of a paragraph labels nonnormative commentary;
`{example}` similarly labels concrete examples.
`src/routing.rs` routes diagram edges orthogonally around boxes.
Unique leases store a runtime `Place`; access paths resolve to places.
Anchor IDs must be globally unique, and unresolved references fail the build.
Heap facts use `lease(node.field)` (or an array slot) for unique edge targets;
owned, showned, and shlease references target objects.
Graph structure checks do not establish heap invariants. Initial Lean state declarations live in `v2/lean/Heap.lean`; `{lean.type}`
is a fenced directive selecting one or more file:name lines, with a shared
Grammar/Lean selector. It extracts them using `src/lean.rs` and the `lean-source` book setting.
The compact view displays List/Array applications with sequence overbars and
FiniteMap applications with finite-map arrows. The book bundles the KaTeX main
font and license under `v2/md/fonts/` for mathematical typography.
The declarations compile with Lean 4.35.0. No transitions, proofs,
claim-content extraction, or review/evidence verification exist yet. Read `v2/md/questions.md` before formalizing unresolved semantics.
Keep candidate claims distinct from established proofs and executable examples.

## Build and test

- `just test` runs the v1 Cargo and mdBook example tests plus v2 preprocessor tests.
- From `v1/`, run `cargo test --all --workspace` and `mdbook build`.
- From `v2/`, run `cargo fmt --all`, `cargo clippy --workspace --all-targets -- -D warnings`,
  and `cargo test --workspace` for changes to the Rust tooling.
- `just book-v2` builds the v2 draft; `cd v2 && mdbook serve` previews it.
- The Rust and book dependency tools are still required for these commands.

## Publishing

GitHub Actions workflows remain in `.github/workflows/`. Pages builds the v1
book and uploads a site containing `index.html` from `pages/` and the complete
book under `v1/`, preserving chapter paths beneath that prefix. The v2 draft
is published under `v2/`. Keep generated
source links pointed at the repository's `v1/` directory.

Keep this file and `v1/AGENTS.md` current when changing the repository layout.
