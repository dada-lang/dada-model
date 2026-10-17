# dada-model

The original Rust model and mdBook are preserved in `v1/` as a working reference.
Read `v1/AGENTS.md` before changing that model. Its paths and commands are relative
to `v1/`. The v2 design draft is an mdBook in `v2/md/`, configured by `v2/book.toml`.
The book separates repository methods and specification-system requirements
(`v2/md/repo/`), Dada language goals (`v2/md/dada/`), and the heap model.
`v2/mdbook-dada` is a Rust mdBook preprocessor in the v2 Cargo workspace.
It indexes MyST-style `{anchor}` and `{anchor-ref}` roles and renders `{heap}`
fenced directives as SVG from declarative facts, with a Rendered/Facts selector.
Fenced `{grammar} File:Type ...`, `{judgment} File:Name`, and
`{rule} File:Judgment.constructor` directives pair authored LaTeX bodies with cited
Lean declarations or cases through a Rendered/Lean selector. Grammar blocks accept
one or more whitespace-separated citations on the opening line; judgment and rule
blocks take one. The Markdown mathematics and notation explanations stand on
their own, with Lean as an associated formalization. `src/lean.rs` handles textual
source selection and HTML, not mathematical derivation or Lean elaboration. The
`lean-source` book setting locates Lean files. MathJax is loaded from a CDN.
The former `{lean.type}`, `{lean.judgment}`, and `{lean.rule}` directives are
rejected with migration diagnostics. The old grammar DSL/parser and automatic
Lean-to-LaTeX translator have been removed; Lean notation comments have no
rendering effect. The build checks citations and supported declaration kinds,
not correspondence between mathematics and Lean. Review records and scripts
providing correspondence evidence remain future work. The syntax, notation
conventions, and review obligation are documented in `v2/md/repo/spec-system.md`;
theme CSS lives in `v2/theme/dada.css`.
`{informational}` at the start of a paragraph labels nonnormative commentary;
`{example}` similarly labels concrete examples.
`src/routing.rs` routes diagram edges orthogonally around boxes.
Unique leases store a runtime `Place`; access paths resolve to places.
Anchor IDs must be globally unique, and unresolved references fail the build.
Heap facts group the live variable store with `vars = variables()` and slots such
as `vars.p`; this is a diagram grouping, not a frame identity. Heap facts use
`lease(node.field)` (or an array slot) for unique edge targets;
owned, showned, and shlease references target objects.
Graph structure checks do not establish heap invariants. Initial Lean state
declarations live in `v2/lean/Heap.lean`. The heap chapters use a shared vocabulary
of short mathematical variables; overbars denote finite ordered sequences and
partial-map arrows denote finite maps. Primitive values are an implicit common
parameter. The book explains representation abstractions and hidden proof terms
while preserving their conditions; exact representations remain available in Lean.
The declarations compile with Lean 4.35.0. Heap state contains an object map and
one map of all live variable slots, including temporaries and suspended callers'
variables. `VariableId` identifies a runtime binding lifetime separately from its
source name; `Place.variable` selects its slot. There are no heap frames.
The first `Operation`/`Step` slice allocates absent variables as uninitialized and
deallocates only uninitialized slots, with checked lemmas about these local
effects. The future execution semantics will α-rename bindings to fresh identities
and manage scope and cleanup. Heap allocation checks absence only from the live
map, so freshness across completed lifetimes remains an execution-layer obligation.
Other transitions, ownership proofs, claim-content extraction,
and review/evidence verification remain unimplemented. Read `v2/md/questions.md` before formalizing unresolved semantics.
Keep candidate claims distinct from established proofs and executable examples.

## Build and test

- `just test` runs the v1 Cargo and mdBook example tests plus v2 preprocessor tests.
- From `v1/`, run `cargo test --all --workspace` and `mdbook build`.
- From `v2/`, run `cargo fmt --all`, `cargo clippy --workspace --all-targets -- -D warnings`,
  and `cargo test --workspace` for changes to the Rust tooling.
- `just book-v2` builds the v2 draft; `cd v2 && mdbook serve` previews it.
- `just book-tools` installs pinned mdBook 0.5.4 and mdbook-mermaid 0.17.1;
  the custom preprocessors are built from the two Cargo workspaces.
- `just site` builds both books and the root redirect into the ignored `_site/`
  directory, using the same script as CI. Stable Rust is required.

## Publishing

GitHub Actions workflows remain in `.github/workflows/`. The Pages workflow
tests v1 book examples and builds both books on pull requests and pushes to
`main`; only `main` deploys. It installs tools using `pages/install-tools.sh`
and assembles the site with `pages/build.sh`: `pages/index.html` at the root,
the older book under `/dada-model/v1/`, and the new book under `/dada-model/v2/`.
The root redirects to v2. Its older versions appendix
(`v2/md/appendices/older-versions.md`) explains the a-mir-formality-based v1
model and links back to its book using the assembled site's relative paths.
Each book's `site-url` matches its published prefix for 404 asset resolution.
Keep generated v1 source links pointed at the repository's `v1/` directory.
The checked-in v1 Mermaid initializer must match mdBook's theme menu IDs.
See `pages/README.md` for preview commands, dependencies, and the required
GitHub Actions source setting in repository Pages settings.

Keep this file and `v1/AGENTS.md` current when changing the repository layout.
