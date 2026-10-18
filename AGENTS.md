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
blocks take one. Fenced `{example} File:anchor` directives pair authored Markdown
with an anchored anonymous Lean `example` proof through the same selector.
Standalone `-- ANCHOR: name` and `-- ANCHOR_END: name` comments delimit exactly
one top-level example; they are not Lean declaration names. The selected Lean
`example` starts at column zero, continuation lines are indented, and the next
command after the closing marker starts at column zero. The authored body supports
Markdown and the book's roles and other block directives, but not nested examples.
Use a longer enclosing fence for bodies with code fences. The `.lean` extension
is optional in citations. Missing, duplicate, malformed, or wrong-kind targets and
paths escaping `lean-source` fail the book build. The Markdown mathematics and notation explanations stand on
their own, with Lean as an associated formalization. `src/lean.rs` handles textual
source selection and HTML, not mathematical derivation or Lean elaboration. The
`lean-source` book setting locates Lean files. `v2/theme/mathjax.js` loads pinned
MathJax 4.1.3 from a CDN with CommonHTML output and New Computer Modern fonts;
mdBook's built-in MathJax 2 loader is disabled. Authored display line breaks are
preserved, with horizontal scrolling for wide equations.
Always group overbar expressions, as in `{\overline f}`. The command must be
immediately preceded by an opening brace and immediately followed by a literal
ASCII space. The preprocessor rejects a violation of either condition with
a source path and line number. This source lint also applies to literal TeX
samples; a test scans every Markdown file under `v2/md/`, including files absent
from the book's table of contents. Longer TeX command names are not matches.
The former `{lean.type}`, `{lean.judgment}`, and `{lean.rule}` directives are
rejected with migration diagnostics. The old grammar DSL/parser and automatic
Lean-to-LaTeX translator have been removed; Lean notation comments have no
rendering effect. The build checks citations and supported declaration or example
forms, not Lean proofs or correspondence between prose, mathematics, and Lean.
Compile each example's containing Lean file separately to check its proof;
review still establishes that the test covers the prose. Every semantic example
must cite its intended Lean test. Unfinished semantic scenarios are explicitly
proposed or pending. Authoring-syntax illustrations remain ordinary prose and
literal code. Review records and scripts
providing correspondence evidence remain future work. The syntax, notation
conventions, and review obligation are documented in `v2/md/repo/spec-system.md`;
theme CSS lives in `v2/theme/dada.css`.
`{informational}` at the start of a paragraph labels nonnormative commentary.
The former `{example}` paragraph prefix is rejected; use the fenced directive.
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
one ordered store of all live variable slots, including temporaries and suspended
callers' variables. Its finite-map entries record newest-first allocation order.
`VariableId` identifies a runtime binding lifetime separately from its
source name; `Place.variable` selects its slot. There are no heap frames.
The current `Operation`/`Step` slice pushes absent variables as uninitialized,
deallocates only the newest slot (which must be uninitialized), and creates
primitive, aggregate, and array objects. Creation preserves variable order,
chooses a fresh object identity, and initializes an already
allocated, empty destination with its owned reference. Aggregate field names must
be distinct; aggregate fields and array elements begin uninitialized. Empty
aggregates and zero-length arrays are allowed. Checked lemmas characterize these
local effects; they do not prove ownership exclusivity in arbitrary malformed
states. `Operation` now uses the common `Primitive` parameter for primitive
creation. The future execution semantics will α-rename bindings to fresh identities
and manage scope and cleanup. Heap allocation checks absence only from the live
map, so freshness across completed variable lifetimes remains an execution-layer
obligation. Object creation similarly checks current object-map absence;
destruction, identity reuse, and reference invalidation remain to be specified.
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
