# Lean source-selection fixtures

These small declarations exercise the renderer's textual source selector. They
are test data, not a language layer or a retained heap specification. In
particular, `Step` deliberately leaves its state unchanged: its constructors
exist to test first, middle, and final case selection with explicit parameters.

Keep adjacent declarations and examples in place: tests assert that a selected
body includes its final line but excludes its neighbors. The fixture covers
abbreviations, structures, inductives, equation definitions, `:=` definitions,
literal qualified names, proofs, and anchored anonymous examples.

The Cargo tests read the source without running Lean. It is self-contained and
can also be checked with the repository's pinned Lean:

```sh
cd v2/lean
lake env lean ../mdbook-dada/tests/fixtures/lean/Renderer.lean
```
