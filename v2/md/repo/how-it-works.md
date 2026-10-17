# How it works

The book provides a reading order through the design. A chapter first explains a
question and the intended result, then connects that explanation to examples,
definitions, algorithms, and evidence. Readers should be able to recover the
mental model before studying implementation details.

## Developing a claim

We begin with a behavior or distinction worth explaining. We describe it in prose
and work through concrete examples. An anchor names a claim so that we can connect
it to definitions, operations, and evidence without copying its text everywhere.

For some claims we will develop Lean propositions and proofs. One claim may need
several propositions to cover its qualifications. For others, executable tests or
examples may supply useful evidence while formalization remains incomplete.

Human or agent review examines how these views fit together. Does a proposition
exclude an important case? Does an example reveal an ambiguity? Could code satisfy
the formal obligations while violating the behavior described in the book? A
failed proof attempt may motivate changes to any of the views, or to the design.

This is an iterative process, not a pipeline in which English is fixed first and
all later artifacts must accommodate it.

## Reading evidence

Correspondence review, test execution, and proof checking answer different
questions. We intend to show their statuses separately, including assumptions,
partial coverage, and unresolved disagreements. Review records should explain
why a correspondence is adequate, rather than only report approval.

Definitions and their documentation will be included from their sources so that
the book does not maintain a second copy. Lean declarations will be the source of included type definitions;
see [Lean definitions in the book](spec-system.md#lean-definitions-in-the-book).
Definition inclusion is implemented for the supported Lean source style;
compilation and proof verification remain separate work.
Graph renderings already derive from explicit state facts in `heap` blocks. Anchor roles and cross-references are also processed;
see [authoring syntax](spec-system.md#authoring-syntax).

## Working in this repository today

From the repository root, `just book-v2` builds this draft. Run `mdbook serve`
inside `v2/` to preview it. Edit the narrative under `v2/md/` and register chapters
in `v2/md/SUMMARY.md`.

Run `cargo test --workspace` and `cargo clippy --workspace` from `v2/` to check
the Rust preprocessor. These tests exercise presentation tooling.

No command yet verifies the v2 semantic claims or records correspondence reviews.
The next chapter states our working principles; the
[system design](spec-system.md) describes the checks the tooling should eventually
provide.
