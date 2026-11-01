# How it works

The book develops the model through named definitions, rules, theorems, and
examples. Each unit carries its explanation in Markdown and mathematics and
links to the corresponding named part of Lean. The mathematical account stands
on its own; a Rendered/Lean selector lets the reader inspect its formalization.
The reading order introduces concepts before the rules that use them.

## Developing a unit

Begin with a behavior or distinction worth explaining. State it in a unit and
work through examples that make its meaning concrete. Put the unit ID on the
opening line and source citations in `:lean:`. Record contextual definitions in
`:uses:` and link new terminology to where it is introduced. Explanatory content
belongs inside the reviewed boundary rather than in untracked semantic prose.
The [authoring guide](authoring.md) gives the supported forms.

A theorem may need several assumptions to capture the intended guarantee.
Review compares those assumptions and the conclusion with the prose and
mathematics. Lean checks the proof. An example has its own comparison: the cited
Lean case must describe the setup and result actually claimed in the book.
Unfinished formalizations retain their intended unit kind and use `:status: draft`.
They cannot receive affirmative correspondence decisions or pass evidence validation.

Neither representation automatically wins when they differ. A discrepancy may
reveal ambiguous prose, an inadequate proposition, or a design choice that needs
discussion. Record the discrepancy and resolve it before claiming correspondence.

## Keeping the comparison inspectable

`dada-spec prepare` snapshots a unit and its required inputs. A human or agent
reviewer compares them and records a conclusion, rationale, examined inputs, and
limitations. `dada-spec record` checks that the inputs still match current source
before retaining the decision. Exact snapshots remain available so another
reviewer can vet the comparison. Changing an input makes affected evidence stale.

The evidence checker validates structure, required input coverage, and freshness.
It does not itself judge mathematical correspondence or prove a theorem. Its
ordinary Cargo integration test makes missing or stale evidence visible during
`cargo test --workspace`. The [review procedure](correspondence-review.md)
explains how to interpret and repair failures.

Proof checking, test execution, and correspondence review remain separate.
Passing Lean establishes the proposition checked under its assumptions; a
current review records a judgment that this proposition captures the intended
claim. A passing test establishes its tested cases. None of these results should
be silently substituted for another.

## Working in this repository

Edit chapters under `v2/md/` and register them in `v2/md/SUMMARY.md`. From the
repository root, `just book-v2` builds the draft and `just test-lean` checks the
Lean project. Run `mdbook serve` inside `v2/` to preview the book.

From `v2/`, run:

```sh
cargo run -p mdbook-dada --bin dada-spec -- status --explain
cargo run -p mdbook-dada --bin dada-spec -- check
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
```

Every new-style unit participates in evidence validation. `v2/spec.json` names
strict chapters that additionally require all semantic prose to lie within
units. The [Given](../given.md) and [Shared](../shared.md) chapters use the complete
review loop, alongside the [implementation contracts](evidence-pilot.md).
Legacy requirements in the system reference still await migration to review units.

The [system design](spec-system.md) defines the evidence contract. The
[layer extension protocol](layer-extension.md) describes the model
organization: unique ownership with `p→`, then shared ownership with `p→share`,
with a formal correspondence between the two layers.
