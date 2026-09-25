# Work In Progress

The current assessment and discussion is in
[September 2026 soundness assessment](md/wip/2026-09-soundness-assessment.md).
It catalogs borrowing-model failures, intended behavior, and proposed regression
tests. Field-type restrictions and the scope-cleanup goal for explicit drop are agreed;
implementation design is still in discussion. The predicate vocabulary migration
(`copy` to `shared`, old `shared` to `shared` plus `owned`) is implemented.

The preceding implementation plan remains available in
[Var-pop normalization](md/wip/var-pop-normalization.md).

Validated September 25, 2026 with `cargo test --all --workspace`: 627 model
tests and 7 mdBook preprocessor tests passed. Shared permissions can be duplicated;
`ref[d]` describes a shared value that references `d`. Composition syntax is unchanged.

The independent [test organization proposal](md/wip/test-anchors.md) remains a
draft. Earlier [Vec](md/wip/vec.md) and [unsafe-code](md/wip/unsafe.md) notes
retain their implementation history and open questions.
