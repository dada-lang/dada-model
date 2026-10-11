# Work In Progress

The [surface and core syntax migration](md/wip/2026-10-surface-core.md) is complete
as of October 11, 2026. Every program assertion helper parses surface syntax and
lowers to core before checking or interpretation. Calls supply all generic arguments
explicitly; generated permissions follow explicit generics, receiver first and
then inputs left to right. Inference remains future work. The implementation
record tracks independently passing phases and the final validation: 890 model
tests, 11 book-preprocessor tests, and a complete book build.
See [Surface syntax and core judgments](md/surface-syntax.md) for current syntax.

The ongoing soundness assessment and discussion is in
[September 2026 soundness assessment](md/wip/2026-09-soundness-assessment.md).
It catalogs borrowing-model failures, intended behavior, and proposed regression
tests. Field-type restrictions and the scope-cleanup goal for explicit drop are agreed;
implementation design is still in discussion. The predicate vocabulary migration
(`copy` to `shared`, old `shared` to `shared` plus `owned`) is implemented.

The preceding implementation plan remains available in
[Var-pop normalization](md/wip/var-pop-normalization.md).

Validated September 25, 2026 with `cargo test --all --workspace`: 627 model
tests and 7 mdBook preprocessor tests passed. Shared permissions can be duplicated;
`shared[d]` describes a shared value that references `d`. Composition syntax is unchanged.

The independent [property-documentation extraction](md/wip/test-anchors.md) now
includes `moves_preserve_dependencies`,
`given_from_duplication_requires_shared_origins`,
`given_from_mut_requires_mut_origins`,
`given_from_owned_requires_owned_origins`,
`given_from_unique_requires_unique_origins`, `sharing_does_not_grant_mut`, and
`given_from_preserves_origin_dependencies`, and the four `call_returns` properties
on escaping ownership, rejected borrows of consumed arguments, forwarded borrows,
and all possible return referents remaining borrowed. The property record describes their
end-to-end evidence and validation. Earlier
[Vec](md/wip/vec.md) and [unsafe-code](md/wip/unsafe.md) notes
retain their implementation history and open questions.
