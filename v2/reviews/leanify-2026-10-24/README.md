# Given and Shared formalization — 2026-10-24

The reviewed Given chapter now has matching Lean definitions and proofs for
recursive constructor arguments, tagged object identities, expression evaluation,
statement transitions, and finished configurations. The empty-field example
proves that no execution can finish. Shared and the two-way correspondence on the
Given fragment use the same expression structure.

Evaluation preserves ownership while earlier argument results await placement in
the new object's fields. The statement binds the final result and restores the
ordinary storage invariant. Additional checked examples cover left-to-right
allocation, repeated unique gives, and nested construction with shared arguments.

## Correspondence review

- [Given](given/status.txt): all 18 units have current affirmative reviews by an
  agent that did not implement Unique. Individual review JSON files are in the
  same directory.
- [Shared](shared/README.md): all 15 units have current affirmative reviews by an
  agent that did not implement Shared or the correspondence module.
- [Tooling and finite-map reviews](meta/bundles.json): eight affected units were
  reviewed with unit-specific rationale and explicit authorship limitations.
- [Semantics audit](semantics-audit.md): separate review of evaluation,
  temporary ownership, preservation, liveness, and example statements.

Review findings corrected finite-map/key-uniqueness wording and clarified that a
second give fails after access through an entirely unique path. A uniquely stored
field reached through shared access can instead be copied. The stale packet from
before that correction was rejected by the evidence checker.

## Validation

The following commands completed successfully during this change:

- `just test-lean` (24 build jobs, warnings treated as errors).
- `just book-v2`, including a final build after the prose corrections.
- `cargo fmt --all -- --check` and
  `cargo clippy --workspace --all-targets -- -D warnings` from `v2/`.
- The separately enabled real-mdBook integration test; its output is in
  [mdbook-integration.log](mdbook-integration.log).
- `git diff --check`.

The final [workspace test run](workspace-tests.log) had 122 passing tests, one
ignored test (then run successfully above), and one failure:
`evidence_is_complete_and_current`. Its only diagnostic is the pre-existing
`meta.system.remaining_coverage` draft in `md/repo/spec-system.md`. No Given or
Shared unit remains a draft or lacks current correspondence evidence.

The browser's evaluation block was checked in both views: Rendered shows the
reviewed rule and its where-clause; Lean shows `Eval`, `EvalArgs`, and
`State.allocate`. The rendered view was restored afterward.

These command results are a human-readable run record, not mechanically bound
proof-check records in dada-spec. Correspondence status still reports mechanical
checks as not recorded. [Final status](status.txt) records that distinction and
the outstanding tooling draft. This report does not assert freshness after
subsequent source changes.
