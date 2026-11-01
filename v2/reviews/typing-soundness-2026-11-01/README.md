# Given typing soundness — 2026-11-01

This completes the normalization and static soundness work left open by the
first formalization pass. The typing rules and executable view operations are
unchanged. No operational-success premise was added to static typing.

## Results

- `Unique/Normalization.normalization_correct` proves that normalization
  preserves the nominal class, well-formedness, and positive and negative
  observations. It is idempotent and independent of entry order. Supporting
  proofs are in `ViewSoundness`, `ViewNormalization`, `ViewCanonical`,
  `ViewReconstruction`, and `ViewIdempotence`.
- `Unique/TypingSafety.expression_soundness` establishes evaluation existence
  and realization preservation for every evaluation. Pending values are
  arbitrary, so earlier constructor arguments remain protected while later
  arguments run. `TypingHeap`, `TypingOwnership`, `TypingAllocation`,
  `TypingExpressionSoundness`, and `TypingGiveSoundness` supply the heap,
  separation, allocation, and move lemmas.
- `TypingBindingSoundness` establishes binding existence and preservation,
  including reordered unpacking patterns and empty-field transfers.
- `TypingSafety` proves progress and preservation for the unpacking machine.
  From every finite execution prefix of a well-typed program, a completion
  exists. Its total length is exactly the original statement count, and its
  final storage realizes the specified final environment.
- `TypingRejectionChecks` covers all rejection examples, including unknown
  versus empty fields, transferring a partial value without recovering its
  whole type, constructors rejecting partial inputs despite untyped execution
  being possible, exhaustive unpacking with a hidden field, and repeated gives
  in constructor arguments.

The public book citations select the discharged results, not helper lemmas
parameterized by expression soundness. There are no admissions. The axiom
inspection in `axioms.log` lists only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` for the public results.

## Review

An independent statement audit compared the public theorem assumptions and
quantifiers with the chapter. It checked that storage realization is independent
of evaluation, static typing contains no success predicate, arbitrary pending
owners are covered, and preservation includes every operational successor.
The audit found no mismatch.

Fresh correspondence reviews use the immutable packets in `*-bundles.json`.
The `typing/`, `given/`, `shared/`, and `meta/` directories retain their reasoning,
examined input keys, limitations, and explicit supersessions of earlier active
decisions. Reviewers compared statements and definitions; they did not recheck
proof tactics or claim to have run the mechanical checks.

All 68 renewed decisions were accepted by `dada-spec record`: 23 typing units,
25 Given/finite-map units, 15 Shared units, and five superstructure requirements.
The `*-recorded.json` files retain the CLI results; `review-counts.json` summarizes
them. Earlier records are retained and explicitly superseded.

The Shared review found that its embedding introduction and boundary theorem
could be read as including Given's unpacking extension. The correspondence
actually covers the original fragment with single-variable bindings. The book
now states that boundary explicitly; affected packets were prepared again and
reviewed against the corrected text. The preliminary notes preserve the finding.

## Mechanical checks

`lean-build.log` records the complete `lake build --wfail` run. `book-build.log`
records the mdBook build. Browser inspection found no MathJax errors or Draft
labels in the typing chapter and verified the progress theorem's Lean selector.
`preview.png` shows the resulting theorem statements.

Correspondence status and the workspace evidence gate are separate from these
checks. The future generic-view proposal and the remaining superstructure
coverage unit are intentionally still Draft; this work does not formalize either
proposal or weaken the evidence policy to accept drafts.

`evidence-check.log` confirms 68 current positive units and exactly those two
draft failures, with no stale or missing decisions. `cargo test --workspace`
passed 37 library tests and 39 book tests before the repository evidence test
failed on the same two drafts. The remaining integration suites were then run
separately because Cargo stops at that failed test executable; their results are
retained in `remaining-tests.log`. `doctests.log` records the doc-test check.
