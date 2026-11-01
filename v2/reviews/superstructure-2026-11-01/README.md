# Superstructure completion — 2026-11-01

The remaining renderer coverage draft is now a cited inventory contract.
Fifteen grouped renderer contracts replace the previous unreviewed renderer
requirements; all 65 original reference anchors are retained (35 migrated,
30 remain as policy/reference anchors). The migration map is retained here.

Mechanical execution is recorded separately from correspondence review.
`dada-spec run-check NAME` executes a profile from `spec-checks.json`, captures
raw output, exit statuses, version probes, and source/directory snapshots before
and after the run. `mechanical-status` reports the latest result per profile.
Failures remain in immutable history. Ordinary evidence validation reads and
checks receipts without invoking commands or requiring a pass for itself.

The source snapshots deliberately exclude generated outputs and do not capture
a hermetic environment. In particular, a Rust run's receipt does not certify
that the current correspondence records are complete: those are checked
separately. Timestamps and hashes are not authentication of execution.

## Findings addressed

- Fresh review reproduced a coverage gap: dot-prefixed Markdown files and
  directories were skipped, even when linked in SUMMARY. The inventory now
  includes them; a regression test requires evidence for both hidden forms.

- Renderer theme JavaScript/CSS were missing from correspondence freshness
  inputs. Inventory now includes them; tests cover omitted, changed, and newly
  added assets.
- Mechanical receipts initially lacked independent checks for their required
  input roots and directory membership. Validation now checks the complete
  recorded tree closure and matches the profile to its configuration snapshot.
- Timestamp ties could conceal failures or identify the wrong receipt. Tied
  stale/failing receipts now prevent a pass, and status selects a responsible
  receipt deterministically.
- The new axiom-report profile initially passed Lake's `--wfail` option to Lean
  itself. The failed execution was retained. The corrected script builds imports
  with `lake build --wfail` before running the query file.
- Fresh review found missing context for the claim about that script. The
  mechanical and coverage comparison bundles now explicitly retain
  `spec-checks.json`, `scripts/check-assumptions.sh`, and `lean/CheckAxioms.lean`.
- Evidence checking repeatedly derived current source snapshots for every
  historical bundle. It now derives them once per unit during a check, while
  still comparing each historical bundle and each explicit extra input.

## Verification and scope

The final Lean build completes all 48 jobs with warnings treated as failures.
The assumption query covers ten named foundation and type-safety theorems;
its output lists only `propext`, `Classical.choice`, and `Quot.sound` (the Shared
path-exclusivity theorem does not use choice). See the separate execution
receipts named in `lean.log` and `lean-assumptions.log`.

The book builds. Browser inspection verified the new renderer-contract chapter
and its Rust selector; `preview.png` retains the rendered view.

The generic-views example remains a future design proposal. It is deliberately
not implemented or relabelled as completed to clear evidence validation. The
current Given typing model and its normalization, progress, preservation, and
termination proofs remain complete. No language semantics changed in this work.

Fresh review records and their prepared-bundle manifests are retained in this
directory. Each record identifies the exact inputs examined and its rationale;
Lean checks proof bodies, while correspondence reviews compare statements and
examples with their prose. Mechanical logs do not substitute for those decisions.

## Final results

- 85 current positive correspondence reviews: 23 typing, 40 Given/Shared/map,
  and 22 tooling. No stale, missing, or unresolved implemented-unit reviews.
- 142 ordinary targeted tests pass. The normally ignored actual-mdBook pipeline
  test was also run explicitly and passed; doc tests pass (none defined).
- Formatting and Clippy with `-D warnings` pass.
- Lean, Lean assumption reporting, and the book each have a current recorded
  pass. The final Rust workspace receipt records the real failure: the evidence
  integration test rejects the deliberately deferred `future.generic_views`
  draft. No other evidence issue remains. This failure is not hidden or waived.
- `before-hidden-fix/` retains the initially reviewed inputs/proposals, including
  the tooling review's coverage mismatch. Final records inspect the corrected
  source and test. Immutable correspondence records preserve the superseded
  language reviews as well.
