# Adversarial review — 24 October 2026

The evidence checker can report a current, positive review even when the book
shows different prose or a different Lean declaration. Five reproduced tooling
bugs explain how. The Given and Shared semantics survived the targeted review,
but the positive review of their provisional promotion rule overstated what had
been settled. The book also needs a more direct reading order.

Three reviewers started without the earlier design conversation: one read every
chapter in `md/SUMMARY.md`, one reviewed the Rust tooling, and one examined the
small-language semantics and selected full-heap claims. The coordinating reviewer
inspected the active evidence records, reproduced the tooling counterexamples,
and retained additional inputs for renewed reviews. This reviews the current
working tree, including uncommitted implementation work.

## Findings that affect correctness

1. **P1 — Included prose can change without invalidating evidence.**
   `Inventory::add_unit` snapshots the literal unit at
   `mdbook-dada/src/inventory.rs:256`, but mdBook expands `{{#include ...}}`.
   Changing an included sentence changes the published claim while `dada-spec`
   still reports `current/corresponds`. The fixture uses an actual mdBook build.
   Reject includes in reviewed units or capture their transitive expansion inputs
   using the same rules as rendering.

2. **P1 — Rendering and review can select different Lean roots.**
   `inventory.rs:264` hardcodes `lean/`; `src/main.rs:20` reads `lean-source`
   from the book configuration. `book.toml` is not a freshness input. Switching
   the configured root displays `def value := 2` while evidence remains current
   for `def value := 1`. Both consumers need one enforced configuration; hashing
   the configuration alone would not correct the source-selection disagreement.

3. **P2 — Nested citations escape required-input discovery.**
   A supported legacy grammar block inside a structured Rust-backed definition
   renders Lean, but `inventory.rs:263` visits only the parent's `:lean:` options.
   Changing the nested declaration leaves evidence current; the bundle contains
   no Lean inputs. Reject such nesting or collect its exact citations with the
   same parser that renders it.

4. **P2 — A rule citation can select a nonexistent constructor.**
   The type-selection exception at `lean.rs:319` permits an indented sibling
   declaration to be absorbed into its predecessor. A citation to `First.second`
   succeeds when `second` belongs to `Second`, displaying a fabricated combination
   of `First`'s header and `Second`'s constructor. Reject unsupported declaration
   boundaries for type/rule selection too.

5. **P2 — Rule selection drops final literal tokens.**
   `lean.rs:773` trims the masked text rather than the actual source extent.
   `zero : Indexed "zero"` becomes `zero : Indexed`. The index is part of the
   constructor's type, so this is a changed statement, not a cosmetic omission.
   Use the scanner's literal-aware extent and test final literals explicitly.

6. **P2 — A positive semantic review leaves a known design alternative unresolved.**
   `shared.give` agrees with Lean: copying a unique field through shared access
   promotes that final field to shared. The implementation explicitly chose this
   provisionally while alternatives remained open. The review policy requires
   an inconclusive verdict for ambiguous intent. Preservation and the Given-to-
   Shared embedding do not decide between promotion strategies. This is not a
   requirement to seek approval for every routine choice; it concerns the
   particular ambiguity already recorded during implementation.

The complete [tooling review](tooling.md) gives minimal inputs, source locations,
observed outputs, and suggested regression tests. [Semantic review](semantics.md)
records both the findings and attempted counterexamples that did not invalidate
the stated theorems.

## Narrative findings

- **Put the language before contributor machinery.** Seven repository-method
  chapters, totaling 1,372 source lines, precede Dada in the default reading path
  (`md/SUMMARY.md:3`). They explain how the document is maintained before the
  reader knows what behavior it describes.
- **Explain the operation before its representation.** Given introduces tables,
  counters, and storage places before explaining a move. Shared repeats those
  structures before introducing the move/copy distinction. Begin with the
  intended behavior and one small program; then define the objects and rules
  needed to explain it.
- **Correct contradictory completion claims.** `md/operations.md:416` says the
  next chapter defines complete give/lease/share/drop transitions and that
  invalidation remains unspecified. `place-operations.md` instead marks complete
  path contracts pending, while `state.md:314` already defines invalidation.
- **Separate failed checks from faults and UB.** The heap draft uses all three
  while explicitly leaving fault semantics open (`operations.md:52`). State
  which successful effects exist, which accesses fail a judgment, and which
  source-level failure policy remains proposed.
- **Put preservation after the transitions it quantifies over.** The heap's
  invariants chapter precedes its operation definitions, while its state chapter
  contains substantial operational material. Also explain the deliberate change
  of model between Shared and the separate heap draft.
- **Remove repeated checking commentary and routine proof paraphrases.** A reader
  needs the trust distinctions once. Source selectors can carry implementation
  names; the narrative should emphasize ownership, reachability, mutation, and
  the nontrivial guarantees.

The [narrative review](narrative.md) contains precise spans, proposed wording, and
a fuller outline. A shorter primary reading order is:

1. Dada and the scope of these models.
2. Given: ownership transfer → example → slots and places → execution → invariants.
3. Shared: copying ownership → example → route permissions → rules → correspondence.
4. The separate heap draft, with its changed assumptions and incomplete parts explicit.
5. Authoring, evidence, and implementation methods as contributor reference material.

For each definition: say what the concept is for, state its behavior, then give
the notation or rule. New explanatory material can remain inside named units
with source associations; a clearer narrative does not require untracked claims.

## Evidence audit and revisions

The inventory has 30 reviewed units: 26 in Given/Shared, three finite-map pilot
units, and one Rust-backed meta unit. Most superstructure requirements and the
full heap remain legacy anchors outside this evidence inventory. Their appearance
in context snapshots is not a completed correspondence review. Thus the current
gate does not establish coverage of the entire book or superstructure; that
migration remains to be done despite `meta.system.self_specification`'s broader
requirement at `md/repo/spec-system.md:107`.

Two reviews were repeated with additional recoverable inputs and recorded through
the normal CLI. Their previous positive records remain preserved:

| Unit | New verdict | Additional inputs and reason |
| --- | --- | --- |
| `meta.evidence.required_inputs` | **Mismatch** | Reproduction script, observed outputs, detailed findings, and `book.toml`. The old test attacks an already-derived manifest; it cannot detect omissions or incorrect selections in that derivation. |
| `shared.give` | **Inconclusive** | [Design context](design-context.md) retaining the user requirement and unresolved alternatives. Internal prose/Lean agreement does not settle the intended state changes. |

New records:

- [Meta input-completeness review](../../evidence/records/meta.evidence.required_inputs/eb1d278b0fd7d7d5f3fd3ff9a16ad0f95bcb574bab5fb4f9b55a46561e77f0de.json)
- [Shared give review](../../evidence/records/shared.give/226d2870bf5106489f5d1f3072495c2d01b5d3fbf597e1de7a935ec759e81b5c.json)

No additional concrete mismatch was found in the reviewed Given/Shared
preservation, rooted liveness, or correspondence statements. Their operational
rules do not assume the desired successor invariant. Backward correspondence
quantifies arbitrary Shared successors, rather than assuming the successor is
already an embedding. The theorems allow stuck programs and do not promise
progress. These observations support their stated scope; they are not a blanket
correctness claim or a fresh positive review of the entire heap draft.

## Reproduction and checks

From `v2/`, after building the tooling:

```sh
cargo build --bins
python3 reviews/adversarial-2026-10-24/reproduce_tooling.py
```

The script writes only to fresh temporary fixture directories. Its synthetic
approvals test the validator; they never become repository correspondence records.
[Recorded output](tooling-results.txt) shows all five counterexamples.

The independent [Lean probes](SemanticsProbes.lean) compiled with:

```sh
# From v2/lean/
lake env lean -DwarningAsError=true ../reviews/adversarial-2026-10-24/SemanticsProbes.lean
```

They exercise repeated shared arguments, the significance of well-formed class
tables, and sibling lease invalidation. Sibling borrows surviving a write through
another root match the stated heap policy, so the review records that behavior
as a design boundary rather than inventing a contradiction.

Before the revised evidence was recorded, all 105 Rust tests passed. The full
Lean build passed with warnings treated as errors (57 jobs), and the mdBook
build passed. After recording the
two adverse decisions, `cargo test --locked --workspace` fails at
`evidence_is_complete_and_current`, reporting exactly the mismatch and the
inconclusive review. See [test output](final-tests.txt) and
[evidence status](final-evidence-status.txt). This failure is the intended effect
of retaining findings; it must not be bypassed with a fresh positive record.

Implementation and chapter text were left unchanged during this review. Repair
the five tooling defects, add the reproductions as regression tests, resolve the
promotion choice, and then renew the affected reviews. The narrative reordering
can follow those corrections without changing the semantic claims by accident.
