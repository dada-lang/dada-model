# Correspondence review

A correspondence review asks whether a unit's prose and mathematics express the
intended meaning of its cited formalization. Lean checks the proof of a theorem;
the review checks that its statement is the theorem we intended to prove.
Evidence retains both the inputs and the reasoning behind that judgment.

## Scope and configuration

`spec.json` makes the validation scope explicit. Its JSON uses `schema: 1`, a
`chapters` array of paths relative to `v2/`, a `policies` array of review-policy
files, and a `context` array for additional required input files. The book and Lean roots come from `book.toml`; this repository uses `md/`
and `lean/`. Every new-style unit under `md/` participates in the inventory.
Specification units require evidence; future notes are explicitly nonnormative
and have no correspondence claim. Adding
a strict chapter additionally rejects prose outside unit boundaries in that
chapter; removing it is a coverage change, not a remedy for missing evidence.

Policy and extra context files become inputs to the comparison. Changes to
those files, the configuration, or validator implementation can invalidate
existing reviews. Evidence files themselves are outputs and do not recursively
participate in their own input digests.

## Prepare the comparison

Run these commands from `v2/`. Inspect the current inventory and failures with:

```sh
cargo run -p mdbook-dada --bin dada-spec -- status --explain
cargo run -p mdbook-dada --bin dada-spec -- check
```

Prepare one unit's packet:

```sh
cargo run -p mdbook-dada --bin dada-spec -- prepare UNIT_ID
```

Preparation writes a JSON bundle under `evidence/bundles/` and prints its path.
It snapshots the complete authored unit, the required source selections and
context, dependent units, and review policy. It records content hashes so that
recording and validation can reject a comparison made against changed inputs.
Preparation does not supply a verdict.

A unit marked `:status: draft` retains its semantic kind but is unfinished.
Drafts may omit citations; supplied citations are still checked by kind.
Evidence validation rejects drafts, and recording an affirmative correspondence
decision for one is forbidden. Complete the formalization and remove draft
status before attempting that review. A definition needs a matching Lean
definition, not a proof; only a claimed result needs a proof.

A `{future-note} ID` records exploratory design outside the current specification.
It must not have formalization citations (`:lean:`, `:rust:`, or `:tests:`) or
`:status: draft`. Its structure, ID, and contextual references remain checked,
but it needs no correspondence evidence and cannot be prepared or recorded for
correspondence review. Status reports `future note` / `not applicable`, never
approval. Context links do not formalize the note. Change its kind before adding
a formalization; draft specification units retain their existing blocking behavior.

The input set is constructed from the current specification. At minimum it
includes the exact unit being reviewed and every cited Lean declaration. All
local Lean source files are retained conservatively for a Lean-backed unit,
rather than claiming that a textual scan discovered elaborated semantic
dependencies. The Lean toolchain and Lake metadata, configured policy and context,
and validator source/tests, `book.toml`, and Cargo metadata are also inputs. Rust-backed units
retain their selected implementation/test sources and complete containing files.
Structured units reject mdBook expansion directives and nested legacy source
citations, so neither can introduce uncaptured content into a reviewed body.
This may invalidate evidence after an edit elsewhere in the formalization or
a proof-only change. That conservative scope is explicit and reproducible.

## Review the packet

Prefer a reviewer with fresh context. Give the reviewer the immutable packet,
this procedure, and the task of finding discrepancies; an earlier author's
assurance is not evidence. Read the authored units, exact source selections,
policy, and explicitly added context that the packet marks as required review
inputs, and record their keys
in the review. Inspect additional source context needed for the comparison and
record those inputs too. The bundle also retains conservative full-source and
tool snapshots for freshness; listing those snapshots does not require claiming
that every line of every existing proof was examined. For each unit:

1. Identify its intended objects, operations, quantifiers, and assumptions.
2. Compare the complete prose and math with the selected source, including
   hidden parameters, side conditions, and omitted representation details.
3. Check that concepts are introduced with an italicized name and inline
   metavariable, and that every metavariable has a grammar or domain before use.
   Check that judgments have defining rules before results rely on them. Inspect
   the introducing units, including those cited through `:uses:`.
4. Look for a case admitted by one account and excluded by the other. For an
   example, check its setup and stated result rather than merely finding a
   similarly named test.
5. Record what matches, any discrepancy, the scope of the comparison, and its
   limitations with references to the examined inputs.

In the rationale, identify the units that introduce the notation and judgments
needed for the comparison. Report undefined symbols and forward references as
discrepancies; if their meaning cannot be established, mark the review
inconclusive. These are review criteria. The validator does not check notation
introductions or the order of mathematical definitions.

Do not re-prove a theorem or audit its tactic choices as part of this review.
Do inspect assumptions that affect its statement. A successfully checked proof
of a narrower proposition does not cover a broader prose claim. Draft status
must remain explicit and does not permit approval.

For a meta requirement, compare its body with the cited implementation and
tests. Explain which paths or rejection cases the tests cover and which parts
of the behavior are supported only by inspection. Do not infer universal
correctness from a passing test.

If the comparison needs another unit, add it to the authored dependencies and
prepare a new packet. Additional consulted files can be included with repeatable
`--input` arguments, for example:

```sh
cargo run -p mdbook-dada --bin dada-spec -- prepare UNIT_ID --input md/repo/authoring.md
```

These extra file inputs must also appear in `examined`. Configured `context`
files are conservative freshness inputs; they are not automatically an attestation
that the reviewer read the whole file. Do not silently consult material
that another reviewer cannot recover from the evidence. If the intended design
is ambiguous, record an inconclusive result or mismatch and describe the choice
that needs resolution. Do not change the design just to obtain approval.

## Record the decision

The review file identifies the prepared bundle, the reviewer and provenance,
examined input keys, a conclusion, comparison rationale, and limitations. The
three conclusions are `corresponds`, `mismatch`, and `inconclusive`. The rationale
must explain the comparison rather than report that filenames exist or tests
passed. The review JSON has this shape; use the actual digest and required
review input keys from the bundle, plus any further inputs actually examined:

```json
{
  "schema": 1,
  "bundle": "DIGEST_FROM_PREPARED_BUNDLE",
  "reviewer": "Reviewer identity",
  "provenance": "How this review was performed; agent/model identity when applicable",
  "examined": ["EVERY_REQUIRED_REVIEW_INPUT_KEY"],
  "conclusion": "corresponds",
  "rationale": "Specific comparison of the authored claim and formal statement, with input references",
  "limitations": [],
  "supersedes": []
}
```

This is a schema illustration, not a review to copy and approve. Retain an
explicit empty limitations list when none were identified. `examined` is an
attestation that the reviewer read the listed inputs; the validator can check its
coverage of the required review inputs, but cannot establish that the reading
actually happened. Do not claim to have examined a whole conservative source
snapshot just because the packet contains it.
`supersedes` records the digests of earlier decisions for the same unit that the
new decision intentionally replaces; it does not conceal them. A replacement
may use a different bundle, for example after adding context needed to resolve
a disagreement. Recording still validates the new bundle against current inputs.
Every unsuperseded decision for a unit must apply to current inputs and conclude
`corresponds` for the evidence check to pass. When reviewing changed inputs,
explicitly supersede the earlier active decisions; creating an unrelated positive
record does not silently discard a negative or stale one. If a replacement later
becomes stale, the check fails rather than falling back to an older positive
review.

Record a completed review with:

```sh
cargo run -p mdbook-dada --bin dada-spec -- record BUNDLE_PATH REVIEW_JSON_PATH
```

Recording validates the review and recomputes required inputs from current
source. If the unit, formalization, dependencies, or policy changed after
preparation, it refuses the obsolete comparison. Prepare again and review the
changed packet. Accepted records are retained under `evidence/records/` alongside
their retrievable bundles. Never manufacture a favorable review or rewrite old
input hashes to satisfy the workspace test.

## Interpret the result

`dada-spec check` and the Cargo integration test perform syntactic validation.
They check that required evidence exists, includes the independently derived
minimum inputs, has valid contents and hashes, and applies to current sources.
They also distinguish a positive review from an unresolved mismatch or
inconclusive comparison. Draft units fail validation and cannot receive
affirmative correspondence decisions. The checks do not judge whether the recorded reasoning is
correct, launch a reviewer, compile Lean, or run the cited tests.

Run the mechanical checks separately:

```sh
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
```

From the repository root, `just test-lean` checks the formalization with
`lake build --wfail`, rejecting warnings such as those emitted by `sorry`.
`just book-v2` checks the rendered book and citations. Report those results
separately from the correspondence conclusion. A current review can coexist
with a failing proof check, and a passing proof check can coexist with a
missing or negative review.

The validator's `annotate-snippets` diagnostics point to the affected unit or
citation and give the preparation command. Read the reported cause before
preparing again: an invalid source target needs a source or citation fix, while
a stale packet needs renewed comparison. The test is a guard against missing
or stale work, not a semantic oracle.

## Record mechanical checks

`spec-checks.json` names executable checks separately from review units. From
`v2/`, build the CLI and run a selected check:

```sh
cargo build -p mdbook-dada --bin dada-spec
./target/debug/dada-spec run-check lean
./target/debug/dada-spec run-check lean-assumptions
./target/debug/dada-spec run-check rust
./target/debug/dada-spec run-check book
./target/debug/dada-spec mechanical-status
```

Each profile supplies an argument vector, working directory, tool-version
command, and source inputs. The runner stores an immutable receipt under
`evidence/executions/`, including both command outputs, exit statuses, and
snapshots before and after execution. It retains failures too. A recorded pass
requires exit zero, successful matching version probes, and unchanged source
snapshots. The assumptions check rebuilds Lean imports before printing the axiom
dependencies of the theorems named in `lean/CheckAxioms.lean`; its output covers
those declarations, not every theorem in the project.

Source directories include their file membership and contents. The fixed
exclusions are `.git`, `.lake`, `target`, `book`, and `evidence` directories;
selecting one as an input is rejected. Profiles and runner sources are always
included. These are declared source snapshots, not a hermetic capture: generated
artifacts, review records, installed dependencies, environment variables, and
network responses are not recorded as execution inputs. Endpoint comparison
also cannot detect an edit that is restored before the second snapshot.

`mechanical-status` compares the latest receipt for each named check with its
current profile and source inputs. A later failure or stale receipt cannot be
replaced silently by an older success. A timestamp tie is treated conservatively:
any stale or failing receipt at that time prevents a reported pass. Timestamps
are local provenance, not an authenticated ordering service.

`dada-spec check` and the ordinary Cargo evidence test validate retained receipt
integrity without executing commands. They do not require a fresh mechanical
pass: requiring the Cargo test to have a successful receipt for its own run would
be circular. Use `mechanical-status` to require current recorded passes. Records
are grouped by named check, not attributed automatically to every specification
unit. Neither hashes nor a saved exit code authenticate who ran the command or
establish correspondence with the prose.
