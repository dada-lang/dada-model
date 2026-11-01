# Given and finite-map preliminary comparison

Reviewer: independent Codex subagent `/root/review_given_renewal`, 2026-11-01.
This is a source audit before receipt of the final immutable bundles, not an
affirmative evidence record. No tests were run and no proof tactics were audited.

## Inputs examined

- Root `AGENTS.md`, `v2/AGENTS.md`, `v2/spec.json`, and
  `md/repo/correspondence-review.md` and `md/repo/writing-style.md`.
- All 22 units in `md/given.md` and the three `evidence.map*` units in
  `md/repo/evidence-pilot.md`.
- `Unique/Syntax`, `Unique/State`, and `Unique/Step`: cited declarations and
  supporting `Take`, `State.bind`, and constructor/evaluation definitions.
- The `ClassesWellFormed`, `WellFormed`, `WellFormedWith`, and
  `Steps.from_initial` definitions/statements in `Unique/Soundness`.
- `WellFormed.live_iff_allocated` and `WellFormed.owner_count` statements in
  `Unique/Liveness`, including their implicit state/class/object parameters.
- `Unique/Examples`: cited example statements and named class, program, and
  state definitions needed to interpret them.
- `Unique/Unpacking`: patterns, configurations, transfer, binding and step
  definitions; preservation statement. `Unique/UnpackingChecks`: cited example
  statement and its class/program/state definitions.
- `Common/FiniteMap` and `Common/FiniteMapExamples`.

## Preliminary findings

No material discrepancy identified in these units. Final packet comparison is
still required before writing evidence decisions.

The introductions proceed from class/name categories to places and values,
program/class tables, identities/slots/states, direct storage places, and machine
configurations. Resolution and evaluation are then defined before the statement
rule and finite-execution/stuckness judgments. Liveness and well-formedness are
defined before the results using them. The machine unit introduces the step
notation and explicitly defers its rules to the subsequent operational section;
it does not use an undeclared judgment to establish a result.

The raw Lean types admit arbitrary lists, while the prose uses finite-map
notation and distinct fields. The state unit explicitly says that finite-map
notation assumes distinct keys and later well-formedness enforces it. This is
an exposed representation convention, rather than an unmentioned extra theorem
assumption. ClassesWellFormed checks both unique class names and each field list;
the program unit already states unique class names before its field-list
well-formedness sentence.

The give rule's slot update matches Take on the stated distinct-key model:
resolution locates an occupied slot, and taking replaces precisely that occupied
slot with an empty slot. Constructor evaluation is left to right, requires the
declared arity and a fresh next identity, creates fields in declaration order,
and increments the evaluated state's counter. Statement binding checks freshness
in the evaluated variable table, including names with empty slots. Finite traces
and stuckness match their reflexive/step and unfinished/no-successor definitions.

The token, field-give, nested-constructor, and repeated-empty-field examples
use the displayed class declarations, starting states/programs, and final states.
Their selected statements include the claimed step or trace, finished code, or
stuckness/non-completion. The three-step count of the field example follows from
its three statements and the Step definition's consumption of one statement.

The well-formedness prose covers unique table keys, declared ordered fields,
allocation bounds, older field targets, and unique complete reference occurrence
coverage. The liveness equivalence requires only storage well-formedness; owner
count additionally requires allocation. Steps.from_initial requires a well-formed
class table and a successful finite trace from the program's empty initial state.
The prose explicitly does not claim progress for arbitrary untyped programs.

Unpacking's Transfer consumes every field, permits field-order permutations,
and transfers empty slots. Bind checks class/layout identity, unique pattern field
and variable names, and fresh destinations; it removes only the consumed
container. The displayed rule uses declaration order as explicitly announced,
while the accompanying pattern definition permits other orders. Preservation
requires a well-formed class table and well-formed starting storage. The example
asserts the complete trace/final state and failure of a give from the transferred
empty left slot.

The finite-map definition has ordered entries and a Nodup key projection. Its
uniqueness theorem quantifies over a map, a key, two values and two membership
premises, concluding equality without ordering or decidable-equality assumptions.
The example specializes to natural numbers and states the empty entry list.

## Limits

This comparison checks statements and semantic dependencies, not proof tactic
correctness, Lean compilation, renderer behavior, or execution of cited examples.
Only the listed semantic material was examined; conservative context snapshots
must not be represented as a line-by-line audit of every proof in the repository.
