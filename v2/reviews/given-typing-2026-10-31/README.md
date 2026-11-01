# Given typing design audit — 2026-10-31

This is a review of a Markdown design draft, not a Lean proof or an affirmative
correspondence decision. The exact source snapshots and examined scopes are in
[inputs.json](inputs.json). Source changes invalidate the affected observations;
new hashes alone would not constitute a renewed review.

## Scope and provenance

`/root/typing_soundness_design` checked the typing chapter, the proposed unpacking
extension, and the existing Given machine and ownership invariant. The parent
assembled the chapter with contributions from `/root/typing_views_design`,
`/root/typing_soundness_design`, and `/root/unpack_opsem_draft`. These agents helped
design the material they reviewed; this is not a blind or fully independent audit.

The review compared the proposed rules with their intended behavior and looked
for counterexamples. No new typing declarations or unpacking transitions exist
in Lean, so no prose/Lean correspondence is asserted for these draft units.

## Conclusion and rationale

No semantic counterexample was found. Progress and preservation appear plausible
under the stated restrictions, but remain proposed, unproved results.

- Realization describes every variable slot, including empty slots, making
  static freshness agree with runtime freshness.
- Global ownership accounting includes hidden fields and pending results.
  Forgetting a view does not remove references or abandon their objects.
- Expression soundness asserts that evaluation exists and describes every actual
  evaluation. Successful execution is not a premise of static typing.
- Unpacking requires known status for every direct field and transfers every
  slot, including empty ones. Only the enclosing object is removed.
- Configuration preservation keeps the final environment fixed while the
  current environment follows moves and bindings. Finished storage remains
  owned; no destruction or scope-exit theorem is assumed.

During review the draft made the declared-base/class well-formedness conditions
explicit, clarified the prefix meaning used by focus, moved the first view
examples before the formal observation sets, and replaced the undefined
“maximal execution” wording with a concrete extension-to-completion statement.

## Choices for human review and later formalization

The following choices are provisional: positive entries expose whole declared
subtrees; view entries are prefix-incomparable; constructor arguments must have
whole declared class types. These make the current rules coherent but reject
some dynamically safe programs. Unknown direct fields also prevent unpacking.

Lean formalization will need an owned-root separation lemma: moving through one
variable must preserve the views of all other variables and pending roots. It
will also need binding soundness, especially ownership preservation when
unpacking deletes a container and transfers its slots. These are proof tasks,
not additional assumptions in the draft typing rules.

## Mechanical checks and evidence status

The parent reports that `just book-v2` and 39 book tests passed. This reviewer did
not run those commands. No Lean source was changed or new typing proof checked.
The parent attached the final [evidence status](status.txt): 23 draft units and
41 stale older records after configuration and instruction changes. The command
exited with status 1. This audit does not approve or refresh those records.
The parent also checked the rendered chapter and retained a
[walkthrough preview](preview.png). `git diff --check` passed.
