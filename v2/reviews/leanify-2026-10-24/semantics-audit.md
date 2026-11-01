# Semantics audit — 2026-10-24

Reviewer: Codex subagent `/root/correspondence_formalization`.

This was a read-only adversarial review of the recursive expression semantics,
temporary ownership invariant, preservation statements, and examples. The reviewer
authored the correspondence module and mutual-inductive source selector, but did
not author the Unique/Shared evaluation or preservation implementation reviewed
here. No semantic source was changed during this review.

## Inputs examined

- `v2/lean/Unique/Step.lean` and `v2/lean/Shared/Step.lean`: `Eval`, `EvalArgs`,
  allocation, binding, statement transitions, and execution boundaries.
- `v2/lean/Unique/Soundness.lean` and `v2/lean/Shared/Soundness.lean`:
  `ClassesWellFormed`, `WellFormed`, `WellFormedWith`, pending-owner preservation,
  empty-pending conversions, statement preservation, and `Steps.from_initial`.
- `v2/lean/Unique/Liveness.lean` and `v2/lean/Shared/Liveness.lean`: rooted liveness,
  ownership counts, and shared/unique path exclusivity.
- `v2/lean/Unique/Examples.lean`: construction, field transfer, the failed second
  give, and nested construction.
- `v2/lean/Shared/Examples.lean`: sharing a container, field copying, shared access
  inside a longer path, and nested constructor arguments with repeated shared
  access.
- `v2/md/given.md` and `v2/md/shared.md`: the stated operational and invariant
  contracts against which those definitions and theorem statements were read.

## Conclusion

No actionable semantic findings.

`WellFormedWith` retains the original key, layout, allocation-bound, and age
conditions. It includes pending expression results in the same ownership
uniqueness or compatibility constraints and allocation-coverage condition as
stored references. Empty-pending conversions recover ordinary well-formedness.
The evaluation preservation statements quantify arbitrary prior pending owners;
neither evaluation nor its preservation theorem assumes a well-formed result.

`EvalArgs` threads storage left to right. Allocation checks freshness after the
arguments finish, and its arity condition together with `EvalArgs.length` prevents
field construction by `zip` from discarding results. A statement binds the single
pending result and restores the ordinary invariant.

The failed-second-give example states both stuckness and the impossibility of
reaching any finished configuration. The nested constructor example states the
complete final storage after one statement step. The shared nested-argument
example covers a pending unique constructor result while a later argument copies
the original shared source again.

## Mechanical evidence examined

The following temporary file was written as
`/tmp/dada-semantics-audit.lean` and checked from `v2/lean/` with:

```sh
lake env lean /tmp/dada-semantics-audit.lean
```

```lean
import Unique.Liveness
import Unique.Examples
import Shared.Liveness
import Shared.Examples
#print axioms Dada.Unique.Eval.preserves_pending
#print axioms Dada.Unique.Step.preserves_wellFormed
#print axioms Dada.Unique.Steps.from_initial
#print axioms Dada.Unique.WellFormed.live_iff_allocated
#print axioms Dada.Unique.second_give_stuck
#print axioms Dada.Shared.Eval.preserves_wellFormedWith
#print axioms Dada.Shared.Step.preserves_wellFormed
#print axioms Dada.Shared.Steps.from_initial
#print axioms Dada.Shared.WellFormed.live_iff_allocated
#print axioms Dada.Shared.WellFormed.path_mode_exclusive
```

The command exited successfully. Unique evaluation, statement and trace
preservation, and `second_give_stuck` reported
`[propext, Classical.choice, Quot.sound]`. Unique liveness and all five listed
Shared results reported `[propext, Quot.sound]`. None reported `sorryAx` or a
custom axiom. This check inspected compiled declarations; it was not a new full
project build or a replacement for the main task's build results.

## Limits

The claims establish preservation for successful execution, not progress. A
well-formed storage state can accompany a program that becomes stuck. The raw
relations also permit malformed inputs; duplicate-key or class ambiguity and
dangling references are excluded by the stated well-formedness assumptions.
This review does not establish determinism or a type-system safety theorem.

This report records the inputs and reasoning examined. It does not replace the
content-hashed correspondence evidence or assert freshness after later source
changes.
