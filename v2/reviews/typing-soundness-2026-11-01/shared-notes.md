# Shared correspondence renewal

Reviewer: Codex GPT-6 subagent `/root/review_shared_renewal`, 2026-11-01.

This is a source and statement comparison. It does not report Lean, Cargo, or
book-build execution, and it does not recheck theorem proof tactics. The review
read the Shared chapter, the bundled required units and exact source selections,
the correspondence-review policy, and supporting Shared example definitions,
well-formedness statements, and the Common/Rooted theorem assumptions.

## Scope clarification found during review

The original `shared.embedding` text said Shared translated “the Given language,”
and `shared.boundaries` quantified over “every Given program.” Given now also has
the separately described unpacking extension. The selected definitions operate
on `Unique.Statement`, whose only form binds one destination variable, and
`Unique.Program`; they do not translate `Unique.Unpacking.Statement` or its
machine. The repository instructions state this boundary, but the chapter
should state it too. This finding was sent to the coordinating agent before
affirmative reviews of those packets. The requested correction is to identify
the base Given fragment with single-variable bindings and exclude unpacking.

The correction was applied to `shared.embedding`, `shared.correspondence`, and
`shared.boundaries`. The replacement embedding packet also includes
`given.unpacking` and its dependencies. I read the complete revised units and
their added exact source selections before issuing the fifteen positive reviews
under `shared/`. The reviewed replacement bundle digests are
`c1946fc7c767cfb9a0a86acc0c6ff37714d00f9104b7b58e37696c7c5fe49905`
(embedding),
`f4a0a2177d255980a0b819b5f1b4bddfc51ab809b11e31e4f5d48584a43d4a5e`
(correspondence), and
`e4a797ef53176246b798842061b452a9144be2e0d05cb2099f5e4a400efd20ef`
(boundaries). No unresolved discrepancy remains in these reviewed claims.

## Semantic comparison

- `Mode` is a field of `Reference`, while `Object` holds only a class name and
  field slots. `Resolve.field` joins the prefix and final stored-reference
  modes; `Mode.join` is unique only for two unique inputs.
- `Give.move` combines unique resolution with `Take`. `Give.copy` requires
  shared resolution and a stored shared final reference. `Give.promote`
  requires shared resolution and changes the final stored unique reference to
  shared. The result's object identity is preserved in all three cases.
  `Take` and `Promote` replace one occurrence, preserving other slots, keys,
  object identities, and the counter. `Eval.giveShare` changes the returned
  reference's mode without recursively changing object fields.
- `EvalArgs.cons` evaluates the head before the remaining arguments, carrying
  the resulting state forward. `Eval.new` checks declared fields, matching
  argument count, and freshness at the counter after argument evaluation.
  `Step.letValue` checks destination freshness after evaluation, binds the
  result, and removes exactly the first statement.
- The three examples name complete source and destination states. Their
  definitions show the two empty variables, the unchanged box-field mode after
  give-share, final promotion on field copy, all named object identities, and
  counters 2 or 3 as described. The nested example includes the unique/shared/
  unique route and preserves the outer unique reference.
- `WellFormed` imposes unique table keys, declared ordered field shapes,
  allocated-ID bounds, strictly older field targets, pairwise compatibility of
  owning occurrences, and equivalence between stored targets and allocated
  objects. Compatibility counts occurrences, not distinct reference values;
  duplicated shared references are permitted and any unique incoming owner
  excludes all other owners of that object.
- Liveness follows variable roots and field edges regardless of mode.
  `WellFormed.live_iff_allocated` requires well-formedness, with no reachability
  or class-table-well-formedness assumption. The supporting generic graph
  theorem uses bounded ranks, coverage by roots or incoming fields, and strictly
  decreasing field edges. The Shared well-formedness conditions supply these.
- `WellFormed.path_mode_exclusive` assumes well-formedness and two resolutions
  to the same object, one unique and one shared, and concludes `False`.
  Paths start at variables by `Place` and `Resolve`; the result does not claim
  that every unique stored reference is accessible by an entirely unique path.
- `Steps.from_initial` quantifies over any finite successful execution of a
  program with a well-formed class table. It gives structural well-formedness
  at the reached configuration. The liveness and exclusivity consequences use
  the cited dependencies; it does not assert progress or successful execution
  of an arbitrary program.
- `step_correspondence` quantifies over an arbitrary Shared successor. It
  produces a Given successor and equality with its embedding, rather than
  assuming the Shared destination is already in the embedding's image. There
  is no hidden well-formedness or reachability premise. `boundary_correspondence`
  uses the program's class table for stuckness and covers arbitrary base Given
  configurations, not just reachable ones.

Notation comes from `shared.give` and `shared.syntax` for places, expression
forms, and statements; `shared.state` for modes, references, slots, identities,
and storage; `shared.resolution` for access-mode resolution; `shared.steps` for
configurations and execution; and `shared.well_formed` for the liveness and
well-formedness concepts. Earlier Given units supply class-table and finite-map
notation, and the original Given syntax and transition rules used by the
embedding. The theorem claims do not rely on proof-tactic descriptions.
