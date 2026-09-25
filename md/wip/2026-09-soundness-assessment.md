# September 2026 soundness assessment

Status: assessment and regression-test catalog; constructor field-type restrictions and the goal of scope-equivalent explicit drop are agreed; implementation design is still in discussion. The predicate vocabulary migration is implemented; the soundness fixes remain pending.

This document records the September 22, 2026 review of the borrowing model and the
subsequent discussion. It distinguishes reproduced failures from concerns that
still need isolated tests. The findings concern the current implementation; they
do not establish that the permission algebra itself is unsound.

The existing baseline passed `cargo test --all --workspace`: 624 model tests and
7 mdBook preprocessor tests. Temporary probes used `test_util::test_interpret`,
which checks a program before interpreting it. Those probes were not committed
as regression tests. The snippets below preserve the relevant inputs and results.

## Summary

| ID | Case | Evidence | Intended outcome |
|---|---|---|---|
| S1 | Loans in partially constructed aggregates | Accepted program reads uninitialized storage; duplicate mutable aliases also accepted | Reject conflicting initializer accesses |
| S2 | Block scope exit | Accepted out-of-scope use faults; escaping local borrow accepted | Pop locals and validate escaping values/dependencies |
| S3 | Explicit drop of copyable values | Accepted scalar/shared-value programs fault after drop | Destroy the stored value as scope cleanup would, including borrowed-reference storage |
| S4 | Destructor liveness and dispatch | Borrowing destructor probe accepted but destructor skipped | Establish destructor lifetime and execution rules; add isolated tests |
| S5 | Branch environment flow | Source inspection: branches are checked sequentially | Check from a common incoming environment and reconcile outcomes |

## S1: Loans in partially constructed aggregates

Relevant code: `type_field_exprs_as` and `type_exprs` in
`src/type_system/expressions.rs`; `env_permits_access` in
`src/type_system/accesses.rs`; `liens` in `src/type_system/local_liens.rs`.

### Reproduced: later initializer destroys an earlier field's referent

```dada
class Data { n: Int; }
class Pair[ty T] { a: T; b: Int; }
class Main {
    fn main(given self) {
        let x = new Data(42);
        let p = new Pair[mut[x] Data](x.mut, { x.drop; 0; });
        print(p.a.n.ref);
    }
}
```

The checker accepts this. The interpreter faults with `access of uninitialized
value` when reading `p.a.n`. Giving a previously named borrow as the first
initializer (`let a = x.mut; ... (a.give, { x.drop; 0; })`) also reproduces it.

### Reproduced: two mutable aliases

With `class Twins[ty T] { a: T; b: T; }`, this body is accepted:

```dada
let x = new Data(42);
let p = new Twins[mut[x] Data](x.mut, x.mut);
p.a.n = 1;
print(p.b.n.ref);
```

Execution prints `1`. The two independently addressable fields retain mutable
aliases to the same data.

### Discussion: place liveness versus a live value's dependencies

This appears to be an implementation oversight. The later `x.drop` already
makes `x` syntactically live while the earlier initializer is checked. That
only says that the source will be accessed again; it does not represent the
loan retained by the first evaluated argument when checking the second.

The later `p.a.n.ref` does require the stored `mut[x] Data` to remain valid.
Once `p` exists, access checking can derive its loans from its type. During
initialization, however, `p` is not yet bound. The loan must be carried by the
already evaluated field value or partial aggregate at that point.

One possible formulation is liveness of values/types, with their dependencies
protected transitively. The current `liens` machinery already recursively
follows permission dependencies for the live types it is given. The missing
piece here is including the retained initializer value among those live values.
Simply adding `x` to the ordinary live-place set does not establish that `x` is
mutably borrowed, and would not by itself reject the second `x.mut`.

We should distinguish protecting a referent from keeping every intermediary
syntactically live: the latter can affect intended dead-link cancellation and
move tracking. The current proposed direction is independent argument temporaries,
with field dependencies translated between those temporaries and aggregate fields.
Whether to share the argument-checking implementation with method calls remains open.

### Agreed field-type restrictions

These restrictions apply specifically to **the types of fields**:

- Bare `self` is forbidden in a field type. A place rooted in `self` must select a field, such as `self.foo` or `self.foo.bar`.
- That first field must occur strictly earlier in declaration order than the field whose type is being checked. Forward references and references to the current field are forbidden.
- This decision does not ban bare `self` in method signatures or bodies.

The earlier-field restriction makes construction dependencies follow initialization
order and avoids requiring access to a not-yet-initialized argument.

### Proposed implementation steps

This is a multi-step change; only the restrictions above are settled policy.

1. **Field-type well-formedness.** Check references rooted in `self` against the
   preceding fields. Add negative tests for bare `self`, forward references, and
   current-field references, plus positive tests for earlier-field projections.
   Apply the check throughout nested field-type/permission arguments.
2. **Translate expected field types.** Map `self.foo` to the independent argument
   temporary for `foo`, preserving any remaining projections. The existing
   variable-root substitution operations may need a place-prefix substitution
   helper; inspect this before choosing the implementation.
3. **Retain evaluated arguments.** Evaluate arguments left to right, keeping all
   completed argument temporaries live while checking subsequent arguments.
   Use their actual evaluated types to retain loans, as method calls do.
   Do not activate loans for unevaluated fields by marking the entire aggregate
   temporary live from the start.
4. **Assemble the result.** Transfer each argument into its destination field and
   remap dependent places from argument temporaries to aggregate fields before
   removing the temporaries. Preserve dependencies in both the resulting type
   and other affected environment bindings. This is ownership transfer, not
   destruction of argument values.
5. **Validate the complete behavior.** Add S1's negative cases and positive
   self-reference/move-tracking cases. Audit existing constructor tests for
   compatibility with the agreed field-order restriction. Decide separately
   whether factoring out a shared method-call/constructor argument rule improves
   clarity.

Method calls already keep evaluated receiver/argument temporaries live. Once a
constructor or call result has been bound to `p`, a later use such as `p.a.n = 1`
makes `p` live and its type contributes loans. The missing protection is during
initializer evaluation, before `p` is bound.

### Candidate tests and questions

- [ ] Reject the borrow-then-drop constructor above.
- [ ] Reject two mutable aliases in different constructor fields.
- [ ] Cover a named borrow moved into the first initializer.
- [ ] Preserve valid construction with disjoint referents.
- [ ] Compare with method arguments, which already keep evaluated arguments in live temporaries.
- [ ] Audit tuple evaluation for the same missing retained values.

Tuple probes `(x.mut x.drop)` and `(x.mut x.mut)` are accepted. They are not
runtime proofs of retained tuple aliases: the interpreter currently evaluates
and drops each tuple element and returns unit. Tuple representation must be
accounted for when designing end-to-end tests.

## S2: Block scope exit

Relevant code: `src/type_system/blocks.rs`, `src/type_system/pop_normalize.rs`,
and interpreter `eval_block` / `drop_block_scoped_vars`.

The checker returns the entire environment produced by a block. The interpreter
removes the block's locals. Block-local popping was explicitly deferred in
`var-pop-normalization.md`; this is an omitted implementation step rather than
evidence against the permission design.

### Reproduced: name escapes its lexical scope

Using `Data` from S1, this method body is accepted:

```dada
{ let x = new Data(42); (); };
print(x.give);
```

The interpreter faults with `undefined variable` (the actual name is alpha-renamed).

### Reproduced: borrow escapes its referent's scope

```dada
let r = { let x = new Data(42); x.mut; };
print(r.n.ref);
```

This also passes checking. The runtime probe displayed an unexpected `MutRef`
word instead of an integer. Replacing the final statement with `print(r.give)`
triggered an interpreter assertion. These runtime symptoms also involve runtime
type/scope handling; neither constitutes a successful execution of the borrow.

### Candidate tests and questions

- [ ] Reject out-of-scope variable use.
- [ ] Reject an escaping borrow of an owned block local.
- [ ] Accept an owned value moved out of a block.
- [ ] Accept a borrow forwarded through a local when its actual referent outlives the block.
- [ ] Check loans in outer variables affected by the block, not only the returned type.
- [ ] Preserve ordinary drop order and destructor dependencies at exit.

The scope omission is straightforward, but repairing it requires validating
escaping types/dependencies before deleting the bindings needed to resolve them.
Reuse of call-pop normalization is a candidate, not yet a settled implementation.

## S3: Explicit drop of copyable values

Relevant code: the `drop place` and `move_place` rules in
`src/type_system/expressions.rs`; interpreter `drop_place`.

### Reproduced mismatch

```dada
let x = 42;
x.drop;
print(x.give);
```

The checker accepts this; execution faults with `access of uninitialized value`.
The same occurs with `let x = new Data(42).share; x.drop; print(x.n.ref);`.

### Agreed goal: explicit drop performs scope cleanup of the stored value

`x.drop` should destroy the value stored in `x` just as scope cleanup would.
It does not first copy/give that value. This supersedes the initial
copy-then-drop proposal. For a borrowed reference stored in our own slot, destroy
that stored reference, not the referent. For `r.field.drop` through a borrowed
receiver, the intended behavior is a no-op: do not destroy the referent's field. Copyability does not permit reading the destroyed value later.
Unlike leaving lexical scope, explicit drop can leave the binding available for
reinitialization; cleanup semantics, not name removal, are being equated here.

### Current paths and differences

- Explicit `.drop` resolves a place all the way to `ObjectData`, asserts its
  contents initialized, then calls `drop_place`. Given/shared access calls
  `drop_value`; borrowed/mut access is a no-op.
- `eval_block` drops locals in reverse declaration order. `call_method` then
  drops remaining receiver/parameter slots. Both call `drop_value` directly on
  an `ObjectValue` (storage pointer plus stored type), without copying or
  dereferencing the final stored borrow. The returned value is retained.
- `drop_value` runs eligible destructors and traverses stored fields. Cleanup
  scrubs mut-reference words, clears borrowed boxed wrappers without releasing
  their referents, and releases owned/shared resources. Already uninitialized
  boxed fields are skipped; a partial object's destructor is skipped while its
  remaining fields are cleaned up.
- Reassignment also calls `drop_value` on old destination contents.
- Explicit-drop typing reuses `move_place`, which allows later reads when the
  type is copyable and can rename dependent places to an in-flight result. Drop
  has no transferred result, so that is not the appropriate operation.

### Proposed changes (not implemented)

1. **A distinct checker rule for destruction.** Preserve `Access::Drop` loan
   conflict checks, but remove the copy escape from `move_place`. For the basic
   initialized-place case, require `!live_after.is_live(place)` independently of
   copyability. Do not relocate the destroyed place into `@in_flight`. Retain
   the declared binding/type for assignment. Existing backward liveness kills
   uses across whole-place reassignment, so `x.drop; x = ...; use(x)` need not
   be rejected merely because the newly initialized value is used.
2. **Resolve the stored value, not its final referent.** Factor place resolution
   so the final `ObjectValue` is available before `object_value_to_data` performs
   the last dereference. Intermediate dereferences are still needed to reach
   fields. Preserve the containing object's access permissions alongside the
   declared storage type. Do not pass an effective borrowed view type when the
   actual slot has a different layout or ownership.
3. **Reuse cleanup.** Route explicit destruction of an authorized slot through
   the same `drop_value` as scope exit, replacing `drop_place`'s borrowed/mut
   no-op. This scrubs the reference slot while leaving its referent intact and
   preserves shared refcount decrements without incrementing them first.
4. **Preserve borrowed-projection behavior.** A local `r.drop` destroys our
   reference slot. In contrast, `r.field.drop` through a borrowed receiver is
   intended to be a no-op, not a destructive operation on the referent's field.
   Preserve the containing access mode during resolution to distinguish these
   cases. A borrowed reference stored as a field of an owned object is still
   our field slot and can itself be cleaned up. Do not apply a blanket
   “declared field type is owned, therefore destroy it” rule. Align the checker
   with these cases rather than indiscriminately requiring every syntactic
   `.drop` target to be dead. Shared projections also need explicit coverage.
5. **Reconcile partial cleanup and documentation.** The unconditional
   `assert_place_initialized` differs from cleanup of partially moved objects.
   Reuse cleanup's behavior on the target while still requiring valid prefixes
   for field traversal. A blanket liveness check may be conservative for
   `move(field); object.drop`: currently drop counts as accessing the whole
   object. Decide whether a distinct drop-liveness/initialization treatment is
   needed to accept exactly the cases scope cleanup can handle. Define whether
   repeated explicit drops are accepted statically; eventual scope cleanup must
   always avoid double destruction.

The straightforward initial case is a local initialized slot. Exact agreement
for projected or partially initialized places requires the additional checks
above. S4's destructor dispatch/liveness problems remain separate: sharing
`drop_value` shares its current behavior, not a proof that all cleanup is sound.

### Regression plan

- [ ] Reject read-after-drop for scalars, shared owned values, ref borrows, and mut borrows.
- [ ] Allow reading/mutating the owner after its last reference is explicitly dropped.
- [ ] Preserve other copies of a ref borrow and their remaining loans.
- [ ] Reject dropping a reference slot while another live value depends on that slot.
- [ ] Accept reinitialization of a dropped local before subsequent use.
- [ ] Check shared refcounts, destructor counts, and absence of double cleanup at scope exit.
- [ ] Drop a borrowed field in an owned aggregate without destroying its referent or sibling fields.
- [ ] Verify `r.field.drop` through ref/mut access is a no-op and leaves the owner intact; distinguish it from dropping a reference stored in an owned field.
- [ ] Specify and test shared-projection behavior without destroying another handle's storage.
- [ ] Compare explicit cleanup and scope cleanup of partially moved aggregates.
- [ ] Test storage scrubbing directly for mut refs: preserving the referent alone does not prove the reference slot was destroyed.

Update `md/interpreter.md` and `md/wip/unsafe.md`, and replace the old successful
borrow-reuse tests (`interp_drop_borrowed_noop` and `drop_borrowed_is_noop`) with
negative checker tests and positive referent-survival tests. The existing
`mut_drop` test's comment claims the reference is scrubbed, but its final heap
snapshot occurs after scope cleanup and therefore does not establish that
explicit `.drop` performed that scrubbing.

## S4: Destructor liveness and dispatch

Relevant code: `src/type_system/liveness.rs`, `env_permits_access` in
`src/type_system/accesses.rs`, and interpreter `drop_value`.

An object's last explicit use need not be its last access: its destructor may
still read or mutate data reached through borrowed fields. Current access
checking draws its live types from syntactic liveness, without an explicit
account of those future destructor accesses.

### Probe and its limitation

```dada
class Data { n: Int; }
given class Watch[perm P] {
    v: P Data;
    drop { print(self.v.n.ref); }
}
class Main {
    fn main(given self) {
        let x = new Data(42);
        let w = new Watch[mut[x]](x.mut);
        x.drop;
    }
}
```

This is accepted, but the interpreter does not execute `Watch`'s destructor.
**Confirmed bug in destructor dispatch:** `drop_value` gates execution on
`is_owned_type`, whose meaning is that a type contains no borrowed values.
The instantiated borrow-containing type fails that predicate, even though we
own the `Watch` wrapper and must run its destructor. The user confirmed this
is a bug: cleanup must distinguish ownership of the wrapper/handle from the
recursive `owned` property. This masks the destructor use-after-drop in the
probe. There are two separate changes to address:

1. Which values must run their destructor? Owning a wrapper and being independent
   of all borrowed data are different properties. Replace the inappropriate
   recursive `owned` dispatch condition with a check for ownership of the value
   being destroyed, retaining the required initialization checks.
2. Which referents must remain protected until that destructor executes?

The guard-related restrictions on permission cancellation do not by themselves
supply destructor liveness for all borrowed fields.

### Candidate tests and questions

- [ ] A live-referent control case verifies that `Watch` actually runs its destructor.
- [ ] Reject destruction of a referent before a dependent destructor executes.
- [ ] Accept explicitly dropping the dependent object first, then its referent.
- [ ] Verify implicit scope-exit ordering and overwrite-triggered destruction.
- [ ] Decide how destructor accesses contribute to liveness without unnecessarily extending all ordinary borrows.

## S5: Branch environments

Relevant code: the `if` rule in `src/type_system/expressions.rs`.

The rule currently passes the environment produced by the true branch into the
false branch and returns the latter environment. Execution chooses just one
branch. This matters for introduced bindings and for place dependencies renamed
by moves. The issue was identified by source inspection; no isolated branch
regression was run in the original assessment.

### Proposed tests (not yet validated)

A simple negative candidate, using `Data` from S1:

```dada
if false { let x = new Data(42); (); } else { print(x.give); };
```

The false branch must not see a declaration from the true branch. This also
exercises S2, so it should not be the only branch regression.

A complementary positive candidate:

```dada
let x = new Data(42);
if true { let y = x.give; (); } else { let y = x.give; (); };
```

Each branch has its own `y` and independently consumes `x`. Sequential branch
environments can cause false rejection as well as unsound acceptance.

- [ ] Validate the candidates and record their actual current outcomes.
- [ ] Add branch-local scope tests with both condition values.
- [ ] Isolate dependency-renaming cases using outer bindings, so they remain meaningful after S2 is fixed.
- [ ] Test both branch orders to expose accidental dependence on checking order.
- [ ] Include valid exclusive-branch moves and invalid post-branch uses.
- [ ] Choose how to reconcile different outgoing environments/loan locations.

Yes, these should be expressible as failing regression tests. Merely checking
both branches from the same incoming environment is not a complete fix: the
post-branch environment must also conservatively describe either outcome.

## Predicate vocabulary change (implemented September 25, 2026)

Renamed the former `copy` predicate to `shared`: it describes shared values,
including borrowed references. Any shared permission can be duplicated. `share` still means shareable. Removed the former
narrower `shared` predicate (`copy` plus `owned`); users express that less common
requirement as the conjunction of the new `shared` and `owned`.
This records predicate meaning, not a decision about adding shorthand grammar
for writing the conjunction.

| Previous predicate | Implemented spelling/meaning |
|---|---|
| `copy` | `shared` (shared values; can be duplicated) |
| `share` | `share` (shareable; unchanged) |
| `owned` | `owned` (fully owned; unchanged) |
| `shared` = `copy` + `owned` | Conjunction of new `shared` and `owned`; no separate predicate |

The `shared` permission remains shared ownership. The broader predicate can also
hold for a borrowed reference; it does not imply full ownership. Shallow ownership
of a wrapper/handle is an operational distinction needed by destructor dispatch,
not a new user-facing predicate.

- [x] Rename existing `copy` syntax, judgments, assumptions, and documentation.
- [x] Migrate uses of the old `shared` predicate to the conjunction where its
  ownership requirement matters; audit derived class-field requirements as well
  as explicit where-clauses so the rename does not silently weaken constraints.
- [x] Preserve permission/class syntax unless a separate change is decided.
- [x] Verify borrowed references satisfy new `shared` without necessarily
  satisfying `owned`, and that the conjunction preserves the old predicate.

### Vocabulary implementation notes

- The broader predicate is `ParameterPredicate::Shared`, proved by
  `prove_is_shared` / `prove_shared_predicate`. Removed the old narrower
  predicate; `prove_is_shared_owned` remains an internal conjunction helper.
- `ClassPredicate::Shared::parameter_predicates` now requires both `Shared`
  and `Owned`, preserving the old field requirement and its type-parameter
  assumptions. Permission/class syntax is unchanged.
- Where-clauses use `P is shared, P is owned` for the conjunction. No new
  shorthand grammar was introduced. The removed `copy` keyword is no longer
  reserved, and `is copy` is no longer accepted as a predicate.
- Added grouped regression cases for borrowed/owned/shareable types, generic
  shared-class field ownership, and predicate parsing.
- Validation: `cargo test --all --workspace` passes (627 model tests and 7
  mdBook preprocessor tests); `git diff --check` passes. The book build is blocked by the installed mdbook 0.4.51 versus
  the repository's mdbook-preprocessor 0.5 dependency (`missing field items`);
  dependency/toolchain changes are outside this vocabulary migration.

### Validation and deferred proof issue

The full workspace suite was rerun on September 25 after the documentation wording
changes: 627 model tests and 7 mdBook preprocessor tests passed, with no failures.
Six existing error snapshots changed during the migration because judgment names
and the narrower predicate's proof layer changed; their rejection outcomes did not.

- [ ] Investigate generic assumptions during composition proofs.
  `prove_shared_composed_predicate` calls `prove_shared_predicate` directly for
  each side, bypassing the assumption-aware `prove_predicate` dispatcher. This
  appears to predate the rename and complicated the generic shared-class field
  regression. That regression uses `shared P Data` with `P is relative` to
  isolate the ownership requirement. Add a focused reproducer before choosing a
  fix; the vocabulary migration does not change this proof path.

## Independent test-suite follow-ups

- [ ] Group positive/negative variants of the same scenario in one test function
  where it improves readability. Keep this independent of semantic fixes and
  preserve mdBook anchors when moving examples.
- [ ] Audit `assert_interpret_only!`, `assert_interpret_fault!`, and direct
  interpreter entry points. Prefer type-check-and-interpret for ordinary valid
  programs. For intentional UB counterfactuals, also assert checker rejection
  before testing the unchecked runtime fault, where applicable. Identify unsafe
  primitive examples separately; document any other temporary coverage gaps
  rather than silently bypassing the checker.
- [x] Recheck `partially_moved_class_drops_remaining_fields`: on September 23 its
  existing program passed both checking and interpretation. Converted it from
  `assert_interpret_only!` to `assert_interpret!`, preserving its snapshot. The
  wider bypass audit has not yet been completed.

## Next discussion

The central invariant to clarify is that every value which may still be
accessed—through explicit code, an unfinished expression, a returned value, or
a destructor—keeps the dependencies necessary for that access valid.

Before implementation, settle the representation of retained constructor loans,
block exit obligations, and destructor liveness. S3
records the agreed scope-cleanup goal and the remaining implementation questions. Keep regression results and implementation
decisions in this document as work proceeds.

- [x] Catalog reproduced cases and distinguish remaining hypotheses.
- [x] Trace existing explicit-drop and scope-cleanup semantics.
- [x] Agree that explicit drop should clean up the stored value like scope exit, including borrowed-reference storage.
- [x] Agree that field types forbid bare `self` and may reference only earlier fields of `self`.
- [ ] Select fixes after discussion.
- [ ] Add permanent regression tests, with failures checked for the intended reasons.
- [ ] Implement fixes and record validation/results here.

### Presentation of shared permissions

Use **shared permissions** as the category name. `shared` describes a shared
value, and `ref[d]` describes a shared value that references `d`. Any shared
permission can be duplicated. This is a wording change only; alternative
spellings and the presentation of permission composition remain undecided.
