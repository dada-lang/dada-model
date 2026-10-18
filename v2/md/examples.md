# Following an execution

Examples with a Rendered/Lean selector cite a checked Lean `example` declaration.
They assert particular transitions and their complete resulting states. The
longer scenarios below are explicitly proposed: path operations, lease-following
moves, and resource cleanup effects are checked in the
[place-operations chapter](place-operations.md), but initialization, invalidation,
and complete scope cleanup remain unfinished.

We use integers as the primitive parameter where a payload is needed and names
such as `p` as readable labels for distinct runtime variable identities.
Arrows describe references, not concrete memory pointers.

## Checked creation examples

Every case starts with empty object and variable stores, allocates a destination,
and creates an object there. The Lean cases fix the destination and object
identities to index zero in their distinct identity types. Each checks the
complete successor state, including the destination's owned reference.

```{example} Heap:integer_primitive
Choose integers as the primitive values. Allocate `x`, then perform
`createPrimitive(22, x)`. The object store contains exactly one primitive object,
whose payload is `22`; the variable store contains exactly `x`, holding that
object's owned reference.
```

```{example} Heap:aggregate_fields
Allocate `x`, then perform `createAggregate(["x", "y"], x)`, where the quoted
names are fields and the final `x` is the runtime variable identity. The
result contains one aggregate with exactly those two uninitialized field slots.
The destination holds the aggregate's owned reference.
```

```{example} Heap:empty_aggregate
Allocate `x`, then perform `createAggregate([], x)`. This succeeds: the object
store contains an aggregate whose field map is empty, and `x` holds its owner.
No primitive value is needed, so this case works for any primitive parameter.
```

```{example} Heap:array_slots
Allocate `x`, then perform `createArray(2, x)`. The new array contains exactly two
uninitialized slots, and `x` holds its owned reference. Array length is independent
of the primitive-value parameter.
```

```{example} Heap:empty_array
Allocate `x`, then perform `createArray(0, x)`. The resulting array has no elements,
and `x` still owns a newly created object. A zero-length array is different from
an absent object or an uninitialized destination.
```

The [variable-lifetime example](operations.md#variable-allocation-and-deallocation)
also checks allocation of two slots, rejection of removing the outer slot while
the inner one is live, and removal of both slots in reverse allocation order.

## Proposed complete executions

{informational} These scenarios have no Lean test for the complete execution yet.
They identify intended behavior for rules still under development; the checked
examples above cover only allocation and creation. They must acquire cited Lean
cases as the remaining rules are formalized.

### Construct a point

1. Starting with no variables, allocate fresh variable slots `p`, `t0`, and `t1`.
   Each begins uninitialized.
2. Perform `createPrimitive(22, t0)` and `createPrimitive(44, t1)`, choosing fresh
   object identities `beta` and `gamma`. The temporaries now hold their owners.
3. Perform `createAggregate([x, y], p)`, choosing fresh identity `alpha`. Its
   fields begin uninitialized, and `p` holds its owner.
4. Initialize `p.x` by transferring the owner of `beta` into that field.
5. Initialize `p.y` by transferring the owner of `gamma` into that field.

Steps 1–3 use the formalized allocation and creation rules. Steps 4–5 describe
the intended initialization and transfer rules that remain to be defined.

```{heap}
vars = variables()
α = object(Point, "α")
β = primitive(22, "β")
γ = primitive(44, "γ")
vars.p = owned(α)
vars.t0 = uninitialized()
vars.t1 = uninitialized()
α.x = owned(β)
α.y = owned(γ)
```

The resulting state contains three objects and exactly one owned reference to
each. Moving the temporary references into fields does not duplicate ownership.
The empty temporary slots can now be deallocated in reverse allocation order:
first `t1`, then `t0`. The slot `p` must then have its contents moved out or
dropped before it can be deallocated.

### Nested scopes and fresh identities

An outer source binding `p` and an inner binding that shadows it receive distinct
runtime identities, say `p₀` and `p₁`. Allocate `p₀` when entering its binding's
lifetime, then allocate `p₁` when entering the inner binding's lifetime. Leaving
the inner scope releases any contents of `p₁` and deallocates its now-empty slot;
`p₀` remains allocated throughout. Source-name lookup chooses the visible binding,
but the heap retains both slots while both lifetimes are active.

Function calls follow the same convention: the execution semantics α-renames the
callee's variables to fresh runtime identities. The caller's live variables stay
in the store while the callee executes. A later call uses new identities even if
it has the same source-level parameter names. The heap rules alone do not enforce
this freshness across completed lifetimes. They do enforce last-in-first-out
deallocation: the callee's slots must be removed before the caller's older slots.
Fresh-name generation and the scheduling of lexical cleanup belong to the
execution semantics.

### A shared lease survives a change of ownership

For this example use a single primitive object `alpha = 22`, avoiding field-access
composition while we focus on lifetime. Allocate fresh, uninitialized variable
slots `p`, `q`, `t`, `s`, and `u` before using them as destinations.

| Step | Owning references to alpha | Shared leases to alpha |
| --- | --- | --- |
| Create alpha in p | p: owned | none |
| Share p into q | p: owned | q |
| Give p into temporary t | t: owned; p is empty | q |
| Independently share t into s | s: showned; t is empty | q |
| Share s into u | s and u: showned | q |
| Drop s | u: showned | q |
| Drop u | none; alpha is destroyed | q is invalid |

This scenario illustrates {anchor-ref}`heap.drop.nonfinal_showned` and
{anchor-ref}`heap.drop.final_owner`.

After dropping `s`, access through `q` can still succeed: the remaining owner
keeps the same object alive. After dropping `u`, access through `q` must fault.
The invalid reference may remain visible in a diagnostic diagram even though it
cannot be used. How the state records that invalidity is an open representation
choice.

This proposed execution distinguishes dynamic validity from acceptance by a
conservative type system. Its validity conditions and static acceptance remain
separate obligations.

### Mutation can disrupt sharing

Start with an owner `p` of the point from the first example and a shared lease
`q` of that point. Replace `p.x` with an owned reference to a fresh primitive
object containing `23`.

The intended example invalidates `q` through the mutation of the point. A later
attempt to access `q.x` faults; it does not merely observe `23`. If `q` is never
used again, that invalidation need not itself make execution fail.

This example specifies the whole-point shlease case. It does not decide how
references to disjoint fields interact; that needs separate examples and rules.

### Arrays expose partial initialization

Allocate an empty destination `a`, then perform `createArray(2, a)`. The creation
rule gives `a` ownership of a fresh array with two uninitialized slots. The
remaining steps are proposed: initialize element zero by transferring an owned
reference to a primitive object, and leave element one uninitialized.

- Its length is two.
- Giving element zero through the owning array reference transfers that owner
  into a temporary and leaves the slot uninitialized.
- Giving element one faults because no value is present.
- Accessing element two faults because it is out of bounds.

Treat each faulting case as a separate execution from the described state; we
have not chosen whether faults leave partially changed states. Dropping the
array releases any still-initialized elements, while the value successfully
moved out remains owned by its temporary.
