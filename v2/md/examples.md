# Following an execution

These are proposed machine scenarios. They are not yet executed or proved.
We use integers as the primitive parameter and names such as `p` as readable
labels for distinct runtime variable identities.
Arrows describe references, not concrete memory pointers.

## Construct a point

1. Starting with no variables, allocate fresh variable slots `p`, `t0`, and `t1`.
   Each begins uninitialized.
2. Create primitive objects `beta = 22` and `gamma = 44`, each owned by a temporary.
3. Create aggregate `alpha` with uninitialized fields `x` and `y`, owned by `p`.
4. Initialize `p.x` by transferring the owner of `beta` into that field.
5. Initialize `p.y` by transferring the owner of `gamma` into that field.

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
The empty temporary slots `t0` and `t1` can now be deallocated. The slot `p` must
first have its contents moved out or dropped before it can be deallocated.

## Nested scopes and fresh identities

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
this freshness across completed lifetimes or impose a last-in, first-out order.
Fresh-name generation and lexical cleanup belong to the execution semantics.

## A shared lease survives a change of ownership

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

This example deliberately distinguishes dynamically safe behavior from what a
future conservative type system may accept. It does not assert that v1 accepts
or correctly diagnoses this entire sequence.

## Mutation can disrupt sharing

Start with an owner `p` of the point from the first example and a shared lease
`q` of that point. Replace `p.x` with an owned reference to a fresh primitive
object containing `23`.

The intended example invalidates `q` through the mutation of the point. A later
attempt to access `q.x` faults; it does not merely observe `23`. If `q` is never
used again, that invalidation need not itself make execution fail.

This example specifies the whole-point shlease case. It does not decide how
references to disjoint fields interact; that needs separate examples and rules.

## Arrays expose partial initialization

Create an array of length two. Initialize element zero by transferring an owned
reference to a primitive object; leave element one uninitialized.

- Its length is two.
- Giving element zero through the owning array reference transfers that owner
  into a temporary and leaves the slot uninitialized.
- Giving element one faults because no value is present.
- Accessing element two faults because it is out of bounds.

Treat each faulting case as a separate execution from the described state; we
have not chosen whether faults leave partially changed states. Dropping the
array releases any still-initialized elements, while the value successfully
moved out remains owned by its temporary.
