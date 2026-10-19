# Place operations

A place operation gives, leases, shares, or drops through an access path. The
path determines both a storage slot and the permission with which it is reached.
A result is stored in an allocated, uninitialized destination variable; no owner
exists outside the successor state. Variable allocation and object creation are
specified in [Operations on the machine](operations.md).

The runtime rules combine path resolution with reference updates. Dependent
leases follow a consumed reference to its destination, preserving their resolved
targets. Static access restrictions and runtime borrow validity are separate
obligations; the ownership proofs below do not establish either one.

## Resolving an access path

Write \\(\pi\\) for an access path, \\(p\\) for its selected place,
\\(\alpha\\) for the referenced object, and \\(\kappa\\) for effective access.
The four effective permissions are:

```{grammar} Access:AccessPermission
\kappa ::= \mathsf{given}\mid\mathsf{leased}\mid\mathsf{showned}\mid\mathsf{shlease}
```

`given` permits transferring unique ownership; `leased` provides unique borrowed
access; `showned` provides shared ownership; `shlease` provides shared borrowed
access. These describe the entire route, not just the final stored reference.
At each projection, the next reference changes the effective permission as follows:

| Next reference | Incoming `given` | Incoming `leased` | Incoming `showned` | Incoming `shlease` |
| --- | --- | --- | --- | --- |
| `owned` | `given` | `leased` | `showned` | `shlease` |
| `leased` | `leased` | `leased` | unavailable | unavailable |
| `showned` | `showned` | `showned` | `showned` | `showned` |
| `shlease` | `shlease` | `shlease` | `shlease` | `shlease` |

An owned field retains the restriction of its prefix. An independently shared
owner retains shared ownership even through a borrowed prefix. A unique lease
cannot be traversed through shared access.

```{judgment} Access:ResolvePath
S\vdash\pi\Downarrow p:\alpha\ @\ \kappa
```

For a reference already selected under incoming permission \\(\kappa_0\\),
the corresponding judgment resolves its target and effective permission:

```{judgment} Access:ResolveReference
S;\kappa_0\vdash r\Downarrow\alpha\ @\ \kappa
```

Resolution starts at the path's variable with incoming permission `given`. Each
field or index projection resolves its prefix to an object and then selects a
slot of that object. Fields must exist and array indices must be in bounds.
Following a unique lease reads its supporting slot and continues through a
finite chain providing unique access. Every referenced target must be allocated.

This judgment has no derivation for absent or uninitialized storage, a missing
target, or a support cycle without a finite resolution. It does not decide
whether an otherwise resolvable lease is currently active or has been invalidated
by a conflicting operation.

```{example} Access:shared_route_owned_field
A variable holds a shared lease of an aggregate, and the aggregate's `f` field
holds an owner of a primitive. Resolving the field gives `shlease` access to the
primitive. Encountering the inner owner does not restore unique access.
```

```{example} Access:shared_route_showned_field
With the same shared route to the aggregate, change its `f` field to an
independent showned reference. The field then resolves with `showned` access.
```

```{example} Access:shared_route_rejects_lease
A unique lease cannot resolve under incoming `shlease` access, regardless of
its supporting place or target.
```

```{example} Access:cyclic_lease_support
A slot containing a unique lease of itself cannot supply a finite resolution.
```

## Selected places and slot updates

We write \\(S(p)=s\\) when a slot exists with contents \\(s\\), and
\\(S[p\mapsto s]\\) for a successful update. An absent place differs from a
slot containing \\(\bot\\). A slot update cannot create a variable or field,
change an array's length, or write an out-of-bounds element.

```{theorem} Places:writeSlot_effects
A successful slot update changes exactly the selected lookup.

\\[
\frac{S'=S[p\mapsto s]}{
 S'(q)=\begin{cases}s&q=p\\S(q)&q\ne p\end{cases}
}
\\]

**Proof outline.** Split on whether the selected place and the observed place are
variables, fields, or array elements. Replacing a finite-map entry changes only
the matching key; replacing an array element changes only the matching index.
Every other lookup, including an absent place, retains its previous result.
```

This equality includes absence: every other lookup has exactly its previous
result. Updating a slot preserves the allocation order of variables:

```{theorem} Places:writeSlot_preserves_variable_order
A slot update preserves the exact allocation order of the variable store.

\\[
\frac{\langle O',V'\rangle=\langle O,V\rangle[p\mapsto s]}{
 \operatorname{keys}(V')=\operatorname{keys}(V)
}
\\]

**Proof outline.** Updating a variable replaces its contents in place, preserving
the sequence of keys. Updating an object field or array element leaves the
variable store unchanged.
```

A variable identity \\(x\\) in slot notation abbreviates its variable place.
Storage functions grant no access permission; the operation rules also require
path resolution.

```{grammar} PathOperations:PathOperation
\begin{array}{rcl}
\rho &::=& \mathsf{give}(\pi,x)\\
 &\mid& \mathsf{lease}(\pi,x)\\
 &\mid& \mathsf{share}(\pi,x)\\
 &\mid& \mathsf{drop}(\pi)
\end{array}
```

```{judgment} PathOperations:PathStep
S\xrightarrow{\rho}_{\mathsf{path}}S'
```

This is the successful runtime path-operation relation. A missing rule does not
by itself define a fault. The basic live-dependency restrictions described below
are a separate judgment.

## Give

Giving has different effects according to the effective permission:

| Effective access | Result in the destination | Source |
| --- | --- | --- |
| `given` | The unique owner | Cleared; dependent leases follow the move |
| `leased` | A unique lease of the selected place | Retained |
| `showned` | Another showned reference, when the selected slot already stores one | Retained |
| `shlease` | A shared lease of the target object | Retained |

The consuming-move judgment \\(S\rightsquigarrow_{p\to x}S'\\), defined in
[Consuming a reference](#consuming-a-reference), moves the reference and retargets
its dependents:

```{rule} PathOperations:PathStep.giveGiven
\frac{
 \begin{gathered}
 S\vdash\pi\Downarrow p:\alpha\ @\ \mathsf{given}\\
 S\rightsquigarrow_{p\to x}S'
 \end{gathered}
}{S\xrightarrow{\mathsf{give}(\pi,x)}_{\mathsf{path}}S'}
```

```{example} PathExamples:path_give_owner_retargets
Variable `x` owns primitive `22`, `y` holds `leased(x)`, and `z` is empty.
Giving `x` into `z` empties `x`, moves the owner into `z`, and changes `y` to
`leased(z)`. The primitive keeps its identity and value.
```

Giving through unique borrowed access creates a sublease. It does not consume
the selected reference:

```{rule} PathOperations:PathStep.giveLeased
\frac{
 \begin{gathered}
 S\vdash\pi\Downarrow p:\alpha\ @\ \mathsf{leased}\\
 S(x)=\bot\\
 S'=S[x\mapsto\mathsf{leased}(p)]
 \end{gathered}
}{S\xrightarrow{\mathsf{give}(\pi,x)}_{\mathsf{path}}S'}
```

```{example} PathExamples:path_give_lease_reborrows
With `x` owning a primitive and `y` storing `leased(x)`, giving `y` into empty
`z` stores `leased(y)` in `z`. Both `x` and `y` retain their contents.
```

```{rule} PathOperations:PathStep.giveShowned
\frac{
 \begin{gathered}
 S\vdash\pi\Downarrow p:\alpha\ @\ \mathsf{showned}\\
 S(p)=\mathsf{showned}(\alpha)\qquad S(x)=\bot\\
 S'=S[x\mapsto\mathsf{showned}(\alpha)]
 \end{gathered}
}{S\xrightarrow{\mathsf{give}(\pi,x)}_{\mathsf{path}}S'}
```

The stored-reference premise matters. Effective `showned` access can be inherited
through an inner `owned` edge. Simply adding a showned reference in that case
would leave unique and shared ownership together. An ownership-conversion rule
for that case remains to be defined; this rule does not silently perform one.

```{rule} PathOperations:PathStep.giveShlease
\frac{
 \begin{gathered}
 S\vdash\pi\Downarrow p:\alpha\ @\ \mathsf{shlease}\\
 S(x)=\bot\\
 S'=S[x\mapsto\mathsf{shlease}(\alpha)]
 \end{gathered}
}{S\xrightarrow{\mathsf{give}(\pi,x)}_{\mathsf{path}}S'}
```

```{example} PathExamples:path_give_shared_borrow
Variable `x` owns a primitive and `y` holds its shared lease. Giving `y` into
empty `z` creates another shared lease in `z`; `y` remains initialized and `x`
remains the owner.
```

Primitive payloads are opaque and all values are represented through objects.
Giving through borrowed access therefore follows the reference rules above;
type-specific copying of primitive payloads is not part of this machine.

## Lease and share

Leasing requires unique effective access and records the selected supporting
place. Both the existing reference and its target remain:

```{rule} PathOperations:PathStep.lease
\frac{
 \begin{gathered}
 S\vdash\pi\Downarrow p:\alpha\ @\ \kappa\\
 \kappa\in\{\mathsf{given},\mathsf{leased}\}\\
 S(x)=\bot\\
 S'=S[x\mapsto\mathsf{leased}(p)]
 \end{gathered}
}{S\xrightarrow{\mathsf{lease}(\pi,x)}_{\mathsf{path}}S'}
```

Sharing `given`, `leased`, or `shlease` access produces a shared lease of the
resolved object:

```{rule} PathOperations:PathStep.shareBorrow
\frac{
 \begin{gathered}
 S\vdash\pi\Downarrow p:\alpha\ @\ \kappa\\
 \kappa\ne\mathsf{showned}\\
 S(x)=\bot\\
 S'=S[x\mapsto\mathsf{shlease}(\alpha)]
 \end{gathered}
}{S\xrightarrow{\mathsf{share}(\pi,x)}_{\mathsf{path}}S'}
```

```{example} PathExamples:path_owner_borrows
Starting with an owner of primitive `22` in `x` and empty `y`, leasing `x` into
`y` produces `leased(x)`. Sharing `x` into `y` instead produces a shared lease of
the primitive object. Each result retains the owner in `x`.
```

Sharing actual shared ownership produces another owner:

```{rule} PathOperations:PathStep.shareShowned
\frac{
 \begin{gathered}
 S\vdash\pi\Downarrow p:\alpha\ @\ \mathsf{showned}\\
 S(p)=\mathsf{showned}(\alpha)\qquad S(x)=\bot\\
 S'=S[x\mapsto\mathsf{showned}(\alpha)]
 \end{gathered}
}{S\xrightarrow{\mathsf{share}(\pi,x)}_{\mathsf{path}}S'}
```

```{example} PathExamples:path_shared_owner_copies
When `x` already holds a showned reference and `y` is empty, either giving or
sharing `x` into `y` produces a second showned reference to the same primitive.
Neither operation removes the first owner.
```

Sharing an owned place creates borrowing; converting a unique owner into shared
ownership is a different operation and remains to be specified.

## Consuming a reference

A consuming move transfers one stored occurrence into an empty destination.
It applies when an operation consumes a reference, including a unique lease.
The `give` rule above uses it for `given` access; giving through `leased` access
reborrows instead.

Let \\(R_{p\to q}(S)\\) replace every stored `leased(p)` with `leased(q)`,
including occurrences in variables, aggregate fields, and array elements. All
other references retain their value. This simultaneous update preserves object
identities, object shapes, and variable order.

```{rule} Moves:MoveReference.move
\frac{
 \begin{gathered}
 S(p)=r\qquad S(q)=\bot\qquad p\ne q\\
 T=S[p\mapsto\bot]\\
 U=T[q\mapsto r]\\
 S'=R_{p\to q}(U)
 \end{gathered}
}{S\rightsquigarrow_{p\to q}S'}
```

Direct dependents follow the moved reference. Descendants still refer to their
unchanged intermediate supports:

```{theorem} Moves:MoveReference.dependent_follows
A consuming move redirects every direct dependent lease to the destination.

\\[
\frac{
 \begin{gathered}
 S\rightsquigarrow_{p\to q}S'\\
 S(t)=\mathsf{leased}(p)\qquad t\ne p
 \end{gathered}
}{S'(t)=\mathsf{leased}(q)}
\\]

**Proof outline.** The destination was empty, so it cannot be an existing
dependent lease. Transferring the selected reference preserves every other slot;
the simultaneous retargeting then replaces each direct support at the source
with a support at the destination.
```

```{example} Moves:move_owner_with_dependents
Let `x`, `y`, `z`, and `t` have runtime identities `0`, `1`, `2`, and `3`.
With `x` owning primitive `22`, `y = leased(x)`, `t = leased(y)`, and empty `z`,
moving `x` to `z` changes `y` to `leased(z)`. `t` still stores `leased(y)`, and
`x` becomes uninitialized.
```

```{example} Moves:move_lease_with_sublease
Starting from that same chain, consume `y` into `z` instead. `z` receives
`leased(x)`, `t` changes to `leased(z)`, and `y` becomes uninitialized. This tests
consuming transfer of the lease handle, not `give` through leased access.
```

```{example} ReferenceUpdates:retarget_all_storage
The whole-state retargeting helper updates direct dependents stored in a
variable, an aggregate field, and an array element. An array element supported
by an unchanged intermediate lease keeps that support. This test isolates the
retargeting phase; moving and clearing the source are checked separately above.
```

Retargeting also preserves what a successful lease resolution reaches. It does
not merely replace a name while leaving its meaning unchecked:

```{theorem} MoveValidity:MoveReference.dependent_keeps_target
A retargeted lease keeps the object and effective permission it previously resolved to.

\\[
\frac{
 \begin{gathered}
 S\rightsquigarrow_{p\to q}S'\\
 S;\kappa_0\vdash\mathsf{leased}(p)\Downarrow\alpha\ @\ \kappa
 \end{gathered}
}{S';\kappa_0\vdash\mathsf{leased}(q)\Downarrow\alpha\ @\ \kappa}
\\]

**Proof outline.** Induct on the finite resolution of the support chain. The move
preserves allocated objects and transports each initialized support occurrence: the
source moves to the destination, and every other occurrence stays in its slot.
Retargeting preserves reference kinds, so each permission-composition step
continues to hold.
```

```{example} MoveValidity:move_preserves_lease_resolution
For any successful consuming move and any unique lease that resolved through
its source before the move, the retargeted lease resolves to the same object
with the same effective permission afterwards. This checks finite support-chain
resolution, not the separate active-borrow restrictions.
```

Object-relative places stay stable when an enclosing owner moves. Moving the
owner of an aggregate therefore does not rename its field places. Moving a
reference out of one of those fields does retarget leases of that selected field.

## Drop and cleanup

Dropping a uniquely owned path invokes recursive reference release at its
selected place:

```{rule} PathOperations:PathStep.dropGiven
\frac{
 \begin{gathered}
 S\vdash\pi\Downarrow p:\alpha\ @\ \mathsf{given}\\
 S\xrightarrow{\mathsf{drop}(p)}_{\mathsf{effect}}S'
 \end{gathered}
}{S\xrightarrow{\mathsf{drop}(\pi)}_{\mathsf{path}}S'}
```

Dropping shared ownership requires the selected slot to hold the showned
reference. It also requires a writable route: every resolved strict prefix of
\\(\pi\\) must provide `given` or `leased` access. A direct variable path has
no strict prefixes and satisfies this condition.

```{rule} PathOperations:PathStep.dropShowned
\frac{
 \begin{gathered}
 S\vdash\pi\Downarrow p:\alpha\ @\ \mathsf{showned}\\
 S(p)=\mathsf{showned}(\alpha)\\
 \mathsf{writable}(S,\pi)\\
 S\xrightarrow{\mathsf{drop}(p)}_{\mathsf{effect}}S'
 \end{gathered}
}{S\xrightarrow{\mathsf{drop}(\pi)}_{\mathsf{path}}S'}
```

A shared prefix followed by an independently showned field permits duplicating
that field's ownership. Destructive drop would instead mutate the field in the
shared object, so it requires a writable route. Destructive access through a
shared prefix remains unspecified; the missing transition is not a declared
fault.

```{example} PathExamples:path_shared_prefix_not_writable
An owner and a shared lease both refer to an aggregate whose `f` field holds
showned ownership of a primitive. The path through the shared lease resolves
`f` with `showned` access, but its shared prefix makes the route nonwritable.
The destructive showned-drop rule therefore cannot use that route.
```

```{example} PathExamples:path_drop_final_owner
Variable `x` owns primitive `22`. Dropping the path `x` removes the primitive
object and leaves the allocated variable slot uninitialized.
```

```{example} PathExamples:path_drop_nonfinal_shared_owner
Variables `x` and `y` hold showned references to one primitive. Dropping `x`
clears its slot but preserves `y` and the primitive object.
```

### Borrowed-path drop versus releasing a handle

Dropping through borrowed access leaves the state unchanged, including the
borrow's own slot:

```{rule} PathOperations:PathStep.dropBorrow
\frac{
 \begin{gathered}
 S\vdash\pi\Downarrow p:\alpha\ @\ \kappa\\
 \kappa\in\{\mathsf{leased},\mathsf{shlease}\}
 \end{gathered}
}{S\xrightarrow{\mathsf{drop}(\pi)}_{\mathsf{path}}S}
```

```{example} PathExamples:path_drop_borrow_noop
Dropping a path whose variable holds a shared lease leaves the entire state
unchanged. The variable is still initialized afterwards.
```

This behavior does not supply the handle release needed before variable
deallocation. Scope cleanup needs a separate reference-removal effect, which
clears a borrowed slot without destroying its target:

```{rule} PlaceOperations:PlaceEffect.dropLeased
\frac{S(p)=\mathsf{leased}(q)\qquad S'=S[p\mapsto\bot]}{
 S\xrightarrow{\mathsf{drop}(p)}_{\mathsf{effect}}S'}
```

```{rule} PlaceOperations:PlaceEffect.dropShlease
\frac{S(p)=\mathsf{shlease}(\alpha)\qquad S'=S[p\mapsto\bot]}{
 S\xrightarrow{\mathsf{drop}(p)}_{\mathsf{effect}}S'}
```

```{example} PlaceExamples:unique_lease_release
The reference-update layer first creates `leased(x)` in empty `y`, then releases
that handle. It returns exactly to the original state, preserving the owner and
primitive. This is a cleanup effect, not the borrowed-path drop rule.
```

The relationship between borrowed-path drop and scope cleanup remains to be
specified. In particular, cleanup of a handle with surviving dependent leases
needs an explicit policy; these effects do not promote or invalidate those
dependents.

### Releasing the final owner

The effect relation works directly on selected storage:

```{judgment} PlaceOperations:PlaceEffect
S\xrightarrow{\mathsf{drop}(p)}_{\mathsf{effect}}S'
```

A showned occurrence can be removed while another owner remains:

```{rule} PlaceOperations:PlaceEffect.dropShowned
\frac{
 \begin{gathered}
 S(p)=\mathsf{showned}(\alpha)\\
 S(q)=\mathsf{showned}(\alpha)\qquad q\ne p\\
 S'=S[p\mapsto\bot]
 \end{gathered}
}{S\xrightarrow{\mathsf{drop}(p)}_{\mathsf{effect}}S'}
```

Write \\(\mathsf{last}(S,p,\alpha)\\) when \\(p\\) holds an owner of
\\(\alpha\\) and all owning occurrences targeting it are at \\(p\\).
An object is empty of references when it is primitive, or all its fields or
array elements are uninitialized. Releasing its final owner removes it:

```{rule} Destruction:DropLeaf.release
\frac{
 \begin{gathered}
 \mathsf{last}(S,p,\alpha)\\
 \mathsf{emptyObject}(S,\alpha)\\
 T=S[p\mapsto\bot]\\
 S'=T\setminus\alpha
 \end{gathered}
}{S\xrightarrow{p,\alpha}_{\mathsf{leaf}}S'}
```

Here \\(T\setminus\alpha\\) removes exactly object \\(\alpha\\). The source
slot survives, uninitialized. This is a leaf case of the drop effect:

```{rule} PlaceOperations:PlaceEffect.dropLeaf
\frac{S\xrightarrow{p,\alpha}_{\mathsf{leaf}}S'}{
 S\xrightarrow{\mathsf{drop}(p)}_{\mathsf{effect}}S'}
```

An aggregate or array with initialized contents first releases a child, then
continues releasing its parent:

```{rule} PlaceOperations:PlaceEffect.dropChild
\frac{
 \begin{gathered}
 \mathsf{last}(S,p,\alpha)\\
 q\text{ is a field or element of }\alpha\\
 S\xrightarrow{\mathsf{drop}(q)}_{\mathsf{effect}}T\\
 T\xrightarrow{\mathsf{drop}(p)}_{\mathsf{effect}}S'
 \end{gathered}
}{S\xrightarrow{\mathsf{drop}(p)}_{\mathsf{effect}}S'}
```

```{example} PlaceExamples:drop_aggregate_recursively
Variable `x` owns an aggregate whose `item` field owns primitive `22`. Releasing
the field removes the primitive, then releasing the parent removes the aggregate.
The resulting object map is empty and `x` remains allocated and uninitialized.
```

```{example} PlaceExamples:drop_array_recursively
Variable `x` owns a two-element array. Element zero owns primitive `22`; element
one is uninitialized. Release removes the primitive, skips the empty element,
and removes the array, leaving only the empty variable slot.
```

```{example} PlaceExamples:nonfinal_owner_cannot_destroy
If `x` and `y` both hold showned references to a primitive, final-owner
destruction cannot apply to `x`: `y` contradicts its last-owner premise.
```

Recursive release describes finite successful derivations with unspecified
child order. It does not prove termination for every ownership graph. Surviving
borrow representations remain unchanged by release; destruction, stale-reference
invalidation, and identity reuse still require a joint policy.

## Restrictions from live dependencies

A lien records shared or unique dependence on a supporting access path. Access
restrictions use the liens of variables live *after* the operation. These static
dependencies are distinct from runtime reference representations.

For this basic table, paths overlap when one is a syntactic prefix of the other.
Paths with different roots are syntactically disjoint; this is not a proof that
they reach different heap objects.

| Live lien on path \\(q\\) | Sharing \\(\pi\\) | Leasing or dropping \\(\pi\\) | Giving \\(\pi\\) |
| --- | --- | --- | --- |
| Shared | Permitted by this lien | Requires disjoint paths | Requires disjoint paths or \\(\pi\\) a prefix of \\(q\\) |
| Unique | Requires disjoint paths | Requires disjoint paths | Requires disjoint paths or \\(\pi\\) a prefix of \\(q\\) |

`LiveLiensPermit` checks every supplied lien against this table. The caller must
supply the live-after liens; the predicate does not compute liveness, resolve
aliases, or invalidate references. It is not yet a premise of `PathStep`.
Restrictions from dependencies declared in fields, and the conditions for
removing intermediate dependencies across destructors, remain to be specified.

```{example} AccessConflicts:give_prefix_of_live_borrows
Giving `x` is permitted by both a unique lien and a shared lien on `x.item`:
the moved path is a prefix of each dependent path.
```

```{example} AccessConflicts:live_unique_conflict
A live unique lien on `x.item` blocks sharing, leasing, and dropping that same
path according to the basic lien table.
```

```{example} AccessConflicts:disjoint_siblings_permit
Liens on `x.right` permit each of the four accesses to `x.left`, because neither
sibling path is a prefix of the other.
```

Combining the static restrictions with runtime support chains requires rules
for computing live dependencies and for mutation invalidation. Successful
resolution alone does not establish borrow validity.

## Ownership preservation

The path transitions preserve the occurrence-sensitive ownership invariant from
[Heap invariants](properties.md):

```{theorem} PathOperations:PathStep.preserves_ownership
Every defined path transition preserves ownership when the source state satisfies it.

\\[
\frac{\mathsf{Own}(S)\qquad S\xrightarrow{\rho}_{\mathsf{path}}S'}{
 \mathsf{Own}(S')}
\\]

**Proof outline.** Split on the transition. Consuming movement transports an owner
without duplicating it; borrowing creates a nonowning reference; shared-owner
copying and release preserve the required owner counts. Destruction uses the
checked recursive release effects, and a borrowed-drop no-op leaves the state
unchanged. The successor invariant is a conclusion, never a premise.
```

Path operations also preserve the exact sequence of allocated variables:

```{theorem} PathOperations:PathStep.preserves_variable_order
Path operations preserve the exact sequence of allocated variable identities.

\\[
\frac{\langle O,V\rangle\xrightarrow{\rho}_{\mathsf{path}}\langle O',V'\rangle}{
 \operatorname{keys}(V')=\operatorname{keys}(V)}
\\]

**Proof outline.** Each slot update preserves variable order. Consuming moves and
recursive release compose such updates without allocating or removing variable
slots; a no-op preserves the sequence immediately.
```

`MachineStep` combines these transitions with the existing variable-lifetime and
object-creation steps. Its ownership theorem covers either kind of step:

```{theorem} PathOperations:MachineStep.preserves_ownership
Every defined machine step preserves ownership when the source state satisfies it.

\\[
\frac{\mathsf{Own}(S)\qquad S\xrightarrow{\omega}_{\mathsf{machine}}S'}{
 \mathsf{Own}(S')}
\\]

**Proof outline.** A machine step is either a variable-lifetime or object-creation
step, or a path transition. Apply the corresponding preservation theorem in
each case.
```

Consequently every state reachable from the empty machine by these steps has
valid owning targets, an owner for each allocated object, and exclusive unique
ownership. The proof does not establish borrow validity, freedom from ownership
cycles, or a complete fault semantics. Initialization and replacement of fields,
independent sharing, primitive observations, array length, and cleanup policy
remain [questions to settle](questions.md).
