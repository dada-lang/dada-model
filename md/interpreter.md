# Running a program

The previous chapters showed how the type checker verifies a program.
The interpreter evaluates the resulting core program, producing a value and a
memory snapshot. Program assertions parse surface syntax and lower it to core
before interpretation. `assert_interpret!` also checks the program;
`assert_interpret_only!` deliberately skips the checker for runtime tests.

Here is a program that creates a `Point` and returns it:

{anchor}`interp_point_example`

The interpreter creates a `Main()` instance and calls its `main` method.
The result is `Point { x: 22, y: 44 }`.

## The memory model

Memory is a collection of flat **allocations**. Each allocation contains words,
without type tags or named field maps:

{anchor}`Alloc`

Words represent scalar values, flags, pointers, mutable leases, array metadata,
or uninitialized storage:

{anchor}`Word`

The flags on a boxed handle record its runtime ownership:

{anchor}`Flags`

- **`Given`**: the handle owns its data uniquely.
- **`SharedOwned`**: the handle participates in shared ownership.
- **`SharedPlace`**: the handle shares data owned elsewhere, without owning it.

An uninitialized slot is a `Word::Uninitialized`, not a flag variant.
A pointer identifies an allocation and an offset within it:

{anchor}`Pointer`

### Object layout

Inline objects contain only their fields. For example, a `Point` with two
integer fields occupies two words, regardless of its class predicate:

```text
Point value:
+-------------------+
| Int(22)           |   <- x
| Int(44)           |   <- y
+-------------------+
```

There is no per-object flags word for inline classes. Boxed types such as
`Array[T]` instead have a two-word wrapper `[Flags, Pointer]`, whose pointer
leads to a separate heap allocation. A mutable lease uses a single
`Lease(Pointer)` word to reach its origin's data.

An `Int` or `Bool` is one word. Unit `()` has no words. Nested inline fields are
laid out consecutively; a field's type determines its size.

### Types flow through evaluation, not memory

An `ObjectValue` pairs a pointer with the type needed to interpret its words:

{anchor}`TypedValue`

The stack frame maps variables to these typed values:

{anchor}`StackFrame`

When traversing a place, the interpreter combines the static type with any
boxed flags and mutable lease indirections encountered along the path. The
resulting effective permissions determine whether access moves, duplicates,
or mutably borrows the data.

## The interpreter and stack frames

The interpreter holds the program, a typing environment used to classify types,
and the allocations:

{anchor}`Interpreter`

Each method call creates a new `StackFrame`, evaluates the body, and cleans up
its locals and temporaries when returning.

## Walking through evaluation

`Main` in the example has no fields, so its inline value occupies zero words.
Evaluating `new Point(22, 44)` first creates integer arguments and then builds
the flat object `[Int(22), Int(44)]`. Field `x` begins at offset zero and field
`y` at offset one.

`p^` gives the object. For a uniquely owned value, the interpreter copies the
words into result storage and uninitializes the source. Returning transfers
the result out of the callee's frame. The test snapshot retains only the final
`Point` allocation; it does not expose temporary storage as part of the result.

## Arithmetic

The interpreter supports integer arithmetic:

{anchor}`interp_arithmetic`

## Method calls

The receiver's type determines which method to call. The interpreter evaluates
the receiver and arguments, creates the callee's frame, and evaluates its body:

{anchor}`interp_method_calls`

For `adder^.sum()`, `adder^` is evaluated first. Its value becomes `self` in the
new frame. Generic arguments are supplied explicitly in the core call.

## Place and value operations at runtime

The checker verifies that accesses are permitted. The interpreter executes
those operations using effective permissions. Accessing uninitialized storage
faults, allowing runtime tests to expose errors that the checker should reject.

### Giving a place

`place^` copies the value's words into result storage. Its effective permissions
determine what happens to ownership:

| Permission | Behavior |
| --- | --- |
| Unique ownership | Transfer ownership and uninitialize the source |
| Independent shared ownership | Duplicate; increment refcounts of owning boxed handles |
| Sharing from a place | Duplicate without gaining ownership of the origin |
| Mutable lease | Preserve mutable access through a lease indirection |

Giving uniquely owned data transfers it:

{anchor}`interp_give_given`

Giving independently shared data can be repeated:

{anchor}`interp_give_shared`

### Sharing a place

`place` and `place.share` make the same shared access. The source stays intact.
For boxed handles in the copied result, the flags determine ownership accounting:

| Source flags | Result |
| --- | --- |
| `Given` | `SharedPlace`; no ownership transfer or refcount increment |
| `SharedOwned` | `SharedOwned`; increment the refcount |
| `SharedPlace` | `SharedPlace`; no refcount increment |

Sharing a uniquely owned place leaves the original usable:

{anchor}`interp_ref_given`

Sharing a place containing independently shared data retains that ownership:

{anchor}`interp_ref_shared`

For inline data, the interpreter copies the fields. The result type carries
the shared permission; nested boxed fields receive the ownership treatment
shown above.

### Sharing a value

`expr.share`, when the operand is a value expression, shares the evaluated
value. To give an existing place's value and share it independently, write
`d^.share`. Bare `d.share` instead shares the place.

The value operation applies `shared[]` to the result type and changes owned
boxed handles from `Given` to `SharedOwned`. It does not create a second handle,
so it does not increment refcounts. Already shared handles need no conversion.
Sharing does not invent ownership of data reached through `SharedPlace` or a
mutable lease; dependencies in the inner type remain relevant.

The operation visits nested fields:

{anchor}`interp_share_recursive`

Inline fields have no flags to flip. Their permissions follow the result type;
owned boxed fields encountered during traversal are converted to shared ownership.

### Dropping a place

Dropping releases any ownership held at a place:

| Effective permission | Behavior |
| --- | --- |
| Unique ownership | Run cleanup, drop owned fields, and uninitialize |
| Independent shared ownership | Release owning handles, decrementing refcounts |
| Sharing from a place or a mutable lease | Leave the origin's data intact |

Dropping a place-dependent shared view does not drop its origin:

{anchor}`interp_drop_borrowed_noop`

The example also records the model's current behavior for explicitly dropping
such a view: this place operation is a no-op, so the view can still be used.
Frame cleanup separately clears temporary storage.

### Mutably borrowing a place

`place!` creates a `Lease(Pointer)` word pointing at the place's data. Its type
records `![place]`. Traversing the lease grants mutable access to that data;
shared effective permissions reject mutable access. Dropping the lease does
not drop the origin's value.

## Conditionals

The `if` expression evaluates a condition and selects a branch. Since it
returns unit, these examples communicate a result through assignment:

{anchor}`interp_conditional_true`

{anchor}`interp_conditional_false`

## Arrays

`Array[T]` is the model's heap-allocation primitive. Its two-word wrapper points
to a refcounted backing allocation:

```text
Array[T] wrapper:
+-------------------+
| Flags(Given)      |
| Pointer(alloc)    |
+-------------------+

Backing allocation:
+-------------------+
| RefCount(1)       |
| Capacity(n)       |
| element 0 words   |
| element 1 words   |
| ...               |
+-------------------+
```

Each element occupies `size_of(T)` words. An inline `Data { x: Int }` element
occupies one integer word, just like `Int`; an element that is itself boxed has
its own flags and pointer wrapper. Element types come from the array's type,
not from tags stored in the backing allocation.

### Creating and accessing arrays

The built-in operations are:

- **`array_new[T](n)`** allocates capacity for `n` initially uninitialized elements.
- **`array_write[T, P](a, i, v)`** writes an element through mutable permission `P`.
- **`array_give[T, P, Q](a, i)`** gives an element with permission `P` through array
  permission `Q`.
- **`array_drop[T, P, Q](a, from, to)`** drops a range of elements through array
  permission `Q`, with element permission `P`.
- **`array_capacity[T, P](a)`** returns the capacity through array permission `P`.

The program supplies the generic arguments explicitly. For example,
`array_write[Int, ![a]](a!, 0, 10)` writes through a mutable lease of `a`.

{anchor}`interp_array_new_and_get`

### Duplicating or moving elements

Giving an `Int` element duplicates its value:

{anchor}`interp_array_int_is_copy`

The array's effective permissions propagate to element accesses. Access through
an independently shared array duplicates elements and accounts for any nested
owning boxed handles, even if a nested handle's stored flag is `Given`:

{anchor}`interp_array_class_shared_no_move`

This is the same permission propagation used for fields. Inline class elements
can be duplicated repeatedly through shared access:

{anchor}`interp_array_class_elements`

### Sharing and reference counting

A new array has a `Given` handle and refcount one. `a^.share` converts the handle
to `SharedOwned` without changing that count. Duplicating the independently
shared handle increments it:

{anchor}`interp_array_shared_refcount`

In this example, `let b = s^` creates the second owning handle. Dropping `s`
decrements the count to one; `b` keeps the backing allocation alive.

The implementation distinguishes conversion from duplication:

- `and_convert_given_to_shared` changes ownership flags during value sharing.
- `and_copy_shared_fields` accounts for duplication of owning boxed handles.
- `and_share_fields_owned_elsewhere` handles place sharing: it produces
  `SharedPlace` from unique handles, but increments the count when duplicating
  an existing `SharedOwned` handle.

Reference counts track owning handles, not every shared access to a place.

### Uniquely owned arrays

Without value sharing, giving an array transfers its ownership:

{anchor}`interp_array_given_move`

`let b = a^` moves the uniquely owned array, leaving `a` uninitialized.

### Dropping arrays

Releasing the final owning handle drops initialized elements and frees the
backing allocation:

{anchor}`interp_array_drop_frees`

The model represents freed storage with `Uninitialized` words. The final heap
snapshot contains only the result integer, with no live array allocation.
