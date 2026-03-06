# Unsafe code

## Levels of classes

* `give class` (can be given)
* `share class` (can be shared, the default)
* `shared class` (already shared)

## Memory representation of values

We have two classes of values

* unique -- these are give classes, share classes, and shared classes that have a type parameter which is unique
* shared -- these are shared classes, integers, flags, characters (when we add those)

## Unsafe primitives

There is a built-in type

* `Array[T]` -- stores a ref count, a length, and N elements of type `T` (elements are initially uninitialized)

`Array[T]` is a `share class` and offers the following built-in operations (special expressions):

* `ArrayNew[T](length: uint) -> Array[T]`, allocates an array of the given length
* `ArrayCapacity[T](array: Array[T]) -> uint`, returns the capacity that the array was created with
* `ArrayGive[T](array: Array[T], index) -> given[array] T`, gets an element from the array
* `ArrayDrop[T](array: ref Array[T], index)`, drops an element from the array (recursively drops the element, marks slot uninitialized)
* `ArraySet[T](array: Array[T], index, value: given T)`, initializes an element from the array for first time

## Type sizes

`size_of[T]()` is a built-in expression that returns the number of `Word`s needed to store a value of type `T`. It takes a single type parameter and no arguments. It type-checks to `Int`.

The interpreter evaluates `size_of[T]()` as:

* `Int` → 1
* `Tuple(0)` (i.e., `()`) → 0
* A class → 1 (for the flags word if unique, 0 if shared) + sum of `size_of` for each field's type
* Other (including `Array[T]` once added) → 1

The real system has more complex layout rules obviously.
### Unique values

Unique values are 4-aligned and begin with a flags field:

```text
+--------------+
| flags        |
| ...fields... |
+--------------+
```

### Shared values

Shared values are just stored as a sequence of fields. No flags are needed because they are always copied out.

### Representing in the interpreter

We will have a `Alloc` struct like

```rust,ignore
struct Alloc {
    data: Vec<Word>
}

enum Word {
    Int(isize),
    Array(Pointer),
    MutRef(Pointer),
    Flags(Flags),
    Uninitialized,
}

struct Pointer {
    index: usize,
    offset: usize,
}

enum Flags {
    // Indicates that the value is uninitialized
    Uninitialized,

    // Unique ownership
    Given,

    // Shared ownership
    Shared,

    // Copied fields from value stored elsewhere, either `ref` or `shared mut`
    Borrowed,
}
```

All values, including arrays, use the same `Alloc` struct. An `Array[T]` allocation stores the ref count and length as the first two words, followed by the elements:

```text
+------------------+
| Int(refcount)    |
| Int(length)      |
| element 0        |   \
| ...              |    > each element is size_of[T]() words
| element N-1      |   /
+------------------+
```

## Place operations

There are four operations on places:

* `place.give`
* `place.ref`
* `place.mut`
* `place.drop`

Each begins by *evaluating* the place which results in a `Perm` and a `Pointer`:

* the `Perm` represents the most restrictive we have passed through. If at any point we access an *uninitialized* flags the interpreter faults.
* the `Pointer` identifiers the location in memory that the place is stored

The `Perm` can be one of

```rust,ignore
enum Perm {
    Given,
    Shared,
    Borrowed,
    Mut,
}
```

The operations then proceed as follows:

* `give` examines the `Flags`
    * `Given` => copy the fields to the destination and then mark the Flags as `Uninitialized`
    * `Shared` => copy the fields to the destination, set the flags to `Shared`, and then apply the share operation to them (see below)
    * `Borrowed` => copy the fields to the destination, set the flags to `Borrowed`
    * `Mut` => create a `MutRef` with the pointer
* `ref` examines the `Flags`
    * `Shared` => copy the fields to the destination, set the flags to `Shared`, and then apply the share operation to them (see below)
    * `Given` | `Borrowed` | `Mut` => copy the fields to the destination, set the flags to `Borrowed`
* `mut` examines the `Flags`
    * `Shared` | `Borrowed` => fault
    * `Given` | `Mut` => create a `MutRef` value
* `drop` examines the `Flags`
    * `Given` => drop fields recursively
    * `Shared` => apply "drop shared" operation (see below)
    * `Borrowed` | `Mut` => no-op

### The "drop shared" operation

When dropping a shared value, we visit its fields and check their type:

* for a give|share class, we recursively apply drop shared to its fields
* for an `Array[T]`, decrement the ref count; if it reaches zero, recursively drop all initialized elements and free the array
* for a borrowed class | mut-ref, no-op
* for int | flags, ignore

### The "share operation" (duplication accounting)

When a shared value is duplicated (by `place.give` or `place.ref` on a Shared value), we apply `share_op` to the copy to account for the new references:

* for a given|shared class, we recursively apply share op to its fields
* for an `Array[T]`, inc the ref count
* for a borrowed class | mut-ref, no-op
* for int | flags, ignore

### Converting to shared (in-place)

When `value.share` converts a value from Given to Shared, we apply `convert_to_shared` to recursively flip flags:

* for a given|shared class, flip flags Given→Shared, then recurse into fields
* for an `Array[T]`, flip flags Given→Shared (no refcount change — no duplication)
* for a borrowed class | mut-ref, no-op
* for int | flags, ignore

## Value operations

There is one operation on values:

* `value.share`

This operates on a value that has already been copied to a destination. It converts the value from unique to shared ownership:

* If the flags are `Given`, set them to `Shared` and apply the share operation to the fields
* If the flags are `Shared` or `Borrowed`, no-op (already shared or borrowed)

## Array reference counting

Arrays are `share class` types. The ref count (stored at offset 0 of the array allocation) tracks how many live references exist.

### Two share-related operations

There are two distinct operations that involve sharing:

1. **`convert_to_shared`** — in-place conversion from Given to Shared ownership. Called by `Expr::Share` (i.e., `value.share`). Recursively flips flags from Given→Shared on nested class fields. For arrays: just flips the value's flags, no refcount change. No duplication occurs.

2. **`share_op`** — duplication accounting. Called when a Shared value is copied (by `place.give` or `place.ref` on a Shared value). For arrays: increments the refcount. For classes: recurses into fields to account for nested duplications.

The distinction matters because `Expr::Share` converts in place (one reference → one reference, no refcount change), while `place.give` on Shared duplicates the value (one reference → two references, refcount must increase).

### Lifecycle

1. **ArrayNew** — allocates `[Int(1), Int(length), elements...]`. Refcount starts at 1.
2. **value.share** — flips flags Given→Shared via `convert_to_shared`. Refcount stays 1.
3. **place.give on Shared** — copies the value, calls `share_op` which increments refcount. Each additional copy adds 1.
4. **drop (Given or Shared)** — decrements refcount. If zero: recursively drop all initialized elements, then free the array allocation.

## Implementation plan

### Approach: doc-driven, test-driven

Each step follows the same rhythm:

1. **Write/update mdbook chapter** describing the feature or change
2. **Write tests** (interpreter tests using `assert_interpret!`, type system tests using `assert_ok!`/`assert_err!`) that express the expected behavior
3. **Implement** until the tests pass

The mdbook chapters to write/update:

- **`md/interpreter.md`** (existing) — describes the `Alloc`/`Word`/`Pointer`/`Flags`/`TypedValue` memory model, with word-level walkthrough and access mode table.
- **`md/wip/unsafe.md`** (this doc) — eventually becomes a real chapter covering `Array[T]`, `size_of`, and the unsafe primitives.

### Step 1: Remove PointerOps ✅

Removed `TypeName::Pointer` and all 6 `PointerOps` expression variants. Compiles and existing tests pass.

### Step 2: Add `size_of[T]()` ✅

Added `Expr::SizeOf(Vec<Parameter>)` with `#[grammar(size_of $[v0] ( ))]`. Type-checks to `Int`. Interpreter computes word count: 1 for Int, flags + fields for classes, 0 for unit. 6 interpreter tests.

### Step 3: Restructure interpreter memory model ✅

Replaced `Value`/`ValueData`/`ObjectData`/`ObjectFlag` with flat word-based memory:
- `Alloc { data: Vec<Word> }` — flat word arrays, no type tags in memory
- `Word { Int, Flags, Uninitialized }` — individual memory words
- `Flags { Uninitialized, Given, Shared, Borrowed }` — permission flags for unique objects
- `Pointer { index, offset }` — position within an allocation
- `TypedValue { pointer, ty }` — types flow through evaluation, not stored on allocations

Object layout: `[Flags, field0_words..., field1_words...]` for unique classes, `[field0_words...]` for shared classes (no flags word). Field access uses type-driven offset computation. Display: `flag: Given` (was `Owned`), `flag: Borrowed` (was `Ref`), shared classes omit flag entirely.

### Step 4: Implement place operations (give/ref/mut/drop) ✅

Implemented flags-dependent place operations (give/ref/drop) dispatching on Given/Shared/Borrowed/Uninitialized. Added UB faulting — interpreter bails on all undefined behavior to enable fuzzing the type checker for soundness. Removed `Access::Sh` — share is now exclusively a value operation (`Expr::Share`), users write `d.give.share`. Added `prove_is_shareable` check to `Expr::Share` typing rule. Mut is stubbed (bail on use).

### Step 4b: Doc/code review cleanup ✅

Reviewed interpreter.md + unsafe.md against the implementation. Fixed share_op ordering (flag flip before recurse) and break/return control flow (introduced `Outcome` enum, `anyhow::Error` reserved for UB faults). Remaining items tracked in `WIP.md`.

### Step 5: Add Array[T] to grammar and implement operations

- **Doc**: expand `md/wip/unsafe.md` into a proper chapter — motivating example (building a simple Vec), then walk through ArrayNew/Initialize/Get/Drop.
- **Tests first**: write interpreter tests — create array, initialize elements, read them back, drop elements. Test out-of-bounds faults. Test uninitialized read faults.
- Add `TypeName::Array` (with one type parameter `T`)
- Add 5 Array expression variants: `ArrayNew[T](expr)`, `ArrayCapacity[T](expr)`, `ArrayGive[T](expr, expr)`, `ArrayDrop[T](expr, expr)`, `ArraySet[T](expr, expr, expr)`
- Add Array keyword entries
- Add type-checking rules for all 5 operations
- Add match arms in type system (`env.rs`, `liveness.rs`, `places.rs`, `types.rs`)
- Interpreter implementation:
    - `ArrayNew[T](length)` — allocate `[Int(1), Int(length), Uninitialized...]`
    - `ArrayCapacity[T](array)` — read length word
    - `ArraySet[T](array, index, value)` — write element at computed offset
    - `ArrayGive[T](array, index)` — read element via give semantics
    - `ArrayDrop[T](array, index)` — recursively drop element, mark slot uninitialized
- **Goal: arrays work end-to-end**

### Step 6: Implement reference counting for arrays

- **Doc**: add section to array chapter on sharing and ref counting — walk through what happens when an array is shared, how ref count increments/decrements, when elements get dropped.
- **Tests first**: write interpreter tests — shared array survives after original dropped, array freed when last reference dropped, elements recursively dropped on array free.
- Share operation increments array ref count
- Drop-shared decrements ref count, frees when zero
- **Goal: array ref counting works correctly**

## FAQ

### Why not have a specialized `ArrayAlloc` instead of using generic `Alloc`?

We use a single `Alloc` type for all allocations, with arrays storing their ref count and length as the first two words by convention. A specialized `ArrayAlloc` would be more type-safe in the interpreter, but we expect to add more ref-counted allocation kinds in the future (e.g., a Box-like type that carries just a ref count + value). Keeping one uniform allocation pool with layout-by-convention is simpler and more extensible than adding a new allocation variant for each kind.