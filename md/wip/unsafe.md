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
* `ArrayGet[T](array: Array[T], index) -> given[array] T`, gets an element from the array
* `ArrayDrop[T](array: ref Array[T], index)`, drops an element from the array (recursively drops the element, marks slot uninitialized)
* `ArrayInitialize[T](array: Array[T], index, value: given T)`, initializes an element from the array for first time

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

```
+--------------+
| flags        |
| ...fields... |
+--------------+
```

### Shared values

Shared values are just stored as a sequence of fields. No flags are needed because they are always copied out.

### Representing in the interpreter

We will have a `Alloc` struct like

```rust
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

```
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

```rust
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

### The "share operation"

After a place is shared, we visit its fields and check their type

* for a given|shared class, we recursively apply share op to its fields
* for a borrowed class | mut-ref, no-op
* for an  `Array[T]`, inc the ref count
* for int | flags, ignore

## Value operations

There is one operation on values:

* `value.share`

This operates on a value that has already been copied to a destination. It converts the value from unique to shared ownership:

* If the flags are `Given`, set them to `Shared` and apply the share operation to the fields
* If the flags are `Shared` or `Borrowed`, no-op (already shared or borrowed)

## Implementation plan

Starting point: the codebase has half-implemented PointerOps from an earlier design (commit 1a58ca9) that don't compile. We replace those with the Array[T] design and restructure the interpreter memory model.

### Approach: doc-driven, test-driven

Each step follows the same rhythm:

1. **Write/update mdbook chapter** describing the feature or change
2. **Write tests** (interpreter tests using `assert_interpret!`, type system tests using `assert_ok!`/`assert_err!`) that express the expected behavior
3. **Implement** until the tests pass

The mdbook chapters to write/update:

- **`md/interpreter.md`** (existing) — needs rewrite: the value model section describes the old `Value`/`ValueData`/`ObjectFlag` representation. Update to describe `Alloc`/`Word`/`Pointer`/`Flags`. Update the walkthrough to show word-level layout. Update access mode table for new flag semantics.
- **`md/wip/unsafe.md`** (this doc) — eventually becomes a real chapter covering `Array[T]`, `size_of`, and the unsafe primitives.

### Step 1: Remove PointerOps (get compiling again)

- Remove `TypeName::Pointer` and all 6 `PointerOps` expression variants from grammar
- Remove PointerOps type-checking rules from `type_system/expressions.rs`
- Remove Pointer match arms from `env.rs`, `liveness.rs`, `places.rs`, `types.rs`
- Remove Pointer keyword entries
- **Goal: compiles and existing tests pass**

### Step 2: Add `size_of[T]()` built-in expression

- **Doc**: add section to `md/wip/unsafe.md` explaining size_of semantics
- **Tests first**: write interpreter tests — `size_of[Int]()` returns 1, `size_of[SomeClass]()` returns expected field count + flags
- Add `SizeOf[Ty]` expression variant to grammar (no arguments, just a type parameter)
- Type-checking rule: returns `Int`
- Interpreter: returns 1 for Int/Array, 0 for assertion types, sum of fields for classes (including flags word for unique classes)
- Add keyword entry
- **Goal: tests pass, `size_of` works as a built-in expression**

### Step 3: Restructure interpreter memory model

- **Doc**: rewrite `md/interpreter.md` "The value model" section — describe `Alloc`/`Word`/`Pointer`/`Flags`, object layout (flags + fields for unique, just fields for shared), one alloc per variable. Update the walkthrough to show word-level memory.
- **Tests**: existing interpreter tests should continue to pass (output format will change from `Point { flag: Owned, x: 22, y: 44 }` to whatever the new display format is). Update `assert_interpret!` expected outputs and mdbook examples.
- Replace `Value(usize)` / `ValueData` / `ObjectData` with `Alloc { data: Vec<Word> }` / `Word` / `Pointer { index, offset }` / `Flags`
- Each local variable gets its own `Alloc`
- Objects laid out as: `[Flags, field0..., field1..., ...]` for unique values, `[field0..., field1..., ...]` for shared values
- Use `size_of` for layout calculations
- Refactor `alloc`, `read`, `write`, `copy` to work with word-level operations
- Refactor place evaluation to return `(Perm, Pointer)` as described in doc
- **Goal: existing interpreter tests pass with new memory model, no Array ops yet**

### Step 4: Implement place operations (give/ref/mut/drop)

- **Doc**: update `md/interpreter.md` "Access modes at runtime" section — describe flags-dependent give/ref/mut/drop behavior per this doc's "Place operations" section.
- **Tests first**: write interpreter tests exercising each place operation — give from Given/Shared/Borrowed, ref from various flags, mut creating MutRef, drop recursion. Tests for share operation on nested objects.
- Implement `give` operation per the doc (flags-dependent behavior)
- Implement `ref` operation per the doc
- Implement `mut` operation per the doc (creates MutRef)
- Implement `drop` operation per the doc (recursive drop for Given, drop-shared for Shared)
- Implement the "share operation" (recursive field visiting)
- Implement the "drop shared" operation (recursive field visiting)
- Implement `value.share` operation
- **Goal: place operations work correctly for non-array values**

### Step 5: Add Array[T] to grammar and implement operations

- **Doc**: expand `md/wip/unsafe.md` into a proper chapter — motivating example (building a simple Vec), then walk through ArrayNew/Initialize/Get/Drop.
- **Tests first**: write interpreter tests — create array, initialize elements, read them back, drop elements. Test out-of-bounds faults. Test uninitialized read faults.
- Add `TypeName::Array` (with one type parameter `T`)
- Add 5 Array expression variants: `ArrayNew[T](expr)`, `ArrayCapacity[T](expr)`, `ArrayGet[T](expr, expr)`, `ArrayDrop[T](expr, expr)`, `ArrayInitialize[T](expr, expr, expr)`
- Add Array keyword entries
- Add type-checking rules for all 5 operations
- Add match arms in type system (`env.rs`, `liveness.rs`, `places.rs`, `types.rs`)
- Interpreter implementation:
    - `ArrayNew[T](length)` — allocate `[Int(1), Int(length), Uninitialized...]`
    - `ArrayCapacity[T](array)` — read length word
    - `ArrayInitialize[T](array, index, value)` — write element at computed offset
    - `ArrayGet[T](array, index)` — read element via give semantics
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