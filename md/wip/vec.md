# Vec and array design

We are working our way towards the following design which will cover a "partially initialize" array type called `Vec` (the full `Vec` in the standard library would be expected to support more features, but this is enough for now). I'm also assuming all indices are in-bounds and a few other details.

## Goal: Vector class

```dada
class Vec[type T] {
    data: Array[T]
    len: Int
    
    fn push[perm P](P self, value: given T) where P is mut {
        array_write[T, mut[self.data]](self.data.mut, self.len.give, value.give)
        self.len = self.len.give + 1
    }
    
    fn get[perm P](P self, index: Int) -> given_from[self] T {
        let data: given_from[self.data] Array[T] = self.data.give # P=given: moves data out, self not-whole, Vec.drop won't run.
                                                               # P=ref/shared: copies, self stays whole, Vec.drop runs but is
                                                               # harmless (is_last_ref guards cleanup, array_drop is no-op).
        let len: Int = self.len.give
        array_drop[T, given_from[self], ref[data]](data.ref, 0, index.give)
        array_drop[T, given_from[self], ref[data]](data.ref, index.give + 1, len.give)
        array_give[T, given_from[self], ref[data]](data.ref, index.give)
    }
    
    fn iter[perm P](P self) -> Iterator[P, T] {
        new Iterator[P, T](self.give, 0)
    }

    drop {
        if is_last_ref[ref[self.data]](self.data.ref) {
            array_drop[T, given, ref[self]](self.data.ref, 0, self.len.give)
        } else {}
    }
}

class Iterator[perm P, type T] {
    vec: P Vec[T]
    start: Int
    
    fn next[perm I](I self) -> P T
    where
        I is mut,
    {
        let index = self.start.give
        self.start = self.start.give + 1
        array_give[T, P, ref[self.vec.data]](self.vec.data.ref, index.give)
    }
    
    drop {
        let data = self.vec.data.give # subtle: disables vec dtor
        let start = self.start.give
        let len = self.vec.len.give
        
        # free the elements not yet iterated over:
        array_drop[T, P, ref[data]](data.ref, start.give, len.give)
    }
}
```

## Key points

### boxed classes

A *boxed class* indicates a class whose memory is stored in the heap. Boxed classes permit recursion, internal mutation with mutexes etc, and cheaper data movement. Currently the only boxed class is the built-in `Array`, but we expect to change this later.

A boxed-class is represented as a *pointer* along with *flags* that, in the real thing, will be stored in the low-bits of the pointer:

* dropped -- the value has been moved or dropped
* given -- sole ownership
* shared -- shared ownership (refcount > 1)
* ref -- a borrow (no ownership)

Note that a `mut ref` is different and always stored as a pointer to the object data, independent of whether it refers to a boxed class or a regular class.

Boxed class layout is:

* `[ref-count, fields...]`

Dropping a owned boxed class decrements the ref-count and, if it is zero, drops the fields.

### `Array[T]` type semantics

The `Array[T]` is a special boxed class that carries inline data:

* `[ref-count, capacity, elements...]`

Dropping a owned array decrements the ref-count and, if it is zero, frees the array. IT DOES NOT DROP THE ELEMENTS, users are expected to drop those elements themselves. This is because array elements may not be initialized at all times.

Arrays support the following intrinsic, unsafe operations

* `array_new[type T](capacity: Int) -> given Array[T]`, returns a fresh owned uninitialized array. No permission parameter — always returns `given`.
* `array_capacity[type T, perm A](array: A Array[T]) -> Int where A is ref`, returns capacity of an array
* `array_write[type T, perm A](array: A Array[T], index: Int, value: given T) where A is mut`, writes the value to the given index; any previous value is *ignored*
* `array_drop[type T, perm P, perm A](array: A Array[T], from: Int, to: Int) where A is ref`, drops elements from `from..to` (exclusive) in a way that depends on the type `P T`. If `from >= to`, this is a no-op.
  * If `P T` is given (i.e., `prove_is_given(P T)` — both owned and move), then the value is dropped.
  * Else this is a no-op.
* `array_give[type T, perm P, perm A](array: A Array[T], index: Int) -> P T where A is ref`, reads and returns the element at `index` in a way that depends on the type `P T`:
  * If `P T` is given (i.e., `prove_is_given(P T)` — both owned and move), then the value is moved and the memory is uninitialized.
  * Else, if `P T` is mut, then a mutable reference to the element's fields is created. For boxed types, this dereferences through the `[Flags, Pointer]` wrapper to point at the object data. For flat (non-boxed) types, the `MutRef` points directly into the array allocation at the element's offset.
  * Else, if `P T` is shared, then the value is "shared": the element's words are copied out, and then any boxed fields within the copy are transitioned to shared (flags set to `Shared`, refcount incremented). Flat (non-boxed) fields are just copied — there is no refcount to touch. **Assertion:** `P` is shared ↔ `A` is shared (the array's runtime flags must agree with the requested permission).
  * Else, `P T` is ref, then the result is a borrow: the element's words are copied out, and then any boxed fields within the copy have their flags set to `Borrowed` (if they were `Given`) or refcount incremented (if they were `Shared`). Flat fields are just copied.

**Implementation note:** The four `array_give` cases (given/mut/shared/ref) map directly onto the existing place access operations in `src/interpreter/mod.rs`: `give_place` (given case), `mut_place` (mut case), `ref_place` (ref case), and the shared branch of `give_place` (shared case). Each of these already handles the boxed-vs-flat distinction. The array intrinsics just need to compute the element's `ObjectData` (pointer + offset into the array allocation) and delegate to the same logic.

The semantics of drop and give are setup to support a "poly-permission" operation like `Vec.get` above. The `array_drop` calls in `get` are no-ops when `P` is not `given`, but they are present so that a single function body works correctly across all permissions — in the `given` case, they actually destroy the elements we don't want.

Note that the return type `given_from[self] T` in `Vec.get` is effectively equivalent to `P` — `given_from[place]` picks up the permission of the place, so `given_from[self]` where `self: P Vec[T]` becomes `P T`. It is written as `given_from[self]` because it conveys the intent more clearly: "you get whatever permission you had on self."

### "drop" sections -- defining custom destructors

A *drop* section in a class is a special optional section. The type of `self` in the drop body depends on the class predicate:

* `given class` → `self: given Class[...]` (sole ownership)
* `class` (default, i.e. share) → `self: ref Class[...]`
* `shared class` → `self: ref Class[...]`

When a drop body executes, `self` is treated as *not whole* even though all its fields are initialized. This means the whole-place drop logic will drop each field individually rather than dropping `self` as a unit (which would recursively invoke the drop body again). There is no special "post-drop-body field cleanup" step — the individual field drops are a consequence of the existing whole-place rules applied to a `self` that is never whole.

**Partial moves and field access:** Moving a field out of a struct makes the struct not-whole, but other initialized fields remain accessible. Reading a field of a partially-moved struct is legal as long as *that specific field* has not been moved. The whole-place rules only govern dropping, not reading. The type checker already supports this — liveness is tracked at the place level (e.g., `self.vec.data` and `self.vec.len` are independent places), so moving one field doesn't invalidate sibling fields. No new type-checker feature is needed for the `Iterator.drop` pattern (`self.vec.data.give` then `self.vec.len.give`).

**Places always require an access mode:** A bare place (e.g., `x`, `self.len`) is never valid as an expression. Every use of a place as a value must go through an access mode: `.give`, `.ref`, `.mut`, or `.drop`. This applies to local variables, function parameters, and field accesses alike. For example, `self.len.give` (not `self.len`), `index.give` (not `index`).

### `is_last_ref` primitive

`is_last_ref[perm A](value: A T) -> Bool` is a built-in intrinsic expression (like `array_new`, etc.). It accepts any `ref` value — e.g., `is_last_ref[ref[self.data]](self.data.ref)`. It returns a `Bool` — a new built-in type that needs to be added to `TypeName` alongside `Int`. For boxed types (currently only arrays), it returns true if the refcount is 1 (i.e., this is the last owned handle). For non-boxed types, it always returns false — there is no refcount to check, and the caller cannot assume sole ownership. Under a garbage collector, `is_last_ref` always returns false — elements are collected independently.

Note: `if`/`else` already exists as `Expr::If`.

### Executing "drop"

The *drop* for a class is executed whenever any owned handle to an instance of that class is dropped — not just the last reference. The type of `self` depends on the class predicate: `given class` gets `self: given Class[...]`, while `class` (default) and `shared class` get `self: ref Class[...]`. For the non-given cases, `ref` is the lowest common denominator: `shared` is a subpermission of `ref`, so `self: ref Class` is valid for any owned handle to a share/shared class.

For classes like `Vec` that manage owned resources, the drop body uses `is_last_ref` to conditionally clean up only when this is the final handle:

```dada
drop {
    if is_last_ref[ref[self.data]](self.data.ref) {
        array_drop[T, given, ref[self]](self.data.ref, 0, self.len.give)
    } else {}
}
```

When `is_last_ref` is false (other handles remain, or under GC), the drop body skips element cleanup — another handle will do it, or the GC will collect the elements independently.

### Dropping local variables

When a function/block terminates, it drops all values found in "whole" places. A *whole* value is a value where no part has been moved.

*Definition: accessible place.* An accessible place is either

* a local variable `X`
* a field `P.F` where `P` is an accessible place of type class and `F` is a field
* a field `P[i]` where `P` is an accessible place of type tuple and `i` is a tuple index

Note that *elements of arrays are not accessible places*.

*Definition: whole place.* An accessible place `P` is a *whole place* if

* `P` and all accessible places that extend `P` are initialized
  * This is the one place in the interpreter that we "branch" on uninitialized data. The compiler would be expected to track this statically or with extra flags on the stack as needed.

*Example.* Consider this function

```dada
class Vec[type T] {
    data: Array[T]
    index: Int
    
    fn example(given self) {
        # point A
        let data = self.data.give
        # point B
    }
    
    drop {
      # ...
    }
}
```

For the function `example`, the *accessible places* are `self`, `self.data`, and `self.index`.

At point A, `self` is a whole place. If the function were to return at point A, then `self` would be dropped. This would cause the drop code to execute, since we are dropping a `Vec`.

At point B, `self.data` has been moved, and hence `self` is not a whole place. `self` would not be dropped and hence its drop code would not run. `self.index` is a whole accessible place and would be dropped (but dropping an `Int` is a no-op).

## FAQ

**Q: Why does `Vec.get` call `array_drop` on all elements except the one being returned? Isn't that wasteful for `ref`/`shared`?**

The function body is polymorphic over `P`. When `P` is `given`, those `array_drop` calls actually destroy the elements we don't want (we're consuming the vec). When `P` is `ref` or `shared`, the `array_drop` calls are no-ops. The alternative would be separate implementations per permission, but one body that works for all permissions is simpler and correct.

**Q: What does `given_from[self]` mean as a return type?**

`given_from[place]` picks up the permission of the place. So `given_from[self]` where `self: P Vec[T]` is effectively `P T`. It's written as `given_from[self]` rather than `P` because it conveys intent more clearly: "you get whatever permission you had on self."

**Q: How does the drop body avoid infinite recursion? If `self` is whole at the end of the drop body, wouldn't whole-place dropping invoke the drop body again?**

In a drop body, `self` is treated as *not whole* even though all its fields are initialized. This means the whole-place logic drops each field individually rather than dropping `self` as a unit. No special mechanism — just the existing whole-place rules applied to a `self` that is never whole.

**Q: In `Iterator.drop`, moving `self.vec.data` out disables `Vec.drop`. But what about the array backing itself?**

The local `data` is whole at end of scope, so it gets dropped normally: refcount decremented, backing freed if zero. Any elements not covered by the `array_drop(data.ref, start, len)` call (i.e., elements before `start` that were already iterated and consumed) are already gone — they were moved out by `next()`. So the cleanup is complete: `array_drop` handles un-iterated elements, and dropping `data` frees the backing.

**Q: When `P = shared`, doesn't `array_drop` being a no-op cause leaks in `Iterator.drop`?**

No. When `P = shared`, the iterator doesn't own the vec — `self.vec` is `shared Vec[T]`. So `self.vec.data.give` produces a shared copy of the array (incrementing its refcount), not a move. `self.vec` stays whole, the `array_drop` call is a no-op, and the shared `data` copy just gets its refcount decremented at end of scope. `Vec.drop` runs on every handle being dropped, but the `is_last_ref` check means element cleanup only happens when the final handle is dropped. The "disables vec dtor" comment in `Iterator.drop` is only operative in the `P = given` case.

**Q: What does `array_drop` with `P = given` actually do to each element? Shallow uninitialize, or full recursive drop?**

Full recursive drop. If the element's class has a `drop { }` section, that body runs (and then fields are individually dropped via the not-whole `self` rule). If it has no `drop { }` section, it behaves as if it had an empty `drop {}` — fields are individually dropped directly. This recurses all the way down through nested classes.

**Q: What does `.give` do on a borrowed or shared value?**

`.give` always gives the full permissions you have on a value. If you have `given`, it moves. If you have `shared`, it produces a shared copy (rc++). If you have `ref`, it produces a ref copy. You can *always* `.give` a value — it's not restricted to owned data. This is why `self.vec.data.give` in `Iterator.drop` works for all permissions `P`: when `P = given` it moves the array out (disabling `Vec.drop`), when `P = shared` it produces a shared copy, when `P = ref` it produces a ref copy. In the non-given cases, `self.vec` remains whole, but the dtor is harmless — dropping a shared handle runs the drop body, but `is_last_ref` guards ensure cleanup only happens on the final owned handle. Dropping a `ref` handle is a no-op (borrows don't own anything).

**Q: In `Vec.get` with `P = given`, who frees the array backing allocation?**

The local `data` holds the array after `self.data.give`. At end of scope, `data` is whole, so it gets dropped: refcount decremented, backing freed. The built-in array drop handles the backing allocation. The *elements* in the array are the user's responsibility — that's what the `array_drop` and `array_give` calls in the method body handle.

**Q: What is `.share` in `array.give.share`? Is it an access mode?**

No. `.share` is an expression-level operation (`Expr::Share`), not a place access mode. It operates on *values*, not *places* — that's why we write `array.give.share`: first `.give` converts the place to a value, then `.share` converts that value from given to shared ownership. The access modes (`.give`, `.ref`, `.mut`, `.drop`) operate on places; `.share` is a separate expression form already in the grammar.

**Q: Can drop bodies access class-level generic parameters?**

Yes. Drop bodies have access to the class's generic parameters (e.g., `P` and `T` in `Iterator[perm P, type T]`), just like any method on the class. This is why `Iterator.drop` can pass `P` to `array_drop`.

**Q: How can array intrinsics bypass normal permission rules? Aren't some of these operations obviously unsound?**

Yes — array operations are unsafe intrinsics that deliberately violate the permission rules safe code must follow. Specific examples:

* `array_drop[T, given, ref[a]](a.ref, 0, 3)` — drops and uninitializes element slots through only a `ref` to the array. Normal safe code cannot modify memory through `ref`.
* `array_give[Data, mut[a], ref[a]](a.ref, 0)` — produces a `mut[a] Data` (a mutable reference to an element) through only a `ref` to the array. Normal safe code cannot obtain `mut` access through `ref`. The returned `mut` ref is a pointer directly at the object data for the element.
* `array_write[T, mut[a]](a.mut, 0, value)` — overwrites an element slot without dropping the previous value. Normal safe code would drop the old value first.

The `A is ref` / `A is mut` constraints are the *minimum* the type system enforces on the caller, but the operations themselves bypass normal permission rules internally. Soundness is the caller's responsibility — e.g., `Vec` must ensure it never hands out two `mut` refs to the same element, never reads an uninitialized slot, etc. A full "unsafe effects" system to describe and constrain what unsafe operations can do is future work.

**Q: How does the interpreter compute element offsets in arrays?**

The interpreter already has `size_of(env, ty)` which returns the number of words a type occupies. Array element access computes `ARRAY_ELEMENTS_OFFSET + index * element_size`. This is internal interpreter machinery — user code (like Vec) just passes integer indices to array intrinsics and the interpreter handles offset calculation.

**Q: What happens when `array_drop` is called with `from >= to` (empty or inverted range)?**

It's a no-op. This naturally arises in `Vec.get` when `index == len - 1`, producing `array_drop(..., index + 1, len)` where `from == to`.

**Q: How does the interpreter decide which `array_give`/`array_drop` behavior to use?**

The interpreter has the fully-substituted permission `P` and type `T`, so it can use the existing predicate-proving machinery (e.g., `prove_is_given(P T)` for owned+move, `prove_is_shared(P T)`) to classify the combined type and choose the right behavior. It should also assert that the effective flags on the array data are consistent with the classification (e.g., if classified as shared, the array's flags should be shared).

**Q: Why does the dispatch check `P T` (the combined type) rather than just `P`?**

Because `T` affects the semantics. For example, `given Int` where `Int` is a shared class: even though `P = given`, `prove_is_given(given Int)` fails because `Int` is not a move type (it's copy/shared). So `array_give` should copy rather than move+uninitialize, and `array_drop` should be a no-op rather than dropping. Dispatching on `P T` via `prove_is_given` ensures that shared/copy types are handled correctly regardless of what permission is passed.

**Q: In `Vec.get` with `P = given`, the array has uninitialized trailing slots (capacity > len). Is that a problem when the array is dropped?**

No. Dropping the array just decrements the refcount, and when it hits zero, the entire backing allocation is scrubbed (all words set to `Word::Uninitialized`). This does not inspect or iterate over element contents — it's a bulk uninitialize of the raw memory. Trailing uninitialized slots are harmless; they get overwritten with the same `Word::Uninitialized` value they already had.

## Random notes to check on

* `given_from[a.b] Foo` -- can this be contracted to `given_from[a]`? Only when the field `b` is declared with `given` permission (or no permission prefix). The `Mv` expansion rule in `redperms.rs` *replaces* `given_from[place]` with the permission of `place`. So `given_from[a.b]` reduces to the permission of `a.b`, which composes the permission of `a` with the declared permission of field `b`. If `a: mut[x] Foo` and `b: shared Bar`, then `a.b` has permission `shared` (mut applied to shared = shared), so `given_from[a.b]` ≠ `given_from[a]` (which would be `mut[x]`). The existing reduction rules handle this correctly — no special case needed.

## Implementation plan

Implementation follows a TDD approach: write or update tests first to express intent, then implement until they pass. Each phase produces a working, all-tests-passing state. Tests that don't yet match intent are fixed in the phase where the feature that enables correct behavior lands.

**Agent workflow:** Complete ONE phase at a time. After each phase, commit the work, run `cargo test --all --all-targets` to confirm 100% of tests pass (0 failures, 0 ignored unless pre-existing), and **stop**. Do not begin the next phase. A human must review the completed phase and explicitly approve before the next phase begins. This is a hard rule — never do more than one phase without human-in-the-loop review. Each phase should be a separate commit (or small series of commits).

### Phase 1: Standalone renames and syntax ✅

No semantic changes. Clears the deck so subsequent code matches the doc's notation.

* [x] **Rename `array_set` → `array_write`** — pure rename across grammar, interpreter, type system, and all tests. Current `array_set` already has "ignore previous value" semantics.
* [x] ~~**Rename `given_from` → `given`**~~ — skipped. The parser prefix ambiguity between `given` and `given_from[...]` is unresolved and not worth the risk. Keeping `given_from[places]` as-is.
* [x] **Remove `Flags::Dropped`** — replaced all uses of `Flags::Dropped` with `Word::Uninitialized`. Removed `Dropped` from the `Flags` enum. Added `try_read_flags()` helper that returns `Option<Flags>` (`None` for uninitialized, `Some(flags)` for live values). Callers now check for `Word::Uninitialized` before calling `expect_flags()`. Error messages are "access of uninitialized value" uniformly. **Note:** `and_drop_fields` still silently skips uninitialized boxed values rather than erroring — this is needed because the interpreter's end-of-scope cleanup drops ALL variables unconditionally without checking wholeness. Phase 4's whole-place checks will allow this to become an error.
* [x] **Scrub entire array backing on refcount zero** — when an array's refcount reaches 0, all words in the backing allocation (header + elements) are set to `Word::Uninitialized`. Freed arrays now disappear completely from heap snapshots. Updated 44 test snapshots.
* [x] **`param is pred` syntax** — flipped *both* `Predicate::Parameter` and `Predicate::Variance` grammar from `#[grammar($v0($v1))]` to `#[grammar($v1 is $v0)]`. All predicates now use consistent `param is pred` syntax (e.g., `P is mut`, `T is relative`, `T is atomic`). Added `is` to KEYWORDS. Updated all test programs and `where` clauses. Class predicates (`given class`, `shared class`) are unchanged.

### Phase 2: Permission parameter plumbing ✅

Add `P` and `A` parameters to array ops. Loosen access requirements. Keep current behavior — all existing call sites pass `P = given` (or equivalent).

* [x] **Add `P`, `A` parameters to `array_give`** — `array_give[T, P, A](array, index)`. No grammar annotation change needed — `$[v0]` already parses a `Vec<Parameter>` as a comma-separated list inside brackets. The interpreter/type-checker code that destructures the parameter list changes from expecting 1 element to expecting 3. Interpreter: extract P and A from parameters but dispatch only on P=given (move, current behavior). Type system: accept 3 type parameters, check array expression against `A Array[T]`, return `P T`.
* [x] **Add `P`, `A` parameters to `array_drop`** — `array_drop[T, P, A](array, index)`. Same as above — no grammar annotation change for the bracket params. Keep single-index for now. Interpreter: extract P, dispatch only on P=given (drop, current behavior). Type system: check array expression against `A Array[T]` (no mut requirement — loosened from current `mut`).
* [x] **Add `A` parameter to `array_write`** — `array_write[T, A](array, index, value)`. Same — no grammar annotation change. Type system: require `A is mut` via `prove_is_mut(A)`, check array expression against `A Array[T]`.
* [x] **Add `A` parameter to `array_capacity`** — `array_capacity[T, A](array)`. Same — no grammar annotation change. Type system: check array expression against `A Array[T]` (accepts any perm).

**TDD notes:** Update all existing test call sites from `array_give[T](...)` to `array_give[T, given, ref[a]](...)` etc. Tests should pass with identical behavior since P=given matches current semantics. Key tests to watch:
* `array_give_given_class_moves_out` — should keep move semantics with explicit `P = given`
* `array_drop_element`, `array_drop_class_element` — should keep drop semantics with `P = given`
* `array_capacity_given`, `array_capacity_shared`, `array_capacity_ref` — should all work with `A is ref`

### Phase 3: Poly-permission semantics

Implement dispatch on `P` for `array_give` and `array_drop`. Add range semantics to `array_drop`.

* [x] **`array_give` dispatches on P** — given → move and uninitialize source (copies raw words, sets boxed flags to Given, uninitializes source), mut → mut ref to element (dereferences through boxed wrapper for boxed types), shared → shared copy (rc++ on boxed fields), ref → borrow (copy with ref flags). The dispatch uses `prove_is_given`, `prove_is_mut`, `prove_is_copy_owned` on the combined type `P T`. Works directly on the raw element ObjectValue pointer to bypass normal permission rules (these are unsafe intrinsics). **Note:** The `P is shared ↔ A is shared` assertion is deferred — not yet implemented as an interpreter check.
* [x] **`array_drop` dispatches on P** — given → actually drop each element in range, else → no-op. Dispatch uses `prove_is_given(P T)`. For copy types (e.g., `given Int` where Int is a shared class), `prove_is_given` fails so drop is a no-op — correct behavior since copy types don't need explicit cleanup.
* [x] **`array_drop` range semantics** — changed grammar from `(array, index)` to `(array, from, to)`, drops elements in `from..to` range (exclusive) in forward order. `from >= to` is a no-op. All existing single-index `array_drop(a, i)` calls rewritten to `array_drop(a, i, i + 1)`. Updated type system, interpreter, liveness, and all tests.

**TDD notes — tests written and passing:**
* `array_give_p_mut` — `array_give[Data, mut[a], ref[a]](a.ref, 0)` returns a `mut[a] Data` ✅
* `array_give_p_shared` — `array_give[Array[Int], shared, ref[outer]](outer.ref, 0)` returns a shared copy, rc incremented ✅
* `array_give_p_ref` — `array_give[Array[Int], ref[outer], ref[outer]](outer.ref, 0)` returns a borrowed copy ✅
* `array_drop_p_shared_is_noop` — `array_drop[Data, shared, ref[a]](a.ref, 0, 1)` does nothing, element still accessible ✅
* `array_drop_p_given_range` — `array_drop[Data, given, ref[a]](a.ref, 0, 3)` drops elements 0, 1, 2 ✅
* `array_give_p_given_int_is_copy` — giving an Int element with P=given copies without uninitializing ✅
* `array_drop_empty_range_is_noop` — `array_drop` with `from >= to` is a no-op ✅
* `array_drop_shared_class_element_is_noop` — shared class (Pt) elements: `array_drop[Pt, given, ...]` is a no-op since `given Pt` is copy ✅

* `array_give_ref_of_shared_is_shared` — `P = ref[shared_place]` where the place is shared. The type system normalizes `ref[shared_place]` to `shared` before substitution, so `P` arrives as `shared` and the shared branch fires. This tests that the `P is shared ↔ A is shared` assertion holds when both the permission and array access are derived from a shared place.

```dada
class Data {}

fn head[perm P](array: P Array[Data]) -> P Data
where
    P is ref,
{
    array_give[Data, P, ref[array]](array.ref, 0)
}

fn main() {
    let array: given Array[Data] = array_new[Data](1)
    array_write[Data, mut[array]](array.mut, 0, new Data())
    let shared_array = array.give.share
    let elem0 = head[ref[shared_array]](shared_array.ref)
    # elem0 should be `shared Data`, not `ref Data`
}
```

### Phase 3.5: Test rewrite

Rewrite existing tests to use the new array op signatures and express their *intended* semantics now that poly-permission and range ops are available.

* [ ] **Restore shared-array test intent** — tests like `shared_array_give_class_is_shared_copy` should use `P = shared` explicitly instead of relying on runtime flag inference. Verify refcount lifecycle (rc++, no move).
* [ ] **Fix ref-array test intent** — `ref_array_give_int_element`, `ref_array_give_class_element`, `ref_array_of_shared_arrays` should use `P = ref` explicitly.
* [ ] **Verify "freed" test snapshots** — `refcount_reaches_zero_frees_allocation`, `shared_array_all_refs_dropped_frees`, `nested_array_all_refs_freed`: backing allocations should now be absent from heap snapshots (Phase 1's "scrub entire array backing on refcount zero" handles this). Verify and update snapshots.

* [ ] **Intentional leak tests** — tests that deliberately skip `array_drop` on some or all elements, then drop the array. The backing allocation is freed but element allocations remain as orphans in the heap snapshot. These document the unsafe contract: array does NOT drop its elements, that's the user's job.
  * `array_leak_all_elements` — create array of Data, drop array without dropping elements. Heap shows orphaned Data allocations.
  * `array_leak_some_elements` — drop elements 0..2 of a 3-element array, skip element 2, drop array. Element 2's allocation remains.

**TDD notes:** This phase produces no new features — only test corrections that reflect the capabilities added in Phase 3 (poly-permission dispatch, range semantics). Do NOT add tests for Phase 4 features (drop sections, `is_last_ref`) or adjust snapshots to account for them. All tests should pass before and after, but the *snapshots* change to reflect correct behavior enabled by Phase 3. Use `UPDATE_EXPECT=1` after verifying each test's intent is right.

### Phase 4: Drop sections

Grammar, type checking, and interpreter support for `drop { ... }` blocks and whole-place drop semantics.

#### 4a: Grammar
* [ ] **`drop { ... }` in ClassDecl** — add an optional `DropBody` section to `ClassDeclBoundData`. Parse `drop { stmts }` after methods.

#### 4b: Type checker
* [ ] **Type-check drop body** — introduce a universal perm variable `P` with `P is ref` assumed in the environment. Type-check the body with `self: P Class[...]`. This avoids needing to synthesize a concrete `ref[place]` — the drop body is checked generically against any ref-compatible permission. For `given class`, type-check with `self: given Class[...]` instead (no universal variable needed).
* [ ] **Array elements are not accessible places** — the type checker already rejects place expressions like `array[i].give` because `Projection::Index` is for tuples (compile-time `usize`), not arrays (runtime `Int`). Add a test confirming that `array[i].give` does not type-check. Array element access is only available through the unsafe `array_give`/`array_drop` intrinsics.

#### 4c: Interpreter
* [ ] **Execute drop body** — modify `drop_value` to check whether the value's type is a class with a `drop { ... }` section. Use `prove_is_owned` on the value's type (from `ObjectValue.ty`) to decide whether to run the drop body — only owned handles (`given`/`shared`) execute the drop body, not borrowed ones (`ref`/`mut`). (Today, `drop_value` already ignores borrowed pointers via the `FieldPointer::Borrowed` path in `and_drop_fields` — this extends that principle to drop bodies.) If owned and has a drop body: build a stack frame with `self` bound, execute the body, then proceed with field-by-field cleanup (the existing `traverse_value` + `and_drop_fields` logic). The drop body runs *before* field cleanup, not instead of it. Fields moved out during the drop body become `Word::Uninitialized` and are skipped by the subsequent field cleanup. `self` type depends on class predicate: `given class` → `self: given Class[...]`, else → create a synthetic variable `**magic**` in the stack frame with type `given Class[...]`, then type `self` as `ref[**magic**] Class[...]`. This gives `ref` a concrete place to point at so type-system machinery works correctly. `self` is treated as *not whole* (so whole-place rules drop fields individually, not recursively).
* [ ] **`Bool` type and operators** — add `Bool` to `TypeName` (alongside `Int`). It is a `shared class` (value type, always copyable). Flat (not boxed), 1 word, represented as `Word::Int` (0 = false, 1 = true) — identical to `Int` at the word level, distinguished only by `TypeName`. Needed for `is_last_ref` return type and `if`/`else` conditions. Update `type_expr` for `Expr::If` to check the condition against `Bool` instead of the current `Int`. Add the following to make `Bool` usable:
  * **`Bool` literals** — `true` and `false` as `Expr` variants. Add `true` and `false` to KEYWORDS. Interpreter: `true` → `alloc_int(1)` with `Ty::bool()`, `false` → `alloc_int(0)` with `Ty::bool()`.
  * **Subtraction** — `Expr::Sub(Arc<Expr>, Arc<Expr>)` with grammar `$v0 - $v1`. Both operands `Int`, result `Int`. (Currently only `+` exists.)
  * **Comparison operators** — `Expr::Ge`, `Expr::Le`, `Expr::Gt`, `Expr::Lt`, `Expr::Eq`, `Expr::Ne`. Each takes two `Int` operands and returns `Bool`. Grammar: `$v0 >= $v1`, `$v0 <= $v1`, `$v0 > $v1`, `$v0 < $v1`, `$v0 == $v1`, `$v0 != $v1`.
  * This is a breaking change — existing tests that use `if 1 { ... } else { ... }` or `if stop.give { ... }` (where `stop` is `Int`) must be updated to use `Bool` values (e.g., `if true { ... }`, `if stop.give >= 1 { ... }`). Update all affected tests in `src/interpreter/tests/basics.rs` and elsewhere.
* [ ] **`is_last_ref` intrinsic** — add `is_last_ref[perm A](value: A T) -> Bool` as an `Expr` variant. Type system: requires `A is ref`, returns `Bool`. Interpreter: for boxed types returns refcount == 1, for non-boxed types returns false. Under GC, always returns false.
* [ ] **Whole-place drop at end of scope** — the wholeness check applies ONLY at end-of-scope cleanup, not inside `drop_value` itself. `drop_value` assumes it always receives whole values. The implementation approach: make the existing `traverse_value`/`traverse_object_fields` machinery generic over the return type. Introduce a trait (e.g., `TraverseResult`) with a `combine` operation. Two implementations: `()` for side-effecting traversals (drop), and `Any(bool)` for queries (wholeness check), where `Any(a).combine(Any(b)) = Any(a || b)`. A field is uninitialized if its first word is `Word::Uninitialized` — this works uniformly for flat and boxed types (after Phase 1's removal of `Flags::Dropped`). This is a shallow check per field (no dereferencing through pointers). End-of-scope cleanup uses this: for each variable, check wholeness. If whole → call `drop_value` (which runs the drop body if present, then drops fields). If not whole → recurse into fields, check each sub-field's wholeness, and call `drop_value` on the whole sub-fields. This recursion naturally handles nested partial moves (e.g., `self.vec` is not whole because `self.vec.data` was moved, but `self.vec.len` is whole and gets dropped individually).
* [ ] **Array elements are not accessible places** — already implemented (`find_object_fields` returns empty vec for arrays).

**TDD notes — tests to write before implementing:**
* `class_with_drop_body` — simple class with `drop { print(self.x) }`, verify drop body runs on scope exit
* `drop_body_self_not_whole` — class with drop body that moves one field; verify remaining fields are individually dropped, no infinite recursion
* `partially_moved_class_drops_fields` — move one field out of a class, verify remaining fields drop at scope exit but the class drop body does NOT run (self not whole)
* `partial_move_then_read_other_field` — move one field out of a struct, then read a different field with `.give`. Verify the read succeeds. This is the pattern `Iterator.drop` relies on (`self.vec.data.give` then `self.vec.len.give`). Already works in the interpreter (field projection is pure pointer arithmetic, no wholeness check), but worth an explicit test.
* `vec_drop_cleans_elements` — `Vec` class with `drop { array_drop[T, given, ref[self]](self.data.ref, 0, self.len.give) }`, verify elements are dropped when vec goes out of scope
* `shared_class_drop_gets_ref_self` — shared class with drop body, verify `self: ref Class`
* `drop_runs_on_every_handle` — shared class with drop body, create two shared handles, verify drop body runs twice (once per handle drop)
* `is_last_ref_true_when_sole_owner` — boxed object with one handle, `is_last_ref` returns true
* `is_last_ref_false_when_shared` — boxed object with two handles, `is_last_ref` returns false on first drop, true on second

### Phase 5: Integration — Vec as a test program

Write the full Vec and Iterator from the design doc as a test program that exercises the entire stack.

* [ ] **Vec push and get** — replace the existing `vector_push_and_get` test wholesale (currently ignored, uses outdated syntax and nonexistent intrinsics like `array_move_elements`). Write a fresh test using the target signatures from the design doc. Un-ignore it. Should pass end-to-end.
* [ ] **Vec iter and next** — test iteration consuming elements with given permission, verify elements are moved out and iterator drop cleans up remaining.
* [ ] **Shared Vec access** — `P = shared` on `Vec.get`, verify elements are shared copies, vec remains usable.
* [ ] **Ref Vec access** — `P = ref` on `Vec.get`, verify elements are borrows.
* [ ] **Vec drop lifecycle** — create vec, push elements, let it go out of scope, verify drop body runs and all allocations are freed.

**TDD notes:** The Vec test is the capstone — if it passes, the whole system works together. Write it first as an aspirational test (like the current ignored `vector_push_and_get`), then un-ignore it when Phase 4 is complete.

### Future: unsafe effects system

* [ ] **Design unsafe effects** — array operations are currently "magic" intrinsics that bypass normal permission rules (e.g., `array_drop` uninitializes element slots through `A is ref`). A proper unsafe effects system would describe and constrain what unsafe operations can do. Not needed for the current Vec milestone, but important for the broader language design.
