# Vec and array design

We are working our way towards the following design which will cover a "partially initialize" array type called `Vec` (the full `Vec` in the standard library would be expected to support more features, but this is enough for now). I'm also assuming all indices are in-bounds and a few other details.

## Goal: Vector class

```dada
class Vec[type T] {
    data: Array[T]
    len: uint
    
    fn push[perm P](P self, value: given T) where P is mut {
        array_write(self.data.mut, self.len, value.give)
        self.len += 1
    }
    
    fn get[perm P](P self, index: uint) -> given[self] T {
        let data: given[self.data] Array[T] = self.data.give # subtle: disables dtor, see below
        let len: uint = self.len.give
        array_drop[T, given[self], ref[data]](data.ref, 0, index)
        array_drop[T, given[self], ref[data]](data.ref, index + 1, len)
        array_give[T, given[self], ref[data]](data.ref, index)
    }
    
    fn iter[perm P](P self) -> Iterator[P, T] {
        Iterator { vec: self.give, start: 0 }
    }

    drop {
        array_drop[T, given, ref[self]](self.data.ref, 0, self.len)
    }
}

class Iterator[perm P, type T] {
    vec: P Vec[T]
    start: uint
    
    fn next[perm I](I self) -> P T
    where
        I is mut,
    {
        self.start += 1
        array_give[T, P, ref[self.vec]](self.vec, self.start - 1)
    }
    
    drop {
        let data = self.vec.data.give # subtle: disables vec dtor
        let start = self.start.give
        let len = self.vec.len.give
        
        # free the elements not yet iterated over:
        array_drop[T, P, ref[self]](data.ref, start, len)
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

* `array_new[type T](capacity: uint) -> Array[T]`, returns an uninitialized array
* `array_capacity[type T, perm A](array: A Array[T]) where A is ref`, returns capacity of an array
* `array_write[type T, perm A](array: A Array[T], index: usize, value: given T) where A is mut`, writes the value to the given index; any previous value is *ignored*
* `array_drop[type T, perm P, perm A](array: A Array[T], from: usize, to: usize) where A is ref`, drops elements from `from..to` (exclude) in a way that depends on the permission P:
  * If `P` is `given`, then the value is dropped.
  * Else this is a no-op.
* `array_give[type T, perm P, perm A](array: A Array[T], index: usize) -> P T where A is ref`, reads and returns the element at `index` in a way that depends on the permission P:
  * If `P` is `given`, then the value is moved and the memory is uninitialized.
  * Else, if `P` is `mut`, then a mutable reference to the value is created.
  * Else, if `P` is `shared` *or* if `A` is shared, then the value is "shared" (i.e., read and then internal ref-counts are inc'd).
  * Else, `P` is `ref`, then the result is a borrowed (i.e., read and then internal flags are set to ref).

The semantics of drop and give are setup to support a "poly-permission" operation like `Vec.get` above. The `array_drop` calls in `get` are no-ops when `P` is not `given`, but they are present so that a single function body works correctly across all permissions — in the `given` case, they actually destroy the elements we don't want.

Note that the return type `given[self] T` in `Vec.get` is effectively equivalent to `P` — `given[place]` picks up the permission of the place, so `given[self]` where `self: P Vec[T]` becomes `P T`. It is written as `given[self]` because it conveys the intent more clearly: "you get whatever permission you had on self."

### "drop" sections -- defining custom destructors

A *drop* section in a class is a special optional section. It is type-checked in a way that depends on the permissions of the class:

* If this is a `given` class, then it gets `self: given Class`;
* else if gets `self: ref Class`.

When a drop body executes, `self` is treated as *not whole* even though all its fields are initialized. This means the whole-place drop logic will drop each field individually rather than dropping `self` as a unit (which would recursively invoke the drop body again). There is no special "post-drop-body field cleanup" step — the individual field drops are a consequence of the existing whole-place rules applied to a `self` that is never whole.

### Executing "drop"

The *drop* for a class is executed when the last reference to an instance of that class is dropped. If this is a `given class`, then there is only ever one instance, and hence the type of `self` is a `given Class`.

If this is a `share class`, then the fields may have been shared, and hence the type is a `ref` permission, to indicate that this class does not necessarily have unique ownership over those values.

*Subtle:* in our `Vec` example, the drop code drops the contents of array recursively. This is sound because `Vec` does not allow `Array` to escape, even when the vec is shared.

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
    index: uint
    
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

At point B, `self.data` has been moved, and hence `self` is not a whole place. `self` would not be dropped and hence its drop code would not run. `self.index` is a whole accessible place and would be dropped (but dropping a `uint` is a no-op).

## FAQ

**Q: Why does `Vec.get` call `array_drop` on all elements except the one being returned? Isn't that wasteful for `ref`/`shared`?**

The function body is polymorphic over `P`. When `P` is `given`, those `array_drop` calls actually destroy the elements we don't want (we're consuming the vec). When `P` is `ref` or `shared`, the `array_drop` calls are no-ops. The alternative would be separate implementations per permission, but one body that works for all permissions is simpler and correct.

**Q: What does `given[self]` mean as a return type?**

`given[place]` picks up the permission of the place. So `given[self]` where `self: P Vec[T]` is effectively `P T`. It's written as `given[self]` rather than `P` because it conveys intent more clearly: "you get whatever permission you had on self."

**Q: How does the drop body avoid infinite recursion? If `self` is whole at the end of the drop body, wouldn't whole-place dropping invoke the drop body again?**

In a drop body, `self` is treated as *not whole* even though all its fields are initialized. This means the whole-place logic drops each field individually rather than dropping `self` as a unit. No special mechanism — just the existing whole-place rules applied to a `self` that is never whole.

**Q: In `Iterator.drop`, moving `self.vec.data` out disables `Vec.drop`. But what about the array backing itself?**

The local `data` is whole at end of scope, so it gets dropped normally: refcount decremented, backing freed if zero. Any elements not covered by the `array_drop(data.ref, start, len)` call (i.e., elements before `start` that were already iterated and consumed) are already gone — they were moved out by `next()`. So the cleanup is complete: `array_drop` handles un-iterated elements, and dropping `data` frees the backing.

**Q: When `P = shared`, doesn't `array_drop` being a no-op cause leaks in `Iterator.drop`?**

No. When `P = shared`, the iterator doesn't own the vec — `self.vec` is `shared Vec[T]`. So `self.vec.data.give` produces a shared copy of the array (incrementing its refcount), not a move. `self.vec` stays whole, the `array_drop` call is a no-op, and the shared `data` copy just gets its refcount decremented at end of scope. The real cleanup happens when the last actual owner of the `Vec` is dropped, which fires `Vec.drop` with `P = given` and does the real element cleanup. The "disables vec dtor" comment in `Iterator.drop` is only operative in the `P = given` case.

**Q: What does `array_drop` with `P = given` actually do to each element? Shallow uninitialize, or full recursive drop?**

Full recursive drop. If the element's class has a `drop { }` section, that body runs (and then fields are individually dropped via the not-whole `self` rule). If it has no `drop { }` section, it behaves as if it had an empty `drop {}` — fields are individually dropped directly. This recurses all the way down through nested classes.

**Q: How can `array_drop` with `P = given` uninitialize element slots through just `A is ref`? Doesn't modifying memory require `mut`?**

Array operations are unsafe intrinsics — they are "magic" and can do things normal safe code cannot. The `A is ref` constraint is the minimum the type system enforces on the caller, but the operations themselves bypass normal permission rules internally. A full "unsafe effects" system to describe and constrain what unsafe operations can do is future work.

## Random notes to check on

* `given[a.b] Foo` -- if `a: mut Foo` but its field is `shared Bar`, then `given[a.b]` cannot be contracted to `given[a]`, check if we handle this correctly? (I think we do)

## Implementation plan

Implementation follows a TDD approach: write or update tests first to express intent, then implement until they pass. Each phase produces a working, all-tests-passing state. Tests that don't yet match intent are fixed in the phase where the feature that enables correct behavior lands.

**Agent workflow:** Complete ONE phase at a time. After each phase, commit the work, run `cargo test --all --all-targets` to confirm 100% of tests pass (0 failures, 0 ignored unless pre-existing), and **stop**. Do not begin the next phase. A human must review the completed phase and explicitly approve before the next phase begins. This is a hard rule — never do more than one phase without human-in-the-loop review. Each phase should be a separate commit (or small series of commits).

### Phase 1: Standalone renames and syntax

No semantic changes. Clears the deck so subsequent code matches the doc's notation.

* [ ] **Rename `array_set` → `array_write`** — pure rename across grammar, interpreter, type system, and all tests. Current `array_set` already has "ignore previous value" semantics.
* [ ] **`Perm is Pred` syntax** — flip `Predicate::Parameter` grammar from `#[grammar($v0($v1))]` to `#[grammar($v1 is $v0)]`. Add `is` to KEYWORDS. Update all test programs and `where` clauses.

**TDD notes:** All existing tests should pass after mechanical rename/rewrite. No new tests needed — this is a syntax-only change.

### Phase 2: Permission parameter plumbing

Add `P` and `A` parameters to array ops. Loosen access requirements. Keep current behavior — all existing call sites pass `P = given` (or equivalent).

* [ ] **Add `P`, `A` parameters to `array_give`** — grammar: `array_give[T, P, A](array, index)`. Interpreter: extract P and A from parameters but dispatch only on P=given (move, current behavior). Type system: accept 3 type parameters, require `A is ref`.
* [ ] **Add `P`, `A` parameters to `array_drop`** — grammar: `array_drop[T, P, A](array, index)`. Keep single-index for now. Interpreter: extract P, dispatch only on P=given (drop, current behavior). Type system: require `A is ref` (loosen from current `mut`).
* [ ] **Add `A` parameter to `array_write`** — grammar: `array_write[T, A](array, index, value)`. Type system: require `A is mut` (already enforced).
* [ ] **Add `A` parameter to `array_capacity`** — grammar: `array_capacity[T, A](array)`. Type sse 3, ystem: require `A is ref` (loosen from current give).

**TDD notes:** Update all existing test call sites from `array_give[T](...)` to `array_give[T, given, ref[a]](...)` etc. Tests should pass with identical behavior since P=given matches current semantics. Key tests to watch:
* `array_give_given_class_moves_out` — should keep move semantics with explicit `P = given`
* `array_drop_element`, `array_drop_class_element` — should keep drop semantics with `P = given`
* `array_capacity_given`, `array_capacity_shared`, `array_capacity_ref` — should all work with `A is ref`

### Phase 3: Poly-permission semantics

Implement dispatch on `P` for `array_give` and `array_drop`. Add range semantics to `array_drop`.

* [ ] **`array_give` dispatches on P** — given → move and uninitialize source, mut → mut ref to element, shared (or A is shared) → shared copy (rc++), ref → borrow (copy with ref flags).
* [ ] **`array_drop` dispatches on P** — given → actually drop element, else → no-op.
* [ ] **`array_drop` range semantics** — change from single index to `(array, from, to)`, drops elements in `from..to` range. Applies P-dispatch to each element.

**TDD notes — new tests to write *before* implementing:**
* `array_give_P_mut` — `array_give[Data, mut, ref[a]](a.ref, 0)` returns a `mut[a] Data`
* `array_give_P_shared` — `array_give[Data, shared, ref[a]](a.ref, 0)` returns a shared copy, rc incremented
* `array_give_P_ref` — `array_give[Data, ref, ref[a]](a.ref, 0)` returns a borrowed copy
* `array_drop_P_shared_is_noop` — `array_drop[Data, shared, ref[a]](a.ref, 0, 1)` does nothing, element still accessible
* `array_drop_P_given_range` — `array_drop[Data, given, ref[a]](a.ref, 0, 3)` drops elements 0, 1, 2
* `array_give_P_given_int_is_copy` — giving an Int element with P=given copies without uninitializing (Int is copy)

* `array_give_ref_of_shared_is_shared` — `P = ref[shared_place]` where the place is shared. The interpreter normalizes `ref[shared_place]` to shared and produces a shared copy (rc++), not a borrow. This tests that the "or A is shared" clause in `array_give` works via permission normalization. The interpreter's full-substitution approach gives reference semantics; a real compiler would use coarser dispatch but must produce the same observable behavior.

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
    array_write(array, 0, new Data())
    let shared_array = array.give.share
    let elem0 = head[ref[shared_array]](shared_array.ref)
    # elem0 should be `shared Data`, not `ref Data`
}
```

### Phase 3.5: Test rewrite

Rewrite existing tests to use the new array op signatures and express their *intended* semantics now that poly-permission and range ops are available.

* [ ] **Fix "freed" tests** — `refcount_reaches_zero_frees_allocation`, `shared_array_all_refs_dropped_frees`, `nested_array_all_refs_freed`: add explicit `array_drop[T, given, ...]` for elements before dropping the array. Verify backing allocation is gone from heap snapshot.
* [ ] **Restore shared-array test intent** — tests like `shared_array_give_class_is_shared_copy` should use `P = shared` explicitly instead of relying on runtime flag inference. Verify refcount lifecycle (rc++, no move).
* [ ] **Fix ref-array test intent** — `ref_array_give_int_element`, `ref_array_give_class_element`, `ref_array_of_shared_arrays` should use `P = ref` explicitly.
* [ ] **Verify backing freed on refcount zero** — several tests show `Alloc 0x03: [Uninitialized, ...]` still present after all refs dropped. After proper element cleanup, these allocations should be absent from the heap snapshot.

* [ ] **Intentional leak tests** — tests that deliberately skip `array_drop` on some or all elements, then drop the array. The backing allocation is freed but element allocations remain as orphans in the heap snapshot. These document the unsafe contract: array does NOT drop its elements, that's the user's job.
  * `array_leak_all_elements` — create array of Data, drop array without dropping elements. Heap shows orphaned Data allocations.
  * `array_leak_some_elements` — drop elements 0..2 of a 3-element array, skip element 2, drop array. Element 2's allocation remains.

**TDD notes:** This phase produces no new features — only test corrections. All tests should pass before and after, but the *snapshots* change to reflect correct behavior. Use `UPDATE_EXPECT=1` after verifying each test's intent is right.

### Phase 4: Drop sections

Grammar, type checking, and interpreter support for `drop { ... }` blocks and whole-place drop semantics.

#### 4a: Grammar
* [ ] **`drop { ... }` in ClassDecl** — add an optional `DropBody` section to `ClassDeclBoundData`. Parse `drop { stmts }` after methods.

#### 4b: Type checker
* [ ] **Type-check drop body** — `self` type depends on class predicate: given class → `self: given Class[...]`, else → `self: ref Class[...]`. Check the body in that context.
* [ ] **Array elements are not accessible places** — the type system must not consider array elements when computing accessible places for drop analysis.

#### 4c: Interpreter
* [ ] **Execute drop body** — when the last owned reference to a class instance is dropped, run its `drop { ... }` if present. `self` is bound with all fields initialized but treated as *not whole* (so whole-place rules drop fields individually, not recursively).
* [ ] **Whole-place drop at end of scope** — current: drops all local variables. Target: only drop *whole* accessible places. Partially-moved values have their remaining whole sub-places dropped individually. This is "the one place in the interpreter that we branch on uninitialized data."
* [ ] **Array elements are not accessible places** — already implemented (`find_object_fields` returns empty vec for arrays).

**TDD notes — tests to write before implementing:**
* `class_with_drop_body` — simple class with `drop { print(self.x) }`, verify drop body runs on scope exit
* `drop_body_self_not_whole` — class with drop body that moves one field; verify remaining fields are individually dropped, no infinite recursion
* `partially_moved_class_drops_fields` — move one field out of a class, verify remaining fields drop at scope exit but the class drop body does NOT run (self not whole)
* `vec_drop_cleans_elements` — `Vec` class with `drop { array_drop[T, given, ref[self]](self.data.ref, 0, self.len) }`, verify elements are dropped when vec goes out of scope
* `shared_class_drop_gets_ref_self` — shared class with drop body, verify `self: ref Class` (not given)

### Phase 5: Integration — Vec as a test program

Write the full Vec and Iterator from the design doc as a test program that exercises the entire stack.

* [ ] **Vec push and get** — update the existing `vector_push_and_get` test (currently ignored) with the target signatures from the design doc. Un-ignore it. Should pass end-to-end.
* [ ] **Vec iter and next** — test iteration consuming elements with given permission, verify elements are moved out and iterator drop cleans up remaining.
* [ ] **Shared Vec access** — `P = shared` on `Vec.get`, verify elements are shared copies, vec remains usable.
* [ ] **Ref Vec access** — `P = ref` on `Vec.get`, verify elements are borrows.
* [ ] **Vec drop lifecycle** — create vec, push elements, let it go out of scope, verify drop body runs and all allocations are freed.

**TDD notes:** The Vec test is the capstone — if it passes, the whole system works together. Write it first as an aspirational test (like the current ignored `vector_push_and_get`), then un-ignore it when Phase 4 is complete.

### Future: unsafe effects system

* [ ] **Design unsafe effects** — array operations are currently "magic" intrinsics that bypass normal permission rules (e.g., `array_drop` uninitializes element slots through `A is ref`). A proper unsafe effects system would describe and constrain what unsafe operations can do. Not needed for the current Vec milestone, but important for the broader language design.
