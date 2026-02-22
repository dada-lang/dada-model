# Unsafe code

## Levels of classes

* `give class` (can be given)
* `share class` (can be shared, the default)
* `shared class` (already shared)

## Memory representation of values

We have two classes of values

* unique -- these are guard classes, share classes, and shared classes that have a type parameter which is unique
* shared -- these are shared classes, integers, flags, characters (when we add those)

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

## Pointer type

Built-in type `Pointer` equivalent to integer. Shared class. No semantics on its own. Has some built-in operations, modeled as special expressions in a-mir-formality, but as intrinsic methods in the real Dada.

## Type sizes

In a-mir-formality, the `size_of[T]()` intrisnic returns 1 for ints/pointers, 0 for assertion types, and otherwise sums the fields for a class (including flags). The real system has more complex layout rules obviously.

## Allocation and freeing memory

* `PointerNew(size: uint)` allocates a new block of memory of the given size and returns a `Pointer`.
* `PointerFree(pointer: Pointer, size: uint)` frees a block of memory which must have had the given size and alignment.

### Representing in the interpreter

We will have a `Alloc` struct like

```rust
struct Alloc {
    data: Vec<Word>    // data, data.len() == size
}

enum Word {
    Int(isize),
    Pointer(Pointer),
    MutRef(Pointer),
    Flags(Flags),
    Uninitialized,
}

struct Pointer {
    index: usize,
    offset: usize,
}

enum Flags {
    // Unique ownership
    Given,

    // Shared ownership
    Shared,

    // Copied fields from value stored elsewhere, either `ref` or `shared mut`
    Borrowed,
}
```

## Giving places

When you give a place `place.give`, you give "all the permissions you have to that place". This means that you consult the flags on the value to find the "minimal perms" along the way:

* Given: if you have given perms, you copy the fields and overwrite the original with uninit
* Shared: if you have shared perms, you copy the fields, set the flags in your copy to Shared, and then invoke the "shared hook" (see below)
* Borrowed: if you have ref perms, you copy the fields, set the flags in your copy to Borrowed

## The shared hook

The 'shared hook' is an operation that executes on a copy of a value that has been shared. The shared hook is a no-op for primitive types like ints, pointers, and flags.

For classes, the shared hook begins by first recursively invoking the shared hook on each field. After that, it executes the user-defined shared hook, if any:

```dada
class Foo {
    shared(self) {
        // Code here executes with a `self: ref Foo` and returns `()`
    }
}
```

## Sharing values (not places)

The `value.share` operation consumes an in-flight value. Its effect depends on the flags in that value:

* Given: convert the flag to shared; the shared hook does not run as this is the first copy
* Shared/Borrowed: no change

## Dropping values and the "drop hook"

Dropping primitives like ints and pointers has no effect.

The effect of dropping a class depends on the flags:

* Borrowed -- no-op
* Given or Shared -- works by executing the "drop hook" in a new mini-stack-frame:
    * First, each field in the class is moved into a local variable
    * Next, the appropriate drop hook is executed, depending on the flags
        * If given, the `drop given { }` hook executes.
        * If shared, the `drop shared { }` hook executes.

Drop hooks are defined in the class like so:

```dada
class Foo {
    drop given {
        // Code that executes when given
    }

    drop shared {
        // Code that executes when given
    }
}
```

If not provided, the default is an empty block. In a `given class`, only `drop given` is permitted.

Note that even with an empty block, the local variables will be recursively dropped at the end of the drop hook (if they've not been consumed in some other fashion).

## Forgetting places

There is an intrinsic `Forget` operation to avoid dropping a value. This is unsafe and must not cause a guard value to not be dropped.

```
fn forget(value: type T)
```

## Kind testing

```
if $place is {
    given =>
    shared =>
    ref => // also covers `shared mut`
    mut =>
}
```

Tests at runtime if this is a given/shared/ref/mut value using the flags. At compilation time does the check with `$place is predicate` in the environment.

## Loading and storing data

* `PointerGive[type T](pointer: Pointer, offset: uint) -> T` reads memory at a given offset and the given type
* `PointerStore[type T](pointer: Pointer, offset: uint, value: T)` writes mermory at a given offset and the given type

Loading/store data:

* A *given* value -- copy from old to new location, overwrite old location with uninit
* A *shared* value -- copy from out, adjusting flags (if needed) in the new value, and then inc the ref-count
* A *ref* value -- copy out, adjust flags
* A *mut* value -- just return the pointer at the given offset. The offset must be 4-aligned.

## Dropping the data

* `PointerDrop[type T](pointer: Pointer, offset: uint)` drops the value

Dropping data:

* A *given* value -- drop it recursively
* A *shared* value -- dec the ref-count and drop if it reaches 0
* A ref/mut value -- no-op

## Dada syntatic sugar

We give examples below using Dada syntactic sugar that is not available in the model

* `Foo { place }` for `Foo { place:place }`
* `TypeName(...)` for `TypeName.new()`
* `fn foo(x: type T)` for `fn foo[type T](x: T)` (also in other positions, e.g., return type)
* `fn foo(self)` for `fn foo[perm P](P self)`
* `pred type T` for `type T` and `where T is pred`
* `pointer.give_data[T](offset)` for `PointerGiveData[T](pointer, offset)`

## Example: The `Alloc` type

The `Alloc` is a convenient type for a pointer that carries a ref-count + add'l data.

It doesn't know what data it contains and you must explicitly drop/free or else the data will leak.

Ref counts must also be namanged explicitly.

```dada
export shared class Alloc {
    pointer: Pointer

    export fn new(size: uint) -> Alloc {
        let pointer = Pointer.alloc(size + 1) // the +1 adds a ref-count
        pointer.store_data(0, 1)
        Alloc {
            pointer: pointer
        }
    }

    export fn free(size: uint) {
        self.pointer.free(1 + size)
    }

    export fn inc_ref_count(self) {
        let ref_count = self.pointer.give_data[int](0)
        self.pointer.store_data(0, ref_count + 1)
    }

    export fn dec_ref_count(self) -> int {
        let ref_count = self.pointer.give_data[int](0) - 1
        self.pointer.store_data(0, ref_count)
        ref_count
    }

    export fn give_data[type T](self, offset: int) -> T {
        self.pointer.give_data[T](1 + offset)
    }
    
    export fn store_data[type T](self, offset: int, value: given T) {
        self.pointer.store_data[T](1 + offset, value.give)
    }

    export fn drop_data[type T](self, offset: int) {
        self.pointer.drop_data[T](1 + offset)
    }
}
```

## Example: The `Box` type

The `Box` type carries a single allocation; it could be in the Dada stdlib.

```dada
export class Box[type T] {
    alloc: Alloc

    export fn new(value: T) {
        let alloc = Alloc(size_of[T]())
        alloc.store_data(0, value)
        Box {
            alloc: alloc
        }
    }

    export fn get(self) -> given[self] T {
        if self is {
            given => {
                let data = self.alloc.give_data[given T](0)
                self.alloc.free(size_of[T] + 1)
                forget(self)
                data
            }

            shared | ref | mut => {
                self.alloc.give_data[given[self] T](0)
            }
        }
    }

    shared {
        self.alloc.inc_ref_count()
    }

    drop given {
        Self.drop_alloc(alloc)
    }

    drop shared {
        if alloc.dec_ref_count() == 0 {
            Self.drop_alloc(alloc)
        }
    }

    fn drop_alloc(alloc: Alloc) {
        alloc.drop_data[T](0)
        alloc.free(size_of[T]())
    }
}
```

## Example: The `Vec` type

The `Vec` type is a building block for other data structures. It stores up to `int.MAX` elements.

For simplicity I am going to ignore the "resizing" elements and just assume it has a fixed capacity for now.

```dada
export class Vec[type T] {
    alloc: Alloc

    // Number of initialized elements.
    length: int

    // If this is a "unique" (given/mut) Vector, this will be >= 0 and represents capacity.
    // If this is a "shared" vector, it may be a negative value, in which case it represents an offset within `Pointer`.
    capacity_or_offset: int   // note: signed!

    export fn new(capacity: int) {
        assert capacity > 0
        let a = Alloc(size_of[T]() * capacity)
        Vec {
            alloc: a
            length: 0
            capacity_or_offset: capacity
        }
    }

    export fn push(self!, value: given T) {
        if self.length < self.capacity() {
            self.alloc.store_data(self.length, value.give)
            self.length += 1
        } else {
            panic // later on, we would resize here
        }
    }

    // Returns the starting offset within pointer for this vec/slice.
    fn capacity(self) -> int {
        assert self.capacity_or_offset >= 0
        self.capacity_or_offset
    }

    // Returns the starting offset within pointer for this vec/slice.
    //
    // If `capacity_or_offset` is positive, this is 0.
    fn offset(self) -> int {
        -min(0, self.capacity_or_offset)
    }

    export fn slice(self, offset: int) -> ref[self] Vec[T] {
        if offset >= self.size {
            panic
        }

        let o = self.offset() + offset
        let l = self.length - offset

        if self is {
            shared => {
                self.alloc.inc_ref_count()
            }
        }

        ref[self] Vec {
            alloc: self.alloc
            length: l
            capacity_or_offset: -o
        }
    }

    export fn get(self, index: int) -> given[self] T {
        if !(index < self.length) {
            panic
        }

        let offset = (self.offset() + index) * size_of[T]()

        if self is {
            given => {
                assert self.offset() == 0

                Self.drop_values(self.alloc, 0, index)
                let data = self.alloc.give_data[given T](offset)
                Self.drop_values(self.alloc, index + 1, self.length)
                Self.free_alloc(self.alloc, self.length)
                forget(self)

                data
            }

            ref | mut | shared => {

            }
        }
    }

    shared {
        self.alloc.inc_ref_count()
    }

    drop given {
        Self.drop_alloc(alloc, length)
    }

    drop shared {
        if alloc.dec_ref_count() == 0 {
            Self.drop_alloc(alloc, length)
        }
    }

    fn drop_values(alloc: Alloc, from: int, to: int) {
        for i in from .. to {
            alloc.drop_data[T](i)
        }
    }

    fn drop_alloc(alloc: Alloc, length: int) {
        Self.drop_values(alloc, 0, length)
        Self.free_alloc(alloc, length)
    }
    
    fn free_alloc(alloc: Alloc, length: int) {
        pointer.free(size_of[T]() * length)
    }
}
```

## FAQ

