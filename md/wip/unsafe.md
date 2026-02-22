# Unsafe code

There is an built-in `Pointer` type. It is equivalent to a `share` class.

There are built-in language operations to interact with it.

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

## Allocation and memory layout

* `PointerAlloc(size: uint, align: uint)` allocates a new block of memory of the given size and returns a `given Pointer`.

This will be represented (at runtime) via a block of memory with a leading ref-count (stored at a negative offset).

```
            +--------------------+
            | (optional padding) |
            | ref-count (size 8) |
pointer --> |--------------------|
            | size N             |
            |                    |
            |                    |
            +--------------------+
```

The ref-count is initially 1. The pointer itself is gonna need some flags. My plan is to use the lower 2 bits at runtime.

This requires that all (non-shared) classes have at least an alignment of 4, but that's fine, as they also have flags in front.

Shared values do not have a minimum alignment requirement but you also cannot have direct pointers to them. We'll do something clever for string slices though.

### Representing in the interpreter

We will have a `Alloc` struct like

```rust
struct Alloc {
    ref_count: usize,
    data: Vec<Word>
}

enum Word {
    Int(isize),
    Pointer(Pointer),
    Flags(Flags),
    Uninitialized,
}

struct Pointer {
    flags: Flags,
    index: usize,
    offset: usize,
}

enum Flags {
    Given,
    Shared,
    Ref,
    Mut,
}
```

## Dropping the pointer

When a pointer value is dropped, the action depends on its flags

* Given: free the memory
* Shared: dec the ref-count and consider freeing the memory
* Ref/Mut: no-op

## Sharing pointers

The `.share` operation applied to a `Pointer` value:

* if the flags are `Given`, changes them to `Shared`
* if the flags are `Shared`, no-op
* if the flags are `Mut` or `Ref`, changes to `Ref`

## Loading and storing data

* `PointerLoad[type T](pointer: Pointer, offset: uint) -> T` reads memory at a given offset and the given type
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

## Example: Vec

```dada
class Vec[type T] {
    pointer: Pointer
    size: uint

    // Subtle: if this is a `given Vec`, this field stores the capacity.
    // But when a vec is *shared*, it is converted to store the offset.
    // (How *exactly* does that happen though, if we don't have a `share` operation)?
    capacity_or_offset: uint

    // Why *exactly* are we fighting the share operation so hard?
    // What if we just did this?
    // (Could we then make Pointer into a shared class?)
    share {
        self.pointer
    }

    drop {
        // Drop is special, you get access to the fields as local variables.
        // It only executes with each value being `given`.
        for i in 0..size {
            pointer.drop_data[T](i * size_of[T]())
        }
    }


    fn slice(self, offset: uint) -> ref[self] Vec[T] {
        // This is an interesting one too.
        // 
    }
}
```

## Example: String

```dada
class String {
    # Points to character data-- just assume u8 for simplicity
    pointer: Pointer

    # 
    size: uint

    # Subtle: if this is a given class, stores capacity.
    # But for a `ref String`, stores the *character offset*
    capacity_or_offset: uint
}

impl String {
    fn slice(self, offset: uint) -> ref[self] String {
        let pointer: ref[self.pointer] Pointer = self.pointer.ref(0)
        ref[self] String {
            pointer,
            size: self.size - offset,
            capacity_or_offset: offset,
        }
    }

    fn get(self, offset: uint) -> char {
        if self is given || self is shared {

        } else {

        }
    }
}
```