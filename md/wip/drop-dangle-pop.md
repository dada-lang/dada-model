# Drop Dangle Pop

> **Status: Design in progress.** We are still working out the right approach. Nothing here is final.

## Problem

We are not accounting for the possibility of popped variables and references very well. I'll explain through examples.

### Example 1. Give referenced value, but reference is dead

This example should be ok.

```dada
class Data()

let base = Data();
let r = base.ref;

{
    base.give;
}
```

### Example 2. Give referenced value, reference is not dead -- ERROR

This example should be an error.

```dada
class Data()

let base = Data();
let r = base.ref;

{
    base.give;
}

print(r)
```

### Example 3. Give `data` when a reference to `data` is used in a share class destructor -- OK

When a share class has a destructor, it should not assume that values of generic type are valid.

```dada
class Wrap[type T] {
  value: T;
  
  drop { 
      // this destructor does not access `value`
  }
}

class Data()

let base = Data();
let r = base.ref;
let wrap = new Wrap(r);

{
    base.give;
}

// wrap dtor runs here, but no harm done
```

### Example 4. `share` class destructor attempting to access generic data -- ERROR

When a share class has a destructor, it should not assume that values of generic type are valid.

```dada
class Wrap[type T] {
  value: T;
  
  drop { 
    let x = self.value.ref; // ERROR
  }
}
```

### Example 5. `given` class destructor can access values -- OK

Given classes get full ownership of their fields and are able to access them.

```dada
given class Wrap[type T] {
  value: T;
  
  drop { 
      // THIS dtor gets ownership of value
      let x = self.value.give; // OK
  }
}
```

### Example 6. Give `data` when a reference to `data` is used in a `given` destructor -- ERROR

Given classes get full ownership of their fields and are able to access them.

```dada
given class Wrap[type T] {
  value: T;
  
  drop { 
      // THIS dtor gets ownership of value
      let x = self.value.give; // OK
  }
}

class Data()

let base = Data();
let r = base.ref;
let wrap = new Wrap(r);

{
    base.give;
}

// wrap dtor runs here -- ERROR
```

## Planned design

### Add `Place::Dropped`

I want to add a special place called `Dropped` -- or maybe a special var? When we drop an inflight value (e.g., after `base.give;`) we will rewrite all references to `Inflight` to `Dropped` in the environment.

Therefore, 

### Validity predicates

We will add a new predicate `T is valid`. It is provable for just about anything but not for

* generic parameters (types, permissions) -- must come from the environment
* any permission that references `Place::Dropped` (i.e., `ref` or `mut`)

### Implicit validity predicate on all methods

We will add `where X is valid` for any generic parameter X on every method and on constructors as an implicit requirement, checked on every method call.

It will therefore be in the environment when proving method bodies etc.

### Validity predicate is present for `drop` in a `given` class, but NOT present for drop in a `share` class

The validity predicate will not be allowed

### Drop of a given type is considered a live use for that value

For a block, the set of values live on exit includes any that will be dropped. Oh, this is interesting.
