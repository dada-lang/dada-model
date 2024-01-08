Notes to myself about possible next steps:

- [x] add some basic tests for share/lease
- [x] incorporate liveness
- [ ] complete type check rules for all the expressions
- [x] convert from fns to methods
- [x] giving places should rename
- [ ] add structs/enums/value types
- [ ] convert Int to a value type (we'll have to fix a lot of tests)
- [x] tests for giving a shared value (I think it'll do the wrong thing now!)
- [x] tests for giving a leased value
- [ ] moving from a class field `x` where other fields reference `self.x` -- this needs to either be an error or invalidate the struct
  - idea: if moving from `x`, and `x` is live, traverse its fields to find out if any of them forbid the place from being moved
