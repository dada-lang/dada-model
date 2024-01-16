Notes to myself about possible next steps:

- [x] add some basic tests for share/lease
- [x] incorporate liveness
- [x] convert from fns to methods
- [x] giving places should rename
- [x] tests for giving a shared value (I think it'll do the wrong thing now!)
- [x] tests for giving a leased value
- [x] moving from a class field `x` where other fields reference `self.x` -- this needs to either be an error or invalidate the struct
- [ ] complete type check rules for all the expressions
- [ ] add structs/enums/value types
- [ ] convert Int to a value type (we'll have to fix a lot of tests)
- [ ] popping variables from environment may need to clear from types
- [ ] pop variables from environment as we exit a block
- [ ] introduce environment consistency check and assert it at various points
- [ ] giving of shared things currently moves, not copies
- [ ] introduce a "maybe copy" rule to limit splitting of paths
- [ ] type inference
- [ ] `foo.give.share` -- does this even parse?
