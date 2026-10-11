use formality_core::test;

#[test]
fn given_and_mut_satisfy_move() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_move[perm P](^ self, value: P Wrapper)
            where P is move { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[^], d2: ^ Container[mut[source2]],
                    x: ^[d1.field, d2.field] Wrapper) {
                self.give.require_move[^[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn mut_and_given_satisfy_move() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_move[perm P](^ self, value: P Wrapper)
            where P is move { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[mut[source1]], d2: ^ Container[^],
                    x: ^[d1.field, d2.field] Wrapper) {
                self.give.require_move[^[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn given_and_shared_do_not_satisfy_move() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_move[perm P](^ self, value: P Wrapper)
            where P is move { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[^], d2: ^ Container[shared],
                    x: ^[d1.field, d2.field] Wrapper) {
                self.give.require_move[^[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is valid when only the move requirement is removed.
    crate::assert_ok!(&program.replace("where P is move", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_move [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is move { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[^], d2 : ^ Container[shared], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self . give . require_move [^ [d1 . field, d2 . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn shared_and_given_do_not_satisfy_move() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_move[perm P](^ self, value: P Wrapper)
            where P is move { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[shared], d2: ^ Container[^],
                    x: ^[d1.field, d2.field] Wrapper) {
                self.give.require_move[^[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is valid when only the move requirement is removed.
    crate::assert_ok!(&program.replace("where P is move", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_move [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is move { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[shared], d2 : ^ Container[^], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self . give . require_move [^ [d1 . field, d2 . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn mut_and_ref_do_not_satisfy_move() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_move[perm P](^ self, value: P Wrapper)
            where P is move { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[mut[source1]], d2: ^ Container[ref[source2]],
                    x: ^[d1.field, d2.field] Wrapper) {
                self.give.require_move[^[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is valid when only the move requirement is removed.
    crate::assert_ok!(&program.replace("where P is move", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_move [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is move { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[mut [source1]], d2 : ^ Container[ref [source2]], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self . give . require_move [^ [d1 . field, d2 . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn ref_and_mut_do_not_satisfy_move() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_move[perm P](^ self, value: P Wrapper)
            where P is move { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[ref[source1]], d2: ^ Container[mut[source2]],
                    x: ^[d1.field, d2.field] Wrapper) {
                self.give.require_move[^[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is valid when only the move requirement is removed.
    crate::assert_ok!(&program.replace("where P is move", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_move [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is move { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[ref [source1]], d2 : ^ Container[mut [source2]], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self . give . require_move [^ [d1 . field, d2 . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}
