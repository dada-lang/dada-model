use formality_core::test;

#[test]
fn given_and_shared_satisfy_owned() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[^], d2: ^ Container[shared],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_owned[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn shared_and_given_satisfy_owned() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[shared], d2: ^ Container[^],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_owned[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn given_and_ref_do_not_satisfy_owned() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[^], d2: ^ Container[shared[source2]],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_owned[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[^], d2 : ^ Container[shared [source2]], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_owned [^ [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn ref_and_given_do_not_satisfy_owned() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[shared[source1]], d2: ^ Container[^],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_owned[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[shared [source1]], d2 : ^ Container[^], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_owned [^ [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn shared_and_mut_do_not_satisfy_owned() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[shared], d2: ^ Container[![source2]],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_owned[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[shared], d2 : ^ Container[! [source2]], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_owned [^ [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn mut_and_shared_do_not_satisfy_owned() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[![source1]], d2: ^ Container[shared],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_owned[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[! [source1]], d2 : ^ Container[shared], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_owned [^ [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}
