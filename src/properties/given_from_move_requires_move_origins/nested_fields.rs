use formality_core::test;

#[test]
fn given_and_mut_satisfy_move() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Inner { field: Wrapper; }
        struct Outer { inner: Inner; }
        struct Main {
            fn require_move[perm P](^ self, value: P Wrapper)
            where P is move { (); }

            fn test(^ self,
                    source1: ^ Outer, source2: ^ Outer,
                    d1: ^ Outer, d2: ![source2] Outer,
                    x: ^[d1.inner.field, d2.inner.field] Wrapper) {
                self^.require_move[^[d1.inner.field, d2.inner.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn mut_and_given_satisfy_move() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Inner { field: Wrapper; }
        struct Outer { inner: Inner; }
        struct Main {
            fn require_move[perm P](^ self, value: P Wrapper)
            where P is move { (); }

            fn test(^ self,
                    source1: ^ Outer, source2: ^ Outer,
                    d1: ![source1] Outer, d2: ^ Outer,
                    x: ^[d1.inner.field, d2.inner.field] Wrapper) {
                self^.require_move[^[d1.inner.field, d2.inner.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn given_and_shared_do_not_satisfy_move() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Inner { field: Wrapper; }
        struct Outer { inner: Inner; }
        struct Main {
            fn require_move[perm P](^ self, value: P Wrapper)
            where P is move { (); }

            fn test(^ self,
                    source1: ^ Outer, source2: ^ Outer,
                    d1: ^ Outer, d2: shared Outer,
                    x: ^[d1.inner.field, d2.inner.field] Wrapper) {
                self^.require_move[^[d1.inner.field, d2.inner.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the move requirement is removed.
    crate::assert_ok!(&program.replace("where P is move", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Inner { field : Wrapper ; } struct Outer { inner : Inner ; } struct Main { fn require_move [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is move { () ; } fn test (^ self source1 : ^ Outer, source2 : ^ Outer, d1 : ^ Outer, d2 : shared Outer, x : ^ [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self ^ . require_move [^ [d1 . inner . field, d2 . inner . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn shared_and_given_do_not_satisfy_move() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Inner { field: Wrapper; }
        struct Outer { inner: Inner; }
        struct Main {
            fn require_move[perm P](^ self, value: P Wrapper)
            where P is move { (); }

            fn test(^ self,
                    source1: ^ Outer, source2: ^ Outer,
                    d1: shared Outer, d2: ^ Outer,
                    x: ^[d1.inner.field, d2.inner.field] Wrapper) {
                self^.require_move[^[d1.inner.field, d2.inner.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the move requirement is removed.
    crate::assert_ok!(&program.replace("where P is move", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Inner { field : Wrapper ; } struct Outer { inner : Inner ; } struct Main { fn require_move [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is move { () ; } fn test (^ self source1 : ^ Outer, source2 : ^ Outer, d1 : shared Outer, d2 : ^ Outer, x : ^ [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self ^ . require_move [^ [d1 . inner . field, d2 . inner . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn mut_and_ref_do_not_satisfy_move() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Inner { field: Wrapper; }
        struct Outer { inner: Inner; }
        struct Main {
            fn require_move[perm P](^ self, value: P Wrapper)
            where P is move { (); }

            fn test(^ self,
                    source1: ^ Outer, source2: ^ Outer,
                    d1: ![source1] Outer, d2: shared[source2] Outer,
                    x: ^[d1.inner.field, d2.inner.field] Wrapper) {
                self^.require_move[^[d1.inner.field, d2.inner.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the move requirement is removed.
    crate::assert_ok!(&program.replace("where P is move", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Inner { field : Wrapper ; } struct Outer { inner : Inner ; } struct Main { fn require_move [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is move { () ; } fn test (^ self source1 : ^ Outer, source2 : ^ Outer, d1 : ! [source1] Outer, d2 : shared [source2] Outer, x : ^ [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self ^ . require_move [^ [d1 . inner . field, d2 . inner . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn ref_and_mut_do_not_satisfy_move() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Inner { field: Wrapper; }
        struct Outer { inner: Inner; }
        struct Main {
            fn require_move[perm P](^ self, value: P Wrapper)
            where P is move { (); }

            fn test(^ self,
                    source1: ^ Outer, source2: ^ Outer,
                    d1: shared[source1] Outer, d2: ![source2] Outer,
                    x: ^[d1.inner.field, d2.inner.field] Wrapper) {
                self^.require_move[^[d1.inner.field, d2.inner.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the move requirement is removed.
    crate::assert_ok!(&program.replace("where P is move", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Inner { field : Wrapper ; } struct Outer { inner : Inner ; } struct Main { fn require_move [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is move { () ; } fn test (^ self source1 : ^ Outer, source2 : ^ Outer, d1 : shared [source1] Outer, d2 : ! [source2] Outer, x : ^ [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self ^ . require_move [^ [d1 . inner . field, d2 . inner . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}
