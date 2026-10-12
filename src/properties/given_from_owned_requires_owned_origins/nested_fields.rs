use formality_core::test;

#[test]
fn given_and_shared_satisfy_owned() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Inner { field: Wrapper; }
        struct Outer { inner: Inner; }
        struct Main {
            fn require_owned[perm P](self->, value: P Wrapper)
            where P is owned { (); }

            fn test(self->,
                    source1: given Outer, source2: given Outer,
                    d1: given Outer, d2: shared Outer,
                    x: given[d1.inner.field, d2.inner.field] Wrapper) {
                self->.require_owned[given[d1.inner.field, d2.inner.field]](x->);
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
        struct Wrapper { value: Int; }
        struct Inner { field: Wrapper; }
        struct Outer { inner: Inner; }
        struct Main {
            fn require_owned[perm P](self->, value: P Wrapper)
            where P is owned { (); }

            fn test(self->,
                    source1: given Outer, source2: given Outer,
                    d1: shared Outer, d2: given Outer,
                    x: given[d1.inner.field, d2.inner.field] Wrapper) {
                self->.require_owned[given[d1.inner.field, d2.inner.field]](x->);
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
        struct Wrapper { value: Int; }
        struct Inner { field: Wrapper; }
        struct Outer { inner: Inner; }
        struct Main {
            fn require_owned[perm P](self->, value: P Wrapper)
            where P is owned { (); }

            fn test(self->,
                    source1: given Outer, source2: given Outer,
                    d1: given Outer, d2: shared[source2] Outer,
                    x: given[d1.inner.field, d2.inner.field] Wrapper) {
                self->.require_owned[given[d1.inner.field, d2.inner.field]](x->);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Inner { field : Wrapper ; } struct Outer { inner : Inner ; } struct Main { fn require_owned [perm] (self-> value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (self-> source1 : given Outer, source2 : given Outer, d1 : given Outer, d2 : shared [source2] Outer, x : given [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self -> . require_owned [given [d1 . inner . field, d2 . inner . field]] (x ->) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn ref_and_given_do_not_satisfy_owned() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Inner { field: Wrapper; }
        struct Outer { inner: Inner; }
        struct Main {
            fn require_owned[perm P](self->, value: P Wrapper)
            where P is owned { (); }

            fn test(self->,
                    source1: given Outer, source2: given Outer,
                    d1: shared[source1] Outer, d2: given Outer,
                    x: given[d1.inner.field, d2.inner.field] Wrapper) {
                self->.require_owned[given[d1.inner.field, d2.inner.field]](x->);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Inner { field : Wrapper ; } struct Outer { inner : Inner ; } struct Main { fn require_owned [perm] (self-> value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (self-> source1 : given Outer, source2 : given Outer, d1 : shared [source1] Outer, d2 : given Outer, x : given [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self -> . require_owned [given [d1 . inner . field, d2 . inner . field]] (x ->) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn shared_and_mut_do_not_satisfy_owned() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Inner { field: Wrapper; }
        struct Outer { inner: Inner; }
        struct Main {
            fn require_owned[perm P](self->, value: P Wrapper)
            where P is owned { (); }

            fn test(self->,
                    source1: given Outer, source2: given Outer,
                    d1: shared Outer, d2: ![source2] Outer,
                    x: given[d1.inner.field, d2.inner.field] Wrapper) {
                self->.require_owned[given[d1.inner.field, d2.inner.field]](x->);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Inner { field : Wrapper ; } struct Outer { inner : Inner ; } struct Main { fn require_owned [perm] (self-> value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (self-> source1 : given Outer, source2 : given Outer, d1 : shared Outer, d2 : ! [source2] Outer, x : given [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self -> . require_owned [given [d1 . inner . field, d2 . inner . field]] (x ->) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn mut_and_shared_do_not_satisfy_owned() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Inner { field: Wrapper; }
        struct Outer { inner: Inner; }
        struct Main {
            fn require_owned[perm P](self->, value: P Wrapper)
            where P is owned { (); }

            fn test(self->,
                    source1: given Outer, source2: given Outer,
                    d1: ![source1] Outer, d2: shared Outer,
                    x: given[d1.inner.field, d2.inner.field] Wrapper) {
                self->.require_owned[given[d1.inner.field, d2.inner.field]](x->);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Inner { field : Wrapper ; } struct Outer { inner : Inner ; } struct Main { fn require_owned [perm] (self-> value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (self-> source1 : given Outer, source2 : given Outer, d1 : ! [source1] Outer, d2 : shared Outer, x : given [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self -> . require_owned [given [d1 . inner . field, d2 . inner . field]] (x ->) ; source1 . share ; source2 . share ; () ; } } }`"]);
}
