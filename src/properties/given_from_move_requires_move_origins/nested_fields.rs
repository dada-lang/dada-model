use formality_core::test;

#[test]
fn given_and_mut_satisfy_move() {
    let program = r#"
        class Wrapper { value: Int; }
        class Inner { field: Wrapper; }
        class Outer { inner: Inner; }
        class Main {
            fn require_move[perm P](given self, value: P Wrapper)
            where P is move { (); }

            fn test(given self,
                    source1: given Outer, source2: given Outer,
                    d1: given Outer, d2: mut[source2] Outer,
                    x: given_from[d1.inner.field, d2.inner.field] Wrapper) {
                self.give.require_move[given_from[d1.inner.field, d2.inner.field]](x.give);
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
        class Inner { field: Wrapper; }
        class Outer { inner: Inner; }
        class Main {
            fn require_move[perm P](given self, value: P Wrapper)
            where P is move { (); }

            fn test(given self,
                    source1: given Outer, source2: given Outer,
                    d1: mut[source1] Outer, d2: given Outer,
                    x: given_from[d1.inner.field, d2.inner.field] Wrapper) {
                self.give.require_move[given_from[d1.inner.field, d2.inner.field]](x.give);
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
        class Inner { field: Wrapper; }
        class Outer { inner: Inner; }
        class Main {
            fn require_move[perm P](given self, value: P Wrapper)
            where P is move { (); }

            fn test(given self,
                    source1: given Outer, source2: given Outer,
                    d1: given Outer, d2: shared Outer,
                    x: given_from[d1.inner.field, d2.inner.field] Wrapper) {
                self.give.require_move[given_from[d1.inner.field, d2.inner.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is valid when only the move requirement is removed.
    crate::assert_ok!(&program.replace("where P is move", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Inner { field : Wrapper ; } class Outer { inner : Inner ; } class Main { fn require_move [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is move { () ; } fn test (given self source1 : given Outer, source2 : given Outer, d1 : given Outer, d2 : shared Outer, x : given_from [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self . give . require_move [given_from [d1 . inner . field, d2 . inner . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn shared_and_given_do_not_satisfy_move() {
    let program = r#"
        class Wrapper { value: Int; }
        class Inner { field: Wrapper; }
        class Outer { inner: Inner; }
        class Main {
            fn require_move[perm P](given self, value: P Wrapper)
            where P is move { (); }

            fn test(given self,
                    source1: given Outer, source2: given Outer,
                    d1: shared Outer, d2: given Outer,
                    x: given_from[d1.inner.field, d2.inner.field] Wrapper) {
                self.give.require_move[given_from[d1.inner.field, d2.inner.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is valid when only the move requirement is removed.
    crate::assert_ok!(&program.replace("where P is move", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Inner { field : Wrapper ; } class Outer { inner : Inner ; } class Main { fn require_move [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is move { () ; } fn test (given self source1 : given Outer, source2 : given Outer, d1 : shared Outer, d2 : given Outer, x : given_from [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self . give . require_move [given_from [d1 . inner . field, d2 . inner . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn mut_and_ref_do_not_satisfy_move() {
    let program = r#"
        class Wrapper { value: Int; }
        class Inner { field: Wrapper; }
        class Outer { inner: Inner; }
        class Main {
            fn require_move[perm P](given self, value: P Wrapper)
            where P is move { (); }

            fn test(given self,
                    source1: given Outer, source2: given Outer,
                    d1: mut[source1] Outer, d2: ref[source2] Outer,
                    x: given_from[d1.inner.field, d2.inner.field] Wrapper) {
                self.give.require_move[given_from[d1.inner.field, d2.inner.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is valid when only the move requirement is removed.
    crate::assert_ok!(&program.replace("where P is move", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Inner { field : Wrapper ; } class Outer { inner : Inner ; } class Main { fn require_move [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is move { () ; } fn test (given self source1 : given Outer, source2 : given Outer, d1 : mut [source1] Outer, d2 : ref [source2] Outer, x : given_from [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self . give . require_move [given_from [d1 . inner . field, d2 . inner . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn ref_and_mut_do_not_satisfy_move() {
    let program = r#"
        class Wrapper { value: Int; }
        class Inner { field: Wrapper; }
        class Outer { inner: Inner; }
        class Main {
            fn require_move[perm P](given self, value: P Wrapper)
            where P is move { (); }

            fn test(given self,
                    source1: given Outer, source2: given Outer,
                    d1: ref[source1] Outer, d2: mut[source2] Outer,
                    x: given_from[d1.inner.field, d2.inner.field] Wrapper) {
                self.give.require_move[given_from[d1.inner.field, d2.inner.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is valid when only the move requirement is removed.
    crate::assert_ok!(&program.replace("where P is move", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Inner { field : Wrapper ; } class Outer { inner : Inner ; } class Main { fn require_move [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is move { () ; } fn test (given self source1 : given Outer, source2 : given Outer, d1 : ref [source1] Outer, d2 : mut [source2] Outer, x : given_from [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self . give . require_move [given_from [d1 . inner . field, d2 . inner . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}
