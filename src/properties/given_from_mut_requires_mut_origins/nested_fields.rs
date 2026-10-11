use formality_core::test;

#[test]
fn given_and_given_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Inner { field: Wrapper; }
        class Outer { inner: Inner; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Outer, source2: ^ Outer,
                    d1: ^ Outer, d2: ^ Outer,
                    x: ^[d1.inner.field, d2.inner.field] Wrapper) {
                self.give.require_mut[^[d1.inner.field, d2.inner.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Inner { field : Wrapper ; } class Outer { inner : Inner ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Outer, source2 : ^ Outer, d1 : ^ Outer, d2 : ^ Outer, x : ^ [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self . give . require_mut [^ [d1 . inner . field, d2 . inner . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn given_and_mut_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Inner { field: Wrapper; }
        class Outer { inner: Inner; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Outer, source2: ^ Outer,
                    d1: ^ Outer, d2: ![source2] Outer,
                    x: ^[d1.inner.field, d2.inner.field] Wrapper) {
                self.give.require_mut[^[d1.inner.field, d2.inner.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Inner { field : Wrapper ; } class Outer { inner : Inner ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Outer, source2 : ^ Outer, d1 : ^ Outer, d2 : ! [source2] Outer, x : ^ [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self . give . require_mut [^ [d1 . inner . field, d2 . inner . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn given_and_shared_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Inner { field: Wrapper; }
        class Outer { inner: Inner; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Outer, source2: ^ Outer,
                    d1: ^ Outer, d2: shared Outer,
                    x: ^[d1.inner.field, d2.inner.field] Wrapper) {
                self.give.require_mut[^[d1.inner.field, d2.inner.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Inner { field : Wrapper ; } class Outer { inner : Inner ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Outer, source2 : ^ Outer, d1 : ^ Outer, d2 : shared Outer, x : ^ [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self . give . require_mut [^ [d1 . inner . field, d2 . inner . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn given_and_ref_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Inner { field: Wrapper; }
        class Outer { inner: Inner; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Outer, source2: ^ Outer,
                    d1: ^ Outer, d2: shared[source2] Outer,
                    x: ^[d1.inner.field, d2.inner.field] Wrapper) {
                self.give.require_mut[^[d1.inner.field, d2.inner.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Inner { field : Wrapper ; } class Outer { inner : Inner ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Outer, source2 : ^ Outer, d1 : ^ Outer, d2 : shared [source2] Outer, x : ^ [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self . give . require_mut [^ [d1 . inner . field, d2 . inner . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn mut_and_given_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Inner { field: Wrapper; }
        class Outer { inner: Inner; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Outer, source2: ^ Outer,
                    d1: ![source1] Outer, d2: ^ Outer,
                    x: ^[d1.inner.field, d2.inner.field] Wrapper) {
                self.give.require_mut[^[d1.inner.field, d2.inner.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Inner { field : Wrapper ; } class Outer { inner : Inner ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Outer, source2 : ^ Outer, d1 : ! [source1] Outer, d2 : ^ Outer, x : ^ [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self . give . require_mut [^ [d1 . inner . field, d2 . inner . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn mut_and_mut_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Inner { field: Wrapper; }
        class Outer { inner: Inner; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Outer, source2: ^ Outer,
                    d1: ![source1] Outer, d2: ![source2] Outer,
                    x: ^[d1.inner.field, d2.inner.field] Wrapper) {
                self.give.require_mut[^[d1.inner.field, d2.inner.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn mut_and_shared_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Inner { field: Wrapper; }
        class Outer { inner: Inner; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Outer, source2: ^ Outer,
                    d1: ![source1] Outer, d2: shared Outer,
                    x: ^[d1.inner.field, d2.inner.field] Wrapper) {
                self.give.require_mut[^[d1.inner.field, d2.inner.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Inner { field : Wrapper ; } class Outer { inner : Inner ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Outer, source2 : ^ Outer, d1 : ! [source1] Outer, d2 : shared Outer, x : ^ [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self . give . require_mut [^ [d1 . inner . field, d2 . inner . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn mut_and_ref_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Inner { field: Wrapper; }
        class Outer { inner: Inner; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Outer, source2: ^ Outer,
                    d1: ![source1] Outer, d2: shared[source2] Outer,
                    x: ^[d1.inner.field, d2.inner.field] Wrapper) {
                self.give.require_mut[^[d1.inner.field, d2.inner.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Inner { field : Wrapper ; } class Outer { inner : Inner ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Outer, source2 : ^ Outer, d1 : ! [source1] Outer, d2 : shared [source2] Outer, x : ^ [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self . give . require_mut [^ [d1 . inner . field, d2 . inner . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn shared_and_given_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Inner { field: Wrapper; }
        class Outer { inner: Inner; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Outer, source2: ^ Outer,
                    d1: shared Outer, d2: ^ Outer,
                    x: ^[d1.inner.field, d2.inner.field] Wrapper) {
                self.give.require_mut[^[d1.inner.field, d2.inner.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Inner { field : Wrapper ; } class Outer { inner : Inner ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Outer, source2 : ^ Outer, d1 : shared Outer, d2 : ^ Outer, x : ^ [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self . give . require_mut [^ [d1 . inner . field, d2 . inner . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn shared_and_mut_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Inner { field: Wrapper; }
        class Outer { inner: Inner; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Outer, source2: ^ Outer,
                    d1: shared Outer, d2: ![source2] Outer,
                    x: ^[d1.inner.field, d2.inner.field] Wrapper) {
                self.give.require_mut[^[d1.inner.field, d2.inner.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Inner { field : Wrapper ; } class Outer { inner : Inner ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Outer, source2 : ^ Outer, d1 : shared Outer, d2 : ! [source2] Outer, x : ^ [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self . give . require_mut [^ [d1 . inner . field, d2 . inner . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn shared_and_shared_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Inner { field: Wrapper; }
        class Outer { inner: Inner; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Outer, source2: ^ Outer,
                    d1: shared Outer, d2: shared Outer,
                    x: ^[d1.inner.field, d2.inner.field] Wrapper) {
                self.give.require_mut[^[d1.inner.field, d2.inner.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Inner { field : Wrapper ; } class Outer { inner : Inner ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Outer, source2 : ^ Outer, d1 : shared Outer, d2 : shared Outer, x : ^ [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self . give . require_mut [^ [d1 . inner . field, d2 . inner . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn shared_and_ref_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Inner { field: Wrapper; }
        class Outer { inner: Inner; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Outer, source2: ^ Outer,
                    d1: shared Outer, d2: shared[source2] Outer,
                    x: ^[d1.inner.field, d2.inner.field] Wrapper) {
                self.give.require_mut[^[d1.inner.field, d2.inner.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Inner { field : Wrapper ; } class Outer { inner : Inner ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Outer, source2 : ^ Outer, d1 : shared Outer, d2 : shared [source2] Outer, x : ^ [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self . give . require_mut [^ [d1 . inner . field, d2 . inner . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn ref_and_given_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Inner { field: Wrapper; }
        class Outer { inner: Inner; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Outer, source2: ^ Outer,
                    d1: shared[source1] Outer, d2: ^ Outer,
                    x: ^[d1.inner.field, d2.inner.field] Wrapper) {
                self.give.require_mut[^[d1.inner.field, d2.inner.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Inner { field : Wrapper ; } class Outer { inner : Inner ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Outer, source2 : ^ Outer, d1 : shared [source1] Outer, d2 : ^ Outer, x : ^ [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self . give . require_mut [^ [d1 . inner . field, d2 . inner . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn ref_and_mut_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Inner { field: Wrapper; }
        class Outer { inner: Inner; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Outer, source2: ^ Outer,
                    d1: shared[source1] Outer, d2: ![source2] Outer,
                    x: ^[d1.inner.field, d2.inner.field] Wrapper) {
                self.give.require_mut[^[d1.inner.field, d2.inner.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Inner { field : Wrapper ; } class Outer { inner : Inner ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Outer, source2 : ^ Outer, d1 : shared [source1] Outer, d2 : ! [source2] Outer, x : ^ [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self . give . require_mut [^ [d1 . inner . field, d2 . inner . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn ref_and_shared_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Inner { field: Wrapper; }
        class Outer { inner: Inner; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Outer, source2: ^ Outer,
                    d1: shared[source1] Outer, d2: shared Outer,
                    x: ^[d1.inner.field, d2.inner.field] Wrapper) {
                self.give.require_mut[^[d1.inner.field, d2.inner.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Inner { field : Wrapper ; } class Outer { inner : Inner ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Outer, source2 : ^ Outer, d1 : shared [source1] Outer, d2 : shared Outer, x : ^ [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self . give . require_mut [^ [d1 . inner . field, d2 . inner . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn ref_and_ref_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Inner { field: Wrapper; }
        class Outer { inner: Inner; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Outer, source2: ^ Outer,
                    d1: shared[source1] Outer, d2: shared[source2] Outer,
                    x: ^[d1.inner.field, d2.inner.field] Wrapper) {
                self.give.require_mut[^[d1.inner.field, d2.inner.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Inner { field : Wrapper ; } class Outer { inner : Inner ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Outer, source2 : ^ Outer, d1 : shared [source1] Outer, d2 : shared [source2] Outer, x : ^ [d1 . inner . field, d2 . inner . field] Wrapper) -> () { self . give . require_mut [^ [d1 . inner . field, d2 . inner . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}
