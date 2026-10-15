use formality_core::test;

#[test]
fn given_and_given_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[given], d2: given Container[given],
                    x: given[d1.field, d2.field] Wrapper) {
                self→.require_mut[given[d1.field, d2.field]](x→);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) → () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[given], d2 : given Container[given], x : given [d1 . field, d2 . field] Wrapper) → () { self → . require_mut [given [d1 . field, d2 . field]] (x →) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn given_and_mut_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[given], d2: given Container[![source2]],
                    x: given[d1.field, d2.field] Wrapper) {
                self→.require_mut[given[d1.field, d2.field]](x→);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) → () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[given], d2 : given Container[! [source2]], x : given [d1 . field, d2 . field] Wrapper) → () { self → . require_mut [given [d1 . field, d2 . field]] (x →) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn given_and_shared_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[given], d2: given Container[shared],
                    x: given[d1.field, d2.field] Wrapper) {
                self→.require_mut[given[d1.field, d2.field]](x→);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) → () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[given], d2 : given Container[shared], x : given [d1 . field, d2 . field] Wrapper) → () { self → . require_mut [given [d1 . field, d2 . field]] (x →) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn given_and_ref_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[given], d2: given Container[shared[source2]],
                    x: given[d1.field, d2.field] Wrapper) {
                self→.require_mut[given[d1.field, d2.field]](x→);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) → () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[given], d2 : given Container[shared [source2]], x : given [d1 . field, d2 . field] Wrapper) → () { self → . require_mut [given [d1 . field, d2 . field]] (x →) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn mut_and_given_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[![source1]], d2: given Container[given],
                    x: given[d1.field, d2.field] Wrapper) {
                self→.require_mut[given[d1.field, d2.field]](x→);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) → () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[! [source1]], d2 : given Container[given], x : given [d1 . field, d2 . field] Wrapper) → () { self → . require_mut [given [d1 . field, d2 . field]] (x →) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn mut_and_mut_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[![source1]], d2: given Container[![source2]],
                    x: given[d1.field, d2.field] Wrapper) {
                self→.require_mut[given[d1.field, d2.field]](x→);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn mut_and_shared_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[![source1]], d2: given Container[shared],
                    x: given[d1.field, d2.field] Wrapper) {
                self→.require_mut[given[d1.field, d2.field]](x→);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) → () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[! [source1]], d2 : given Container[shared], x : given [d1 . field, d2 . field] Wrapper) → () { self → . require_mut [given [d1 . field, d2 . field]] (x →) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn mut_and_ref_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[![source1]], d2: given Container[shared[source2]],
                    x: given[d1.field, d2.field] Wrapper) {
                self→.require_mut[given[d1.field, d2.field]](x→);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) → () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[! [source1]], d2 : given Container[shared [source2]], x : given [d1 . field, d2 . field] Wrapper) → () { self → . require_mut [given [d1 . field, d2 . field]] (x →) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn shared_and_given_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[shared], d2: given Container[given],
                    x: given[d1.field, d2.field] Wrapper) {
                self→.require_mut[given[d1.field, d2.field]](x→);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) → () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[shared], d2 : given Container[given], x : given [d1 . field, d2 . field] Wrapper) → () { self → . require_mut [given [d1 . field, d2 . field]] (x →) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn shared_and_mut_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[shared], d2: given Container[![source2]],
                    x: given[d1.field, d2.field] Wrapper) {
                self→.require_mut[given[d1.field, d2.field]](x→);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) → () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[shared], d2 : given Container[! [source2]], x : given [d1 . field, d2 . field] Wrapper) → () { self → . require_mut [given [d1 . field, d2 . field]] (x →) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn shared_and_shared_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[shared], d2: given Container[shared],
                    x: given[d1.field, d2.field] Wrapper) {
                self→.require_mut[given[d1.field, d2.field]](x→);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) → () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[shared], d2 : given Container[shared], x : given [d1 . field, d2 . field] Wrapper) → () { self → . require_mut [given [d1 . field, d2 . field]] (x →) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn shared_and_ref_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[shared], d2: given Container[shared[source2]],
                    x: given[d1.field, d2.field] Wrapper) {
                self→.require_mut[given[d1.field, d2.field]](x→);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) → () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[shared], d2 : given Container[shared [source2]], x : given [d1 . field, d2 . field] Wrapper) → () { self → . require_mut [given [d1 . field, d2 . field]] (x →) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn ref_and_given_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[shared[source1]], d2: given Container[given],
                    x: given[d1.field, d2.field] Wrapper) {
                self→.require_mut[given[d1.field, d2.field]](x→);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) → () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[shared [source1]], d2 : given Container[given], x : given [d1 . field, d2 . field] Wrapper) → () { self → . require_mut [given [d1 . field, d2 . field]] (x →) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn ref_and_mut_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[shared[source1]], d2: given Container[![source2]],
                    x: given[d1.field, d2.field] Wrapper) {
                self→.require_mut[given[d1.field, d2.field]](x→);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) → () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[shared [source1]], d2 : given Container[! [source2]], x : given [d1 . field, d2 . field] Wrapper) → () { self → . require_mut [given [d1 . field, d2 . field]] (x →) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn ref_and_shared_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[shared[source1]], d2: given Container[shared],
                    x: given[d1.field, d2.field] Wrapper) {
                self→.require_mut[given[d1.field, d2.field]](x→);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) → () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[shared [source1]], d2 : given Container[shared], x : given [d1 . field, d2 . field] Wrapper) → () { self → . require_mut [given [d1 . field, d2 . field]] (x →) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn ref_and_ref_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[shared[source1]], d2: given Container[shared[source2]],
                    x: given[d1.field, d2.field] Wrapper) {
                self→.require_mut[given[d1.field, d2.field]](x→);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) → () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[shared [source1]], d2 : given Container[shared [source2]], x : given [d1 . field, d2 . field] Wrapper) → () { self → . require_mut [given [d1 . field, d2 . field]] (x →) ; source1 . share ; source2 . share ; () ; } } }`"]);
}
