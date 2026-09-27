use formality_core::test;

#[test]
fn given_and_given_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[given], d2: given Container[given],
                    x: given_from[d1.field, d2.field] Wrapper) {
                self.give.require_mut[given_from[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[given], d2 : given Container[given], x : given_from [d1 . field, d2 . field] Wrapper) -> () { self . give . require_mut [given_from [d1 . field, d2 . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn given_and_mut_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[given], d2: given Container[mut[source2]],
                    x: given_from[d1.field, d2.field] Wrapper) {
                self.give.require_mut[given_from[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[given], d2 : given Container[mut [source2]], x : given_from [d1 . field, d2 . field] Wrapper) -> () { self . give . require_mut [given_from [d1 . field, d2 . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn given_and_shared_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[given], d2: given Container[shared],
                    x: given_from[d1.field, d2.field] Wrapper) {
                self.give.require_mut[given_from[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[given], d2 : given Container[shared], x : given_from [d1 . field, d2 . field] Wrapper) -> () { self . give . require_mut [given_from [d1 . field, d2 . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn given_and_ref_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[given], d2: given Container[ref[source2]],
                    x: given_from[d1.field, d2.field] Wrapper) {
                self.give.require_mut[given_from[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[given], d2 : given Container[ref [source2]], x : given_from [d1 . field, d2 . field] Wrapper) -> () { self . give . require_mut [given_from [d1 . field, d2 . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn mut_and_given_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[mut[source1]], d2: given Container[given],
                    x: given_from[d1.field, d2.field] Wrapper) {
                self.give.require_mut[given_from[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[mut [source1]], d2 : given Container[given], x : given_from [d1 . field, d2 . field] Wrapper) -> () { self . give . require_mut [given_from [d1 . field, d2 . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn mut_and_mut_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[mut[source1]], d2: given Container[mut[source2]],
                    x: given_from[d1.field, d2.field] Wrapper) {
                self.give.require_mut[given_from[d1.field, d2.field]](x.give);
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
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[mut[source1]], d2: given Container[shared],
                    x: given_from[d1.field, d2.field] Wrapper) {
                self.give.require_mut[given_from[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[mut [source1]], d2 : given Container[shared], x : given_from [d1 . field, d2 . field] Wrapper) -> () { self . give . require_mut [given_from [d1 . field, d2 . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn mut_and_ref_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[mut[source1]], d2: given Container[ref[source2]],
                    x: given_from[d1.field, d2.field] Wrapper) {
                self.give.require_mut[given_from[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[mut [source1]], d2 : given Container[ref [source2]], x : given_from [d1 . field, d2 . field] Wrapper) -> () { self . give . require_mut [given_from [d1 . field, d2 . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn shared_and_given_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[shared], d2: given Container[given],
                    x: given_from[d1.field, d2.field] Wrapper) {
                self.give.require_mut[given_from[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[shared], d2 : given Container[given], x : given_from [d1 . field, d2 . field] Wrapper) -> () { self . give . require_mut [given_from [d1 . field, d2 . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn shared_and_mut_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[shared], d2: given Container[mut[source2]],
                    x: given_from[d1.field, d2.field] Wrapper) {
                self.give.require_mut[given_from[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[shared], d2 : given Container[mut [source2]], x : given_from [d1 . field, d2 . field] Wrapper) -> () { self . give . require_mut [given_from [d1 . field, d2 . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn shared_and_shared_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[shared], d2: given Container[shared],
                    x: given_from[d1.field, d2.field] Wrapper) {
                self.give.require_mut[given_from[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[shared], d2 : given Container[shared], x : given_from [d1 . field, d2 . field] Wrapper) -> () { self . give . require_mut [given_from [d1 . field, d2 . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn shared_and_ref_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[shared], d2: given Container[ref[source2]],
                    x: given_from[d1.field, d2.field] Wrapper) {
                self.give.require_mut[given_from[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[shared], d2 : given Container[ref [source2]], x : given_from [d1 . field, d2 . field] Wrapper) -> () { self . give . require_mut [given_from [d1 . field, d2 . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn ref_and_given_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[ref[source1]], d2: given Container[given],
                    x: given_from[d1.field, d2.field] Wrapper) {
                self.give.require_mut[given_from[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[ref [source1]], d2 : given Container[given], x : given_from [d1 . field, d2 . field] Wrapper) -> () { self . give . require_mut [given_from [d1 . field, d2 . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn ref_and_mut_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[ref[source1]], d2: given Container[mut[source2]],
                    x: given_from[d1.field, d2.field] Wrapper) {
                self.give.require_mut[given_from[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[ref [source1]], d2 : given Container[mut [source2]], x : given_from [d1 . field, d2 . field] Wrapper) -> () { self . give . require_mut [given_from [d1 . field, d2 . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn ref_and_shared_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[ref[source1]], d2: given Container[shared],
                    x: given_from[d1.field, d2.field] Wrapper) {
                self.give.require_mut[given_from[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[ref [source1]], d2 : given Container[shared], x : given_from [d1 . field, d2 . field] Wrapper) -> () { self . give . require_mut [given_from [d1 . field, d2 . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn ref_and_ref_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](given self, value: P Wrapper)
            where P is mut { (); }

            fn test(given self,
                    source1: given Wrapper, source2: given Wrapper,
                    d1: given Container[ref[source1]], d2: given Container[ref[source2]],
                    x: given_from[d1.field, d2.field] Wrapper) {
                self.give.require_mut[given_from[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (given self source1 : given Wrapper, source2 : given Wrapper, d1 : given Container[ref [source1]], d2 : given Container[ref [source2]], x : given_from [d1 . field, d2 . field] Wrapper) -> () { self . give . require_mut [given_from [d1 . field, d2 . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}
