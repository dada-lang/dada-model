//! ## Unique ownership requires both exclusivity and ownership
//!
//! `P is unique` includes mutable leases as well as unique owners, while
//! `P is owned` includes shared owners as well as unique owners. Requiring both
//! admits independent unique ownership and excludes either shared ownership or
//! mutable leasing alone. There is no separate `given` predicate.
//!
//! The accepted program forwards both assumptions through a generic method,
//! checks an ownership-only disjunction, and executes the returned result.
//! Rejected programs remove one assumption or pass a concrete shared owner or
//! mutable lease. These are examples supporting the conjunction, not a proof
//! that all permission combinations have been characterized.

#[test]
fn unique_owned_assumptions_support_forwarding_and_disjunctions() {
    crate::assert_interpret!({
        struct Data { value: Int; }
        struct Main {
            fn consume[perm P](given self, data: P Data) -> Int
            where P is unique, P is owned
            {
                data.value^;
            }
            fn forward[perm P](given self, data: P Data) -> Int
            where P is unique, P is owned
            {
                self^.consume[P](data^);
            }
            fn disjunction[perm P](given self, data: or(P, given) Data) -> Int
            where P is unique, P is owned { data.value^; }
            fn main(given self) -> Int {
                let result = self^.forward[given](new Data(22));
                let other = new Main().disjunction[given](new Data(33));
                result^ + other^;
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_result = _1_self ^ . forward [given] (new Data (22)) ;
        Output: Trace:   enter Main.forward
        Output: Trace:     _2_self ^ . consume [given] (_2_data ^) ;
        Output: Trace:     enter Main.consume
        Output: Trace:       _3_data . value ^ ;
        Output: Trace:     exit Main.consume => 22
        Output: Trace:   exit Main.forward => 22
        Output: Trace:   _1_result = 22
        Output: Trace:   let _1_other = new Main () . disjunction [given] (new Data (33)) ;
        Output: Trace:   enter Main.disjunction
        Output: Trace:     _4_data . value ^ ;
        Output: Trace:   exit Main.disjunction => 33
        Output: Trace:   _1_other = 33
        Output: Trace:   _1_result ^ + _1_other ^ ;
        Output: Trace: exit Main.main => 55
        Result: Ok: 55
        Alloc 0x13: [Int(55)]"#]]);
}

#[test]
fn shared_ownership_does_not_satisfy_unique_ownership() {
    crate::assert_err!({
        struct Data { value: Int; }
        struct Main {
            fn consume[perm P](given self, data: P Data) -> Int
            where P is unique, P is owned { data.value^; }
            fn main(given self) -> Int {
                let owner = new Data(22).share;
                self^.consume[shared](owner^);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { value : Int ; } struct Main { fn consume [perm] (given self data : ^perm0_0 Data) -> Int where ^perm0_0 is unique, ^perm0_0 is owned { data . value ^ ; } fn main (given self) -> Int { let owner = new Data (22) . share ; self ^ . consume [shared] (owner ^) ; } } }`"]);
}

#[test]
fn mutable_lease_does_not_satisfy_unique_ownership() {
    crate::assert_err!({
        struct Data { value: Int; }
        struct Main {
            fn require_owner[perm P](given self) -> Int
            where P is unique, P is owned { 22; }
            fn main(given self) -> Int {
                let data = new Data(22);
                self^.require_owner[![data]]();
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { value : Int ; } struct Main { fn require_owner [perm] (given self) -> Int where ^perm0_0 is unique, ^perm0_0 is owned { 22 ; } fn main (given self) -> Int { let data = new Data (22) ; self ^ . require_owner [! [data]] () ; } } }`"]);
}

#[test]
fn unique_assumption_alone_cannot_forward_unique_ownership() {
    crate::assert_err!({
        struct Data { value: Int; }
        struct Main {
            fn consume[perm P](given self, data: P Data) -> Int
            where P is unique, P is owned { data.value^; }
            fn forward[perm P](given self, data: P Data) -> Int
            where P is unique { self^.consume[P](data^); }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { value : Int ; } struct Main { fn consume [perm] (given self data : ^perm0_0 Data) -> Int where ^perm0_0 is unique, ^perm0_0 is owned { data . value ^ ; } fn forward [perm] (given self data : ^perm0_0 Data) -> Int where ^perm0_0 is unique { self ^ . consume [^perm0_0] (data ^) ; } } }`"]);
}

#[test]
fn owned_assumption_alone_cannot_forward_unique_ownership() {
    crate::assert_err!({
        struct Data { value: Int; }
        struct Main {
            fn consume[perm P](given self, data: P Data) -> Int
            where P is unique, P is owned { data.value^; }
            fn forward[perm P](given self, data: P Data) -> Int
            where P is owned { self^.consume[P](data^); }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { value : Int ; } struct Main { fn consume [perm] (given self data : ^perm0_0 Data) -> Int where ^perm0_0 is unique, ^perm0_0 is owned { data . value ^ ; } fn forward [perm] (given self data : ^perm0_0 Data) -> Int where ^perm0_0 is owned { self ^ . consume [^perm0_0] (data ^) ; } } }`"]);
}
