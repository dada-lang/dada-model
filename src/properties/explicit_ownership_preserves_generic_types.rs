//! # Explicit ownership preserves a generic type
//!
//! `given` is the identity permission. Making it explicit on a generic input does
//! not require a relative bound on that type. This allows parameter migration
//! from the old owned default without adding constraints. A nonidentity shared
//! permission still requires the relative bound; the paired declarations test
//! that distinction through the surface pipeline.
//! Empty-origin shorthand `[] T` also states ownership explicitly and requires
//! no generated permission argument at a call.

#[test]
fn empty_origins_need_no_permission_argument() {
    crate::assert_interpret!({
        struct Main {
            fn identity(given self, value: [] Int) -> [] Int { value->; }
            fn main(given self) { print(self->.identity(22)); }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   print(_1_self -> . identity (22)) ;
        Output: Trace:   enter Main.identity
        Output: Trace:     _2_value -> ;
        Output: Trace:   exit Main.identity => 22
        Output: ----->   22
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

#[test]
fn explicit_ownership_needs_no_relative_bound() {
    crate::assert_ok!({
        struct Channel[ty T] {
            fn send(given self, value: given T) { (); }
        }
    });
}

#[test]
fn sharing_still_requires_a_relative_bound() {
    crate::assert_err!({
        struct Channel[ty T] {
            fn send(given self, value: shared T) { (); }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Channel [ty] { fn send (given self value : shared ^ty1_0) -> () { () ; } } }`"]);
}
