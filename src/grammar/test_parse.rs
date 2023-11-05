use super::{Perm, Place, Ty};
use formality_core::test;

#[test]
fn test_parse_place() {
    let p: Place = crate::dada_lang::term("a.b.c");
    expect_test::expect![[r#"
        a . b . c
    "#]]
    .assert_debug_eq(&p);
}

#[test]
fn test_parse_shared_perm() {
    let p: Perm = crate::dada_lang::term("shared(a.b.c)");
    expect_test::expect![[r#"
        shared (a . b . c)
    "#]]
    .assert_debug_eq(&p);
}

#[test]
fn test_parse_our_perm_without_parens() {
    let p: Perm = crate::dada_lang::term("shared");
    expect_test::expect![[r#"
        shared
    "#]]
    .assert_debug_eq(&p);
}

#[test]
fn test_parse_our_perm_with_parens() {
    let p: Perm = crate::dada_lang::term("shared()");
    expect_test::expect![[r#"
        shared
    "#]]
    .assert_debug_eq(&p);
}

#[test]
fn test_parse_shared_perm_2() {
    let p: Perm = crate::dada_lang::term("shared(a,b)");
    expect_test::expect![[r#"
        shared (a, b)
    "#]]
    .assert_debug_eq(&p);
}

#[test]
fn test_parse_my_perm() {
    let p: Perm = crate::dada_lang::term("my");
    expect_test::expect![[r#"
        my
    "#]]
    .assert_debug_eq(&p);
}

#[test]
#[allow(non_snake_case)]
fn test_parse_String_ty() {
    let p: Ty = crate::dada_lang::term("shared String");
    expect_test::expect![[r#"
        shared String
    "#]]
    .assert_debug_eq(&p);
}

#[test]
#[allow(non_snake_case)]
fn test_parse_Vec_ty() {
    let p: Ty = crate::dada_lang::term("shared Vec[my U32]");
    expect_test::expect![[r#"
        shared Vec [my U32]
    "#]]
    .assert_debug_eq(&p);
}
