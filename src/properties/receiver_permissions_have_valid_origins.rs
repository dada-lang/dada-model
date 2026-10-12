//! # Receiver permissions have valid origins
//!
//! Receiver permissions obey the same origin well-formedness rules as input
//! permissions. They may name later inputs, but cannot name missing variables.
//! Checking a receiver permission does not add a variance requirement to its
//! enclosing class type. A boundary test also rejects noncanonical empty origins
//! constructed by mutating a valid surface-lowered program.

use std::sync::Arc;

use crate::{
    grammar::{Decl, Perm},
    surface, type_system,
};

#[test]
fn receiver_permission_origins_include_later_inputs() {
    // Trusted declarations exercise signature well-formedness without a
    // body. T deliberately has no relative bound: validating the receiver
    // permission must not add a variance requirement to Holder[T].
    crate::assert_ok!(
        r#"
        class Holder[type T] {
            fn inspect(![source] self, source: given Int) ...;
        }
    "#
    );
}

#[test]
fn malformed_empty_receiver_origins_are_rejected() {
    let source = surface::parse_program(
        "class Holder[type T] { fn inspect(![source] self, source: given Int) ...; }",
    )
    .unwrap();
    assert!(type_system::check_program(&source).is_proven());

    // These malformed representations cannot be written in the surface
    // grammar. Start from a valid lowered program and corrupt only its
    // receiver, so the checker also defends its programmatic boundary.
    for permission in [
        Perm::Mt(Default::default()),
        Perm::Mv(Default::default()),
        Perm::SharedFrom(Default::default()),
    ] {
        let mut malformed = (*source).clone();
        let Decl::ClassDecl(class) = &mut malformed.decls[0];
        class.binder = class.binder.map(|mut data| {
            data.methods[0].binder = data.methods[0].binder.map(|mut method| {
                method.this.perm = permission.clone();
                method
            });
            data
        });
        assert!(
            !type_system::check_program(Arc::new(malformed)).is_proven(),
            "accepted malformed receiver permission {permission:?}"
        );
    }
}

#[test]
fn receiver_permission_rejects_unknown_origins() {
    crate::assert_err!(
        r#"
        class Holder[type T] {
            fn inspect(![missing] self, source: given Int) ...;
        }
    "#,
        expect_test::expect![[r#"
        the rule "check_place" at (types.rs) failed because
          no variable named `missing`"#]]
    );
}
