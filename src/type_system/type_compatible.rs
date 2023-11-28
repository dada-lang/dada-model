use formality_core::{judgment_fn, Cons, Downcast};

use crate::{
    dada_lang::grammar::{ExistentialVar, Variable},
    grammar::{ClassTy, Parameter, Perm, Place, Predicate, Ty},
    type_system::quantifiers::fold,
    type_system::{
        env::{Env, Existential, PermBound},
        quantifiers::fold_zipped,
    },
};

judgment_fn! {
    pub fn compatible(
        env: Env,
        a: Parameter,
        b: Parameter,
    ) => Env {
        debug(a, b, env)

        trivial(a == b => env)
    }
}
