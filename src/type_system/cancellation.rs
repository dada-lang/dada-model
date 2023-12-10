use formality_core::{judgment_fn, set, Set, SetExt, Upcast};

use crate::{
    grammar::{Kind, Perm, Place, Ty},
    type_system::{env::Env, type_places::type_place},
};

judgment_fn! {
    /// Implements *cancellation*, which adjusts permission paths by *canceling* the places
    /// that they named, which is like an implicit `give` that makes the place inaccessible
    /// and therefore takes all the permissions in that place and puts them into the returned type.
    /// This is most common when there is a single place named in the path.
    ///
    /// # How the process works
    ///
    /// ## Given
    ///
    /// The process is easiest to explain with `given`.
    /// We wish to transform a type like `given(p[0]..p[n]) T`
    /// such that some place `p[i]` in the list transfers
    /// all of its permissions to the result:
    ///
    /// 1. Find the type `U` of `p[i]`.
    /// 2. "Rebase" the permissions from `U` atop `T` to yield a type `R`.
    ///   * For example, if `T` is `String` and `U` is `leased(p) Vec<String>`,
    ///     'rebasing' would result in a `R` of `leased(p) String`.
    /// 3. If `n == 1`, result is `R`.
    /// 4. Otherwise, result is union of `R` with `given(p[0]..p[i-1],p[i+1]..p[n]) T`.
    ///
    /// ## Leased
    ///
    /// Leasing is similar to `given` but
    /// cancellation is only possible
    /// if the place to be canceled `p[i]`
    /// has a type `U` that is leased.
    ///
    /// *Why not an owned value?* A `leased(p)` value
    /// is a pointer to the original value.
    /// If the leased value is actually owned by `p`,
    /// then  when `p` is dropped, the leased value
    /// will be freed and the pointer would be invalid.
    ///
    /// *Why not a shared value?* You can never have
    /// a `leased(p)` value derivd from a shared value.
    /// The result is simplifiable to just the shared
    /// value.
    ///
    /// ## Shared
    ///
    /// Shared is similar to `leased` in that
    /// cancellation is only possible
    /// if the place to be canceled `p[i]`
    /// has a type `U` that is leased,
    /// but with `shared` the resulting
    /// permission is transformed to `shared leased(...)`.
    /// This is a 4th permission we don't talk much about.
    /// It means that there is a unique lease on `...`
    /// but that lease has been shared.
    ///
    /// *Why not an owned value?* A `shared(p)` value is
    /// dependent on `p` to maintain the reference count.
    /// If `p` is canceled, the shared value would be invalid.
    /// **It would be possible to transform `p` to carry
    /// a reference count, and then accept this, but that would
    /// make cancellation not a *subtype* but a kind of coercion
    /// (since the value must change).** We might consider that.
    /// An alternative would be to make shared values carry
    /// reference counts always. This is going to be a systemic
    /// cost that is at odds with our top design tenet of being
    /// "performant".
    ///
    /// *Why not a shared value?* Sharing a shared value
    /// is simplifiable to just the inner shared value anyway,
    /// so we don't need to apply cancellation.
    ///
    /// # Examples of where this gets used
    ///
    /// ## Leased from leased
    ///
    /// This program is allowed because of cancellation:
    ///
    /// ```text
    /// fn foo(p: leased String) -> leased(p) String {
    ///     let q = p.lease    // q: leased(p) String
    ///     let u = q.lease    // u: leased(q) String
    ///     u.give
    /// }
    /// ```
    ///
    /// The actual return type is `leased(q) String`,
    /// but the expected return type
    /// is `leased(p) String`. So why is the program
    /// accepted? Answer: `leased(q) String` can be adjusted
    /// by *cancellation*. This will examine the type of `q`
    /// and find `leased(p) String`. It will then add `q` to the cancel
    /// list and adjust the type from `leased(q) String` to `leased(p) String`.
    ///
    /// ## From given
    ///
    /// Consider this function:
    ///
    /// ```text
    /// fn take_one(p: leased Vec<T>) -> given(p) T {...}
    /// ```
    ///
    /// which desugars to:
    ///
    /// ```text
    /// fn take_one[perm P](
    ///     p: P Vec<T>,
    /// ) -> given(p) T
    /// where
    ///     leased(P),
    /// {
    ///     ...
    /// }
    /// ```
    ///
    /// A call to this function like `take_one(some_vec.lease)`
    /// will be typed by first putting the argument (`some_vec`)
    /// into a temporary:
    ///
    /// ```text
    /// arg0: leased(some_vec) Vec<String> = some_vec.lease
    /// ```
    ///
    /// The return type is then `given(arg0) String`. We then
    /// cancel `arg0`, which yields the type `leased(some_vec) String`.
    ///
    /// ## Shared from leased
    ///
    /// Consider this function:
    ///
    /// ```text
    /// fn take_one(p: leased Vec<T>) -> shared(p) T {...}
    /// ```
    ///
    /// which desugars to:
    ///
    /// ```text
    /// fn take_one[perm P](
    ///     p: P Vec<T>,
    /// ) -> shared(p) T
    /// where
    ///     leased(P),
    /// {
    ///     ...
    /// }
    /// ```
    ///
    /// A call to this function like `take_one(some_vec.lease)`
    /// will be typed by first putting the argument (`some_vec`)
    /// into a temporary:
    ///
    /// ```text
    /// arg0: leased(some_vec) Vec<String> = some_vec.lease
    /// ```
    ///
    /// The return type is then `shared(arg0) String`. We then
    /// cancel `arg0`, which yields the type `shared leased(some_vec) String`.
    ///
    /// This type will allow users to copy around the `String`
    /// but continue to disallow access to `some_vec`.
    /// **Note the subtle distinction between `shared leased(some_vec) String`
    /// and `shared(some_vec) String` -- the latter would allow
    /// reads from `some_vec` or other shares.**
    ///
    /// ## Shared from shared (not cancellation)
    ///
    /// Consider this function:
    ///
    /// ```text
    /// fn foo(s: our String) -> our String {
    ///     s.share                         // shared(s) String
    /// }
    /// ```
    ///
    /// where `our String` is syntactic sugar for `shared() String`.
    /// The type `shared(s) String` can be canceled to yield `our String`.
    /// In fact,
    /// because the type of `s` is owned.
    /// To make this type-check, the user must write `s.give.share`
    /// explicitly.
    ///
    /// ## Shared from owned (not cancellation)
    ///
    /// Consider this function:
    ///
    /// ```text
    /// fn foo() -> shared String {
    ///     let s: my String = "foo"
    ///     s.share                         // shared(s) String
    /// }
    /// ```
    ///
    /// The type `shared(s) String` cannot be canceled
    /// because the type of `s` is owned.
    /// To make this type-check, the user must write `s.give.share`
    /// explicitly.
    pub fn cancel(
        env: Env,
        a: Ty,
    ) => (Env, Ty, Set<Place>) {
        debug(a, env)

        // FIXME: cancelation

        // FIXME: Canceling `shared(..., x, ...)` looks up the type of `x` and yields
        // "shares" it -- ah, yes, we need `shared leased(x)` for this -- and then
        // "unions" that with other places from `shared` list (if any).

        // FIXME: Canceling `leased(..., x, ...)` looks up the type of `x` and, if it is
        // leased, you can cancel `x` and replace it with the inner lease.

        // FIXME: Canceling `given(..., x, ...)` looks up the type of `x` and, if it is
        // leased, you can cancel `x` and replace it with the inner lease.




        (
            (if let Perm::Given(places) = perm)
            (0..places.len() => i)
            (places.split_nth(i) => (place, other_places))
            (type_place(&env, &place) => place_ty)
            (let canceled_ty = place_ty.rebase_perms(&*ty))
            (let (env, result_ty) = union_with_given(&env, canceled_ty, &other_places, &*ty))
            ---------------------- ("(given() P) => P")
            (cancel(env, Ty::ApplyPerm(perm, ty)) => (env, result_ty, set![place.clone()]))
        )
    }
}

fn union_with_given(
    env: impl Upcast<Env>,
    canceled_ty: Ty,
    other_places: &Set<Place>,
    base_ty: &Ty,
) -> (Env, Ty) {
    let mut env = env.upcast();
    if other_places.is_empty() {
        return (env, canceled_ty);
    }

    // Create
    let other_ty = Ty::apply_perm(Perm::given(other_places), base_ty);
    let var: formality_core::variable::CoreExistentialVar<crate::dada_lang::FormalityLang> =
        env.push_next_existential_var(Kind::Ty);
    env.new_lower_bound(&canceled_ty, var).unwrap();
    if other_ty != canceled_ty {
        // unlikely that `other_ty == canceled_ty`, but technically *possible*
        env.new_lower_bound(other_ty, var).unwrap();
    }
    (env, Ty::Var(var.upcast()))
}
