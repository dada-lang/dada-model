use std::fmt::Debug;

use formality_core::{Cons, ProvenSet, Set, Upcast};

/// Proves judgment for each of the given items.
pub fn for_all<T>(
    items: impl IntoIterator<Item = T>,
    judgment: &impl Fn(&T) -> ProvenSet<()>,
) -> ProvenSet<()> {
    fold((), items, &|(), item| judgment(item))
}

/// Proves judgment for each of the given items.
pub fn map<T, U>(
    items: impl IntoIterator<Item = T>,
    judgment: &impl Fn(&T) -> ProvenSet<U>,
) -> ProvenSet<Vec<U>>
where
    U: Clone + Ord + Debug + Upcast<U>,
{
    fold((), items, &|vec: Vec<U>, item| {
        judgment(item).map(|u| Cons(u, &vec).upcast())
    })
}

/// Variation on fold which unions together the results of
/// `judgment` applied to each of `items`.
pub fn union<V, T>(
    items: impl IntoIterator<Item = T>,
    judgment: &impl Fn(&T) -> ProvenSet<Set<V>>,
) -> ProvenSet<Set<V>>
where
    V: Clone + Ord + Debug + Upcast<V>,
{
    fold::<Set<V>, T>((), items, &|set, item| {
        judgment(item).map(|s| (&set, s).upcast())
    })
}

/// Proves judgment for each of the given items.
pub fn fold<V, T>(
    base: impl Upcast<V>,
    items: impl IntoIterator<Item = T>,
    judgment: &impl Fn(V, &T) -> ProvenSet<V>,
) -> ProvenSet<V>
where
    V: Clone + Ord + Debug,
{
    let base = base.upcast();
    let items: Vec<T> = items.into_iter().collect();
    return fold_slice(base, &items, judgment);
}

fn fold_slice<V, T>(base: V, items: &[T], judgment: &impl Fn(V, &T) -> ProvenSet<V>) -> ProvenSet<V>
where
    V: Clone + Ord + Debug,
{
    let Some((item0, items)) = items.split_first() else {
        return ProvenSet::singleton(base);
    };

    judgment(base, item0).flat_map(|v| fold_slice(v, items, judgment))
}

macro_rules! judge {
    (
        ($($input:pat),*) => ($output:expr) :-
        $($body:tt)*
    ) => {
        &|$($input,)*| {
            $crate::type_system::quantifiers::judge!(
                @body($($body)*) -> $output
            )
        }
    };

    (@body(
        ($e:expr => $p:pat)
        $($body:tt)*
    ) -> $output:expr) => {
        $e.flat_map(|$p| {
            $crate::type_system::quantifiers::judge!(
                @body($($body)*) -> $output
            )
        })
    };

    (@body(
        (let $p:pat = $e:expr)
        $($body:tt)*
    ) -> $output:expr) => {
        let $p = $e;
        $crate::type_system::quantifiers::judge!(
            @body($($body)*) -> $output
        )
    };

    (@body() -> $output:expr) => {
        formality_core::ProvenSet::singleton($output)
    }
}
pub(crate) use judge;
