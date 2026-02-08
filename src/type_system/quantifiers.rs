use std::fmt::Debug;

use formality_core::{judgment::ProofTree, ProvenSet, Set, Upcast};

/// Proves judgment for each of the given items.
pub fn for_all<T>(
    items: impl IntoIterator<Item = T>,
    judgment: &impl Fn(&T) -> ProvenSet<()>,
) -> ProvenSet<()> {
    fold((), items, &|(), item| judgment(item))
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
        judgment(item).map(|(s, tree)| {
            let merged: Set<V> = set.iter().chain(s.iter()).cloned().collect();
            (merged, tree)
        })
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
        return ProvenSet::singleton((base, ProofTree::leaf("fold_slice: base")));
    };

    judgment(base, item0).flat_map(|(v, tree)| {
        fold_slice(v, items, judgment).map(move |(v2, tree2)| {
            (v2, ProofTree::new("fold_slice", None, vec![tree.clone(), tree2]))
        })
    })
}

#[expect(unused_macros)] // could be useful
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
        formality_core::ProvenSet::singleton(($output, formality_core::judgment::ProofTree::leaf("judge! macro")))
    }
}
