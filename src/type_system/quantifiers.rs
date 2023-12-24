use std::fmt::Debug;

use formality_core::{ProvenSet, Upcast};

/// Proves judgment for each of the given items.
pub fn fold<V, T>(
    base: impl Upcast<V>,
    items: impl IntoIterator<Item = T>,
    judgment: &impl Fn(V, &T) -> ProvenSet<V>,
) -> ProvenSet<V>
where
    V: Clone + Ord,
{
    let base = base.upcast();
    let items: Vec<T> = items.into_iter().collect();
    return fold_slice(base, &items, judgment);
}

fn fold_slice<V, T>(base: V, items: &[T], judgment: &impl Fn(V, &T) -> ProvenSet<V>) -> ProvenSet<V>
where
    V: Clone + Ord,
{
    let Some((item0, items)) = items.split_first() else {
        return ProvenSet::singleton(base);
    };

    judgment(base, item0).flat_map(|v| fold_slice(v, items, judgment))
}

/// Proves judgment for each of the given items.
pub fn fold_zipped<V, T, U>(
    base: V,
    items1: impl IntoIterator<Item = T>,
    items2: impl IntoIterator<Item = U>,
    judgment: &impl Fn(V, &T, &U) -> ProvenSet<V>,
) -> ProvenSet<V>
where
    V: Clone + Ord,
    T: Debug,
    U: Debug,
{
    let items1: Vec<T> = items1.into_iter().collect();
    let items2: Vec<U> = items2.into_iter().collect();

    fold_slice_zipped(base, &items1, &items2, judgment)
}

fn fold_slice_zipped<V, T, U>(
    base: V,
    items1: &[T],
    items2: &[U],
    judgment: &impl Fn(V, &T, &U) -> ProvenSet<V>,
) -> ProvenSet<V>
where
    V: Clone + Ord,
    T: Debug,
    U: Debug,
{
    match (items1.split_first(), items2.split_first()) {
        (Some((head1, items1)), Some((head2, items2))) => judgment(base, head1, head2)
            .flat_map(|v| fold_slice_zipped(v, items1, items2, judgment)),

        (None, None) => ProvenSet::singleton(base),

        (Some((xtra, _)), None) => {
            panic!("fold_zipped iterator 1 has extra item: {xtra:?}")
        }

        (None, Some((xtra, _))) => {
            panic!("fold_zipped iterator 2 has extra item: {xtra:?}")
        }
    }
}
