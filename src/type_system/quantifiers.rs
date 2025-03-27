use std::fmt::Debug;

use formality_core::{set, ProvenSet, Set, Upcast};

/// Proves judgment for each of the given items.
pub fn collect<T: Ord + Debug>(judgment: ProvenSet<T>) -> ProvenSet<Set<T>> {
    match judgment.into_set() {
        Ok(s) => ProvenSet::proven(set![s]),
        Err(e) => ProvenSet::from(*e),
    }
}

/// Proves judgment for each of the given items.
pub fn for_all<T>(
    items: impl IntoIterator<Item = T>,
    judgment: &impl Fn(&T) -> ProvenSet<()>,
) -> ProvenSet<()> {
    fold((), items, &|(), item| judgment(item))
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
