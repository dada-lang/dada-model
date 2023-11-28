use std::fmt::Debug;

use formality_core::{set, Set, Upcast, UpcastFrom};

/// Proves `judgment` for all items in `items`, yielding a vector of results.
pub fn for_all<T, R>(
    items: impl IntoIterator<Item = T>,
    judgment: impl Fn(T) -> Set<R>,
) -> Set<Vec<R>>
where
    R: Clone + Ord,
    T: Clone + UpcastFrom<T>,
{
    let mut items = items.into_iter();

    let Some(item) = items.next() else {
        return set![vec![]];
    };

    let r_elem = judgment(item);
    for_all(items, judgment)
        .iter()
        .flat_map(|v| {
            r_elem.iter().map(|r_elem| {
                v.iter()
                    .chain(std::iter::once(r_elem))
                    .cloned()
                    .collect::<Vec<R>>()
            })
        })
        .collect()
}

/// Proves judgment for each of the given items.
pub fn fold<V, T>(
    base: V,
    items: impl IntoIterator<Item = T>,
    judgment: &impl Fn(V, T) -> Set<V>,
) -> Set<V>
where
    V: Clone + Ord,
{
    let mut items = items.into_iter();
    let Some(item0) = items.next() else {
        return set![base];
    };

    judgment(base, item0)
        .into_iter()
        .flat_map(|v| fold(v, items, judgment))
        .collect()
}

/// Proves judgment for each of the given items.
pub fn fold_zipped<V, T, U>(
    base: V,
    items1: impl IntoIterator<Item = T>,
    items2: impl IntoIterator<Item = U>,
    judgment: &impl Fn(V, T, U) -> Set<V>,
) -> Set<V>
where
    V: Clone + Ord,
    T: Debug,
    U: Debug,
{
    let mut items1 = items1.into_iter();
    let mut items2 = items2.into_iter();

    match (items1.next(), items2.next()) {
        (Some(head1), Some(head2)) => judgment(base, head1, head2)
            .into_iter()
            .flat_map(|v| fold_zipped(v, items1, items2, judgment))
            .collect(),

        (None, None) => set![base],

        (Some(xtra), None) => {
            panic!("fold_zipped iterator 1 has extra item: {xtra:?}")
        }

        (None, Some(xtra)) => {
            panic!("fold_zipped iterator 2 has extra item: {xtra:?}")
        }
    }
}
