use std::fmt::Debug;

use formality_core::{set, Set, UpcastFrom};

/// Convenient for writing tests: sequence multiple judgments.
#[cfg(test)]
pub fn seq<R1, R2>(s: Set<R1>, c: impl Fn(R1) -> Set<R2>) -> Set<R2>
where
    R1: Ord,
    R2: Ord,
{
    s.into_iter().flat_map(|e| c(e)).collect()
}

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
    judgment: &impl Fn(V, &T) -> Set<V>,
) -> Set<V>
where
    V: Clone + Ord,
{
    let items: Vec<T> = items.into_iter().collect();
    return fold_slice(base, &items, judgment);
}

fn fold_slice<V, T>(base: V, items: &[T], judgment: &impl Fn(V, &T) -> Set<V>) -> Set<V>
where
    V: Clone + Ord,
{
    let Some((item0, items)) = items.split_first() else {
        return set![base];
    };

    judgment(base, item0)
        .into_iter()
        .flat_map(|v| fold_slice(v, items, judgment))
        .collect()
}

/// Proves judgment for each of the given items.
pub fn fold_zipped<V, T, U>(
    base: V,
    items1: impl IntoIterator<Item = T>,
    items2: impl IntoIterator<Item = U>,
    judgment: &impl Fn(V, &T, &U) -> Set<V>,
) -> Set<V>
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
    judgment: &impl Fn(V, &T, &U) -> Set<V>,
) -> Set<V>
where
    V: Clone + Ord,
    T: Debug,
    U: Debug,
{
    match (items1.split_first(), items2.split_first()) {
        (Some((head1, items1)), Some((head2, items2))) => judgment(base, head1, head2)
            .into_iter()
            .flat_map(|v| fold_slice_zipped(v, items1, items2, judgment))
            .collect(),

        (None, None) => set![base],

        (Some((xtra, _)), None) => {
            panic!("fold_zipped iterator 1 has extra item: {xtra:?}")
        }

        (None, Some((xtra, _))) => {
            panic!("fold_zipped iterator 2 has extra item: {xtra:?}")
        }
    }
}
