use formality_core::{set, Set, Upcast, UpcastFrom};

/// Proves `judgment` for all items in `items`, yielding a vector of results.
pub fn for_all<T, R>(items: impl Upcast<Vec<T>>, judgment: impl Fn(T) -> Set<R>) -> Set<Vec<R>>
where
    R: Clone + Ord,
    T: Clone + UpcastFrom<T>,
{
    let mut items: Vec<T> = items.upcast();

    match items.pop() {
        None => set![vec![]],

        Some(elem) => {
            let r_elem = judgment(elem);
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
    }
}

/// Proves judgment for each of the given items.
pub fn fold<V, T>(base: V, items: &[T], judgment: &impl Fn(V, &T) -> Set<V>) -> Set<V>
where
    V: Clone + Ord,
    T: Clone,
{
    let Some((item0, items)) = items.split_first() else {
        return set![base];
    };

    judgment(base, item0)
        .into_iter()
        .flat_map(|v| fold(v, items, judgment))
        .collect()
}
