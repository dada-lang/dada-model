use formality_core::{Set, SetExt, Upcast};

use crate::grammar::Place;

#[derive(Clone, Default, Debug, Ord, Eq, PartialEq, PartialOrd, Hash)]
pub struct Flow {
    moved_places: Set<Place>,
}

formality_core::cast_impl!(Flow);

impl Flow {
    /// Combines two flows into a single flow.
    pub fn merge(&self, flow: impl Upcast<Flow>) -> Flow {
        let flow = flow.upcast();
        Flow {
            moved_places: self.moved_places.clone().union_with(flow.moved_places),
        }
    }

    pub fn is_moved(&self, place: &Place) -> bool {
        self.moved_places
            .iter()
            .any(|moved_place| place.is_prefix_of(moved_place) || moved_place.is_prefix_of(place))
    }
}
