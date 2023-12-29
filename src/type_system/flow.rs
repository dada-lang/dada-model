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

    /// Marks a place as moved.
    ///
    /// Asserts that  `place` is not already considered moved,
    /// as a move of an already moved place
    /// should be a type error.
    pub fn move_place(&self, place: &Place) -> Flow {
        assert!(!self.is_moved(place));
        Flow {
            moved_places: self.moved_places.clone().plus(place.clone()),
        }
    }

    /// Marks a place as assigned.
    pub fn assign_place(&self, place: &Place) -> Flow {
        let mut moved_places = self.moved_places.clone();
        moved_places.retain(|moved_place| !place.is_prefix_of(moved_place));
        Flow { moved_places }
    }
}
