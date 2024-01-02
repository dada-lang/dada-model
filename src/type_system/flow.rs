use formality_core::{Set, SetExt, Upcast};

use crate::grammar::{Place, Var};

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

    pub fn is_moved(&self, place: impl Upcast<Place>) -> bool {
        let place = place.upcast();
        self.moved_places
            .iter()
            .any(|moved_place| place.is_prefix_of(moved_place) || moved_place.is_prefix_of(&place))
    }

    /// True if the given variable is fully uninitialized.
    /// May return false if (e.g.) there is a move from some field of `var` but other parts of `var` remain initialized.
    pub fn variable_uninitialized(&self, var: &Var) -> bool {
        let place: Place = var.upcast();
        self.moved_places.contains(&place)
    }

    /// Marks a place as moved.
    ///
    /// Asserts that  `place` is not already considered moved,
    /// as a move of an already moved place
    /// should be a type error.
    pub fn uninitialize_var(&self, var: &Var) -> Flow {
        assert!(!self.variable_uninitialized(var));
        let mut moved_places = self.moved_places.clone();
        moved_places.retain(|p| p.var != *var);
        moved_places.insert(var.upcast());
        Flow { moved_places }
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
