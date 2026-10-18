import PlaceOperations

namespace Dada.Heap

-- These examples check resource effects on already selected places, including
-- complete successor states. They are not complete authorized machine executions:
-- access-path permissions and invalidation still belong to the unfinished layer
-- above PlaceEffect.

-- ANCHOR: give_with_shared_lease
example :
    let x : VariableId := ⟨0⟩
    let y : VariableId := ⟨1⟩
    let z : VariableId := ⟨2⟩
    let α : ObjectId := ⟨0⟩
    let objects : FiniteMap ObjectId (Object Int) :=
      ⟨[(α, .primitive 22)], by simp⟩
    let before : State Int := .state objects
      ⟨[(z, .initialized (.shlease α)), (y, .uninitialized),
        (x, .initialized (.owned α))], by decide⟩
    let after : State Int := .state objects
      ⟨[(z, .initialized (.shlease α)), (y, .initialized (.owned α)),
        (x, .uninitialized)], by decide⟩
    PlaceEffect before (.give (.variable x) y) after ∧
      readSlot after (.variable z) = some (.initialized (.shlease α)) := by
  constructor
  · apply PlaceEffect.giveOwned (id := ⟨0⟩) (middle := .state
      ⟨[(ObjectId.mk 0, .primitive 22)], by simp⟩
      ⟨[(VariableId.mk 2, .initialized (.shlease ⟨0⟩)),
        (VariableId.mk 1, .uninitialized), (VariableId.mk 0, .uninitialized)], by decide⟩)
    · simp [ReferenceAt, Stored]
    · simp [Stored]
    · simp
    · rfl
    · rfl
  · rfl
-- ANCHOR_END: give_with_shared_lease

-- ANCHOR: unique_lease_release
example :
    let x : VariableId := ⟨0⟩
    let y : VariableId := ⟨1⟩
    let α : ObjectId := ⟨0⟩
    let objects : FiniteMap ObjectId (Object Int) :=
      ⟨[(α, .primitive 22)], by simp⟩
    let before : State Int := .state objects
      ⟨[(y, .uninitialized), (x, .initialized (.owned α))], by decide⟩
    let leased : State Int := .state objects
      ⟨[(y, .initialized (.leased (.variable x))), (x, .initialized (.owned α))], by decide⟩
    PlaceEffect before (.lease (.variable x) y) leased ∧
      PlaceEffect leased (.drop (.variable y)) before := by
  constructor
  · apply PlaceEffect.leaseOwned (id := ⟨0⟩)
    · simp [ReferenceAt, Stored]
    · simp [Stored]
    · rfl
  · apply PlaceEffect.dropLeased (support := .variable ⟨0⟩)
    · simp [ReferenceAt, Stored]
    · rfl
-- ANCHOR_END: unique_lease_release

-- ANCHOR: sublease_chain
example :
    let x : VariableId := ⟨0⟩
    let y : VariableId := ⟨1⟩
    let z : VariableId := ⟨2⟩
    let α : ObjectId := ⟨0⟩
    let objects : FiniteMap ObjectId (Object Int) :=
      ⟨[(α, .primitive 22)], by simp⟩
    let before : State Int := .state objects
      ⟨[(z, .uninitialized), (y, .initialized (.leased (.variable x))),
        (x, .initialized (.owned α))], by decide⟩
    let subleased : State Int := .state objects
      ⟨[(z, .initialized (.leased (.variable y))),
        (y, .initialized (.leased (.variable x))),
        (x, .initialized (.owned α))], by decide⟩
    PlaceEffect before (.lease (.variable y) z) subleased ∧
      PlaceEffect subleased (.drop (.variable z)) before := by
  constructor
  · apply PlaceEffect.leaseLeased (support := .variable ⟨0⟩)
    · simp [ReferenceAt, Stored]
    · simp [Stored]
    · rfl
  · apply PlaceEffect.dropLeased (support := .variable ⟨1⟩)
    · simp [ReferenceAt, Stored]
    · rfl
-- ANCHOR_END: sublease_chain

-- ANCHOR: shared_lease_release
example :
    let x : VariableId := ⟨0⟩
    let y : VariableId := ⟨1⟩
    let α : ObjectId := ⟨0⟩
    let objects : FiniteMap ObjectId (Object Int) :=
      ⟨[(α, .primitive 22)], by simp⟩
    let before : State Int := .state objects
      ⟨[(y, .uninitialized), (x, .initialized (.owned α))], by decide⟩
    let shared : State Int := .state objects
      ⟨[(y, .initialized (.shlease α)), (x, .initialized (.owned α))], by decide⟩
    PlaceEffect before (.share (.variable x) y) shared ∧
      PlaceEffect shared (.drop (.variable y)) before := by
  constructor
  · apply PlaceEffect.shareOwned (id := ⟨0⟩)
    · simp [ReferenceAt, Stored]
    · simp [Stored]
    · rfl
  · apply PlaceEffect.dropShlease (id := ⟨0⟩)
    · simp [ReferenceAt, Stored]
    · rfl
-- ANCHOR_END: shared_lease_release

-- This starts with an existing showned reference. It does not claim that any
-- current operation converts unique ownership into shared ownership.
-- ANCHOR: shared_owner_duplicate_release
example :
    let x : VariableId := ⟨0⟩
    let y : VariableId := ⟨1⟩
    let α : ObjectId := ⟨0⟩
    let objects : FiniteMap ObjectId (Object Int) :=
      ⟨[(α, .primitive 22)], by simp⟩
    let before : State Int := .state objects
      ⟨[(y, .uninitialized), (x, .initialized (.showned α))], by decide⟩
    let shared : State Int := .state objects
      ⟨[(y, .initialized (.showned α)), (x, .initialized (.showned α))], by decide⟩
    PlaceEffect before (.share (.variable x) y) shared ∧
      PlaceEffect shared (.drop (.variable y)) before := by
  constructor
  · apply PlaceEffect.shareShowned (id := ⟨0⟩)
    · simp [ReferenceAt, Stored]
    · simp [Stored]
    · rfl
  · apply PlaceEffect.dropShowned (id := ⟨0⟩) (other := .variable ⟨0⟩)
    · simp [ReferenceAt, Stored]
    · simp [ReferenceAt, Stored]
    · simp
    · rfl
-- ANCHOR_END: shared_owner_duplicate_release

-- ANCHOR: give_aggregate_field
example :
    let x : VariableId := ⟨0⟩
    let y : VariableId := ⟨1⟩
    let α : ObjectId := ⟨0⟩
    let β : ObjectId := ⟨1⟩
    let before : State Int := .state
      ⟨[(α, .aggregate ⟨[("item", .initialized (.owned β))], by simp⟩),
        (β, .primitive 22)], by decide⟩
      ⟨[(y, .uninitialized), (x, .initialized (.owned α))], by decide⟩
    let after : State Int := .state
      ⟨[(α, .aggregate ⟨[("item", .uninitialized)], by simp⟩),
        (β, .primitive 22)], by decide⟩
      ⟨[(y, .initialized (.owned β)), (x, .initialized (.owned α))], by decide⟩
    PlaceEffect before (.give (.field α "item") y) after := by
  apply PlaceEffect.giveOwned (middle := .state
    ⟨[(ObjectId.mk 0, .aggregate ⟨[("item", .uninitialized)], by simp⟩),
      (ObjectId.mk 1, .primitive 22)], by decide⟩
    ⟨[(VariableId.mk 1, .uninitialized),
      (VariableId.mk 0, .initialized (.owned ⟨0⟩))], by decide⟩)
  · apply readSlot_stored.mp
    rfl
  · simp [Stored]
  · simp
  · rfl
  · rfl
-- ANCHOR_END: give_aggregate_field

-- ANCHOR: give_array_element
example :
    let x : VariableId := ⟨0⟩
    let y : VariableId := ⟨1⟩
    let α : ObjectId := ⟨0⟩
    let β : ObjectId := ⟨1⟩
    let before : State Int := .state
      ⟨[(α, .array #[.initialized (.owned β), .uninitialized]),
        (β, .primitive 22)], by decide⟩
      ⟨[(y, .uninitialized), (x, .initialized (.owned α))], by decide⟩
    let after : State Int := .state
      ⟨[(α, .array #[.uninitialized, .uninitialized]),
        (β, .primitive 22)], by decide⟩
      ⟨[(y, .initialized (.owned β)), (x, .initialized (.owned α))], by decide⟩
    PlaceEffect before (.give (.element α 0) y) after := by
  apply PlaceEffect.giveOwned (middle := .state
    ⟨[(ObjectId.mk 0, .array #[.uninitialized, .uninitialized]),
      (ObjectId.mk 1, .primitive 22)], by decide⟩
    ⟨[(VariableId.mk 1, .uninitialized),
      (VariableId.mk 0, .initialized (.owned ⟨0⟩))], by decide⟩)
  · apply readSlot_stored.mp
    rfl
  · simp [Stored]
  · simp
  · rfl
  · rfl
-- ANCHOR_END: give_array_element

-- A mixed sequence: allocation and creation use Step; destruction uses the
-- proved resource-effect relation. This does not invent a Step.drop constructor.
-- ANCHOR: primitive_resource_lifecycle
example :
    let x : VariableId := ⟨0⟩
    let α : ObjectId := ⟨0⟩
    let allocated : State Int := .state .empty
      ⟨[(x, .uninitialized)], by simp⟩
    let created : State Int := .state
      ⟨[(α, .primitive 22)], by simp⟩
      ⟨[(x, .initialized (.owned α))], by simp⟩
    Step Int (State.initial Int) (.allocVariable x) allocated ∧
      Step Int allocated (.createPrimitive 22 x) created ∧
      PlaceEffect created (.drop (.variable x)) allocated ∧
      Step Int allocated (.deallocVariable x) (State.initial Int) := by
  constructor
  · exact Step.allocVariable _ _ _ (by simp [FiniteMap.empty])
  constructor
  · exact Step.createPrimitive _ _ _ _ (by simp) _ (by simp [FiniteMap.empty])
  constructor
  · let before : State Int := .state
      ⟨[(ObjectId.mk 0, .primitive 22)], by simp⟩
      ⟨[(VariableId.mk 0, .initialized (.owned ⟨0⟩))], by simp⟩
    let middle : State Int := .state
      ⟨[(ObjectId.mk 0, .primitive 22)], by simp⟩
      ⟨[(VariableId.mk 0, .uninitialized)], by simp⟩
    have lastOwner : ∀ place, OwnerAt before place ⟨0⟩ → place = .variable ⟨0⟩ := by
      intro place owner
      cases place <;> simp [before, OwnerAt, ReferenceAt, Stored] at owner ⊢
      exact owner
    have released := DropLeaf.release before middle (.variable ⟨0⟩) ⟨0⟩
      (Or.inl (by simp [before, ReferenceAt, Stored])) lastOwner
      ⟨.primitive 22, by simp, True.intro⟩ (by rfl)
    apply PlaceEffect.dropLeaf
    simpa [before, middle, eraseObject, FiniteMap.erase, FiniteMap.empty] using released
  · exact Step.deallocVariable _ _ _ (by simp) (by rfl)
-- ANCHOR_END: primitive_resource_lifecycle

-- ANCHOR: drop_aggregate_recursively
example :
    let x : VariableId := ⟨0⟩
    let α : ObjectId := ⟨0⟩
    let β : ObjectId := ⟨1⟩
    let before : State Int := .state
      ⟨[(α, .aggregate ⟨[("item", .initialized (.owned β))], by simp⟩),
        (β, .primitive 22)], by decide⟩
      ⟨[(x, .initialized (.owned α))], by simp⟩
    let after : State Int := .state .empty
      ⟨[(x, .uninitialized)], by simp⟩
    PlaceEffect before (.drop (.variable x)) after := by
  dsimp only
  let before : State Int := .state
    ⟨[(ObjectId.mk 0, .aggregate ⟨[("item", .initialized (.owned ⟨1⟩))], by simp⟩),
      (ObjectId.mk 1, .primitive 22)], by decide⟩
    ⟨[(VariableId.mk 0, .initialized (.owned ⟨0⟩))], by simp⟩
  let childCleared : State Int := .state
    ⟨[(ObjectId.mk 0, .aggregate ⟨[("item", .uninitialized)], by simp⟩),
      (ObjectId.mk 1, .primitive 22)], by decide⟩
    ⟨[(VariableId.mk 0, .initialized (.owned ⟨0⟩))], by simp⟩
  let childDropped : State Int := .state
    ⟨[(ObjectId.mk 0, .aggregate ⟨[("item", .uninitialized)], by simp⟩)], by simp⟩
    ⟨[(VariableId.mk 0, .initialized (.owned ⟨0⟩))], by simp⟩
  let parentCleared : State Int := .state
    ⟨[(ObjectId.mk 0, .aggregate ⟨[("item", .uninitialized)], by simp⟩)], by simp⟩
    ⟨[(VariableId.mk 0, .uninitialized)], by simp⟩
  have lastParent : ∀ place, OwnerAt before place ⟨0⟩ → place = .variable ⟨0⟩ := by
    intro place owner
    cases place <;> simp [before, OwnerAt, ReferenceAt, Stored] at owner ⊢
    · exact owner
    · rcases owner with ⟨fields, ⟨_, rfl⟩, field⟩ | ⟨fields, ⟨_, rfl⟩, field⟩ <;> simp at field
  have lastChild : ∀ place, OwnerAt before place ⟨1⟩ → place = .field ⟨0⟩ "item" := by
    intro place owner
    cases place <;> simp [before, OwnerAt, ReferenceAt, Stored] at owner ⊢
    rcases owner with ⟨fields, ⟨equal, rfl⟩, field⟩ | ⟨fields, ⟨_, rfl⟩, field⟩
    · exact ⟨equal, by simpa using field⟩
    · simp at field
  have childRelease := DropLeaf.release before childCleared (.field ⟨0⟩ "item") ⟨1⟩
    (Or.inl (readSlot_stored.mp (by rfl))) lastChild
    ⟨.primitive 22, by simp, True.intro⟩ (by rfl)
  have childEffect : PlaceEffect before (.drop (.field ⟨0⟩ "item")) childDropped := by
    apply PlaceEffect.dropLeaf
    simpa [childCleared, childDropped, eraseObject, FiniteMap.erase] using childRelease
  have lastParent' : ∀ place, OwnerAt childDropped place ⟨0⟩ → place = .variable ⟨0⟩ := by
    intro place owner
    cases place <;> simp [childDropped, OwnerAt, ReferenceAt, Stored] at owner ⊢
    · exact owner
    · rcases owner with ⟨fields, ⟨_, rfl⟩, field⟩ | ⟨fields, ⟨_, rfl⟩, field⟩ <;> simp at field
  have parentRelease := DropLeaf.release childDropped parentCleared (.variable ⟨0⟩) ⟨0⟩
    (Or.inl (readSlot_stored.mp (by rfl))) lastParent'
    ⟨.aggregate ⟨[("item", .uninitialized)], by simp⟩,
      by simp, by simp [ObjectEmpty]⟩ (by rfl)
  apply PlaceEffect.dropChild (child := .field ⟨0⟩ "item")
    (owner := Or.inl (readSlot_stored.mp (show readSlot before (.variable ⟨0⟩) =
      some (.initialized (.owned ⟨0⟩)) from rfl)))
    (lastOwner := lastParent) (childEffect := childEffect) (inside := rfl)
  apply PlaceEffect.dropLeaf
  simpa [parentCleared, eraseObject, FiniteMap.erase, FiniteMap.empty] using parentRelease
-- ANCHOR_END: drop_aggregate_recursively

-- ANCHOR: drop_array_recursively
example :
    let x : VariableId := ⟨0⟩
    let α : ObjectId := ⟨0⟩
    let β : ObjectId := ⟨1⟩
    let before : State Int := .state
      ⟨[(α, .array #[.initialized (.owned β), .uninitialized]),
        (β, .primitive 22)], by decide⟩
      ⟨[(x, .initialized (.owned α))], by simp⟩
    let after : State Int := .state .empty
      ⟨[(x, .uninitialized)], by simp⟩
    PlaceEffect before (.drop (.variable x)) after := by
  dsimp only
  let before : State Int := .state
    ⟨[(ObjectId.mk 0, .array #[.initialized (.owned ⟨1⟩), .uninitialized]),
      (ObjectId.mk 1, .primitive 22)], by decide⟩
    ⟨[(VariableId.mk 0, .initialized (.owned ⟨0⟩))], by simp⟩
  let childCleared : State Int := .state
    ⟨[(ObjectId.mk 0, .array #[.uninitialized, .uninitialized]),
      (ObjectId.mk 1, .primitive 22)], by decide⟩
    ⟨[(VariableId.mk 0, .initialized (.owned ⟨0⟩))], by simp⟩
  let childDropped : State Int := .state
    ⟨[(ObjectId.mk 0, .array #[.uninitialized, .uninitialized])], by simp⟩
    ⟨[(VariableId.mk 0, .initialized (.owned ⟨0⟩))], by simp⟩
  let parentCleared : State Int := .state
    ⟨[(ObjectId.mk 0, .array #[.uninitialized, .uninitialized])], by simp⟩
    ⟨[(VariableId.mk 0, .uninitialized)], by simp⟩
  have lastParent : ∀ place, OwnerAt before place ⟨0⟩ → place = .variable ⟨0⟩ := by
    intro place owner
    cases place <;> simp [before, OwnerAt, ReferenceAt, Stored] at owner ⊢
    · exact owner
    · rcases owner with ⟨elements, ⟨_, rfl⟩, element⟩ | ⟨elements, ⟨_, rfl⟩, element⟩ <;>
        simp [List.getElem?_cons] at element <;>
        split at element <;> (try split at element) <;> simp_all
  have lastChild : ∀ place, OwnerAt before place ⟨1⟩ → place = .element ⟨0⟩ 0 := by
    intro place owner
    cases place <;> simp [before, OwnerAt, ReferenceAt, Stored] at owner ⊢
    rcases owner with ⟨elements, ⟨equal, rfl⟩, element⟩ | ⟨elements, ⟨_, rfl⟩, element⟩
    · subst_vars
      simp [List.getElem?_cons] at element
      exact ⟨rfl, element⟩
    · simp [List.getElem?_cons] at element
      split at element <;> (try split at element) <;> simp_all
  have childRelease := DropLeaf.release before childCleared (.element ⟨0⟩ 0) ⟨1⟩
    (Or.inl (readSlot_stored.mp (by rfl))) lastChild
    ⟨.primitive 22, by simp, True.intro⟩ (by rfl)
  have childEffect : PlaceEffect before (.drop (.element ⟨0⟩ 0)) childDropped := by
    apply PlaceEffect.dropLeaf
    simpa [childCleared, childDropped, eraseObject, FiniteMap.erase] using childRelease
  have lastParent' : ∀ place, OwnerAt childDropped place ⟨0⟩ → place = .variable ⟨0⟩ := by
    intro place owner
    cases place <;> simp [childDropped, OwnerAt, ReferenceAt, Stored] at owner ⊢
    · exact owner
    · rcases owner with ⟨elements, ⟨_, rfl⟩, element⟩ | ⟨elements, ⟨_, rfl⟩, element⟩ <;>
        simp [List.getElem?_cons] at element <;>
        split at element <;> (try split at element) <;> simp_all
  have parentRelease := DropLeaf.release childDropped parentCleared (.variable ⟨0⟩) ⟨0⟩
    (Or.inl (readSlot_stored.mp (by rfl))) lastParent'
    ⟨.array #[.uninitialized, .uninitialized], by simp,
      by
        intro index reference impossible
        simp [List.getElem?_cons] at impossible
        split at impossible <;> (try split at impossible) <;> simp_all⟩ (by rfl)
  apply PlaceEffect.dropChild (child := .element ⟨0⟩ 0)
    (owner := Or.inl (readSlot_stored.mp (show readSlot before (.variable ⟨0⟩) =
      some (.initialized (.owned ⟨0⟩)) from rfl)))
    (lastOwner := lastParent) (childEffect := childEffect) (inside := rfl)
  apply PlaceEffect.dropLeaf
  simpa [parentCleared, eraseObject, FiniteMap.erase, FiniteMap.empty] using parentRelease
-- ANCHOR_END: drop_array_recursively

-- ANCHOR: nonfinal_owner_cannot_destroy
example :
    let x : VariableId := ⟨0⟩
    let y : VariableId := ⟨1⟩
    let α : ObjectId := ⟨0⟩
    let before : State Int := .state
      ⟨[(α, .primitive 22)], by simp⟩
      ⟨[(y, .initialized (.showned α)), (x, .initialized (.showned α))], by decide⟩
    ∀ after, ¬ DropLeaf before (.variable y) α after := by
  dsimp only
  intro after released
  cases released with
  | release middle source id owner lastOwner empty cleared =>
    have equal := lastOwner (.variable ⟨0⟩) (Or.inr (by simp [ReferenceAt, Stored]))
    cases equal
-- ANCHOR_END: nonfinal_owner_cannot_destroy

end Dada.Heap
