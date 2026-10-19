import PathOperations

namespace Dada.Heap

-- These are exact runtime successors, not evidence of static borrow acceptance.

-- ANCHOR: path_give_owner_retargets
example :
    let objects : FiniteMap ObjectId (Object Int) :=
      ⟨[(⟨0⟩, .primitive 22)], by simp⟩
    let before : State Int := .state objects
      ⟨[(⟨2⟩, .uninitialized), (⟨1⟩, .initialized (.leased (.variable ⟨0⟩))),
        (⟨0⟩, .initialized (.owned ⟨0⟩))], by decide⟩
    let after : State Int := .state objects
      ⟨[(⟨2⟩, .initialized (.owned ⟨0⟩)),
        (⟨1⟩, .initialized (.leased (.variable ⟨2⟩))),
        (⟨0⟩, .uninitialized)], by decide⟩
    PathStep before (.give (.path ⟨0⟩ []) ⟨2⟩) after := by
  dsimp only
  apply PathStep.giveGiven (source := .variable ⟨0⟩) (object := ⟨0⟩)
  · apply ResolvePath.variable
    apply ResolvePlace.intro (by rfl)
    apply ResolveReference.owned
    simp [AllocatedObject]
  · let middle : State Int := .state ⟨[(⟨0⟩, .primitive 22)], by simp⟩
      ⟨[(⟨2⟩, .uninitialized), (⟨1⟩, .initialized (.leased (.variable ⟨0⟩))),
        (⟨0⟩, .uninitialized)], by decide⟩
    let writtenState : State Int := .state ⟨[(⟨0⟩, .primitive 22)], by simp⟩
      ⟨[(⟨2⟩, .initialized (.owned ⟨0⟩)),
        (⟨1⟩, .initialized (.leased (.variable ⟨0⟩))),
        (⟨0⟩, .uninitialized)], by decide⟩
    have moved := MoveReference.move (middle := middle) (writtenState := writtenState)
      (source := .variable ⟨0⟩) (destination := .variable ⟨2⟩)
      (before := .state ⟨[(ObjectId.mk 0, .primitive (22 : Int))], by simp⟩
        ⟨[(⟨2⟩, .uninitialized), (⟨1⟩, .initialized (.leased (.variable ⟨0⟩))),
          (⟨0⟩, .initialized (.owned ⟨0⟩))], by decide⟩)
      (reference := .owned ⟨0⟩)
      (by simp [ReferenceAt, Stored]) (by simp [Stored]) (by decide)
      (by rfl) (by rfl)
    simpa [writtenState, retargetLeases, mapReferences, Object.mapReferences,
      Slot.mapReferences, FiniteMap.mapValues, retargetReference] using moved
-- ANCHOR_END: path_give_owner_retargets

-- ANCHOR: path_give_shared_borrow
example :
    let objects : FiniteMap ObjectId (Object Int) :=
      ⟨[(⟨0⟩, .primitive 22)], by simp⟩
    let before : State Int := .state objects
      ⟨[(⟨2⟩, .uninitialized), (⟨1⟩, .initialized (.shlease ⟨0⟩)),
        (⟨0⟩, .initialized (.owned ⟨0⟩))], by decide⟩
    let after : State Int := .state objects
      ⟨[(⟨2⟩, .initialized (.shlease ⟨0⟩)), (⟨1⟩, .initialized (.shlease ⟨0⟩)),
        (⟨0⟩, .initialized (.owned ⟨0⟩))], by decide⟩
    PathStep before (.give (.path ⟨1⟩ []) ⟨2⟩) after ∧
      readSlot after (.variable ⟨1⟩) = some (.initialized (.shlease ⟨0⟩)) := by
  constructor
  · apply PathStep.giveShlease (source := .variable ⟨1⟩) (object := ⟨0⟩)
    · apply ResolvePath.variable
      apply ResolvePlace.intro (by rfl)
      apply ResolveReference.shlease
      simp [AllocatedObject]
    · simp [Stored]
    · rfl
  · rfl
-- ANCHOR_END: path_give_shared_borrow

-- ANCHOR: path_give_lease_reborrows
example :
    let objects : FiniteMap ObjectId (Object Int) :=
      ⟨[(⟨0⟩, .primitive 22)], by simp⟩
    let before : State Int := .state objects
      ⟨[(⟨2⟩, .uninitialized), (⟨1⟩, .initialized (.leased (.variable ⟨0⟩))),
        (⟨0⟩, .initialized (.owned ⟨0⟩))], by decide⟩
    let after : State Int := .state objects
      ⟨[(⟨2⟩, .initialized (.leased (.variable ⟨1⟩))),
        (⟨1⟩, .initialized (.leased (.variable ⟨0⟩))),
        (⟨0⟩, .initialized (.owned ⟨0⟩))], by decide⟩
    PathStep before (.give (.path ⟨1⟩ []) ⟨2⟩) after ∧
      readSlot after (.variable ⟨1⟩) = some (.initialized (.leased (.variable ⟨0⟩))) := by
  constructor
  · apply PathStep.giveLeased (source := .variable ⟨1⟩) (object := ⟨0⟩)
    · apply ResolvePath.variable
      apply ResolvePlace.intro (by rfl)
      apply ResolveReference.leased (by rfl) (by rfl)
      apply ResolveReference.owned
      simp [AllocatedObject]
    · simp [Stored]
    · rfl
  · rfl
-- ANCHOR_END: path_give_lease_reborrows

-- ANCHOR: path_shared_owner_copies
example :
    let objects : FiniteMap ObjectId (Object Int) :=
      ⟨[(⟨0⟩, .primitive 22)], by simp⟩
    let before : State Int := .state objects
      ⟨[(⟨1⟩, .uninitialized), (⟨0⟩, .initialized (.showned ⟨0⟩))], by decide⟩
    let after : State Int := .state objects
      ⟨[(⟨1⟩, .initialized (.showned ⟨0⟩)),
        (⟨0⟩, .initialized (.showned ⟨0⟩))], by decide⟩
    PathStep before (.give (.path ⟨0⟩ []) ⟨1⟩) after ∧
      PathStep before (.share (.path ⟨0⟩ []) ⟨1⟩) after := by
  constructor
  · apply PathStep.giveShowned (source := .variable ⟨0⟩) (object := ⟨0⟩)
    · apply ResolvePath.variable
      apply ResolvePlace.intro (by rfl)
      apply ResolveReference.showned
      simp [AllocatedObject]
    · simp [ReferenceAt, Stored]
    · simp [Stored]
    · rfl
  · apply PathStep.shareShowned (source := .variable ⟨0⟩) (object := ⟨0⟩)
    · apply ResolvePath.variable
      apply ResolvePlace.intro (by rfl)
      apply ResolveReference.showned
      simp [AllocatedObject]
    · simp [ReferenceAt, Stored]
    · simp [Stored]
    · rfl
-- ANCHOR_END: path_shared_owner_copies

-- ANCHOR: path_owner_borrows
example :
    let objects : FiniteMap ObjectId (Object Int) :=
      ⟨[(⟨0⟩, .primitive 22)], by simp⟩
    let before : State Int := .state objects
      ⟨[(⟨1⟩, .uninitialized), (⟨0⟩, .initialized (.owned ⟨0⟩))], by decide⟩
    let leased : State Int := .state objects
      ⟨[(⟨1⟩, .initialized (.leased (.variable ⟨0⟩))),
        (⟨0⟩, .initialized (.owned ⟨0⟩))], by decide⟩
    let shared : State Int := .state objects
      ⟨[(⟨1⟩, .initialized (.shlease ⟨0⟩)),
        (⟨0⟩, .initialized (.owned ⟨0⟩))], by decide⟩
    PathStep before (.lease (.path ⟨0⟩ []) ⟨1⟩) leased ∧
      PathStep before (.share (.path ⟨0⟩ []) ⟨1⟩) shared := by
  constructor
  · apply PathStep.lease (source := .variable ⟨0⟩) (object := ⟨0⟩) (permission := .given)
    · apply ResolvePath.variable
      apply ResolvePlace.intro (by rfl)
      apply ResolveReference.owned
      simp [AllocatedObject]
    · exact Or.inl rfl
    · simp [Stored]
    · rfl
  · apply PathStep.shareBorrow (source := .variable ⟨0⟩) (object := ⟨0⟩) (permission := .given)
    · apply ResolvePath.variable
      apply ResolvePlace.intro (by rfl)
      apply ResolveReference.owned
      simp [AllocatedObject]
    · decide
    · simp [Stored]
    · rfl
-- ANCHOR_END: path_owner_borrows

-- This intentionally records v1's explicit borrowed-place drop no-op. Clearing
-- the handle during scope cleanup is a separate resource effect.
-- ANCHOR: path_drop_borrow_noop
example :
    let before : State Int := .state
      ⟨[(⟨0⟩, .primitive 22)], by simp⟩
      ⟨[(⟨1⟩, .initialized (.shlease ⟨0⟩)),
        (⟨0⟩, .initialized (.owned ⟨0⟩))], by decide⟩
    PathStep before (.drop (.path ⟨1⟩ [])) before ∧
      readSlot before (.variable ⟨1⟩) = some (.initialized (.shlease ⟨0⟩)) := by
  constructor
  · apply PathStep.dropBorrow (source := .variable ⟨1⟩) (object := ⟨0⟩) (permission := .shlease)
    · apply ResolvePath.variable
      apply ResolvePlace.intro (by rfl)
      apply ResolveReference.shlease
      simp [AllocatedObject]
    · exact Or.inr rfl
  · rfl
-- ANCHOR_END: path_drop_borrow_noop

-- ANCHOR: path_drop_final_owner
example :
    let before : State Int := .state
      ⟨[(⟨0⟩, .primitive 22)], by simp⟩
      ⟨[(⟨0⟩, .initialized (.owned ⟨0⟩))], by simp⟩
    let after : State Int := .state .empty
      ⟨[(⟨0⟩, .uninitialized)], by simp⟩
    PathStep before (.drop (.path ⟨0⟩ [])) after := by
  dsimp only
  let before : State Int := .state
    ⟨[(ObjectId.mk 0, .primitive 22)], by simp⟩
    ⟨[(VariableId.mk 0, .initialized (.owned ⟨0⟩))], by simp⟩
  let middle : State Int := .state
    ⟨[(ObjectId.mk 0, .primitive 22)], by simp⟩
    ⟨[(VariableId.mk 0, .uninitialized)], by simp⟩
  apply PathStep.dropGiven (source := .variable ⟨0⟩) (object := ⟨0⟩)
  · apply ResolvePath.variable
    apply ResolvePlace.intro (by rfl)
    apply ResolveReference.owned
    simp [AllocatedObject]
  · have lastOwner : ∀ place, OwnerAt before place ⟨0⟩ → place = .variable ⟨0⟩ := by
      intro place owner
      cases place <;> simp [before, OwnerAt, ReferenceAt, Stored] at owner ⊢
      exact owner
    have released := DropLeaf.release before middle (.variable ⟨0⟩) ⟨0⟩
      (Or.inl (readSlot_stored.mp (by rfl))) lastOwner
      ⟨.primitive 22, by simp, True.intro⟩ (by rfl)
    apply PlaceEffect.dropLeaf
    simpa [before, middle, eraseObject, FiniteMap.erase, FiniteMap.empty] using released
-- ANCHOR_END: path_drop_final_owner

-- ANCHOR: path_drop_nonfinal_shared_owner
example :
    let objects : FiniteMap ObjectId (Object Int) :=
      ⟨[(⟨0⟩, .primitive 22)], by simp⟩
    let before : State Int := .state objects
      ⟨[(⟨1⟩, .initialized (.showned ⟨0⟩)),
        (⟨0⟩, .initialized (.showned ⟨0⟩))], by decide⟩
    let after : State Int := .state objects
      ⟨[(⟨1⟩, .initialized (.showned ⟨0⟩)), (⟨0⟩, .uninitialized)], by decide⟩
    PathStep before (.drop (.path ⟨0⟩ [])) after := by
  apply PathStep.dropShowned (source := .variable ⟨0⟩) (object := ⟨0⟩)
  · apply ResolvePath.variable
    apply ResolvePlace.intro (by rfl)
    apply ResolveReference.showned
    simp [AllocatedObject]
  · simp [ReferenceAt, Stored]
  · exact WritablePath.variable _ _
  · apply PlaceEffect.dropShowned (other := .variable ⟨1⟩) (id := ⟨0⟩)
    · simp [ReferenceAt, Stored]
    · simp [ReferenceAt, Stored]
    · decide
    · rfl
-- ANCHOR_END: path_drop_nonfinal_shared_owner

-- The final field is showned, but releasing its occurrence would mutate the
-- aggregate shared with the original owner. The destructive rule is withheld.
-- ANCHOR: path_shared_prefix_not_writable
example :
    let before : State Int := .state
      ⟨[(⟨0⟩, .aggregate ⟨[("f", .initialized (.showned ⟨1⟩))], by simp⟩),
        (⟨1⟩, .primitive 22)], by decide⟩
      ⟨[(⟨1⟩, .initialized (.shlease ⟨0⟩)),
        (⟨0⟩, .initialized (.owned ⟨0⟩))], by decide⟩
    ResolvePath before (.path ⟨1⟩ [.field "f"]) (.field ⟨0⟩ "f") ⟨1⟩ .showned ∧
      ¬ WritablePath before (.path ⟨1⟩ [.field "f"]) := by
  dsimp only
  have shared : ResolvePath (State.state (Primitive := Int)
      ⟨[(⟨0⟩, .aggregate ⟨[("f", .initialized (.showned ⟨1⟩))], by simp⟩),
        (⟨1⟩, .primitive 22)], by decide⟩
      ⟨[(⟨1⟩, .initialized (.shlease ⟨0⟩)),
        (⟨0⟩, .initialized (.owned ⟨0⟩))], by decide⟩)
      (.path ⟨1⟩ []) (.variable ⟨1⟩) ⟨0⟩ .shlease := by
    apply ResolvePath.variable
    apply ResolvePlace.intro (by rfl)
    apply ResolveReference.shlease
    simp [AllocatedObject]
  constructor
  · apply ResolvePath.field (projections := []) shared
    apply ResolvePlace.intro (by rfl)
    apply ResolveReference.showned
    simp [AllocatedObject]
  · exact WritablePath.no_shared_prefix shared (.field "f") []
-- ANCHOR_END: path_shared_prefix_not_writable

end Dada.Heap
