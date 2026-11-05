import Assignment.WriteEffects

namespace Dada.Assignment
open Shared Shared.Typing

-- A writable destination identifies its current slot even when it is empty.
theorem Writable.stored (writable : Writable state place source previous) :
    Stored state source previous := by
  cases writable with
  | «variable» member => exact member
  | field _ stored field => exact ⟨_, stored, field⟩

-- A store changes neither the nominal class nor the set of field names.
theorem Write.new_object_data (written : Write before source incoming after)
    {id : ObjectId} {data : Object}
    (stored : (id, data) ∈ after.objects) :
    ∃ oldData, (id, oldData) ∈ before.objects ∧ oldData.className = data.className ∧
      oldData.fields.map Prod.fst = data.fields.map Prod.fst := by
  cases written with
  | «variable» => exact ⟨data, stored, rfl, rfl⟩
  | field variables nextId leading trailing parent className beforeFields afterFields name previous incoming =>
    simp only [List.mem_append, List.mem_cons] at stored
    rcases stored with member | same | member
    · exact ⟨data, List.mem_append_left _ member, rfl, rfl⟩
    · cases same
      exact ⟨⟨className, beforeFields ++ (name, previous) :: afterFields⟩, by simp, rfl, by simp⟩
    · exact ⟨data, List.mem_append_right _ (List.mem_cons_of_mem _ member), rfl, rfl⟩

private theorem route_live (route : Route state pending site path reference) :
    LiveWith state pending reference.object := by
  induction route with
  | root root =>
    cases root with
    | «variable» member => exact .variable member
    | pending member => exact .pending member
  | @field path parent data name reference _ stored field ih =>
    exact (show LiveWith state pending reference.object from .field ih stored field)

-- The incoming root becomes reachable through the slot. A field destination's
-- unique parent route cannot cross that destination and therefore survives.
theorem Write.incoming_live {previous : Slot} (wf : WellFormedWith classes before pending)
    (writable : Writable before place source previous)
    (written : Write before source incoming after) :
    LiveWith after otherPending incoming.object := by
  cases writable with
  | «variable» member => exact .variable written.installed
  | @field base source parent data name previous resolved stored field =>
    have cut : Route before pending (.variable (splitPlace base).1) (splitPlace base).2
        (.owned parent) := route_of_resolve resolved
    have survives := written.parent_route (otherPending := otherPending) wf cut cut (Nat.le_refl _)
    obtain ⟨newData, newStored, newField⟩ := written.installed
    exact .field (route_live survives) newStored newField

-- Every old path survives either through its old edge or through the displaced
-- reference, now held as an additional pending root.
theorem Write.liveWith {previous : Slot} (wf : WellFormedWith classes before (incoming :: pending))
    (writable : Writable before place source previous)
    (written : Write before source incoming after)
    (live : LiveWith before (incoming :: pending) object) :
    LiveWith after (previous.toList ++ pending) object := by
  have displaced : ∀ reference, Stored before source (some reference) →
      LiveWith after (previous.toList ++ pending) reference.object := by
    intro reference stored
    have same := stored_value_unique wf writable.stored stored
    subst previous
    exact .pending (by simp)
  apply live.transport
  · intro reference member
    rcases List.mem_cons.mp member with rfl | member
    · exact written.incoming_live wf writable
    · exact .pending (List.mem_append_right _ member)
  · intro name reference member
    by_cases same : StoragePlace.variable name = source
    · exact displaced reference (same ▸ member)
    · exact .variable (written.stored_unchanged same member)
  · intro parent data name reference stored field parentLive
    by_cases same : StoragePlace.field parent name = source
    · exact displaced reference (same ▸ (show Stored before (.field parent name) (some reference) from
        ⟨data, stored, field⟩))
    · obtain ⟨newData, newStored, newField⟩ :=
        written.stored_unchanged same ⟨data, stored, field⟩
      exact .field parentLive newStored newField

private theorem owners_targets (state : State) :
    (Owners state).map Reference.object = References state := by
  simp [Owners, References, List.map_filterMap, List.map_flatMap]

private theorem compatible_symm {first second : Reference} (h : Compatible first second) :
    Compatible second first := by
  rcases h with different | shared
  · exact Or.inl (Ne.symm different)
  · exact Or.inr ⟨shared.2, shared.1⟩

-- Store transfers the incoming reference to the destination and transfers the
-- displaced reference to the pending roots; ownership occurrences are conserved.
theorem Write.owners_pending {previous : Slot} (wf : WellFormedWith classes before pending)
    (writable : Writable before place source previous)
    (written : Write before source incoming after) (other : List Reference) :
    ((incoming :: other) ++ Owners before).Perm
      ((previous.toList ++ other) ++ Owners after) := by
  obtain ⟨old, stored, permutation⟩ := written.previous
  have same := stored_value_unique wf writable.stored stored
  subst old
  have first : ((incoming :: other) ++ Owners before).Perm
      (other ++ incoming :: Owners before) :=
    (List.perm_middle (a := incoming) (l₁ := other) (l₂ := Owners before)).symm
  have middle := permutation.append_left other
  have last : (other ++ (previous.toList ++ Owners after)).Perm
      ((previous.toList ++ other) ++ Owners after) := by
    simpa only [List.append_assoc] using
      (show (other ++ previous.toList).Perm (previous.toList ++ other) from
        List.perm_append_comm).append_right (Owners after)
  exact first.trans (middle.trans last)

theorem Write.preserves_pending {previous : Slot} (wf : WellFormedWith classes before (incoming :: pending))
    (writable : Writable before place source previous)
    (written : Write before source incoming after) :
    WellFormedWith classes after (previous.toList ++ pending) := by
  have owners := written.owners_pending wf writable pending
  constructor
  · simpa only [written.objectKeys] using wf.objectKeys
  · simpa only [written.variableKeys] using wf.variableKeys
  · intro id data stored
    obtain ⟨oldData, oldStored, sameClass, sameFields⟩ := written.new_object_data stored
    obtain ⟨declaration, declared, shape, unique⟩ := wf.shapes id oldData oldStored
    exact ⟨declaration, sameClass ▸ declared, sameFields ▸ shape, unique⟩
  · intro id data stored
    obtain ⟨oldData, oldStored, _, _⟩ := written.new_object_data stored
    simpa only [written.nextId] using wf.bounds id oldData oldStored
  · intro id allocated
    have oldAllocated : Allocated before id := by
      simpa only [Allocated, written.objectKeys] using allocated
    exact written.liveWith wf writable (wf.rooted id oldAllocated)
  · exact owners.pairwise wf.ownersCompatible compatible_symm
  · intro id
    have targets := (owners.map Reference.object).mem_iff (a := id)
    simp only [List.map_append, owners_targets] at targets
    have allocation : Allocated before id ↔ Allocated after id := by
      simp only [Allocated, written.objectKeys]
    simpa only [List.map_append] using
      targets.symm.trans ((wf.referencesComplete id).trans allocation)

end Dada.Assignment
