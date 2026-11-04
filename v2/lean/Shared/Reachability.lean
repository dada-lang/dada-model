import Shared.Effects

namespace Dada.Shared

-- Temporary values are roots just like local variables. Reachability does not
-- constrain allocation order and permits cycles among shared objects.
inductive LiveWith (state : State) (pending : List Reference) : ObjectId → Prop where
  | pending {reference} : reference ∈ pending → LiveWith state pending reference.object
  | variable {name reference} : (name, some reference) ∈ state.variables →
      LiveWith state pending reference.object
  | field {parent data name reference} : LiveWith state pending parent →
      (parent, data) ∈ state.objects → (name, some reference) ∈ data.fields →
      LiveWith state pending reference.object

theorem Live.with_pending (live : Live state object) : LiveWith state pending object := by
  induction live with
  | «variable» member => exact .variable member
  | field _ stored field ih => exact .field ih stored field

theorem LiveWith.to_live (live : LiveWith state [] object) : Live state object := by
  induction live with
  | pending member => simp at member
  | «variable» member => exact .variable member
  | field _ stored field ih => exact .field ih stored field

theorem LiveWith.transport {pending other : List Reference} (live : LiveWith before pending object)
    (roots : ∀ reference ∈ pending, LiveWith after other reference.object)
    (variables : ∀ name reference, (name, some reference) ∈ before.variables →
      LiveWith after other reference.object)
    (fields : ∀ parent data name reference, (parent, data) ∈ before.objects →
      (name, some reference) ∈ data.fields → LiveWith after other parent →
      LiveWith after other reference.object) : LiveWith after other object := by
  induction live with
  | pending member => exact roots _ member
  | «variable» member => exact variables _ _ member
  | field _ stored field ih => exact fields _ _ _ _ stored field ih

theorem LiveWith.pending_mono {pending other : List Reference} (live : LiveWith state pending object)
    (roots : ∀ reference ∈ pending, ∃ otherReference ∈ other, otherReference.object = reference.object) :
    LiveWith state other object := by
  apply live.transport
  · intro reference member
    obtain ⟨target, present, same⟩ := roots reference member
    exact same ▸ LiveWith.pending present
  · exact fun _ _ member => .variable member
  · exact fun _ _ _ _ stored field live => .field live stored field

theorem LiveWith.perm {pending other : List Reference} (live : LiveWith state pending object) (perm : pending.Perm other) :
    LiveWith state other object :=
  live.pending_mono (fun ref member => ⟨ref, perm.mem_iff.mp member, rfl⟩)

theorem LiveWith.bind (live : LiveWith state [reference] object) :
    Live (state.bind name reference) object := by
  apply LiveWith.to_live
  apply live.transport
  · intro ref member
    have same : ref = reference := by simpa using member
    cases same
    exact .variable (name := name) (by simp [State.bind])
  · intro var ref member
    exact .variable (name := var) (by simp [State.bind, member])
  · exact fun _ _ _ _ stored field live => .field live stored field

private theorem Take.variable_forward (take : Take before place removed after)
    (member : (name, some reference) ∈ before.variables) :
    reference.object = removed ∨ (name, some reference) ∈ after.variables := by
  cases take with
  | «variable» objects next leading suffix name removed =>
    simp only [List.mem_append, List.mem_cons] at member ⊢
    rcases member with h | h | h
    · exact Or.inr (Or.inl h)
    · cases h; exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr h))
  | field => exact Or.inr member

private theorem Take.field_forward (take : Take before place removed after)
    (stored : (parent, data) ∈ before.objects) (field : (name, some reference) ∈ data.fields) :
    reference.object = removed ∨
      ∃ newData, (parent, newData) ∈ after.objects ∧ (name, some reference) ∈ newData.fields := by
  cases take with
  | «variable» => exact Or.inr ⟨data, stored, field⟩
  | field variables next leading trailing owner cls leadingFields suffix fieldName removed =>
    simp only [List.mem_append, List.mem_cons] at stored
    rcases stored with h | h | h
    · exact Or.inr ⟨data, by simp [h], field⟩
    · cases h
      simp only [List.mem_append, List.mem_cons] at field
      rcases field with h | h | h
      · exact Or.inr ⟨⟨cls, leadingFields ++ (fieldName, none) :: suffix⟩, by simp, by simp [h]⟩
      · cases h; exact Or.inl rfl
      · exact Or.inr ⟨⟨cls, leadingFields ++ (fieldName, none) :: suffix⟩, by simp, by simp [h]⟩
    · exact Or.inr ⟨data, by simp [h], field⟩

theorem Take.liveWith (take : Take before place removed after)
    (live : LiveWith before pending object) : LiveWith after (.owned removed :: pending) object := by
  apply live.transport
  · intro ref member; exact .pending (List.mem_cons_of_mem _ member)
  · intro name reference member
    rcases take.variable_forward member with same | stored
    · exact same.symm ▸ (LiveWith.pending (reference := .owned removed) (List.mem_cons_self ..))
    · exact .variable stored
  · intro parent data name reference stored field parentLive
    rcases take.field_forward stored field with same | ⟨newData, newStored, newField⟩
    · exact same.symm ▸ (LiveWith.pending (reference := .owned removed) (List.mem_cons_self ..))
    · exact .field parentLive newStored newField

private theorem Promote.variable_forward (promotion : Promote before place object after)
    (member : (name, some reference) ∈ before.variables) :
    ∃ newReference, (name, some newReference) ∈ after.variables ∧ newReference.object = reference.object := by
  cases promotion with
  | «variable» objects next leading suffix var object =>
    simp only [List.mem_append, List.mem_cons] at member
    rcases member with h | h | h
    · exact ⟨reference, by simp [h], rfl⟩
    · cases h; exact ⟨.shared object, by simp, rfl⟩
    · exact ⟨reference, by simp [h], rfl⟩
  | field => exact ⟨reference, member, rfl⟩

private theorem Promote.field_forward (promotion : Promote before place object after)
    (stored : (parent, data) ∈ before.objects) (field : (name, some reference) ∈ data.fields) :
    ∃ newData newReference, (parent, newData) ∈ after.objects ∧
      (name, some newReference) ∈ newData.fields ∧ newReference.object = reference.object := by
  cases promotion with
  | «variable» => exact ⟨data, reference, stored, field, rfl⟩
  | field variables next leading trailing owner cls leadingFields suffix fieldName object =>
    simp only [List.mem_append, List.mem_cons] at stored
    rcases stored with h | h | h
    · exact ⟨data, reference, by simp [h], field, rfl⟩
    · cases h
      simp only [List.mem_append, List.mem_cons] at field
      rcases field with h | h | h
      · exact ⟨⟨cls, leadingFields ++ (fieldName, some (.shared object)) :: suffix⟩, reference, by simp, by simp [h], rfl⟩
      · cases h; exact ⟨⟨cls, leadingFields ++ (name, some (.shared object)) :: suffix⟩, .shared object, by simp, by simp, rfl⟩
      · exact ⟨⟨cls, leadingFields ++ (fieldName, some (.shared object)) :: suffix⟩, reference, by simp, by simp [h], rfl⟩
    · exact ⟨data, reference, by simp [h], field, rfl⟩

theorem Promote.liveWith (promotion : Promote before place object after)
    (live : LiveWith before pending target) : LiveWith after pending target := by
  apply live.transport
  · exact fun _ member => .pending member
  · intro name reference member
    obtain ⟨newReference, stored, same⟩ := promotion.variable_forward member
    exact same ▸ LiveWith.variable stored
  · intro parent data name reference stored field parentLive
    obtain ⟨newData, newReference, newStored, newField, same⟩ := promotion.field_forward stored field
    exact same ▸ LiveWith.field parentLive newStored newField

theorem Give.liveWith (give : Give before path reference after)
    (live : LiveWith before pending object) : LiveWith after (reference :: pending) object := by
  cases give with
  | move _ taken => exact taken.liveWith live
  | copy => exact live.pending_mono (fun ref member => ⟨ref, List.mem_cons_of_mem _ member, rfl⟩)
  | promote _ promoted =>
    exact (promoted.liveWith live).pending_mono (fun ref member => ⟨ref, List.mem_cons_of_mem _ member, rfl⟩)

end Dada.Shared
