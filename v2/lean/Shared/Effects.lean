import Shared.Step

namespace Dada.Shared

-- Taking a reference never changes an object's class or field domain. Every
-- owner remaining in a field was already present in that same field.
theorem Take.object_data {before after : State} {place : StoragePlace} {object : ObjectId}
    (taken : Take before place object after) (id : ObjectId) (data : Object)
    (stored : (id, data) ∈ after.objects) :
    ∃ oldData, (id, oldData) ∈ before.objects ∧
      data.className = oldData.className ∧
      data.fields.map Prod.fst = oldData.fields.map Prod.fst ∧
      ∀ name target, (name, some target) ∈ data.fields →
        (name, some target) ∈ oldData.fields := by
  cases taken with
  | «variable» objects nextId leading suffix name object =>
    exact ⟨data, stored, rfl, rfl, fun _ _ member => member⟩
  | field variables nextId leadingObjects trailingObjects parent className
      leadingFields trailingFields fieldName object =>
    simp only [List.mem_append, List.mem_cons] at stored
    rcases stored with unchanged | changed | unchanged
    · exact ⟨data, List.mem_append_left _ unchanged, rfl, rfl, fun _ _ member => member⟩
    · cases changed
      refine ⟨⟨className, leadingFields ++ (fieldName, some (.owned object)) :: trailingFields⟩,
        ?_, rfl, ?_, ?_⟩
      · simp
      · simp
      · intro name target member
        simp only [List.mem_append, List.mem_cons] at member ⊢
        rcases member with member | impossible | member
        · exact Or.inl member
        · have : some target = none := congrArg Prod.snd impossible
          contradiction
        · exact Or.inr (Or.inr member)
    · exact ⟨data, List.mem_append_right _ (List.mem_cons_of_mem _ unchanged),
        rfl, rfl, fun _ _ member => member⟩

-- Promotion preserves every field target, while changing a unique final
-- reference into shared ownership at the same slot.
theorem Promote.object_data {before after : State} {place : StoragePlace} {object : ObjectId}
    (promoted : Promote before place object after) (id : ObjectId) (data : Object)
    (stored : (id, data) ∈ after.objects) :
    ∃ oldData, (id, oldData) ∈ before.objects ∧
      data.className = oldData.className ∧
      data.fields.map Prod.fst = oldData.fields.map Prod.fst ∧
      ∀ name target, (name, some target) ∈ data.fields →
        ∃ oldTarget, (name, some oldTarget) ∈ oldData.fields ∧ target.object = oldTarget.object := by
  cases promoted with
  | «variable» objects nextId leading suffix name object =>
    exact ⟨data, stored, rfl, rfl, fun _ target member => ⟨target, member, rfl⟩⟩
  | field variables nextId leadingObjects trailingObjects parent className
      leadingFields trailingFields fieldName object =>
    simp only [List.mem_append, List.mem_cons] at stored
    rcases stored with unchanged | changed | unchanged
    · exact ⟨data, List.mem_append_left _ unchanged, rfl, rfl,
        fun _ target member => ⟨target, member, rfl⟩⟩
    · cases changed
      refine ⟨⟨className, leadingFields ++ (fieldName, some (.owned object)) :: trailingFields⟩,
        ?_, rfl, ?_, ?_⟩
      · simp
      · simp
      · intro name target member
        simp only [List.mem_append, List.mem_cons] at member
        rcases member with member | promotedField | member
        · exact ⟨target, List.mem_append_left _ member, rfl⟩
        · cases promotedField
          exact ⟨.owned object, by simp, rfl⟩
        · exact ⟨target, List.mem_append_right _ (List.mem_cons_of_mem _ member), rfl⟩
    · exact ⟨data, List.mem_append_right _ (List.mem_cons_of_mem _ unchanged),
        rfl, rfl, fun _ target member => ⟨target, member, rfl⟩⟩

end Dada.Shared
