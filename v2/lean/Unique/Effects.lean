import Unique.Step

namespace Dada.Unique

theorem Take.updated (take : Take before place object after) :
    Updated before place none after := by
  cases take with
  | «variable» => exact .variable ..
  | field => exact .field ..

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
      refine ⟨⟨className, leadingFields ++ (fieldName, some object) :: trailingFields⟩,
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

end Dada.Unique
