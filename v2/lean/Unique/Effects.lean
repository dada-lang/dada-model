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

theorem Take.stored_or (taken : Take before place removed after)
    (stored : Stored before source (some target)) :
    target = removed ∨ Stored after source (some target) := by
  cases taken with
  | «variable» objects next leading suffix name object =>
    cases source with
    | «variable» other =>
      simp only [Stored, List.mem_append, List.mem_cons, Prod.mk.injEq, Option.some.injEq] at stored ⊢
      rcases stored with h | ⟨_, rfl⟩ | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr h))
    | field parent name => exact Or.inr stored
  | field variables next leading suffix parent className before after name object =>
    cases source with
    | «variable» other => exact Or.inr stored
    | field id field =>
      obtain ⟨data, member, atField⟩ := stored
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with h | h | h
      · exact Or.inr ⟨data, List.mem_append_left _ h, atField⟩
      · cases h
        simp only [List.mem_append, List.mem_cons, Prod.mk.injEq, Option.some.injEq] at atField
        rcases atField with h | ⟨_, rfl⟩ | h
        · exact Or.inr ⟨⟨className, before ++ (name, none) :: after⟩, by simp, List.mem_append_left _ h⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨⟨className, before ++ (name, none) :: after⟩, by simp, List.mem_append_right _ (List.mem_cons_of_mem _ h)⟩
      · exact Or.inr ⟨data, List.mem_append_right _ (List.mem_cons_of_mem _ h), atField⟩

theorem Take.liveWith (taken : Take before place removed after)
    (live : LiveWith before pending object) : LiveWith after (removed :: pending) object := by
  induction live with
  | pending member => exact .pending (List.mem_cons_of_mem _ member)
  | «variable» member =>
    rcases taken.stored_or (show Stored before (.variable _) _ from member) with rfl | kept
    · exact .pending (by simp)
    · exact .variable kept
  | field _ member field ih =>
    rcases taken.stored_or (show Stored before (.field _ _) _ from ⟨_, member, field⟩) with rfl | kept
    · exact .pending (by simp)
    · obtain ⟨data, member, field⟩ := kept
      exact .field ih member field

end Dada.Unique
