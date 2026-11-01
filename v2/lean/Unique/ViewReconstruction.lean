import Unique.ViewCanonical

namespace Dada.Unique.Typing

def normalizedChildBody (classes : ClassTable) (fuel : Nat) (entries : List Entry)
    (field : FieldName × ClassName) : List Entry :=
  let selected := entries.filterMap (Entry.dropPrefix [field.1])
  if selected.isEmpty then []
  else if selected.contains (.negative []) then [.negative []]
  else normalizeEntries classes fuel field.2 selected

theorem normalizedChild_eq_prepend (classes : ClassTable) (fuel : Nat) (entries : List Entry)
    (field : FieldName × ClassName) :
    normalizedChild classes fuel entries field =
      (normalizedChildBody classes fuel entries field).map (Entry.prepend [field.1]) := by
  unfold normalizedChild normalizedChildBody
  dsimp only
  split
  · rfl
  · split <;> rfl

@[simp] theorem Entry.dropPrefix_prepend_singleton (field other : FieldName) (entry : Entry) :
    (entry.prepend [other]).dropPrefix [field] = if field = other then some entry else none := by
  cases entry <;> simp [Entry.dropPrefix, Entry.prepend, Entry.path, List.isPrefixOf_cons_cons]

theorem selected_normalizedChild (classes : ClassTable) (fuel : Nat) (entries : List Entry)
    (field : FieldName × ClassName) (selected : FieldName) :
    (normalizedChild classes fuel entries field).filterMap (Entry.dropPrefix [selected]) =
      if selected = field.1 then normalizedChildBody classes fuel entries field else [] := by
  rw [normalizedChild_eq_prepend, List.filterMap_map]
  by_cases same : selected = field.1
  · subst selected
    simp only [Function.comp_def, Entry.dropPrefix_prepend_singleton, ↓reduceIte,
      List.filterMap_some]
  · simp [Function.comp_def, same]

private theorem select_flatMap_unique {fields : List (FieldName × ClassName)}
    (unique : (fields.map Prod.fst).Nodup)
    (selected : FieldName × ClassName) (member : selected ∈ fields)
    (body : FieldName × ClassName → List Entry) :
    (fields.flatMap fun field => if selected.1 = field.1 then body field else []) = body selected := by
  induction fields with
  | nil => simp at member
  | cons field rest ih =>
    have keys := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with rfl | later
    · simp only [List.flatMap_cons, ↓reduceIte]
      have empty : (rest.flatMap fun other => if selected.1 = other.1 then body other else []) = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro other present
        have different : selected.1 ≠ other.1 := by
          intro same
          exact keys.1 (List.mem_map.mpr ⟨other, present, same.symm⟩)
        simp [different]
      rw [empty, List.append_nil]
    · have different : selected.1 ≠ field.1 := by
        intro same
        exact keys.1 (List.mem_map.mpr ⟨selected, later, same⟩)
      simp only [List.flatMap_cons, different, ↓reduceIte, List.nil_append]
      exact ih keys.2 later

theorem normalizedChildren_select {fields : List (FieldName × ClassName)}
    (unique : (fields.map Prod.fst).Nodup)
    (field : FieldName × ClassName) (member : field ∈ fields)
    (classes : ClassTable) (fuel : Nat) (entries : List Entry) :
    (fields.flatMap (normalizedChild classes fuel entries)).filterMap (Entry.dropPrefix [field.1]) =
      normalizedChildBody classes fuel entries field := by
  rw [List.filterMap_flatMap]
  simp only [selected_normalizedChild]
  exact select_flatMap_unique unique field member _

theorem normalizedChildren_no_root (fields : List (FieldName × ClassName))
    (classes : ClassTable) (fuel : Nat) (entries : List Entry) :
    Entry.positive [] ∉ fields.flatMap (normalizedChild classes fuel entries) ∧
      Entry.negative [] ∉ fields.flatMap (normalizedChild classes fuel entries) := by
  constructor <;> intro member
  · obtain ⟨field, _, present⟩ := List.mem_flatMap.mp member
    obtain ⟨path, impossible⟩ := normalizedChild_prefix classes fuel entries field _ present
    contradiction
  · obtain ⟨field, _, present⟩ := List.mem_flatMap.mp member
    obtain ⟨path, impossible⟩ := normalizedChild_prefix classes fuel entries field _ present
    contradiction

theorem normalizeEntries_path_length {classes : ClassTable} {fuel : Nat}
    {name : ClassName} {entries : List Entry} {bound : Nat}
    (bounded : ∀ entry ∈ entries, entry.path.length ≤ bound) :
    ∀ entry ∈ normalizeEntries classes fuel name entries, entry.path.length ≤ bound := by
  induction fuel generalizing name entries bound with
  | zero =>
    intro entry member
    rw [normalizeEntries] at member
    split at member
    · simp only [List.mem_singleton] at member
      subst entry
      exact Nat.zero_le _
    · split at member
      · exact bounded entry member
      · split at member
        · simp only [List.mem_singleton] at member
          subst entry
          exact Nat.zero_le _
        · exact bounded entry member
  | succ fuel ih =>
    intro entry member
    rw [normalizeEntries] at member
    split at member
    · simp only [List.mem_singleton] at member
      subst entry
      exact Nat.zero_le _
    · split at member
      · exact bounded entry member
      · split at member
        · simp only [List.mem_singleton] at member
          subst entry
          exact Nat.zero_le _
        · dsimp only at member
          split at member
          · simp only [List.mem_singleton] at member
            subst entry
            exact Nat.zero_le _
          · obtain ⟨⟨field,target⟩, _, selectedMember⟩ := List.mem_flatMap.mp member
            dsimp only at selectedMember
            split at selectedMember
            · simp at selectedMember
            next nonempty =>
              have selectedBound : ∀ selected ∈ entries.filterMap (Entry.dropPrefix [field]),
                  selected.path.length + 1 ≤ bound := by
                intro selected present
                obtain ⟨original, originalMember, dropped⟩ := List.mem_filterMap.mp present
                have originalBound := bounded original originalMember
                rw [Entry.dropPrefix_eq_some dropped, Entry.path_prepend] at originalBound
                simpa [Nat.add_comm] using originalBound
              have positiveBound : 0 < bound := by
                cases selectedEq : entries.filterMap (Entry.dropPrefix [field]) with
                | nil => simp [selectedEq] at nonempty
                | cons first rest =>
                  have firstBound := selectedBound first (by simp [selectedEq])
                  omega
              split at selectedMember
              · simp only [List.mem_singleton] at selectedMember
                subst entry
                exact positiveBound
              · obtain ⟨result, resultMember, rfl⟩ := List.mem_map.mp selectedMember
                have resultBound := ih (bound := bound - 1)
                  (fun selected present => by have h := selectedBound selected present; omega)
                  result resultMember
                simp only [Entry.path_prepend, List.length_append, List.length_singleton]
                omega

theorem empty_class_entries {classes : ClassTable} {name : ClassName} {declaration : TypedClass}
    {entries : List Entry} (found : classes.lookup name = some declaration)
    (noFields : declaration.fields = [])
    (valid : entries.all (Entry.valid classes name) = true)
    (noPositiveRoot : Entry.positive [] ∉ entries) : entries = [] := by
  cases entries with
  | nil => rfl
  | cons entry rest =>
    have entryValid := List.all_eq_true.mp valid entry (by simp)
    cases entry with
    | positive path =>
      cases path with
      | nil => exact False.elim (noPositiveRoot (by simp))
      | cons field rest => simp [Entry.valid, Entry.path, classAt, found, noFields] at entryValid
    | negative path =>
      cases path with
      | nil => simp [Entry.valid] at entryValid
      | cons field rest => simp [Entry.valid, Entry.path, classAt, found, noFields] at entryValid

end Dada.Unique.Typing
