import Unique.ViewReconstruction

namespace Dada.Unique.Typing

private theorem normalizeEntries_whole (classes : ClassTable) (fuel : Nat) (name : ClassName) :
    normalizeEntries classes fuel name [.positive []] = [.positive []] := by
  rw [normalizeEntries]
  simp

private theorem normalizeEntries_empty {classes : ClassTable} {fuel : Nat} {name : ClassName}
    {declaration : TypedClass} (found : classes.lookup name = some declaration) :
    normalizeEntries classes fuel name [] =
      if declaration.fields.isEmpty then [.positive []] else [] := by
  rw [normalizeEntries]
  simp only [List.contains_nil, Bool.false_eq_true, ↓reduceIte, found,
    List.isEmpty_nil, Bool.and_true]
  split
  · rfl
  next nonempty =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      dsimp only
      simp only [List.filterMap_nil, List.isEmpty_nil, ↓reduceIte]
      have emptyChildren : declaration.fields.flatMap (fun _ => ([] : List Entry)) = [] :=
        List.flatMap_eq_nil_iff.mpr (by simp)
      rw [emptyChildren]
      have absent : declaration.fields.all (fun _ => false) = false := by
        apply List.all_eq_false.mpr
        obtain ⟨field, member⟩ := List.exists_mem_of_ne_nil declaration.fields
          (fun eq => nonempty (by simp [eq]))
        exact ⟨field, member, by simp⟩
      simp only [List.contains_nil, absent, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

private def Stable (classes : ClassTable) (name : ClassName) (entries : List Entry) : Prop :=
  ∀ fuel, (∀ entry ∈ entries, entry.path.length < fuel) →
    normalizeEntries classes fuel name entries = entries

private theorem stable_whole (classes : ClassTable) (name : ClassName) :
    Stable classes name [.positive []] := by
  intro fuel _
  exact normalizeEntries_whole _ _ _

private theorem lookup_mem {K V : Type} [BEq K] [LawfulBEq K]
    {entries : List (K × V)} {key : K} {value : V}
    (found : entries.lookup key = some value) : (key, value) ∈ entries := by
  obtain ⟨before, after, rfl, _⟩ := List.lookup_eq_some_iff.mp found
  simp

private theorem lookup_member {K V : Type} [BEq K] [LawfulBEq K]
    {entries : List (K × V)} {key : K} {value : V}
    (unique : (entries.map Prod.fst).Nodup) (member : (key, value) ∈ entries) :
    entries.lookup key = some value := by
  induction entries with
  | nil => simp at member
  | cons entry rest ih =>
    rcases entry with ⟨head, data⟩
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with same | later
    · cases same; simp
    · have different : key ≠ head := by
        intro same
        exact unique.1 (List.mem_map.mpr ⟨_, later, same⟩)
      rw [List.lookup_cons, show (key == head) = false from beq_eq_false_iff_ne.mpr different]
      exact ih unique.2 later

private theorem normalizedChild_stable {classes : ClassTable} {firstFuel secondFuel : Nat}
    {fields : List (FieldName × ClassName)} {entries : List Entry}
    (unique : (fields.map Prod.fst).Nodup)
    {field : FieldName × ClassName} (member : field ∈ fields)
    (stable : (entries.filterMap (Entry.dropPrefix [field.1])).isEmpty ≠ true →
      (entries.filterMap (Entry.dropPrefix [field.1])).contains (.negative []) ≠ true →
      Stable classes field.2
        (normalizeEntries classes firstFuel field.2 (entries.filterMap (Entry.dropPrefix [field.1]))))
    (bounded : ∀entry ∈ fields.flatMap (normalizedChild classes firstFuel entries),
      entry.path.length < secondFuel + 1) :
    normalizedChild classes secondFuel
      (fields.flatMap (normalizedChild classes firstFuel entries)) field =
      normalizedChild classes firstFuel entries field := by
  have selected := normalizedChildren_select unique field member classes firstFuel entries
  generalize childrenEq : fields.flatMap (normalizedChild classes firstFuel entries) = children at *
  unfold normalizedChild
  dsimp only
  rw [selected]
  unfold normalizedChildBody
  dsimp only
  split
  · simp
  next notEmpty =>
    split
    · simp
    next noRoot =>
      split
      next empty =>
        have empty := List.isEmpty_iff.mp empty
        simp [empty]
      next =>
        split
        next impossible =>
          exact False.elim (noRoot (List.contains_iff_mem.mpr
            (normalizeEntries_negative (List.contains_iff_mem.mp impossible))))
        next =>
          rw [stable notEmpty noRoot secondFuel]
          intro entry entryMember
          have childMember : entry.prepend [field.1] ∈ normalizedChild classes firstFuel entries field := by
            unfold normalizedChild
            dsimp only
            split
            next empty =>
              have empty := List.isEmpty_iff.mp empty
              simp [empty] at *
            next =>
              exact List.mem_map.mpr ⟨entry, entryMember, rfl⟩
          have bound := bounded (entry.prepend [field.1]) (by
            rw [←childrenEq]
            exact List.mem_flatMap.mpr ⟨field, member, childMember⟩)
          simp only [Entry.path_prepend, List.length_append, List.length_singleton] at bound
          omega


private theorem flatMap_congr_member {A B : Type} {entries : List A} {left right : A → List B}
    (equal : ∀entry ∈ entries, left entry = right entry) :
    entries.flatMap left = entries.flatMap right := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [List.flatMap_cons]
    rw [equal entry (by simp), ih (fun other member => equal other (by simp [member]))]

private theorem normalizeEntries_stable {classes : ClassTable} (classesWF : classes.WellFormed)
    (fuel : Nat) {name : ClassName} {entries : List Entry}
    (declared : (classes.lookup name).isSome = true)
    (valid : entries.all (Entry.valid classes name) = true)
    (disjoint : entriesDisjoint entries = true)
    (bounded : ∀ entry ∈ entries, entry.path.length < fuel) :
    Stable classes name (normalizeEntries classes fuel name entries) := by
  induction fuel generalizing name entries with
  | zero =>
    have empty : entries = [] := by
      cases entries with
      | nil => rfl
      | cons entry rest => have impossible := bounded entry (by simp); omega
    subst entries
    cases found : classes.lookup name with
    | none => simp [found] at declared
    | some declaration =>
      rw [normalizeEntries_empty found]
      split
      · exact stable_whole _ _
      next nonempty =>
        intro secondFuel _
        rw [normalizeEntries_empty found]
        simp [nonempty]
  | succ fuel ih =>
    rw [normalizeEntries]
    split
    · exact stable_whole _ _
    next noWhole =>
      cases found : classes.lookup name with
      | none => simp [found] at declared
      | some declaration =>
        dsimp only
        split
        · exact stable_whole _ _
        next notEmpty =>
          have declarationMember := lookup_mem found
          have fieldsWF := classesWF.2 _ declarationMember
          have fieldsNonempty : declaration.fields.isEmpty = false := by
            apply Bool.eq_false_iff.mpr
            intro fieldsEmpty
            have entriesEmpty := empty_class_entries found (List.isEmpty_iff.mp fieldsEmpty)
              valid (fun h => noWhole (List.contains_iff_mem.mpr h))
            exact notEmpty (by simp [fieldsEmpty, entriesEmpty])
          have each : ∀ field ∈ declaration.fields,
              (entries.filterMap (Entry.dropPrefix [field.1])).isEmpty ≠ true →
              (entries.filterMap (Entry.dropPrefix [field.1])).contains (.negative []) ≠ true →
              Stable classes field.2 (normalizeEntries classes fuel field.2
                (entries.filterMap (Entry.dropPrefix [field.1]))) := by
            intro field member _ noNegative
            rcases field with ⟨field,target⟩
            have fieldFound := lookup_member fieldsWF.1 member
            have fieldClass : classAt classes name [field] = some target := by
              simp [classAt, found, fieldFound]
            obtain ⟨⟨_, targetDeclaration⟩, targetMember, same⟩ :=
              List.mem_map.mp (fieldsWF.2 _ member)
            simp only at same
            subst same
            apply ih
            · simp [lookup_member classesWF.1 targetMember]
            · exact selected_valid valid fieldClass
                (fun h => noNegative (List.contains_iff_mem.mpr h))
            · exact selected_disjoint disjoint field
            · intro entry selected
              obtain ⟨source, member, selected⟩ := List.mem_filterMap.mp selected
              have bound := bounded source member
              rw [Entry.dropPrefix_eq_some selected, Entry.path_prepend] at bound
              simpa using bound
          split
          · exact stable_whole _ _
          next notComplete =>
            change Stable classes name
              (declaration.fields.flatMap (normalizedChild classes fuel entries))
            intro secondFuel outputBound
            rw [normalizeEntries]
            have noRoot := (normalizedChildren_no_root declaration.fields classes fuel entries).1
            have noRootBool : (declaration.fields.flatMap (normalizedChild classes fuel entries)).contains
                (.positive []) = false := Bool.eq_false_iff.mpr
                  (fun h => noRoot (List.contains_iff_mem.mp h))
            rw [noRootBool]
            simp only [Bool.false_eq_true, ↓reduceIte, found, fieldsNonempty, Bool.false_and]
            cases secondFuel with
            | zero => rfl
            | succ secondFuel =>
              dsimp only
              have childrenEq : declaration.fields.flatMap (normalizedChild classes secondFuel
                    (declaration.fields.flatMap (normalizedChild classes fuel entries))) =
                  declaration.fields.flatMap (normalizedChild classes fuel entries) := by
                apply flatMap_congr_member
                intro field member
                exact normalizedChild_stable fieldsWF.1 member (each field member) outputBound
              change (if (!false && declaration.fields.all (fun field =>
                  (declaration.fields.flatMap (normalizedChild classes secondFuel
                    (declaration.fields.flatMap (normalizedChild classes fuel entries)))).contains
                      (.positive [field.1]))) = true then [.positive []]
                else declaration.fields.flatMap (normalizedChild classes secondFuel
                  (declaration.fields.flatMap (normalizedChild classes fuel entries)))) = _
              rw [childrenEq]
              apply ite_eq_right
              unfold normalizedChild
              simpa only [fieldsNonempty] using notComplete


theorem normalize_idempotent {classes : ClassTable} (classesWF : classes.WellFormed)
    {ty : ViewType} (wf : ty.WellFormed classes) :
    normalize classes (normalize classes ty) = normalize classes ty := by
  have stable := normalizeEntries_stable classesWF
    (ty.entries.foldl (fun depth entry => max depth entry.path.length) 0 + 1)
    wf.1 wf.2.1 wf.2.2 (fun entry member =>
      Nat.lt_succ_of_le ((entryDepth_bounds ty.entries 0).2 entry member))
  have eq := stable ((normalize classes ty).entries.foldl
    (fun depth entry => max depth entry.path.length) 0 + 1) (fun entry member =>
      Nat.lt_succ_of_le ((entryDepth_bounds (normalize classes ty).entries 0).2 entry member))
  exact congrArg (ViewType.mk ty.className) eq

end Dada.Unique.Typing
