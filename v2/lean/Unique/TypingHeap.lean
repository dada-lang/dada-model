import Unique.TypingRealization

namespace Dada.Unique.Typing

theorem lookup_member {Key Value : Type} [BEq Key] [LawfulBEq Key]
    {entries : List (Key × Value)} {key : Key} {value : Value}
    (found : entries.lookup key = some value) : (key, value) ∈ entries := by
  obtain ⟨before, after, rfl, _⟩ := List.lookup_eq_some_iff.mp found
  simp

theorem lookup_of_member {Key Value : Type} [BEq Key] [LawfulBEq Key]
    {entries : List (Key × Value)} {key : Key} {value : Value}
    (distinct : (entries.map Prod.fst).Nodup) (member : (key, value) ∈ entries) :
    entries.lookup key = some value := by
  induction entries with
  | nil => simp at member
  | cons entry entries ih =>
    rcases entry with ⟨entryKey, entryValue⟩
    rcases List.nodup_cons.mp distinct with ⟨fresh, distinct⟩
    rcases List.mem_cons.mp member with same | member
    · cases same
      simp
    · have different : key ≠ entryKey := by
        intro same
        exact fresh (same ▸ List.mem_map.mpr ⟨(key, value), member, rfl⟩)
      simpa [List.lookup_cons, show (key == entryKey) = false from beq_eq_false_iff_ne.mpr different] using ih distinct member

theorem member_value_unique {Key Value : Type} [BEq Key] [LawfulBEq Key]
    {entries : List (Key × Value)} {key : Key} {first second : Value}
    (distinct : (entries.map Prod.fst).Nodup)
    (left : (key, first) ∈ entries) (right : (key, second) ∈ entries) : first = second := by
  exact Option.some.inj ((lookup_of_member distinct left).symm.trans
    (lookup_of_member distinct right))

theorem readPath_root_allocated (read : readPath state object path = some slot) :
    ∃ data, (object, data) ∈ state.objects := by
  cases path <;> cases found : state.objects.lookup object <;>
    simp [readPath, found] at read
  all_goals exact ⟨_, lookup_member found⟩

theorem readPath_cons (read : readPath state object (field :: rest) = some slot) :
    ∃ data fieldSlot, (object, data) ∈ state.objects ∧
      (field, fieldSlot) ∈ data.fields ∧
      (rest = [] ∧ fieldSlot = slot ∨
        ∃ target, fieldSlot = some target ∧ readPath state target rest = some slot) := by
  cases objectFound : state.objects.lookup object with
  | none => simp [readPath, objectFound] at read
  | some data =>
    cases fieldFound : data.fields.lookup field with
    | none => simp [readPath, objectFound, fieldFound] at read
    | some fieldSlot =>
      refine ⟨data, fieldSlot, lookup_member objectFound, lookup_member fieldFound, ?_⟩
      cases rest with
      | nil => exact Or.inl ⟨rfl, by simpa [readPath, objectFound, fieldFound] using read⟩
      | cons next rest =>
        cases fieldSlot with
        | none => simp [readPath, objectFound, fieldFound] at read
        | some target =>
          exact Or.inr ⟨target, rfl, by simpa [readPath, objectFound, fieldFound] using read⟩

theorem resolve_follow (resolved : Resolve state base source object)
    (read : readPath state object path = some (some target)) :
    ∃ destination, Resolve state (path.foldl Place.field base) destination target := by
  induction path generalizing base source object with
  | nil =>
    cases found : state.objects.lookup object <;> simp [readPath, found] at read
    subst target
    exact ⟨source, resolved⟩
  | cons field rest ih =>
    obtain ⟨data, slot, stored, atField, final | ⟨next, rfl, more⟩⟩ := readPath_cons read
    · rcases final with ⟨rfl, rfl⟩
      exact ⟨.field object field, .field resolved stored atField⟩
    · exact ih (.field resolved stored atField) more

theorem resolve_from_readPath (root : (name, some object) ∈ state.variables)
    (read : readPath state object path = some (some target)) :
    ∃ destination, Resolve state (placeFrom name path) destination target :=
  resolve_follow (.variable root) read

theorem WellFormedWith.field_allocated (wf : WellFormedWith classes state pending)
    (stored : (parent, data) ∈ state.objects) (field : (name, some object) ∈ data.fields) :
    Allocated state object := by
  apply (wf.referencesComplete object).mp
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨(parent, data), stored, List.mem_filterMap.mpr ⟨(name, some object), field, rfl⟩⟩))

theorem readPath_target_allocated (wf : WellFormedWith classes state pending)
    (read : readPath state object path = some (some target)) : Allocated state target := by
  induction path generalizing object with
  | nil =>
    cases found : state.objects.lookup object <;> simp [readPath, found] at read
    subst target
    exact List.mem_map.mpr ⟨_, lookup_member found, rfl⟩
  | cons field rest ih =>
    obtain ⟨data, slot, stored, atField, final | ⟨next, rfl, more⟩⟩ := readPath_cons read
    · rcases final with ⟨rfl, rfl⟩
      exact WellFormedWith.field_allocated wf stored atField
    · exact ih more

theorem readPath_nil_of_allocated (wf : WellFormedWith classes state pending)
    (allocated : Allocated state object) : readPath state object [] = some (some object) := by
  obtain ⟨⟨id, data⟩, stored, same⟩ := List.mem_map.mp allocated
  simp only at same
  subst id
  simp [readPath, lookup_of_member wf.objectKeys stored]

theorem readPath_append (wf : WellFormedWith classes state pending)
    (read : readPath state object path = some (some target)) (suffix : Path) :
    readPath state object (path ++ suffix) = readPath state target suffix := by
  induction path generalizing object with
  | nil =>
    cases found : state.objects.lookup object <;> simp [readPath, found] at read
    subst target
    rfl
  | cons field rest ih =>
    cases objectFound : state.objects.lookup object with
    | none => simp [readPath, objectFound] at read
    | some data =>
      cases fieldFound : data.fields.lookup field with
      | none => simp [readPath, objectFound, fieldFound] at read
      | some slot =>
        cases rest with
        | nil =>
          have same : slot = some target := by
            simpa [readPath, objectFound, fieldFound] using read
          subst slot
          cases suffix with
          | nil =>
            simpa using read.trans (readPath_nil_of_allocated wf
              (readPath_target_allocated wf read)).symm
          | cons next suffix => simp [readPath, objectFound, fieldFound]
        | cons next rest =>
          cases slot with
          | none => simp [readPath, objectFound, fieldFound] at read
          | some child =>
            have tailRead : readPath state child (next :: rest) = some (some target) := by
              simpa [readPath, objectFound, fieldFound] using read
            simpa [readPath, objectFound, fieldFound] using ih tailRead

theorem readPath_append_inv (wf : WellFormedWith classes state pending)
    (nonempty : suffix ≠ [])
    (read : readPath state object (path ++ suffix) = some slot) :
    ∃ target, readPath state object path = some (some target) ∧
      readPath state target suffix = some slot := by
  induction path generalizing object with
  | nil =>
    obtain ⟨data, stored⟩ := readPath_root_allocated read
    exact ⟨object, by simp [readPath, lookup_of_member wf.objectKeys stored], read⟩
  | cons field rest ih =>
    obtain ⟨data, fieldSlot, stored, atField, final | ⟨child, rfl, more⟩⟩ := readPath_cons read
    · have empty : rest = [] ∧ suffix = [] := by simpa using final.1
      have impossible : suffix = [] := empty.2
      exact False.elim (nonempty impossible)
    · obtain ⟨target, prefixRead, suffixRead⟩ := ih more
      have fieldKeys : (data.fields.map Prod.fst).Nodup := by
        obtain ⟨declaration, _, same, distinct⟩ := wf.shapes object data stored
        exact same ▸ distinct
      have firstRead : readPath state object [field] = some (some child) := by
        simp [readPath, lookup_of_member wf.objectKeys stored,
          lookup_of_member fieldKeys atField]
      exact ⟨target, (readPath_append wf firstRead rest).trans prefixRead, suffixRead⟩

end Dada.Unique.Typing

namespace Dada.Unique

theorem Resolve.stored (resolved : Resolve state place source object) :
    Stored state source (some object) := by
  cases resolved with
  | «variable» stored => exact stored
  | field _ stored field => exact ⟨_, stored, field⟩

theorem Stored.take_exists (stored : Stored state source (some object)) :
    ∃ after, Take state source object after := by
  cases state with
  | mk objects variables nextId =>
    cases source with
    | «variable» name =>
      obtain ⟨before, after, equality⟩ := List.mem_iff_append.mp stored
      dsimp at equality
      subst variables
      exact ⟨_, .variable ..⟩
    | field parent name =>
      obtain ⟨⟨className, fields⟩, stored, field⟩ := stored
      obtain ⟨before, after, equality⟩ := List.mem_iff_append.mp stored
      obtain ⟨leading, suffix, fieldsEquality⟩ := List.mem_iff_append.mp field
      dsimp at equality fieldsEquality
      subst objects fields
      exact ⟨_, .field ..⟩

theorem Resolve.take_exists (resolved : Resolve state place source object) :
    ∃ after, Take state source object after := resolved.stored.take_exists

theorem Take.stored (taken : Take before place object after) :
    Stored before place (some object) := by
  cases taken with
  | «variable» => simp [Stored]
  | field variables nextId leading trailing parent className beforeFields afterFields name object =>
    exact ⟨⟨className, beforeFields ++ (name, some object) :: afterFields⟩, by simp, by simp⟩

theorem Take.cleared (taken : Take before place object after) : Stored after place none := by
  cases taken with
  | «variable» => simp [Stored]
  | field variables nextId leading trailing parent className beforeFields afterFields name object =>
    exact ⟨⟨className, beforeFields ++ (name, none) :: afterFields⟩, by simp, by simp⟩

theorem Take.stored_unchanged (taken : Take before source object after)
    (different : place ≠ source) (stored : Stored before place slot) :
    Stored after place slot := by
  cases taken with
  | «variable» objects nextId leading trailing name object =>
    cases place with
    | «variable» other =>
      simp only [Stored, List.mem_append, List.mem_cons] at stored ⊢
      rcases stored with member | same | member
      · exact Or.inl member
      · cases same
        exact False.elim (different rfl)
      · exact Or.inr (Or.inr member)
    | field parent fieldName => exact stored
  | field variables nextId leading trailing parent className beforeFields afterFields name object =>
    cases place with
    | «variable» other => exact stored
    | field other otherField =>
      obtain ⟨data, atObject, atField⟩ := stored
      simp only [List.mem_append, List.mem_cons] at atObject
      rcases atObject with member | same | member
      · exact ⟨data, List.mem_append_left _ member, atField⟩
      · cases same
        refine ⟨⟨className, beforeFields ++ (name, none) :: afterFields⟩, by simp, ?_⟩
        simp only [List.mem_append, List.mem_cons] at atField ⊢
        rcases atField with member | same | member
        · exact Or.inl member
        · cases same
          exact False.elim (different rfl)
        · exact Or.inr (Or.inr member)
      · exact ⟨data, List.mem_append_right _ (List.mem_cons_of_mem _ member), atField⟩

-- Taking changes only one slot: the allocation identities and nominal classes
-- of all objects remain available, including the object just taken.
theorem Take.old_object_data (taken : Take before place object after)
    (id : ObjectId) (data : Object) (stored : (id, data) ∈ before.objects) :
    ∃ newData, (id, newData) ∈ after.objects ∧ newData.className = data.className := by
  cases taken with
  | «variable» => exact ⟨data, stored, rfl⟩
  | field variables nextId leading trailing parent className beforeFields afterFields name object =>
    simp only [List.mem_append, List.mem_cons] at stored
    rcases stored with member | same | member
    · exact ⟨data, List.mem_append_left _ member, rfl⟩
    · cases same
      exact ⟨⟨className, beforeFields ++ (name, none) :: afterFields⟩, by simp, rfl⟩
    · exact ⟨data, List.mem_append_right _ (List.mem_cons_of_mem _ member), rfl⟩

end Dada.Unique

namespace Dada.Unique.Typing

theorem stored_value_unique (wf : WellFormedWith classes state pending)
    (first : Stored state place left) (second : Stored state place right) : left = right := by
  cases place with
  | «variable» name => exact member_value_unique wf.variableKeys first second
  | field parent name =>
    obtain ⟨firstData, firstObject, firstField⟩ := first
    obtain ⟨secondData, secondObject, secondField⟩ := second
    have same := member_value_unique wf.objectKeys firstObject secondObject
    subst secondData
    obtain ⟨declaration, _, sameFields, distinct⟩ := wf.shapes parent firstData firstObject
    exact member_value_unique (sameFields ▸ distinct) firstField secondField

theorem readPath_singleton_of_stored (wf : WellFormedWith classes state pending)
    (stored : Stored state (.field parent name) slot) : readPath state parent [name] = some slot := by
  obtain ⟨data, atObject, atField⟩ := stored
  obtain ⟨declaration, _, sameFields, distinct⟩ := wf.shapes parent data atObject
  simp [readPath, lookup_of_member wf.objectKeys atObject,
    lookup_of_member (sameFields ▸ distinct) atField]

theorem FieldsMatchClasses.take (fields : FieldsMatchClasses classes before)
    (taken : Take before place object after) : FieldsMatchClasses classes after := by
  intro parent data field target stored atField
  obtain ⟨oldData, oldStored, sameClass, _, remaining⟩ := taken.object_data parent data stored
  obtain ⟨declaration, targetClass, targetData, declared, fieldDeclared, targetStored, targetName⟩ :=
    fields parent oldData field target oldStored (remaining field target atField)
  obtain ⟨newData, newStored, newClass⟩ := taken.old_object_data target targetData targetStored
  exact ⟨declaration, targetClass, newData, sameClass ▸ declared, fieldDeclared,
    newStored, newClass.trans targetName⟩

end Dada.Unique.Typing
