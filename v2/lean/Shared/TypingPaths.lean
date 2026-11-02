import Shared.Soundness

namespace Dada.Shared.Typing

-- A reference returned by a path carries the permission of the entire route.
def enter (permission : Mode) (reference : Reference) : Reference :=
  ⟨permission.join reference.mode, reference.object⟩

section EnterProperties

@[simp] theorem enter_mode (permission : Mode) (reference : Reference) :
    (enter permission reference).mode = permission.join reference.mode := rfl

@[simp] theorem enter_object (permission : Mode) (reference : Reference) :
    (enter permission reference).object = reference.object := rfl

@[simp] theorem enter_unique (reference : Reference) : enter .unique reference = reference := by
  cases reference with
  | reference mode object => cases mode <;> rfl

@[simp] theorem enter_shared (reference : Reference) :
    enter .shared reference = .shared reference.object := by
  cases reference with
  | reference mode object => cases mode <;> rfl

theorem enter_assoc (first second : Mode) (reference : Reference) :
    enter first (enter second reference) = enter (first.join second) reference := by
  cases first <;> cases second <;> cases reference with
  | reference mode object => cases mode <;> rfl

end EnterProperties

-- An outer none means lookup failed; some none is an existing empty slot.
-- A final inhabited slot records the effective mode, not its stored mode.
def readPath (state : State) (reference : Reference) : List FieldName → Option Slot
  | [] => do
      let _ ← state.objects.lookup reference.object
      return some reference
  | field :: rest => do
      let data ← state.objects.lookup reference.object
      let slot ← data.fields.lookup field
      match rest with
      | [] => return slot.map (enter reference.mode)
      | _ :: _ => do
          let target ← slot
          readPath state (enter reference.mode target) rest

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

theorem readPath_nil (state : State) (reference : Reference) :
    readPath state reference [] =
      (state.objects.lookup reference.object).map (fun _ => some reference) := by
  cases found : state.objects.lookup reference.object <;> simp [readPath, found]

theorem readPath_singleton (state : State) (reference : Reference) (field : FieldName) :
    readPath state reference [field] =
      ((state.objects.lookup reference.object).bind (fun data => data.fields.lookup field)).map
        (Option.map (enter reference.mode)) := by
  cases found : state.objects.lookup reference.object with
  | none => simp [readPath, found]
  | some data =>
    cases fieldFound : data.fields.lookup field <;> simp [readPath, found, fieldFound]

theorem readPath_empty (reference : Reference) (path : List FieldName) :
    readPath State.empty reference path = none := by
  cases path <;> simp [readPath, State.empty]

theorem readPath_root_allocated (read : readPath state reference path = some slot) :
    ∃ data, (reference.object, data) ∈ state.objects := by
  cases path <;> cases found : state.objects.lookup reference.object <;>
    simp [readPath, found] at read
  all_goals exact ⟨_, lookup_member found⟩

theorem readPath_cons (read : readPath state reference (field :: rest) = some slot) :
    ∃ data fieldSlot, (reference.object, data) ∈ state.objects ∧
      (field, fieldSlot) ∈ data.fields ∧
      (rest = [] ∧ fieldSlot.map (enter reference.mode) = slot ∨
        ∃ target, fieldSlot = some target ∧
          readPath state (enter reference.mode target) rest = some slot) := by
  cases objectFound : state.objects.lookup reference.object with
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

theorem field_allocated (wf : WellFormedWith classes state pending)
    (stored : (parent, data) ∈ state.objects) (field : (name, some reference) ∈ data.fields) :
    Allocated state reference.object := by
  apply (wf.referencesComplete reference.object).mp
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨(parent, data), stored, List.mem_filterMap.mpr ⟨(name, some reference), field, rfl⟩⟩))

theorem readPath_target_allocated (wf : WellFormedWith classes state pending)
    (read : readPath state reference path = some (some target)) : Allocated state target.object := by
  induction path generalizing reference with
  | nil =>
    cases found : state.objects.lookup reference.object <;> simp [readPath, found] at read
    subst target
    exact List.mem_map.mpr ⟨_, lookup_member found, rfl⟩
  | cons field rest ih =>
    obtain ⟨data, slot, stored, atField, final | ⟨next, rfl, more⟩⟩ := readPath_cons read
    · rcases final with ⟨rfl, final⟩
      obtain ⟨child, rfl, same⟩ := Option.map_eq_some_iff.mp final
      subst target
      exact field_allocated (reference := child) wf stored atField
    · exact ih more

theorem readPath_index (wf : WellFormedWith classes state pending)
    (read : readPath state reference path = some (some target)) :
    target.object.index ≤ reference.object.index := by
  induction path generalizing reference with
  | nil =>
    cases found : state.objects.lookup reference.object <;> simp [readPath, found] at read
    subst target
    exact Nat.le_refl _
  | cons field rest ih =>
    obtain ⟨data, slot, stored, atField, final | ⟨next, rfl, more⟩⟩ := readPath_cons read
    · rcases final with ⟨rfl, final⟩
      obtain ⟨child, rfl, same⟩ := Option.map_eq_some_iff.mp final
      subst target
      exact Nat.le_of_lt (wf.older _ _ _ child stored atField)
    · exact Nat.le_trans (ih more) (Nat.le_of_lt (wf.older _ _ _ next stored atField))

theorem readPath_index_strict (wf : WellFormedWith classes state pending)
    (nonempty : path ≠ []) (read : readPath state reference path = some (some target)) :
    target.object.index < reference.object.index := by
  cases path with
  | nil => exact False.elim (nonempty rfl)
  | cons field rest =>
    obtain ⟨data, slot, stored, atField, final | ⟨child, rfl, more⟩⟩ := readPath_cons read
    · rcases final with ⟨rfl, final⟩
      obtain ⟨child, rfl, same⟩ := Option.map_eq_some_iff.mp final
      subst target
      exact wf.older _ _ _ child stored atField
    · exact Nat.lt_of_le_of_lt (readPath_index wf more) (wf.older _ _ _ child stored atField)

theorem readPath_nil_of_allocated (wf : WellFormedWith classes state pending)
    (allocated : Allocated state reference.object) :
    readPath state reference [] = some (some reference) := by
  obtain ⟨⟨id, data⟩, stored, same⟩ := List.mem_map.mp allocated
  simp only at same
  subst id
  simp [readPath, lookup_of_member wf.objectKeys stored]

theorem readPath_append (wf : WellFormedWith classes state pending)
    (read : readPath state reference path = some (some target)) (suffix : List FieldName) :
    readPath state reference (path ++ suffix) = readPath state target suffix := by
  induction path generalizing reference with
  | nil =>
    cases found : state.objects.lookup reference.object <;> simp [readPath, found] at read
    subst target
    rfl
  | cons field rest ih =>
    cases objectFound : state.objects.lookup reference.object with
    | none => simp [readPath, objectFound] at read
    | some data =>
      cases fieldFound : data.fields.lookup field with
      | none => simp [readPath, objectFound, fieldFound] at read
      | some slot =>
        cases rest with
        | nil =>
          have same : slot.map (enter reference.mode) = some target := by
            simpa [readPath, objectFound, fieldFound] using read
          obtain ⟨child, rfl, rfl⟩ := Option.map_eq_some_iff.mp same
          cases suffix with
          | nil =>
            simpa using read.trans (readPath_nil_of_allocated wf
              (readPath_target_allocated wf read)).symm
          | cons next suffix => simp [readPath, objectFound, fieldFound]
        | cons next rest =>
          cases slot with
          | none => simp [readPath, objectFound, fieldFound] at read
          | some child =>
            have tailRead : readPath state (enter reference.mode child) (next :: rest) =
                some (some target) := by
              simpa [readPath, objectFound, fieldFound] using read
            simpa [readPath, objectFound, fieldFound] using ih tailRead

theorem readPath_append_inv (wf : WellFormedWith classes state pending)
    (nonempty : suffix ≠ [])
    (read : readPath state reference (path ++ suffix) = some slot) :
    ∃ target, readPath state reference path = some (some target) ∧
      readPath state target suffix = some slot := by
  induction path generalizing reference with
  | nil =>
    obtain ⟨data, stored⟩ := readPath_root_allocated read
    exact ⟨reference, by simp [readPath, lookup_of_member wf.objectKeys stored], read⟩
  | cons field rest ih =>
    obtain ⟨data, fieldSlot, stored, atField, final | ⟨child, rfl, more⟩⟩ := readPath_cons read
    · have empty : rest = [] ∧ suffix = [] := by simpa using final.1
      exact False.elim (nonempty empty.2)
    · obtain ⟨target, prefixRead, suffixRead⟩ := ih more
      have fieldKeys : (data.fields.map Prod.fst).Nodup := by
        obtain ⟨declaration, _, same, distinct⟩ := wf.shapes reference.object data stored
        exact same ▸ distinct
      have firstRead : readPath state reference [field] =
          some (some (enter reference.mode child)) := by
        simp [readPath, lookup_of_member wf.objectKeys stored,
          lookup_of_member fieldKeys atField]
      exact ⟨target, (readPath_append wf firstRead rest).trans prefixRead, suffixRead⟩

theorem readPath_enter (state : State) (permission : Mode) (reference : Reference)
    (path : List FieldName) :
    readPath state (enter permission reference) path =
      (readPath state reference path).map (Option.map (enter permission)) := by
  induction path generalizing reference with
  | nil =>
    cases found : state.objects.lookup reference.object <;>
      simp [readPath, enter, found]
  | cons field rest ih =>
    cases found : state.objects.lookup reference.object with
    | none => simp [readPath, enter, found]
    | some data =>
      cases fieldFound : data.fields.lookup field with
      | none => simp [readPath, enter, found, fieldFound]
      | some slot =>
        cases rest with
        | nil =>
          cases slot <;>
            simp [readPath, found, fieldFound, enter_assoc]
        | cons next rest =>
          cases slot with
          | none => simp [readPath, found, fieldFound]
          | some target =>
            simpa [readPath, found, fieldFound, enter_assoc] using
              ih (enter reference.mode target)

theorem readPath_targets {first second : Reference} (same : first.object = second.object) (path : List FieldName) :
    (readPath state first path).map (Option.map Reference.object) =
      (readPath state second path).map (Option.map Reference.object) := by
  induction path generalizing first second with
  | nil => cases found : state.objects.lookup second.object <;> simp [readPath, same, found]
  | cons field rest ih =>
    cases objectFound : state.objects.lookup second.object with
    | none => simp [readPath, same, objectFound]
    | some data =>
      cases fieldFound : data.fields.lookup field with
      | none => simp [readPath, same, objectFound, fieldFound]
      | some slot =>
        cases rest with
        | nil => cases slot <;> simp [readPath, same, objectFound, fieldFound]
        | cons next rest =>
          cases slot with
          | none => simp [readPath, same, objectFound, fieldFound]
          | some child =>
            simpa [readPath, same, objectFound, fieldFound] using
              ih (first := enter first.mode child) (second := enter second.mode child) rfl

theorem resolve_follow (resolved : Resolve state base source object permission)
    (read : readPath state ⟨permission, object⟩ path = some (some target)) :
    ∃ destination, Resolve state (path.foldl Place.field base)
      destination target.object target.mode := by
  induction path generalizing base source object permission with
  | nil =>
    cases found : state.objects.lookup object <;> simp [readPath, found] at read
    subst target
    exact ⟨source, resolved⟩
  | cons field rest ih =>
    obtain ⟨data, slot, stored, atField, final | ⟨next, rfl, more⟩⟩ := readPath_cons read
    · rcases final with ⟨rfl, final⟩
      obtain ⟨child, rfl, rfl⟩ := Option.map_eq_some_iff.mp final
      exact ⟨.field object field, .field resolved stored atField⟩
    · exact ih (.field resolved stored atField) more

theorem resolve_from_readPath (root : (name, some reference) ∈ state.variables)
    (read : readPath state reference path = some (some target)) :
    ∃ destination, Resolve state (path.foldl Place.field (.variable name))
      destination target.object target.mode := by
  cases reference
  exact resolve_follow (.variable root) read

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
    (stored : Stored state (.field reference.object name) slot) :
    readPath state reference [name] = some (slot.map (enter reference.mode)) := by
  obtain ⟨data, atObject, atField⟩ := stored
  obtain ⟨declaration, _, sameFields, distinct⟩ := wf.shapes reference.object data atObject
  simp [readPath, lookup_of_member wf.objectKeys atObject,
    lookup_of_member (sameFields ▸ distinct) atField]

theorem resolve_deterministic (wf : WellFormedWith classes state pending)
    (first : Resolve state place source object permission)
    (second : Resolve state place other target mode) :
    source = other ∧ object = target ∧ permission = mode := by
  induction first generalizing other target mode with
  | «variable» stored =>
    cases second with
    | «variable» otherStored =>
      have same := Option.some.inj (member_value_unique wf.variableKeys stored otherStored)
      cases same
      exact ⟨rfl, rfl, rfl⟩
  | @field base source parent permission data name reference resolved stored atField ih =>
    cases second with
    | @field _ _ otherParent _ otherData _ otherReference otherResolved otherStored otherField =>
      obtain ⟨rfl, rfl, rfl⟩ := ih otherResolved
      have sameData := member_value_unique wf.objectKeys stored otherStored
      subst otherData
      obtain ⟨declaration, _, sameFields, distinct⟩ := wf.shapes _ _ stored
      have same := Option.some.inj
        (member_value_unique (sameFields ▸ distinct) atField otherField)
      cases same
      exact ⟨rfl, rfl, rfl⟩

end Dada.Shared.Typing

namespace Dada.Shared

theorem Resolve.stored (resolved : Resolve state place source object permission) :
    ∃ reference, Stored state source (some reference) ∧ reference.object = object := by
  cases resolved with
  | «variable» stored => exact ⟨_, stored, rfl⟩
  | field _ stored field => exact ⟨_, ⟨_, stored, field⟩, rfl⟩

theorem Resolve.stored_unique (resolved : Resolve state place source object permission)
    (unique : permission = .unique) : Stored state source (some (.owned object)) := by
  cases resolved with
  | @«variable» name reference stored =>
    cases reference with
    | reference mode object =>
      dsimp at unique
      subst mode
      exact stored
  | @field base source parent permission data name reference baseResolved stored field =>
    have modes : permission = .unique ∧ reference.mode = .unique := by
      cases permission <;> cases h : reference.mode <;> simp_all [Mode.join]
    cases reference with
    | reference mode object =>
      dsimp at modes
      rw [modes.2] at field
      exact ⟨_, stored, field⟩

theorem Resolve.unique_stored (resolved : Resolve state place source object .unique) :
    Stored state source (some (.owned object)) := resolved.stored_unique rfl

theorem Stored.take_exists (stored : Stored state source (some (.owned object))) :
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

theorem Stored.promote_exists (stored : Stored state source (some (.owned object))) :
    ∃ after, Promote state source object after := by
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

theorem Resolve.give_exists (resolved : Resolve state path source object permission) :
    ∃ after, Give state path ⟨permission, object⟩ after := by
  cases permission with
  | unique =>
    obtain ⟨after, taken⟩ := resolved.unique_stored.take_exists
    exact ⟨after, .move resolved taken⟩
  | shared =>
    obtain ⟨⟨mode, target⟩, stored, rfl⟩ := resolved.stored
    cases mode with
    | shared => exact ⟨state, .copy resolved stored⟩
    | unique =>
      obtain ⟨after, promoted⟩ := stored.promote_exists
      exact ⟨after, .promote resolved promoted⟩

theorem Give.resolved (given : Give before path reference after) :
    ∃ source, Resolve before path source reference.object reference.mode := by
  cases given with
  | move resolved _ => exact ⟨_, resolved⟩
  | copy resolved _ => exact ⟨_, resolved⟩
  | promote resolved _ => exact ⟨_, resolved⟩

end Dada.Shared
