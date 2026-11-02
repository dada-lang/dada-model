import Shared.TypingRealization
import Shared.TypingEffects
import Shared.TypingFocus

namespace Dada.Shared.Typing

theorem _root_.Dada.Shared.Unpacking.Transfer.exists_of_permutation
    (sameFields : (pattern.map Prod.fst).Perm (fields.map Prod.fst)) :
    ∃ bindings, Unpacking.Transfer pattern fields bindings := by
  induction pattern generalizing fields with
  | nil =>
    have : fields = [] := List.length_eq_zero_iff.mp (by simpa using sameFields.length_eq.symm)
    subst fields
    exact ⟨[], .nil⟩
  | cons pair rest ih =>
    rcases pair with ⟨field, destination⟩
    have present : field ∈ fields.map Prod.fst := sameFields.mem_iff.mp (by simp)
    obtain ⟨⟨actual, slot⟩, member, equality⟩ := List.mem_map.mp present
    simp only at equality
    subst actual
    obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp member
    have remaining : (rest.map Prod.fst).Perm ((before ++ after).map Prod.fst) := by
      apply List.Perm.cons_inv (a := field)
      exact sameFields.trans (by simp)
    obtain ⟨bindings, transferred⟩ := ih remaining
    exact ⟨(destination, slot) :: bindings, .cons transferred⟩

theorem readPath_same_objects (same : before.objects = after.objects) (reference : Reference)
    (path : Path) : readPath before reference path = readPath after reference path := by
  induction path generalizing reference with
  | nil => simp [readPath, same]
  | cons field rest ih =>
    cases rest with
    | nil => simp [readPath, same]
    | cons next rest => simp only [readPath, same]; congr 1; funext data; congr 1; funext slot
                        congr 1; funext target; simpa only [readPath, same] using ih (enter reference.mode target)

theorem Satisfies.same_objects (satisfied : Satisfies classes before reference ty)
    (same : before.objects = after.objects) : Satisfies classes after reference ty := by
  constructor
  · exact satisfied.mode
  · simpa [same] using satisfied.root
  · intro path positive
    obtain ⟨target, data, read, present, correctClass⟩ := satisfied.positive path positive
    exact ⟨target, data, (readPath_same_objects same _ _).symm.trans read,
      same ▸ present, correctClass⟩
  · intro path negative
    exact (readPath_same_objects same _ _).symm.trans (satisfied.negative path negative)
  · intro path target permission declared read
    exact satisfied.modes path target permission declared
      ((readPath_same_objects same _ _).trans read)

theorem lookup_remove_other {K V : Type} [BEq K] [LawfulBEq K]
    (leading trailing : List (K × V)) (removed key : K) (value : V)
    (different : key ≠ removed) :
    (leading ++ (removed, value) :: trailing).lookup key =
      (leading ++ trailing).lookup key := by
  simp only [List.lookup_append, List.lookup_cons]
  rw [show (key == removed) = false from beq_eq_false_iff_ne.mpr different]

theorem member_remove_other {K V : Type} (leading trailing : List (K × V))
    (removed key : K) (removedValue value : V) (different : key ≠ removed)
    (member : (key, value) ∈ leading ++ (removed, removedValue) :: trailing) :
    (key, value) ∈ leading ++ trailing := by
  simp only [List.mem_append, List.mem_cons, Prod.mk.injEq] at member ⊢
  rcases member with left | same | right
  · exact Or.inl left
  · exact False.elim (different same.1)
  · exact Or.inr right

theorem field_reference_mem (stored : (parent, data) ∈ state.objects)
    (field : (name, some target) ∈ data.fields) : target.object ∈ References state := by
  apply List.mem_append.mpr; right
  apply List.mem_flatMap.mpr
  refine ⟨(parent, data), stored, ?_⟩
  exact List.mem_filterMap.mpr ⟨(name, some target), field, rfl⟩

theorem variable_reference_mem (stored : (name, some target) ∈ state.variables) :
    target.object ∈ References state := by
  exact List.mem_append.mpr (.inl (List.mem_filterMap.mpr ⟨_, stored, rfl⟩))

theorem Realizes.pending_unique_not_reference
    (realized : Realizes classes environment state [(.owned object, ty)]) :
    object ∉ References state := by
  have targets : (Owners state).map Reference.object = References state := by
    simp [Owners, References, List.map_filterMap, List.map_flatMap]
  rw [← targets]
  intro member
  obtain ⟨reference, member, same⟩ := List.mem_map.mp member
  have compatible : (Reference.owned object :: Owners state).Pairwise Compatible :=
    realized.ownership.ownersCompatible
  rcases (List.pairwise_cons.mp compatible).1 reference member with different | shared
  · exact different same.symm
  · cases shared.1

theorem readPath_remove (leading trailing : List (ObjectId × Object))
    (removed : ObjectId) (removedData : Object)
    (beforeVariables afterVariables : List (VariableId × Slot))
    (beforeNext afterNext : Nat)
    (noIncoming : removed ∉ References
      ⟨leading ++ (removed, removedData) :: trailing, beforeVariables, beforeNext⟩)
    (reference : Reference) (different : reference.object ≠ removed) (path : Path) :
    readPath ⟨leading ++ (removed, removedData) :: trailing, beforeVariables, beforeNext⟩
      reference path =
    readPath ⟨leading ++ trailing, afterVariables, afterNext⟩ reference path := by
  induction path generalizing reference with
  | nil =>
    rw [readPath_nil, readPath_nil]
    exact congrArg (fun (found : Option Object) => found.map (fun _ => some reference))
      (lookup_remove_other leading trailing removed reference.object removedData different)
  | cons field rest ih =>
    cases rest with
    | nil =>
      simp only [readPath_singleton]
      rw [lookup_remove_other leading trailing removed reference.object removedData different]
    | cons next rest =>
      have lookupEq := lookup_remove_other leading trailing removed reference.object removedData different
      cases found : (leading ++ (removed, removedData) :: trailing).lookup reference.object with
      | none => simp [readPath, found, ← lookupEq]
      | some data =>
        have stored := lookup_member found
        cases fieldFound : data.fields.lookup field with
        | none => simp [readPath, found, ← lookupEq, fieldFound]
        | some slot =>
          cases slot with
          | none => simp [readPath, found, ← lookupEq, fieldFound]
          | some target =>
            have differentTarget : target.object ≠ removed := by
              intro same
              apply noIncoming
              have member := field_reference_mem (state := ⟨leading ++ (removed, removedData) :: trailing, beforeVariables, beforeNext⟩) stored (lookup_member fieldFound)
              exact same ▸ member
            simpa [readPath, found, ← lookupEq, fieldFound] using
              ih (enter reference.mode target) differentTarget

theorem readPath_target_ne (noIncoming : removed ∉ References state)
    (different : reference.object ≠ removed)
    (read : readPath state reference path = some (some target)) :
    target.object ≠ removed := by
  induction path generalizing reference with
  | nil =>
    cases found : state.objects.lookup reference.object <;> simp [readPath, found] at read
    subst target
    exact different
  | cons field rest ih =>
    obtain ⟨data, slot, stored, fieldStored, final | ⟨child, rfl, more⟩⟩ := readPath_cons read
    · obtain ⟨rfl, final⟩ := final
      obtain ⟨child, rfl, rfl⟩ := Option.map_eq_some_iff.mp final
      change child.object ≠ removed
      intro same
      exact noIncoming (same ▸ field_reference_mem stored fieldStored)
    · apply ih (reference := enter reference.mode child) _ more
      change child.object ≠ removed
      intro same
      exact noIncoming (same ▸ field_reference_mem stored fieldStored)

theorem Satisfies.remove (satisfied : Satisfies classes
      ⟨leading ++ (removed, removedData) :: trailing, variables, nextId⟩ reference ty)
    (different : reference.object ≠ removed)
    (noIncoming : removed ∉ References
      ⟨leading ++ (removed, removedData) :: trailing, variables, nextId⟩) :
    Satisfies classes ⟨leading ++ trailing, afterVariables, afterNext⟩ reference ty := by
  constructor
  · exact satisfied.mode
  · obtain ⟨data, stored, correctClass⟩ := satisfied.root
    exact ⟨data, member_remove_other _ _ _ _ _ _ different stored, correctClass⟩
  · intro path positive
    obtain ⟨target, data, read, stored, correctClass⟩ := satisfied.positive path positive
    refine ⟨target, data, ?_, ?_, correctClass⟩
    · exact (readPath_remove _ _ _ _ _ _ _ _ noIncoming reference different path).symm.trans read
    · exact member_remove_other _ _ _ _ _ _
        (readPath_target_ne noIncoming different read) stored
  · intro path negative
    exact (readPath_remove _ _ _ _ _ _ _ _ noIncoming reference different path).symm.trans
      (satisfied.negative path negative)
  · intro path target permission declared read
    exact satisfied.modes path target permission declared
      ((readPath_remove _ _ _ _ _ _ _ _ noIncoming reference different path).trans read)

theorem _root_.Dada.Shared.Unpacking.Transfer.pattern_member
    (transfer : Unpacking.Transfer pattern fields bindings)
    (member : (field, destination) ∈ pattern) :
    ∃ slot, (destination, slot) ∈ bindings ∧ (field, slot) ∈ fields := by
  induction transfer with
  | nil => simp at member
  | @cons selected name slot pattern before after bindings rest ih =>
    rcases List.mem_cons.mp member with same | later
    · cases same
      exact ⟨slot, by simp, by simp⟩
    · obtain ⟨value, bound, stored⟩ := ih later
      refine ⟨value, List.mem_cons_of_mem _ bound, ?_⟩
      rcases List.mem_append.mp stored with left | right
      · exact List.mem_append_left _ left
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ right)

def SlotMatches (classes : ClassTable) (state : State) : Slot → SlotDescription → Prop
  | none, none => True
  | some reference, some ty => Satisfies classes state reference ty
  | _, _ => False


theorem BindingTyped.exists_bind
    (typed : BindingTyped classes environment pattern ty afterEnvironment)
    (realized : Realizes classes environment state [(reference, ty)]) :
    ∃ after, Unpacking.Bind classes.erase state reference pattern after := by
  cases typed with
  | «variable» _ _ fresh =>
    exact ⟨_, .variable (fun occupied => fresh ((realized.variableDomain _).mpr occupied))⟩
  | @unpack _ name declaration fields bindings _ _ given sameClass declared
      sameFields uniqueNames fresh _ _ =>
    have satisfied := realized.pendingValues reference ty (by simp)
    have unique : reference.mode = .unique := by rw [satisfied.mode, given]; rfl
    have owned : reference = .owned reference.object := by cases reference; cases unique; rfl
    rw [owned] at realized ⊢
    obtain ⟨data, stored, rootClass⟩ := satisfied.root
    obtain ⟨leading, trailing, objects⟩ := List.mem_iff_append.mp stored
    obtain ⟨untypedDeclaration, untypedDeclared, shape, _⟩ := realized.ownership.shapes _ _ stored
    have erasedDeclared : (name, ⟨declaration.fields.map Prod.fst⟩) ∈ classes.erase :=
      List.mem_map.mpr ⟨(name, declaration), declared, rfl⟩
    have dataClass : data.className = name := rootClass.trans sameClass
    have declarationEq : untypedDeclaration = ⟨declaration.fields.map Prod.fst⟩ :=
      member_value_unique realized.classesWellFormed.erase.1
        (dataClass ▸ untypedDeclared) erasedDeclared
    have actualFields : data.fields.map Prod.fst = declaration.fields.map Prod.fst := by
      simpa [declarationEq] using shape
    obtain ⟨runtimeBindings, transferred⟩ :=
      Unpacking.Transfer.exists_of_permutation (sameFields.trans (List.Perm.of_eq actualFields.symm))
    have fieldsUnique := (sameFields.nodup_iff).mpr
      ((realized.classesWellFormed.2 _ declared).1)
    rcases state with ⟨objectsList, variables, nextId⟩
    simp only at objects
    subst objectsList
    rcases data with ⟨dataName, dataFields⟩
    simp only at dataClass
    subst dataName
    exact ⟨_, .unpack erasedDeclared actualFields fieldsUnique uniqueNames
      (fun destination present occupied =>
        fresh destination present ((realized.variableDomain destination).mpr occupied)) transferred⟩

theorem Realizes.bind_variable
    (realized : Realizes classes environment state [(reference, ty)])
    (fresh : name ∉ environment.map Prod.fst) :
    Realizes classes ((name, some ty) :: environment) (state.bind name reference) [] := by
  have freshState : name ∉ state.variables.map Prod.fst :=
    fun present => fresh ((realized.variableDomain name).mpr present)
  have admissible := realized.pendingTypes reference ty (by simp)
  constructor
  · exact realized.classesWellFormed
  · simpa [Environment.WellFormed, admissible, fresh] using realized.environmentWellFormed
  · simp
  · exact (Unpacking.Bind.preserves_wellFormed (.variable freshState) realized.ownership).with_pending
  · exact realized.fields
  · intro variableName
    simp only [List.map_cons, List.mem_cons, State.bind]
    exact or_congr Iff.rfl (realized.variableDomain variableName)
  · intro variableName member
    rcases List.mem_cons.mp member with impossible | old
    · cases impossible
    · exact List.mem_cons_of_mem _ (realized.emptyVariables _ old)
  · intro variableName variableType member
    rcases List.mem_cons.mp member with new | old
    · cases new
      exact ⟨reference, by simp [State.bind],
        (realized.pendingValues reference ty (by simp)).same_objects rfl⟩
    · obtain ⟨target, stored, satisfied⟩ := realized.initializedVariables _ _ old
      exact ⟨target, List.mem_cons_of_mem _ stored, satisfied.same_objects rfl⟩
  · simp

theorem FieldBindings.description_member
    (typed : FieldBindings classes ty pattern bindings)
    (member : (destination, description) ∈ bindings) :
    ∃ field, (field, destination) ∈ pattern ∧
      fieldDescription classes ty field = some description := by
  induction typed with
  | nil => simp at member
  | @cons field name desc fields bindings described rest ih =>
    rcases List.mem_cons.mp member with same | later
    · cases same
      exact ⟨field, by simp, described⟩
    · obtain ⟨field, present, described⟩ := ih later
      exact ⟨field, List.mem_cons_of_mem _ present, described⟩

theorem Realizes.unpack_of_field_matches {fields : List (FieldName × Slot)}
    (realized : Realizes classes environment
      ⟨leading ++ (object, ⟨className, fields⟩) :: trailing, variables, nextId⟩ [(.owned object, ty)])
    (typed : FieldBindings classes ty pattern bindings)
    (transfer : Unpacking.Transfer pattern fields runtimeBindings)
    (afterWellFormed : (bindings ++ environment).WellFormed classes)
    (operation : Unpacking.Bind classes.erase
      ⟨leading ++ (object, ⟨className, fields⟩) :: trailing, variables, nextId⟩ (.owned object)
      (.unpack className pattern)
      ⟨leading ++ trailing, runtimeBindings ++ variables, nextId⟩)
    (fieldMatches : ∀ field slot description, (field, slot) ∈ fields →
      fieldDescription classes ty field = some description →
      SlotMatches classes
        ⟨leading ++ (object, ⟨className, fields⟩) :: trailing, variables, nextId⟩
        slot description) :
    Realizes classes (bindings ++ environment)
      ⟨leading ++ trailing, runtimeBindings ++ variables, nextId⟩ [] := by
  have noIncoming := realized.pending_unique_not_reference
  have objectStored : (object, ⟨className, fields⟩) ∈
      leading ++ (object, ⟨className, fields⟩) :: trailing := by simp
  have subset : ∀ entry ∈ leading ++ trailing,
      entry ∈ leading ++ (object, ⟨className, fields⟩) :: trailing := by
    intro entry present
    rcases List.mem_append.mp present with left | right
    · exact List.mem_append_left _ left
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ right)
  constructor
  · exact realized.classesWellFormed
  · exact afterWellFormed
  · simp
  · exact (operation.preserves_wellFormed realized.ownership).with_pending
  · intro parent data field target stored fieldStored
    have oldStored := subset _ stored
    obtain ⟨declaration, targetType, targetData, declared, declaredField, targetStored, correct⟩ :=
      realized.fields parent data field target oldStored fieldStored
    have different : target.object ≠ object := by
      intro same
      apply noIncoming
      have member := field_reference_mem (state := ⟨leading ++ (object, ⟨className, fields⟩) :: trailing, variables, nextId⟩) oldStored fieldStored
      exact same ▸ member
    exact ⟨declaration, targetType, targetData, declared, declaredField,
      member_remove_other _ _ _ _ _ _ different targetStored, correct⟩
  · intro name
    simp only [List.map_append, List.mem_append, typed.keys, transfer.keys]
    exact or_congr Iff.rfl (realized.variableDomain name)
  · intro name member
    rcases List.mem_append.mp member with new | old
    · obtain ⟨field, patternMember, description⟩ := typed.description_member new
      obtain ⟨slot, bound, stored⟩ := transfer.pattern_member patternMember
      have matched := fieldMatches field slot none stored description
      cases slot with
      | none => exact List.mem_append_left _ bound
      | some target => cases matched
    · exact List.mem_append_right _ (realized.emptyVariables name old)
  · intro name child member
    rcases List.mem_append.mp member with new | old
    · obtain ⟨field, patternMember, description⟩ := typed.description_member new
      obtain ⟨slot, bound, stored⟩ := transfer.pattern_member patternMember
      have matched := fieldMatches field slot (some child) stored description
      cases slot with
      | none => cases matched
      | some target =>
        have different : target.object ≠ object := by
          intro same
          apply noIncoming
          have member := field_reference_mem (state := ⟨leading ++ (object, ⟨className, fields⟩) :: trailing, variables, nextId⟩) (data := ⟨className, fields⟩) objectStored stored
          exact same ▸ member
        exact ⟨target, List.mem_append_left _ bound, matched.remove different noIncoming⟩
    · obtain ⟨target, stored, satisfied⟩ := realized.initializedVariables name child old
      have different : target.object ≠ object := by
        intro same
        apply noIncoming
        have member := variable_reference_mem (state := ⟨leading ++ (object, ⟨className, fields⟩) :: trailing, variables, nextId⟩) stored
        exact same ▸ member
      exact ⟨target, List.mem_append_right _ stored, satisfied.remove different noIncoming⟩
  · simp


theorem Satisfies.fieldDescription_of_focus
    (satisfied : Satisfies classes state reference ty)
    (unique : reference.mode = .unique)
    (wf : WellFormedWith classes.erase state pending)
    (dataStored : (reference.object, data) ∈ state.objects)
    (fieldStored : (field, slot) ∈ data.fields)
    (described : fieldDescription classes ty field = some description)
    (focusSound : ∀ child, Typing.focus classes ty [field] = some child →
      ∃ target, readPath state reference [field] = some (some target) ∧
        Satisfies classes state target child) :
    SlotMatches classes state slot description := by
  have dataLookup := lookup_of_member wf.objectKeys dataStored
  obtain ⟨declaration, _, shape, uniqueFields⟩ := wf.shapes _ _ dataStored
  have fieldLookup := lookup_of_member (shape ▸ uniqueFields) fieldStored
  have read : readPath state reference [field] = some slot := by
    cases slot <;> simp [readPath, dataLookup, fieldLookup, unique]
  unfold fieldDescription at described
  split at described
  next negative =>
    have empty := satisfied.negative [field] negative
    have slotEmpty : slot = none := Option.some.inj (read.symm.trans empty)
    have descEmpty : description = none := (Option.some.inj described).symm
    subst slot
    subst description
    trivial
  next notNegative =>
    cases description with
    | none => simp at described
    | some child =>
      have focused : Typing.focus classes ty [field] = some child := by simpa using described
      obtain ⟨target, readTarget, childSatisfied⟩ := focusSound child focused
      have slotTarget : slot = some target := Option.some.inj (read.symm.trans readTarget)
      subst slot
      exact childSatisfied

theorem BindingTyped.preserves_realization_of_fields
    (typed : BindingTyped classes environment pattern ty afterEnvironment)
    (realized : Realizes classes environment state [(reference, ty)])
    (operation : Unpacking.Bind classes.erase state reference pattern after)
    (fieldMatches : reference.mode = .unique →
      ∀ data, (reference.object, data) ∈ state.objects →
      ∀ field slot description, (field, slot) ∈ data.fields →
      fieldDescription classes ty field = some description →
      SlotMatches classes state slot description) :
    Realizes classes afterEnvironment after [] := by
  cases typed with
  | «variable» _ _ fresh =>
    cases operation with
    | «variable» _ => exact realized.bind_variable fresh
  | @unpack _ name declaration pattern bindings _ _ _ _ _ _ _ _ fieldTyped afterWf =>
    cases operation with
    | @unpack leading trailing variables nextId object className fields pattern runtimeBindings
        declaration _ _ _ _ _ transfer =>
      apply realized.unpack_of_field_matches fieldTyped transfer afterWf
        (.unpack ‹_› ‹_› ‹_› ‹_› ‹_› transfer)
      exact fieldMatches rfl ⟨name, fields⟩ (by simp [Reference.owned])


theorem BindingTyped.preserves_realization
    (typed : BindingTyped classes environment pattern ty afterEnvironment)
    (realized : Realizes classes environment state [(reference, ty)])
    (operation : Unpacking.Bind classes.erase state reference pattern after) :
    Realizes classes afterEnvironment after [] := by
  apply typed.preserves_realization_of_fields realized operation
  intro unique data stored field slot description fieldStored described
  have satisfied := realized.pendingValues reference ty (by simp)
  apply satisfied.fieldDescription_of_focus unique realized.ownership stored fieldStored described
  intro child focused
  have normal := typed.wellFormed.2.1.2
  have observations := focus_observations realized.classesWellFormed normal focused
  obtain ⟨target, _, read, _, _⟩ := satisfied.positive [field] observations.positive
  exact ⟨target, read, satisfied.focus realized.classesWellFormed realized.ownership normal focused read⟩

end Dada.Shared.Typing
