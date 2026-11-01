import Unique.TypingRealization
import Unique.TypingEffects
import Unique.ViewSoundness

namespace Dada.Unique.Typing

theorem lookup_of_unique_member {K V : Type} [BEq K] [LawfulBEq K]
    {entries : List (K × V)} {key : K} {value : V} (unique : (entries.map Prod.fst).Nodup)
    (member : (key, value) ∈ entries) : entries.lookup key = some value := by
  induction entries with
  | nil => simp at member
  | cons entry rest ih =>
    rcases entry with ⟨head, data⟩
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with same | later
    · cases same
      simp
    · have different : key ≠ head := by
        intro same
        apply unique.1
        exact List.mem_map.mpr ⟨(key, value), later, same⟩
      rw [List.lookup_cons, show (key == head) = false from beq_eq_false_iff_ne.mpr different]
      exact ih unique.2 later

theorem member_of_lookup {K V : Type} [BEq K] [LawfulBEq K]
    {entries : List (K × V)} {key : K} {value : V} (found : entries.lookup key = some value) :
    (key, value) ∈ entries := by
  obtain ⟨before, after, rfl, _⟩ := List.lookup_eq_some_iff.mp found
  simp

theorem same_value_of_unique_members {K V : Type} [BEq K] [LawfulBEq K]
    {entries : List (K × V)} {key : K} {value other : V} (unique : (entries.map Prod.fst).Nodup)
    (first : (key, value) ∈ entries) (second : (key, other) ∈ entries) : value = other := by
  exact Option.some.inj ((lookup_of_unique_member unique first).symm.trans
    (lookup_of_unique_member unique second))

theorem _root_.Dada.Unique.Unpacking.Transfer.exists_of_permutation
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

theorem BindingTyped.exists_bind
    (typed : BindingTyped classes environment pattern ty afterEnvironment)
    (realized : Realizes classes environment state [(object, ty)]) :
    ∃ after, Unpacking.Bind classes.erase state object pattern after := by
  cases typed with
  | «variable» _ _ fresh =>
    exact ⟨_, .variable (fun occupied => fresh ((realized.variableDomain _).mpr occupied))⟩
  | @unpack _ name declaration fields bindings _ _ sameClass declared
      sameFields uniqueNames fresh _ _ =>
    obtain ⟨data, stored, rootClass⟩ := (realized.pendingValues object ty (by simp)).root
    obtain ⟨leading, trailing, objects⟩ := List.mem_iff_append.mp stored
    obtain ⟨untypedDeclaration, untypedDeclared, shape, _⟩ := realized.ownership.shapes _ _ stored
    have erasedDeclared : (name, ⟨declaration.fields.map Prod.fst⟩) ∈ classes.erase :=
      List.mem_map.mpr ⟨(name, declaration), declared, rfl⟩
    have dataClass : data.className = name := rootClass.trans sameClass
    have declarationEq : untypedDeclaration = ⟨declaration.fields.map Prod.fst⟩ :=
      same_value_of_unique_members realized.classesWellFormed.erase.1
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

theorem readPath_same_objects (same : before.objects = after.objects) (object : ObjectId)
    (path : Path) : readPath before object path = readPath after object path := by
  induction path generalizing object with
  | nil => simp [readPath, same]
  | cons field rest ih =>
    cases rest with
    | nil => simp [readPath, same]
    | cons next rest => simp only [readPath, same]; congr 1; funext data; congr 1; funext slot
                        congr 1; funext target; simpa only [readPath, same] using ih target

theorem Satisfies.same_objects (satisfied : Satisfies classes before object ty)
    (same : before.objects = after.objects) : Satisfies classes after object ty := by
  constructor
  · simpa [same] using satisfied.root
  · intro path positive
    obtain ⟨target, data, read, present, correctClass⟩ := satisfied.positive path positive
    exact ⟨target, data, (readPath_same_objects same _ _).symm.trans read,
      same ▸ present, correctClass⟩
  · intro path negative
    exact (readPath_same_objects same _ _).symm.trans (satisfied.negative path negative)

theorem Realizes.bind_variable
    (realized : Realizes classes environment state [(object, ty)])
    (fresh : name ∉ environment.map Prod.fst) :
    Realizes classes ((name, some ty) :: environment) (state.bind name object) [] := by
  have freshState : name ∉ state.variables.map Prod.fst :=
    fun present => fresh ((realized.variableDomain name).mpr present)
  have admissible := realized.pendingTypes object ty (by simp)
  constructor
  · exact realized.classesWellFormed
  · simpa [Environment.WellFormed, admissible, fresh] using realized.environmentWellFormed
  · simp
  · exact (realized.ownership.bind freshState).with_empty
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
      exact ⟨object, by simp [State.bind],
        (realized.pendingValues object ty (by simp)).same_objects rfl⟩
    · obtain ⟨target, stored, satisfied⟩ := realized.initializedVariables _ _ old
      exact ⟨target, List.mem_cons_of_mem _ stored, satisfied.same_objects rfl⟩
  · simp

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
    (field : (name, some target) ∈ data.fields) : target ∈ References state := by
  apply List.mem_append.mpr; right
  apply List.mem_flatMap.mpr
  refine ⟨(parent, data), stored, ?_⟩
  exact List.mem_filterMap.mpr ⟨(name, some target), field, rfl⟩

theorem variable_reference_mem (stored : (name, some target) ∈ state.variables) :
    target ∈ References state := by
  exact List.mem_append.mpr (.inl (List.mem_filterMap.mpr ⟨_, stored, rfl⟩))

theorem Realizes.pending_not_reference
    (realized : Realizes classes environment state [(object, ty)]) :
    object ∉ References state := by
  exact (List.nodup_cons.mp realized.ownership.referencesUnique).1

theorem readPath_remove (leading trailing : List (ObjectId × Object))
    (removed : ObjectId) (removedData : Object)
    (beforeVariables afterVariables : List (VariableId × Slot))
    (beforeNext afterNext : Nat)
    (noIncoming : removed ∉ References
      ⟨leading ++ (removed, removedData) :: trailing, beforeVariables, beforeNext⟩)
    (object : ObjectId) (different : object ≠ removed) (path : Path) :
    readPath ⟨leading ++ (removed, removedData) :: trailing, beforeVariables, beforeNext⟩
      object path =
    readPath ⟨leading ++ trailing, afterVariables, afterNext⟩ object path := by
  induction path generalizing object with
  | nil =>
    rw [readPath_nil, readPath_nil]
    exact congrArg (fun (found : Option Object) => found.map (fun _ => some object))
      (lookup_remove_other leading trailing removed object removedData different)
  | cons field rest ih =>
    cases rest with
    | nil =>
      simp only [readPath_singleton]
      rw [lookup_remove_other leading trailing removed object removedData different]
    | cons next rest =>
      have lookupEq := lookup_remove_other leading trailing removed object removedData different
      cases found : (leading ++ (removed, removedData) :: trailing).lookup object with
      | none => simp [readPath, found, ← lookupEq]
      | some data =>
        have stored := member_of_lookup found
        cases fieldFound : data.fields.lookup field with
        | none => simp [readPath, found, ← lookupEq, fieldFound]
        | some slot =>
          cases slot with
          | none => simp [readPath, found, ← lookupEq, fieldFound]
          | some target =>
            have differentTarget : target ≠ removed := by
              intro same
              apply noIncoming
              subst target
              exact field_reference_mem stored (member_of_lookup fieldFound)
            simpa [readPath, found, ← lookupEq, fieldFound] using
              ih target differentTarget

theorem readPath_target_ne (noIncoming : removed ∉ References state)
    (different : object ≠ removed) (read : readPath state object path = some (some target)) :
    target ≠ removed := by
  induction path generalizing object with
  | nil =>
    cases found : state.objects.lookup object <;> simp [readPath, found] at read
    subst target
    exact different
  | cons field rest ih =>
    cases found : state.objects.lookup object with
    | none => simp [readPath, found] at read
    | some data =>
      have stored := member_of_lookup found
      cases fieldFound : data.fields.lookup field with
      | none => simp [readPath, found, fieldFound] at read
      | some slot =>
        cases slot with
        | none => cases rest <;> simp [readPath, found, fieldFound] at read
        | some next =>
          have differentNext : next ≠ removed := by
            intro same
            apply noIncoming
            subst next
            exact field_reference_mem stored (member_of_lookup fieldFound)
          cases rest with
          | nil =>
            simp [readPath, found, fieldFound] at read
            subst target
            exact differentNext
          | cons field rest =>
            apply ih differentNext
            simpa [readPath, found, fieldFound] using read

theorem Satisfies.remove (satisfied : Satisfies classes
      ⟨leading ++ (removed, removedData) :: trailing, variables, nextId⟩ object ty)
    (different : object ≠ removed)
    (noIncoming : removed ∉ References
      ⟨leading ++ (removed, removedData) :: trailing, variables, nextId⟩) :
    Satisfies classes ⟨leading ++ trailing, afterVariables, afterNext⟩ object ty := by
  constructor
  · obtain ⟨data, stored, correctClass⟩ := satisfied.root
    exact ⟨data, member_remove_other _ _ _ _ _ _ different stored, correctClass⟩
  · intro path positive
    obtain ⟨target, data, read, stored, correctClass⟩ := satisfied.positive path positive
    refine ⟨target, data, ?_, ?_, correctClass⟩
    · exact (readPath_remove _ _ _ _ _ _ _ _ noIncoming object different path).symm.trans read
    · exact member_remove_other _ _ _ _ _ _
        (readPath_target_ne noIncoming different read) stored
  · intro path negative
    exact (readPath_remove _ _ _ _ _ _ _ _ noIncoming object different path).symm.trans
      (satisfied.negative path negative)

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

theorem _root_.Dada.Unique.Unpacking.Transfer.pattern_member
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

theorem readPath_descend
    (rootLookup : state.objects.lookup object = some data)
    (fieldLookup : data.fields.lookup field = some (some target))
    (targetLookup : state.objects.lookup target = some targetData)
    (path : Path) : readPath state object (field :: path) = readPath state target path := by
  cases path <;> simp [readPath, rootLookup, fieldLookup, targetLookup]

theorem Satisfies.field_of_observations
    (satisfied : Satisfies classes state object ty)
    (unique : (state.objects.map Prod.fst).Nodup)
    (rootPositive : Pos classes ty [field])
    (classAgreement : classAt classes ty.className [field] = some child.className)
    (positive : ∀ path, Pos classes child path → Pos classes ty (field :: path))
    (negative : ∀ path, Neg child path → Neg ty (field :: path))
    (classesCompose : ∀ path, classAt classes ty.className (field :: path) =
      classAt classes child.className path) :
    ∃ target, readPath state object [field] = some (some target) ∧
      Satisfies classes state target child := by
  obtain ⟨target, targetData, readField, storedTarget, targetClass⟩ :=
    satisfied.positive [field] rootPositive
  have targetLookup := lookup_of_unique_member unique storedTarget
  obtain ⟨data, storedRoot, _⟩ := satisfied.root
  have rootLookup := lookup_of_unique_member unique storedRoot
  have fieldLookup : data.fields.lookup field = some (some target) := by
    simpa [readPath, rootLookup] using readField
  refine ⟨target, readField, ?_⟩
  constructor
  · exact ⟨targetData, storedTarget, Option.some.inj (targetClass.symm.trans classAgreement)⟩
  · intro path known
    obtain ⟨result, resultData, read, stored, correctClass⟩ :=
      satisfied.positive (field :: path) (positive path known)
    refine ⟨result, resultData, ?_, stored, ?_⟩
    · exact (readPath_descend rootLookup fieldLookup targetLookup path).symm.trans read
    · exact (classesCompose path).symm.trans correctClass
  · intro path empty
    exact (readPath_descend rootLookup fieldLookup targetLookup path).symm.trans
      (satisfied.negative (field :: path) (negative path empty))

def SlotMatches (classes : ClassTable) (state : State) : Slot → SlotDescription → Prop
  | none, none => True
  | some object, some ty => Satisfies classes state object ty
  | _, _ => False

theorem Realizes.unpack_of_field_matches {fields : List (FieldName × Slot)}
    (realized : Realizes classes environment
      ⟨leading ++ (object, ⟨className, fields⟩) :: trailing, variables, nextId⟩ [(object, ty)])
    (typed : FieldBindings classes ty pattern bindings)
    (transfer : Unpacking.Transfer pattern fields runtimeBindings)
    (afterWellFormed : (bindings ++ environment).WellFormed classes)
    (operation : Unpacking.Bind classes.erase
      ⟨leading ++ (object, ⟨className, fields⟩) :: trailing, variables, nextId⟩ object
      (.unpack className pattern)
      ⟨leading ++ trailing, runtimeBindings ++ variables, nextId⟩)
    (fieldMatches : ∀ field slot description, (field, slot) ∈ fields →
      fieldDescription classes ty field = some description →
      SlotMatches classes
        ⟨leading ++ (object, ⟨className, fields⟩) :: trailing, variables, nextId⟩
        slot description) :
    Realizes classes (bindings ++ environment)
      ⟨leading ++ trailing, runtimeBindings ++ variables, nextId⟩ [] := by
  have noIncoming := realized.pending_not_reference
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
  · exact (operation.preserves_wellFormed realized.ownership).with_empty
  · intro parent data field target stored fieldStored
    have oldStored := subset _ stored
    obtain ⟨declaration, targetClass, targetData, declared, declaredField, targetStored, correct⟩ :=
      realized.fields parent data field target oldStored fieldStored
    have different : target ≠ object := by
      intro same
      apply noIncoming
      subst target
      exact field_reference_mem oldStored fieldStored
    exact ⟨declaration, targetClass, targetData, declared, declaredField,
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
        have different : target ≠ object := by
          intro same
          apply noIncoming
          subst target
          exact field_reference_mem objectStored stored
        exact ⟨target, List.mem_append_left _ bound, matched.remove different noIncoming⟩
    · obtain ⟨target, stored, satisfied⟩ := realized.initializedVariables name child old
      have different : target ≠ object := by
        intro same
        apply noIncoming
        subst target
        exact variable_reference_mem stored
      exact ⟨target, List.mem_append_right _ stored, satisfied.remove different noIncoming⟩
  · simp

theorem classAt_field_suffix
    (found : classAt classes base [field] = some target) (path : Path) :
    classAt classes base (field :: path) = classAt classes target path := by
  cases declarationFound : classes.lookup base with
  | none => simp [classAt, declarationFound] at found
  | some declaration =>
    cases fieldFound : declaration.fields.lookup field with
    | none => simp [classAt, declarationFound, fieldFound] at found
    | some name =>
      simp [classAt, declarationFound, fieldFound] at found
      subst name
      simp [classAt, declarationFound, fieldFound]

theorem Satisfies.fieldDescription_of_focus
    (satisfied : Satisfies classes state object ty)
    (wf : WellFormedWith classes.erase state pending)
    (dataStored : (object, data) ∈ state.objects)
    (fieldStored : (field, slot) ∈ data.fields)
    (described : fieldDescription classes ty field = some description)
    (focusSound : ∀ child, focus classes ty [field] = some child →
      ∃ target, readPath state object [field] = some (some target) ∧
        Satisfies classes state target child) :
    SlotMatches classes state slot description := by
  have dataLookup := lookup_of_unique_member wf.objectKeys dataStored
  obtain ⟨declaration, _, shape, uniqueFields⟩ := wf.shapes _ _ dataStored
  have fieldLookup := lookup_of_unique_member (shape ▸ uniqueFields) fieldStored
  have read : readPath state object [field] = some slot := by
    simpa [readPath, dataLookup] using fieldLookup
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
      have focused : focus classes ty [field] = some child := by simpa using described
      obtain ⟨target, readTarget, childSatisfied⟩ := focusSound child focused
      have slotTarget : slot = some target := Option.some.inj (read.symm.trans readTarget)
      subst slot
      exact childSatisfied

theorem BindingTyped.preserves_realization_of_fields
    (typed : BindingTyped classes environment pattern ty afterEnvironment)
    (realized : Realizes classes environment state [(object, ty)])
    (operation : Unpacking.Bind classes.erase state object pattern after)
    (fieldMatches : ∀ data, (object, data) ∈ state.objects →
      ∀ field slot description, (field, slot) ∈ data.fields →
      fieldDescription classes ty field = some description →
      SlotMatches classes state slot description) :
    Realizes classes afterEnvironment after [] := by
  cases typed with
  | «variable» _ _ fresh =>
    cases operation with
    | «variable» _ => exact realized.bind_variable fresh
  | @unpack _ name declaration pattern bindings _ _ _ _ _ _ _ fieldTyped afterWf =>
    cases operation with
    | @unpack leading trailing variables nextId object className fields pattern runtimeBindings
        declaration _ _ _ _ _ transfer =>
      apply realized.unpack_of_field_matches fieldTyped transfer afterWf
        (.unpack ‹_› ‹_› ‹_› ‹_› ‹_› transfer)
      exact fieldMatches ⟨name, fields⟩ (by simp)

theorem Satisfies.focus_field
    (satisfied : Satisfies classes state object ty)
    (wf : WellFormedWith classes.erase state pending)
    (classesWF : classes.WellFormed) (normal : Normalized classes ty)
    (focused : focus classes ty [field] = some child) :
    ∃ target, readPath state object [field] = some (some target) ∧
      Satisfies classes state target child := by
  have observations := focus_observations classesWF normal focused
  apply satisfied.field_of_observations wf.objectKeys observations.positive observations.className
  · intro path positive
    exact observations.positives path positive
  · intro path negative
    exact observations.negatives path negative
  · exact classAt_field_suffix observations.className

theorem BindingTyped.preserves_realization
    (typed : BindingTyped classes environment pattern ty afterEnvironment)
    (realized : Realizes classes environment state [(object, ty)])
    (operation : Unpacking.Bind classes.erase state object pattern after) :
    Realizes classes afterEnvironment after [] := by
  apply typed.preserves_realization_of_fields realized operation
  intro data stored field slot description fieldStored described
  apply (realized.pendingValues object ty (by simp)).fieldDescription_of_focus
    realized.ownership stored fieldStored described
  intro child focused
  exact (realized.pendingValues object ty (by simp)).focus_field realized.ownership
    realized.classesWellFormed typed.wellFormed.2.1.2 focused

end Dada.Unique.Typing
