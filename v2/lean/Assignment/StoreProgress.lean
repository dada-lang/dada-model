import Assignment.StorageTypes
import Assignment.WriteOwnership
import Shared.TypingGiveCore
import Shared.TypingBindingSoundness
import Destructors.Safety

namespace Dada.Assignment
open Shared Shared.Typing

inductive StoreFacts (classes : ClassTable) (before : Context) (incoming : ValueType)
    (after : Context) : Place → Prop where
  | variable {name fixed previous} :
      before.bindings.lookup name = some fixed →
      before.current.lookup name = some previous →
      storageType incoming = fixed → replaceable classes previous = true →
      after = before.withCurrent (before.current.replace name (some incoming)) →
      StoreFacts classes before incoming after (.variable name)
  | field {base name fixed source parent declaration fieldType previous} :
      before.bindings.lookup (splitPlace base).1 = some fixed →
      before.current.lookup (splitPlace base).1 = some (some source) →
      focus classes source (splitPlace base).2 = some parent →
      parent.permission = .given →
      classes.lookup parent.base = some declaration →
      declaration.fields.lookup name = some fieldType →
      fieldDescription classes parent name = some previous →
      storageType incoming = fieldType → replaceable classes previous = true →
      after = before.withCurrent (before.current.replace (splitPlace base).1
        (some (replaceView classes source incoming ((splitPlace base).2 ++ [name])))) →
      StoreFacts classes before incoming after (.field base name)

theorem store_facts (stored : store classes before place incoming = some after) :
    before.WellFormed classes ∧ Admissible classes incoming ∧
      StoreFacts classes before incoming after place := by
  unfold store at stored
  obtain ⟨current, updated, checked⟩ := Option.bind_eq_some_iff.mp stored
  simp only [decide_eq_true_eq] at checked
  split at checked <;> simp_all only [Option.some.injEq, reduceCtorEq]
  subst after
  unfold storeCurrent at updated
  split at updated
  · contradiction
  next accepted =>
    have wf : before.WellFormed classes ∧ Admissible classes incoming := by simpa using accepted
    refine ⟨wf.1, wf.2, ?_⟩
    cases place with
    | «variable» name =>
      simp only [splitPlace, List.isEmpty_nil, ↓reduceIte] at updated
      obtain ⟨fixed, declared, rest⟩ := Option.bind_eq_some_iff.mp updated
      obtain ⟨previous, found, rest⟩ := Option.bind_eq_some_iff.mp rest
      split at rest
      · simp at rest
      next permitted =>
        have conditions : storageType incoming = fixed ∧ replaceable classes previous = true := by
          simpa using permitted
        change some (before.current.replace name (some incoming)) = some current at rest
        injection rest with equal
        subst current
        exact .variable declared found conditions.1 conditions.2 rfl
    | field base name =>
      have nonempty : ((splitPlace base).2 ++ [name]).isEmpty = false := by simp
      simp only [splitPlace, List.length_append, List.length_singleton, Nat.add_sub_cancel,
        List.take_left, List.getLast?_append, List.getLast?_singleton,
        Option.some_or, nonempty, Bool.false_eq_true,
        ↓reduceIte] at updated
      obtain ⟨fixed, declared, afterFixed⟩ := Option.bind_eq_some_iff.mp updated
      obtain ⟨slot, found, afterSlot⟩ := Option.bind_eq_some_iff.mp afterFixed
      obtain ⟨source, present, afterSource⟩ := Option.bind_eq_some_iff.mp afterSlot
      rw [present] at found
      dsimp only [Bind.bind, Option.bind] at afterSource
      obtain ⟨parent, focused, rest⟩ := Option.bind_eq_some_iff.mp afterSource
      split at rest
      · simp at rest
      next unique =>
        have unique : parent.permission = .given := by simpa using unique
        obtain ⟨declaration, parentDeclared, rest⟩ := Option.bind_eq_some_iff.mp rest
        obtain ⟨fieldType, fieldDeclared, rest⟩ := Option.bind_eq_some_iff.mp rest
        obtain ⟨previous, described, rest⟩ := Option.bind_eq_some_iff.mp rest
        split at rest
        · simp at rest
        next permitted =>
          have conditions : storageType incoming = fieldType ∧ replaceable classes previous = true := by
            simpa using permitted
          change some (before.current.replace (splitPlace base).1
            (some (replaceView classes source incoming ((splitPlace base).2 ++ [name])))) = some current at rest
          injection rest with equal
          subst current
          exact .field declared found focused unique parentDeclared fieldDeclared described
            conditions.1 conditions.2 rfl

theorem write_exists (stored : Stored state target previous) (incoming : Reference) :
    ∃ result, Write state target incoming result := by
  rcases state with ⟨objects, variables, nextId⟩
  cases target with
  | «variable» name =>
    obtain ⟨leading, suffix, equality⟩ := List.mem_iff_append.mp stored
    dsimp at equality
    subst variables
    exact ⟨_, .variable ..⟩
  | field parent name =>
    obtain ⟨⟨className, fields⟩, objectStored, fieldStored⟩ := stored
    obtain ⟨before, after, equality⟩ := List.mem_iff_append.mp objectStored
    obtain ⟨leading, suffix, fieldsEquality⟩ := List.mem_iff_append.mp fieldStored
    dsimp at equality fieldsEquality
    subst objects fields
    exact ⟨_, .field ..⟩

theorem slot_replaceable (matched : SlotMatches classes state slot description)
    (permitted : replaceable classes description = true) :
    Replaceable classes.erase state slot := by
  cases slot <;> cases description <;> try contradiction
  · trivial
  · exact Destructors.Satisfies_struct matched (by simpa [replaceable] using permitted)

private theorem focus_class (focused : focus classes ty path = some result) :
    Unique.Typing.classAt classes.nominal ty.base path = some result.base := by
  have nominal := focus_nominal focused
  unfold Unique.Typing.focus at nominal
  split at nominal
  · contradiction
  dsimp only at nominal
  split at nominal
  · contradiction
  obtain ⟨target, atClass, rest⟩ := Option.bind_eq_some_iff.mp nominal
  change Unique.Typing.classAt classes.nominal ty.base path = some target at atClass
  split at rest
  next empty =>
    have empty := List.isEmpty_iff.mp empty
    subst path
    injection rest with equal
    simpa [ValueType.base, Unique.Typing.classAt, Unique.Typing.normalize_className] using
      congrArg (fun t : Unique.Typing.ViewType => some t.className) equal
  next =>
    split at rest <;> injection rest with equal <;>
      simpa [ValueType.base, ← equal, Unique.Typing.ViewType.whole,
        Unique.Typing.normalize_className] using atClass

private theorem focus_field_class (declared : classes.lookup ty.base = some declaration)
    (fieldDeclared : declaration.fields.lookup field = some fieldType)
    (focused : focus classes ty [field] = some child) : child.base = fieldType.className := by
  have atClass := focus_class focused
  simpa [Unique.Typing.classAt, ClassTable.nominal_lookup,
    nominal_field_lookup, declared, fieldDeclared] using atClass.symm

private theorem field_replaceable
    (realized : Realizes classes environment state pending)
    (satisfied : Satisfies classes state reference ty)
    (unique : reference.mode = .unique)
    (dataStored : (reference.object, data) ∈ state.objects)
    (dataClass : data.className = ty.base)
    (fieldStored : (field, slot) ∈ data.fields)
    (declared : classes.lookup ty.base = some declaration)
    (fieldDeclared : declaration.fields.lookup field = some fieldType)
    (described : fieldDescription classes ty field = some description)
    (permitted : replaceable classes description = true) :
    Replaceable classes.erase state slot := by
  cases slot with
  | none => trivial
  | some child =>
    have read : readPath state reference [field] = some (some child) := by
      have dataLookup := lookup_of_member realized.ownership.objectKeys dataStored
      obtain ⟨_, _, shape, fieldsDistinct⟩ := realized.ownership.shapes _ _ dataStored
      have fieldLookup := lookup_of_member (shape ▸ fieldsDistinct) fieldStored
      simp [readPath, dataLookup, fieldLookup, unique]
    unfold fieldDescription at described
    split at described
    next empty =>
      have impossible := (satisfied.negative [field] empty).symm.trans read
      simp at impossible
    next occupied =>
      obtain ⟨previous, focused, same⟩ := Option.map_eq_some_iff.mp described
      subst description
      have structPrevious : StructType classes previous := by simpa [replaceable] using permitted
      have sameClass := focus_field_class declared fieldDeclared focused
      obtain ⟨actualDeclaration, actualField, childData, actualDeclared, actualFieldDeclared,
        childStored, childClass⟩ := realized.fields _ _ _ _ dataStored fieldStored
      have sameDeclaration : actualDeclaration = declaration :=
        member_value_unique realized.classesWellFormed.1
          (dataClass ▸ actualDeclared) (lookup_member declared)
      subst actualDeclaration
      have sameField : actualField = fieldType :=
        member_value_unique (realized.classesWellFormed.2 _ (lookup_member declared)).1
          actualFieldDeclared (lookup_member fieldDeclared)
      subst actualField
      obtain ⟨childDeclaration, childDeclared, kind⟩ := structPrevious.declaration
      refine ⟨childData, ⟨childDeclaration.fields.map Prod.fst, childDeclaration.kind⟩,
        childStored, ?_, kind⟩
      apply List.mem_map.mpr
      exact ⟨(previous.base, childDeclaration), lookup_member childDeclared,
        by simp [childClass, sameClass]⟩

theorem store_writable (stored : store classes before place incoming = some after)
    (realized : Realizes classes before.current state pending) :
    ∃ target previous, Writable state place target previous ∧
      Replaceable classes.erase state previous := by
  cases (store_facts stored).2.2 with
  | @«variable» name fixed previous _ found _ permitted _ =>
    have member := Environment.lookup_member found
    cases previous with
    | none => exact ⟨_, _, .variable (realized.emptyVariables _ member), trivial⟩
    | some ty =>
      obtain ⟨reference, stored, satisfied⟩ := realized.initializedVariables _ _ member
      exact ⟨_, _, .variable stored,
        slot_replaceable (description := some ty) satisfied permitted⟩
  | @field base name fixed source parent declaration fieldType previous
      _ found focused given declared fieldDeclared described _ permitted _ =>
    have member := Environment.lookup_member found
    have admissible := Environment.admissible realized.environmentWellFormed member
    obtain ⟨root, rootStored, sourceSatisfied⟩ := realized.initializedVariables _ _ member
    have observations := focus_observations realized.classesWellFormed admissible.2 focused
    obtain ⟨reference, _, read, _, _⟩ := sourceSatisfied.positive _ observations.positive
    have satisfied := sourceSatisfied.focus realized.classesWellFormed realized.ownership
      admissible.2 focused read
    have unique : reference.mode = .unique := by rw [satisfied.mode, given]; rfl
    obtain ⟨target, resolved⟩ := resolve_from_readPath rootStored read
    change Resolve state (placeFrom (splitPlace base).1 (splitPlace base).2) _ _ _ at resolved
    rw [placeFrom_splitPlace, unique] at resolved
    obtain ⟨data, dataStored, dataClass⟩ := satisfied.root
    change data.className = parent.base at dataClass
    obtain ⟨untypedDeclaration, untypedDeclared, shape, _⟩ := realized.ownership.shapes _ _ dataStored
    have erasedDeclared :
        (parent.base, ⟨declaration.fields.map Prod.fst, declaration.kind⟩) ∈ classes.erase :=
      List.mem_map.mpr ⟨(parent.base, declaration), lookup_member declared, rfl⟩
    have sameDeclaration : untypedDeclaration =
        ⟨declaration.fields.map Prod.fst, declaration.kind⟩ :=
      member_value_unique realized.classesWellFormed.erase.1
        (dataClass ▸ untypedDeclared) erasedDeclared
    have actualFields : data.fields.map Prod.fst = declaration.fields.map Prod.fst := by
      simpa [sameDeclaration] using shape
    have namePresent : name ∈ data.fields.map Prod.fst := by
      rw [actualFields]
      exact List.mem_map.mpr ⟨(name, fieldType), lookup_member fieldDeclared, rfl⟩
    obtain ⟨⟨actual, slot⟩, fieldStored, equality⟩ := List.mem_map.mp namePresent
    dsimp at equality
    subst actual
    exact ⟨_, _, .field resolved dataStored fieldStored,
      field_replaceable realized satisfied unique dataStored dataClass fieldStored
        declared fieldDeclared described permitted⟩

theorem store_exists (stored : store classes before place ty = some after)
    (realized : Realizes classes before.current state ((incoming, ty) :: pending)) :
    ∃ target previous result, Writable state place target previous ∧
      Replaceable classes.erase state previous ∧ Write state target incoming result := by
  obtain ⟨target, previous, writable, replaceable⟩ := store_writable stored realized
  obtain ⟨result, written⟩ := write_exists writable.stored incoming
  exact ⟨target, previous, result, writable, replaceable, written⟩

end Dada.Assignment
