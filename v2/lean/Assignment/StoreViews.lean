import Assignment.ViewLemmas
import Shared.TypingFocus

namespace Dada.Assignment
open Shared Shared.Typing

-- Facts about the statically selected field, independent of any heap update.
structure StorePathFacts (classes : ClassTable) (source incoming : ValueType)
    (target : Path) : Prop where
  sourceGiven : source.permission = .given
  atClass : Unique.Typing.classAt classes.nominal source.base target = some incoming.base
  atPermission : declaredPermission classes source.base target = some incoming.permission
  properPositive : ∀ path, path <+: target → path.length < target.length → Pos classes source path

theorem storePathFacts {classes : ClassTable} (classesWF : classes.WellFormed)
    {source incoming parent : ValueType} {parentPath : Path} {field : FieldName}
    {declaration : TypedClass} {fieldType : FieldType}
    (normal : Normalized classes source)
    (focused : focus classes source parentPath = some parent)
    (givenParent : parent.permission = .given)
    (classFound : classes.lookup parent.base = some declaration)
    (fieldFound : declaration.fields.lookup field = some fieldType)
    (sameType : storageType incoming = fieldType) :
    StorePathFacts classes source incoming (parentPath ++ [field]) := by
  have observations := focus_observations classesWF normal focused
  obtain ⟨permission, declared, composed⟩ := focus_permission focused
  obtain ⟨sourceGiven, pathGiven⟩ := (Perm.comp_eq_given_iff _ _).mp (composed.symm.trans givenParent)
  have fieldClass : fieldType.className = incoming.base := by
    simpa [storageType] using (congrArg FieldType.className sameType).symm
  have fieldPerm : fieldType.permission = incoming.permission := by
    simpa [storageType] using (congrArg FieldType.permission sameType).symm
  have parentClass : Unique.Typing.classAt classes.nominal source.base parentPath = some parent.base := observations.className
  constructor
  · exact sourceGiven
  · rw [Unique.Typing.classAt_append, parentClass]
    simp [Unique.Typing.classAt, ClassTable.nominal_lookup, nominal_field_lookup,
      classFound, fieldFound, fieldClass]
  · rw [declaredPermission_append parentClass]
    simp [declared, pathGiven, declaredPermission, classFound, fieldFound,
      fieldPerm, Perm.comp_given_right, Perm.comp_given_left]
  · intro path pre short
    have parentPrefix : path <+: parentPath := by
      have length : path.length ≤ parentPath.length := by
        simp only [List.length_append, List.length_singleton] at short
        omega
      exact List.prefix_of_prefix_length_le pre (List.prefix_append _ _) length
    exact observations.positive.prefix parentPrefix

theorem StorePathFacts.classAt_append (facts : StorePathFacts classes source incoming target)
    (suffix : Path) :
    Unique.Typing.classAt classes.nominal source.base (target ++ suffix) =
      Unique.Typing.classAt classes.nominal incoming.base suffix := by
  rw [Unique.Typing.classAt_append, facts.atClass]
  rfl

theorem StorePathFacts.permission_append (facts : StorePathFacts classes source incoming target)
    (suffix : Path) :
    declaredPermission classes source.base (target ++ suffix) =
      (declaredPermission classes incoming.base suffix).map (incoming.permission.comp) := by
  rw [declaredPermission_append facts.atClass, facts.atPermission]
  cases declaredPermission classes incoming.base suffix <;> rfl

theorem satisfies_preserved
    {classes : ClassTable} {before after : State} {ty : ValueType} {reference : Reference}
    (satisfied : Satisfies classes before reference ty)
    (preserveClasses : ∀ object data, (object, data) ∈ before.objects →
      ∃ newData, (object, newData) ∈ after.objects ∧ newData.className = data.className)
    (forward : ∀ path slot,
      readPath before reference path = some slot → readPath after reference path = some slot)
    (backward : ∀ path reached,
      readPath after reference path = some (some reached) →
      readPath before reference path = some (some reached)) :
    Satisfies classes after reference ty := by
  constructor
  · exact satisfied.mode
  · obtain ⟨data, member, named⟩ := satisfied.root
    obtain ⟨newData, member, same⟩ := preserveClasses _ _ member
    exact ⟨newData, member, same.trans named⟩
  · intro path known
    obtain ⟨reached, data, read, member, named⟩ := satisfied.positive path known
    obtain ⟨newData, member, same⟩ := preserveClasses _ _ member
    exact ⟨reached, newData, forward path _ read, member, by simpa only [same] using named⟩
  · intro path known
    exact forward path _ (satisfied.negative path known)
  · intro path reached permission declared read
    exact satisfied.modes path reached permission declared (backward path reached read)

-- Heap effects are supplied separately from the static replacement calculation.
-- The reverse observation premise is needed for the modes of every readable path,
-- including paths hidden by the current view.
theorem satisfies_replaceView
    {classes : ClassTable} {before after : State} {source incoming : ValueType}
    {reference value : Reference} {target : Path} {pending : List Reference}
    (classesWF : classes.WellFormed)
    (facts : StorePathFacts classes source incoming target)
    (nonempty : target ≠ [])
    (sourceSatisfied : Satisfies classes before reference source)
    (incomingSatisfied : Satisfies classes after value incoming)
    (afterWF : WellFormedWith classes.erase after pending)
    (preserveClasses : ∀ object data, (object, data) ∈ before.objects →
      ∃ newData, (object, newData) ∈ after.objects ∧ newData.className = data.className)
    (forward : ∀ path slot, ¬target <+: path →
      readPath before reference path = some slot → readPath after reference path = some slot)
    (backward : ∀ path reached, ¬target <+: path →
      readPath after reference path = some (some reached) →
      readPath before reference path = some (some reached))
    (installed : readPath after reference target = some (some value)) :
    Satisfies classes after reference (replaceView classes source incoming target) := by
  constructor
  · exact sourceSatisfied.mode
  · obtain ⟨data, member, named⟩ := sourceSatisfied.root
    obtain ⟨newData, member, same⟩ := preserveClasses _ _ member
    exact ⟨newData, member, same.trans named⟩
  · intro path known
    rcases replaceView_positive classesWF nonempty facts.atClass facts.properPositive known with
      ⟨oldKnown, outside⟩ | ⟨suffix, rfl, incomingKnown⟩
    · obtain ⟨reached, data, read, member, named⟩ := sourceSatisfied.positive path oldKnown
      obtain ⟨newData, member, same⟩ := preserveClasses _ _ member
      refine ⟨reached, newData, forward path _ outside read, member, ?_⟩
      change Unique.Typing.classAt classes.nominal source.nominal.className path = some newData.className
      simpa only [same] using named
    · obtain ⟨reached, data, read, member, named⟩ := incomingSatisfied.positive suffix incomingKnown
      refine ⟨reached, data, (readPath_append afterWF installed suffix).trans read, member, ?_⟩
      change Unique.Typing.classAt classes.nominal source.base (target ++ suffix) = some data.className
      rw [facts.classAt_append]
      exact named
  · intro path known
    rcases replaceView_negative known with ⟨oldKnown, outside⟩ | ⟨suffix, rfl, incomingKnown⟩
    · exact forward path _ outside (sourceSatisfied.negative path oldKnown)
    · exact (readPath_append afterWF installed suffix).trans
        (incomingSatisfied.negative suffix incomingKnown)
  · intro path reached permission declared read
    change declaredPermission classes source.base path = some permission at declared
    change reached.mode = (source.permission.comp permission).toMode
    by_cases inside : target <+: path
    · obtain ⟨suffix, rfl⟩ := inside
      rw [facts.permission_append] at declared
      obtain ⟨tailPermission, tailDeclared, same⟩ := Option.map_eq_some_iff.mp declared
      have tailRead := (readPath_append afterWF installed suffix).symm.trans read
      have mode := incomingSatisfied.modes suffix reached tailPermission tailDeclared tailRead
      rw [facts.sourceGiven, Perm.comp_given_left, ←same]
      exact mode
    · exact sourceSatisfied.modes path reached permission declared (backward path reached inside read)

end Dada.Assignment
