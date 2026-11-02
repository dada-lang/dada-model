import Shared.TypingGiveCore

namespace Dada.Shared.Typing

theorem FieldsMatchClasses.take (fields : FieldsMatchClasses classes before)
    (taken : Take before place object after) : FieldsMatchClasses classes after := by
  intro parent data field target stored atField
  obtain ⟨oldData, oldStored, sameClass, _, remaining⟩ := taken.object_data parent data stored
  obtain ⟨declaration, targetClass, targetData, declared, fieldDeclared, targetStored, targetName⟩ :=
    fields parent oldData field target oldStored (remaining field target atField)
  obtain ⟨newData, newStored, newClass⟩ := taken.old_object_data target.object targetData targetStored
  exact ⟨declaration, targetClass, newData, sameClass ▸ declared, fieldDeclared,
    newStored, newClass.trans targetName⟩

theorem FieldsMatchClasses.promote (fields : FieldsMatchClasses classes before)
    (promoted : Promote before place object after) : FieldsMatchClasses classes after := by
  intro parent data field target stored atField
  obtain ⟨oldData, oldStored, sameClass, _, remaining⟩ := promoted.object_data parent data stored
  obtain ⟨oldReference, oldField, sameTarget⟩ := remaining field target atField
  obtain ⟨declaration, targetClass, targetData, declared, fieldDeclared, targetStored, targetName⟩ :=
    fields parent oldData field oldReference oldStored oldField
  obtain ⟨newData, newStored, newClass⟩ := promoted.old_object_data oldReference.object targetData targetStored
  exact ⟨declaration, targetClass, newData, sameClass ▸ declared, fieldDeclared,
    sameTarget ▸ newStored, newClass.trans targetName⟩

theorem Satisfies.take_taken (wf : WellFormedWith classes.erase before pending)
    (afterWf : WellFormedWith classes.erase after afterPending)
    (taken : Take before source reference.object after) (satisfied : Satisfies classes before reference ty) :
    Satisfies classes after reference ty := by
  constructor
  · exact satisfied.mode
  · obtain ⟨data, stored, same⟩ := satisfied.root
    obtain ⟨newData, newStored, newSame⟩ := taken.old_object_data reference.object data stored
    exact ⟨newData, newStored, newSame.trans same⟩
  · intro path positive
    obtain ⟨target, data, read, stored, correctClass⟩ := satisfied.positive path positive
    obtain ⟨newData, newStored, sameClass⟩ := taken.old_object_data target.object data stored
    exact ⟨target, newData, take_readPath_taken wf afterWf taken read, newStored, sameClass ▸ correctClass⟩
  · intro path negative
    exact take_readPath_taken wf afterWf taken (satisfied.negative path negative)

  · intro path target permission declared read
    exact satisfied.modes path target permission declared (take_readPath_back wf taken read)

theorem Satisfies.take_frame (wf : WellFormedWith classes.erase before pending)
    (afterWf : WellFormedWith classes.erase after afterPending)
    (taken : Take before source removed after)
    (cut : Route before pending cutSite cutPath (.owned removed))
    (route : Route before pending site initial reference)
    (satisfied : Satisfies classes before reference ty)
    (separate : ∀ path, Pos classes ty path ∨ Neg ty path →
      ¬ (site = cutSite ∧ cutPath.IsPrefix (initial ++ path))) :
    Satisfies classes after reference ty := by
  constructor
  · exact satisfied.mode
  · obtain ⟨data, stored, same⟩ := satisfied.root
    obtain ⟨newData, newStored, newSame⟩ := taken.old_object_data reference.object data stored
    exact ⟨newData, newStored, newSame.trans same⟩
  · intro path positive
    obtain ⟨target, data, read, stored, correctClass⟩ := satisfied.positive path positive
    obtain ⟨newData, newStored, sameClass⟩ := taken.old_object_data target.object data stored
    exact ⟨target, newData,
      take_readPath_frame wf afterWf taken cut route read (separate path (Or.inl positive)),
      newStored, sameClass ▸ correctClass⟩
  · intro path negative
    exact take_readPath_frame wf afterWf taken cut route (satisfied.negative path negative)
      (separate path (Or.inr negative))

  · intro path target permission declared read
    exact satisfied.modes path target permission declared (take_readPath_back wf taken read)

theorem Satisfies.take_other_root (wf : WellFormedWith classes.erase before pending)
    (afterWf : WellFormedWith classes.erase after afterPending)
    (resolved : Resolve before place source removed .unique) (taken : Take before source removed after)
    (owner : RootOwns before pending site reference)
    (different : site ≠ .variable (splitPlace place).1)
    (satisfied : Satisfies classes before reference ty) : Satisfies classes after reference ty := by
  apply satisfied.take_frame wf afterWf taken (route_of_resolve resolved) (.root owner)
  intro path _ same
  exact different same.1

theorem Satisfies.emptyPath (wf : WellFormedWith classes.erase before pending)
    (afterWf : WellFormedWith classes.erase after afterPending)
    (classesWf : classes.WellFormed) (normal : Normalized classes ty)
    (satisfied : Satisfies classes before reference ty)
    (root : RootOwns before pending site reference)
    (cut : Route before pending site path (.owned removed))
    (taken : Take before source removed after)
    (read : readPath before reference path = some (some (.owned removed)))
    (emptied : emptyPath classes ty path = some remaining) :
    Satisfies classes after reference remaining := by
  have facts := Unique.Typing.emptyPath_observations classesWf.nominal normal (emptyPath_nominal emptied)
  constructor
  · simpa [emptyPath_permission emptied] using satisfied.mode
  · obtain ⟨data, stored, correct⟩ := satisfied.root
    obtain ⟨newData, newStored, same⟩ := taken.old_object_data reference.object data stored
    exact ⟨newData, newStored, same.trans (correct.trans facts.className.symm)⟩
  · intro query positive
    obtain ⟨wasPositive, outside⟩ := facts.positives query positive
    obtain ⟨target, data, oldRead, stored, correct⟩ := satisfied.positive query wasPositive
    obtain ⟨newData, newStored, same⟩ := taken.old_object_data target.object data stored
    refine ⟨target, newData,
      take_readPath_frame wf afterWf taken cut (.root root) oldRead (fun both => outside both.2),
      newStored, ?_⟩
    simpa [facts.className, same] using correct
  · intro query negative
    rcases facts.negatives query negative with rfl | ⟨wasNegative, outside⟩
    · exact take_readPath_cleared wf afterWf taken facts.nonempty read rfl
    · exact take_readPath_frame wf afterWf taken cut (.root root) (satisfied.negative query wasNegative)
        (fun both => outside both.2)

  · intro query target permission declared read
    rw [facts.className] at declared
    rw [emptyPath_permission emptied]
    exact satisfied.modes query target permission declared (take_readPath_back wf taken read)

-- All unrelated variables and pending roots retain their descriptions. The
-- moved root is added to the pending results and only its source variable's
-- description is replaced.
theorem Realizes.give_replace (realized : Realizes classes environment before pending)
    (resolved : Resolve before place source object .unique) (taken : Take before source object after)
    (admissible : Admissible classes ty)
    (target : Satisfies classes after (.owned object) ty)
    (afterWf : (environment.replace (splitPlace place).1 replacement).WellFormed classes)
    (changed : match replacement with
      | none => ((splitPlace place).1, none) ∈ after.variables
      | some remaining => ∃ root, ((splitPlace place).1, some root) ∈ after.variables ∧
          Satisfies classes after root remaining) :
    Realizes classes (environment.replace (splitPlace place).1 replacement) after
      ((Reference.owned object, ty) :: pending) := by
  have afterOwnership := (Give.move resolved taken).preserves_pending realized.ownership
  constructor
  · exact realized.classesWellFormed
  · exact afterWf
  · intro id view member
    rcases List.mem_cons.mp member with same | member
    · cases same; exact admissible
    · exact realized.pendingTypes id view member
  · exact afterOwnership
  · exact realized.fields.take taken
  · intro name
    rw [Environment.replace_keys, taken.variable_keys]
    exact realized.variableDomain name
  · intro name member
    rcases Environment.replace_member member with ⟨rfl, same⟩ | ⟨different, old⟩
    · subst replacement
      exact changed
    · exact take_preserves_other_variable resolved taken different (realized.emptyVariables name old)
  · intro name view member
    rcases Environment.replace_member member with ⟨rfl, same⟩ | ⟨different, old⟩
    · subst replacement
      exact changed
    · obtain ⟨root, atRoot, satisfied⟩ := realized.initializedVariables name view old
      exact ⟨root, take_preserves_other_variable resolved taken different atRoot,
        satisfied.take_other_root realized.ownership afterOwnership resolved taken (.variable atRoot)
          (by intro same; exact different (RootSite.variable.inj same))⟩
  · intro id view member
    rcases List.mem_cons.mp member with same | member
    · cases same; exact target
    · exact (realized.pendingValues id view member).take_other_root realized.ownership afterOwnership
        resolved taken (.pending (List.mem_map.mpr ⟨(id, view), member, rfl⟩))
        (by intro impossible; cases impossible)

end Dada.Shared.Typing
