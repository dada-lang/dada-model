import Unique.TypingExpressionSoundness
import Unique.ViewSoundness
import Unique.TypingOwnership

namespace Dada.Unique.Typing

theorem Environment.lookup_member {environment : Environment} (found : environment.lookup name = some description) :
    (name, description) ∈ environment := by
  unfold Environment.lookup at found
  obtain ⟨entry, present, equal⟩ := Option.map_eq_some_iff.mp found
  have member := List.mem_of_find?_eq_some present
  have key := List.find?_some present
  have same : entry.1 = name := by simpa using key
  cases entry
  simp only at same equal
  subst_vars
  exact member

theorem Environment.admissible {environment : Environment} (wf : environment.WellFormed classes)
    (member : (name, some ty) ∈ environment) : Admissible classes ty := by
  have all := List.all_eq_true.mp wf.2
  simpa using all (name, some ty) member

-- Successful static taking identifies the owning variable, its current view,
-- the relative path, and exactly the one environment entry that is changed.
theorem take_description (taken : take classes before place = some (ty, after)) :
    ∃ source,
      before.lookup (splitPlace place).1 = some (some source) ∧
      focus classes source (splitPlace place).2 = some ty ∧
      (((splitPlace place).2 = [] ∧ after = before.replace (splitPlace place).1 none) ∨
       ∃ remaining, (splitPlace place).2 ≠ [] ∧
         emptyPath classes source (splitPlace place).2 = some remaining ∧
         after = before.replace (splitPlace place).1 (some remaining)) := by
  unfold take at taken
  obtain ⟨slot, found, slotBind⟩ := Option.bind_eq_some_iff.mp taken
  obtain ⟨source, value, resultBind⟩ := Option.bind_eq_some_iff.mp slotBind
  have foundSource : before.lookup (splitPlace place).1 = some (some source) := by
    rw [value] at found
    exact found
  obtain ⟨result, focused, resultBody⟩ := Option.bind_eq_some_iff.mp resultBind
  by_cases empty : (splitPlace place).2 = []
  · simp [empty] at resultBody
    rcases resultBody with ⟨rfl, rfl⟩
    exact ⟨source, foundSource, focused, Or.inl ⟨empty, rfl⟩⟩
  · simp only [empty, ↓reduceIte] at resultBody
    obtain ⟨remaining, emptied, finalBind⟩ := Option.bind_eq_some_iff.mp resultBody
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at finalBind
    rcases finalBind with ⟨rfl, rfl⟩
    exact ⟨source, foundSource, focused, Or.inr ⟨remaining, empty, emptied, rfl⟩⟩

theorem take_evaluates (taken : take classes before place = some (ty, after))
    (realized : Realizes classes before state pending) :
    ∃ result object, Eval classes.erase state (.give place) result object := by
  obtain ⟨source, found, focused, _⟩ := take_description taken
  have member := Environment.lookup_member found
  have admissible := Environment.admissible realized.environmentWellFormed member
  obtain ⟨object, stored, satisfied⟩ := realized.initializedVariables _ _ member
  have facts := focus_observations realized.classesWellFormed admissible.2 focused
  obtain ⟨target, data, read, _, _⟩ := satisfied.positive _ facts.positive
  obtain ⟨destination, resolved⟩ := resolve_from_readPath stored read
  rw [placeFrom_splitPlace] at resolved
  obtain ⟨result, cleared⟩ := resolved.take_exists
  exact ⟨result, target, .give resolved cleared⟩

theorem Satisfies.focus (satisfied : Satisfies classes state object source)
    (classesWf : classes.WellFormed) (wf : WellFormedWith classes.erase state pending)
    (normal : Normalized classes source)
    (focused : focus classes source path = some result)
    (read : readPath state object path = some (some target)) :
    Satisfies classes state target result := by
  have observations := focus_observations classesWf normal focused
  constructor
  · obtain ⟨target', data, read', member, correct⟩ := satisfied.positive path observations.positive
    have same : target' = target := by simpa [read] using read'.symm
    subst target'
    exact ⟨data, member, by simpa [observations.className] using correct.symm⟩
  · intro suffix known
    obtain ⟨resultObject, data, completeRead, member, correct⟩ :=
      satisfied.positive _ (observations.positives suffix known)
    refine ⟨resultObject, data, (readPath_append wf read suffix).symm.trans completeRead, member, ?_⟩
    simpa [classAt_append, observations.className] using correct
  · intro suffix known
    exact (readPath_append wf read suffix).symm.trans
      (satisfied.negative _ (observations.negatives suffix known))

theorem Environment.replace_member {environment : Environment}
    (member : (name, description) ∈ environment.replace root replacement) :
    (name = root ∧ description = replacement) ∨
      (name ≠ root ∧ (name, description) ∈ environment) := by
  obtain ⟨⟨key, value⟩, old, changed⟩ := List.mem_map.mp member
  by_cases same : key = root
  · simp [same] at changed
    exact Or.inl ⟨changed.1.symm, changed.2.symm⟩
  · simp [same] at changed
    rcases changed with ⟨rfl, rfl⟩
    exact Or.inr ⟨same, old⟩

theorem resolve_source_nonempty (resolved : Resolve state place source object)
    (nonempty : (splitPlace place).2 ≠ []) : ∃ parent field, source = .field parent field := by
  cases resolved with
  | «variable» _ => exact False.elim (nonempty rfl)
  | field _ _ _ => exact ⟨_, _, rfl⟩

theorem resolve_source_empty (resolved : Resolve state place source object)
    (empty : (splitPlace place).2 = []) : source = .variable (splitPlace place).1 := by
  cases resolved with
  | «variable» _ => rfl
  | field _ _ _ => simp [splitPlace] at empty

theorem take_preserves_other_variable
    (resolved : Resolve before place source object) (taken : Take before source object after)
    (different : name ≠ (splitPlace place).1) (stored : (name, slot) ∈ before.variables) :
    (name, slot) ∈ after.variables := by
  apply taken.stored_unchanged (place := .variable name) _ stored
  intro same
  cases resolved with
  | «variable» _ => cases same; exact different rfl
  | field _ _ _ => cases same

theorem take_preserves_variable_field (resolved : Resolve before place source object)
    (taken : Take before source object after) (nonempty : (splitPlace place).2 ≠ [])
    (stored : (name, slot) ∈ before.variables) : (name, slot) ∈ after.variables := by
  obtain ⟨parent, field, rfl⟩ := resolve_source_nonempty resolved nonempty
  exact taken.stored_unchanged (place := .variable name) (by intro impossible; cases impossible) stored

theorem Satisfies.take_other_root (wf : WellFormedWith classes.erase before pending)
    (resolved : Resolve before place source removed) (taken : Take before source removed after)
    (owner : RootOwns before pending site object)
    (different : site ≠ .variable (splitPlace place).1)
    (satisfied : Satisfies classes before object ty) : Satisfies classes after object ty := by
  apply satisfied.take_frame wf taken (route_of_resolve resolved) (.root owner)
  intro path _ same
  exact different same.1

theorem Satisfies.emptyPath (wf : WellFormedWith classes.erase before pending)
    (classesWf : classes.WellFormed) (normal : Normalized classes ty)
    (satisfied : Satisfies classes before object ty)
    (root : RootOwns before pending site object)
    (cut : Route before pending site path removed)
    (taken : Take before source removed after)
    (read : readPath before object path = some (some removed))
    (emptied : emptyPath classes ty path = some remaining) :
    Satisfies classes after object remaining := by
  have facts := emptyPath_observations classesWf normal emptied
  constructor
  · obtain ⟨data, stored, correct⟩ := satisfied.root
    obtain ⟨newData, newStored, same⟩ := taken.old_object_data object data stored
    exact ⟨newData, newStored, same.trans (correct.trans facts.className.symm)⟩
  · intro query positive
    obtain ⟨wasPositive, outside⟩ := facts.positives query positive
    obtain ⟨target, data, oldRead, stored, correct⟩ := satisfied.positive query wasPositive
    obtain ⟨newData, newStored, same⟩ := taken.old_object_data target data stored
    refine ⟨target, newData,
      take_readPath_frame wf taken cut (.root root) oldRead (fun both => outside both.2),
      newStored, ?_⟩
    simpa [facts.className, same] using correct
  · intro query negative
    rcases facts.negatives query negative with rfl | ⟨wasNegative, outside⟩
    · exact take_readPath_cleared wf taken facts.nonempty read
    · exact take_readPath_frame wf taken cut (.root root) (satisfied.negative query wasNegative)
        (fun both => outside both.2)

-- All unrelated variables and pending roots retain their descriptions. The
-- moved root is added to the pending results and only its source variable's
-- description is replaced.
theorem Realizes.give_replace (realized : Realizes classes environment before pending)
    (resolved : Resolve before place source object) (taken : Take before source object after)
    (admissible : Admissible classes ty)
    (target : Satisfies classes after object ty)
    (afterWf : (environment.replace (splitPlace place).1 replacement).WellFormed classes)
    (changed : match replacement with
      | none => ((splitPlace place).1, none) ∈ after.variables
      | some remaining => ∃ root, ((splitPlace place).1, some root) ∈ after.variables ∧
          Satisfies classes after root remaining) :
    Realizes classes (environment.replace (splitPlace place).1 replacement) after
      ((object, ty) :: pending) := by
  constructor
  · exact realized.classesWellFormed
  · exact afterWf
  · intro id view member
    rcases List.mem_cons.mp member with same | member
    · cases same; exact admissible
    · exact realized.pendingTypes id view member
  · exact taken.preserves_pending realized.ownership
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
        satisfied.take_other_root realized.ownership resolved taken (.variable atRoot)
          (by intro same; exact different (RootSite.variable.inj same))⟩
  · intro id view member
    rcases List.mem_cons.mp member with same | member
    · cases same; exact target
    · exact (realized.pendingValues id view member).take_other_root realized.ownership
        resolved taken (.pending (List.mem_map.mpr ⟨(id, view), member, rfl⟩))
        (by intro impossible; cases impossible)

theorem give_sound (beforeWf : before.WellFormed classes)
    (taken : take classes before place = some (ty, after)) (admissible : Admissible classes ty)
    (afterWf : after.WellFormed classes) : ExpressionSound classes before (.give place) ty after := by
  intro state pending realized
  refine ⟨take_evaluates taken realized, ?_⟩
  intro result object evaluation
  cases evaluation with
  | give resolved cleared =>
    obtain ⟨sourceTy, found, focused, effect⟩ := take_description taken
    have sourceMember := Environment.lookup_member found
    have sourceAdmissible := Environment.admissible beforeWf sourceMember
    obtain ⟨root, atRoot, satisfied⟩ := realized.initializedVariables _ _ sourceMember
    have observations := focus_observations realized.classesWellFormed sourceAdmissible.2 focused
    obtain ⟨targetObject, targetData, read, _, _⟩ := satisfied.positive _ observations.positive
    obtain ⟨destination, expectedResolve⟩ := resolve_from_readPath atRoot read
    rw [placeFrom_splitPlace] at expectedResolve
    have sameObject := (resolve_deterministic realized.ownership expectedResolve resolved).2
    subst targetObject
    have targetSatisfied := (satisfied.focus realized.classesWellFormed realized.ownership
      sourceAdmissible.2 focused read).take_taken realized.ownership cleared
    rcases effect with ⟨empty, rfl⟩ | ⟨remaining, nonempty, emptied, rfl⟩
    · apply realized.give_replace resolved cleared admissible targetSatisfied afterWf
      have sourceIsVariable := resolve_source_empty resolved empty
      change ((splitPlace place).1, none) ∈ result.variables
      have atVariable : Stored result (.variable (splitPlace place).1) none :=
        sourceIsVariable ▸ cleared.cleared
      exact atVariable
    · apply realized.give_replace resolved cleared admissible targetSatisfied afterWf
      exact ⟨root, take_preserves_variable_field resolved cleared nonempty atRoot,
        satisfied.emptyPath realized.ownership realized.classesWellFormed sourceAdmissible.2
          (.variable atRoot) (route_of_resolve resolved) cleared read emptied⟩

theorem ExprTyped.sound (typed : ExprTyped classes before value ty after) :
    ExpressionSound classes before value ty after :=
  typed.sound_of_give (fun _ _ _ _ => give_sound)

theorem ArgsTyped.sound (typed : ArgsTyped classes before values names after) :
    ArgumentsSound classes before values names after := by
  induction typed using ArgsTyped.rec (motive_1 := fun _ _ _ _ _ => True) with
  | give => trivial
  | new => trivial
  | weaken => trivial
  | nil wf =>
    intro state pending realized
    refine ⟨⟨state, [], .nil state⟩, ?_⟩
    intro result objects evaluated
    cases evaluated
    exact realized
  | @cons before middle after value values name names first rest _ ih =>
    intro state pending realized
    obtain ⟨firstExists, allFirst⟩ := first.sound state pending realized
    constructor
    · obtain ⟨middleState, object, firstEvaluation⟩ := firstExists
      obtain ⟨⟨result, objects, restEvaluation⟩, _⟩ :=
        ih middleState ((object, .whole name) :: pending)
          (allFirst middleState object firstEvaluation)
      exact ⟨result, object :: objects, .cons firstEvaluation restEvaluation⟩
    · intro result objects evaluated
      cases evaluated with
      | cons firstEvaluation restEvaluation =>
        have firstRealized := allFirst _ _ firstEvaluation
        exact ((ih _ _ firstRealized).2 _ _ restEvaluation).perm List.perm_middle

end Dada.Unique.Typing
