import Shared.TypingFocus
import Shared.TypingEffects
import Shared.TypingPathEffects

namespace Dada.Shared.Typing

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

theorem give_description (given : give classes before place = some (ty, after)) :
    ∃ source,
      before.lookup (splitPlace place).1 = some (some source) ∧
      focus classes source (splitPlace place).2 = some ty ∧
      ((ty.permission = .shared ∧ after = before) ∨
       (ty.permission = .given ∧
        (((splitPlace place).2 = [] ∧ after = before.replace (splitPlace place).1 none) ∨
         ∃ remaining, (splitPlace place).2 ≠ [] ∧
           emptyPath classes source (splitPlace place).2 = some remaining ∧
           after = before.replace (splitPlace place).1 (some remaining)))) := by
  unfold give at given
  obtain ⟨slot, found, slotBind⟩ := Option.bind_eq_some_iff.mp given
  obtain ⟨source, value, resultBind⟩ := Option.bind_eq_some_iff.mp slotBind
  rw [value] at found
  obtain ⟨result, focused, body⟩ := Option.bind_eq_some_iff.mp resultBind
  by_cases shared : result.permission = .shared
  · simp [shared] at body
    rcases body with ⟨rfl, rfl⟩
    exact ⟨source, found, focused, Or.inl ⟨shared, rfl⟩⟩
  · have unique : result.permission = .given := by
      cases h : result.permission <;> simp_all
    simp only [shared, ↓reduceIte] at body
    by_cases empty : (splitPlace place).2 = []
    · simp [empty] at body
      rcases body with ⟨rfl, rfl⟩
      exact ⟨source, found, focused, Or.inr ⟨unique, Or.inl ⟨empty, rfl⟩⟩⟩
    · simp only [empty, ↓reduceIte] at body
      obtain ⟨remaining, emptied, finalBind⟩ := Option.bind_eq_some_iff.mp body
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at finalBind
      rcases finalBind with ⟨rfl, rfl⟩
      exact ⟨source, found, focused,
        Or.inr ⟨unique, Or.inr ⟨remaining, empty, emptied, rfl⟩⟩⟩

theorem give_evaluates (given : give classes before place = some (ty, after))
    (realized : Realizes classes before state pending) :
    ∃ result reference, Eval classes.erase state (.give place) result reference := by
  obtain ⟨source, found, focused, _⟩ := give_description given
  have member := Environment.lookup_member found
  have admissible := Environment.admissible realized.environmentWellFormed member
  obtain ⟨reference, stored, satisfied⟩ := realized.initializedVariables _ _ member
  have facts := focus_observations realized.classesWellFormed admissible.2 focused
  obtain ⟨target, data, read, _, _⟩ := satisfied.positive _ facts.positive
  obtain ⟨destination, resolved⟩ := resolve_from_readPath stored read
  change Resolve state (placeFrom (splitPlace place).1 (splitPlace place).2) _ _ _ at resolved
  rw [placeFrom_splitPlace] at resolved
  obtain ⟨result, given⟩ := resolved.give_exists
  exact ⟨result, target, .give given⟩

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

theorem resolve_source_nonempty (resolved : Resolve state place source object permission)
    (nonempty : (splitPlace place).2 ≠ []) : ∃ parent field, source = .field parent field := by
  cases resolved with
  | «variable» _ => exact False.elim (nonempty rfl)
  | field _ _ _ => exact ⟨_, _, rfl⟩

theorem resolve_source_empty (resolved : Resolve state place source object permission)
    (empty : (splitPlace place).2 = []) : source = .variable (splitPlace place).1 := by
  cases resolved with
  | «variable» _ => rfl
  | field _ _ _ => simp [splitPlace] at empty

theorem take_preserves_other_variable
    (resolved : Resolve before place source object permission) (taken : Take before source object after)
    (different : name ≠ (splitPlace place).1) (stored : (name, slot) ∈ before.variables) :
    (name, slot) ∈ after.variables := by
  apply taken.stored_unchanged (place := .variable name) _ stored
  intro same
  cases resolved with
  | «variable» _ => cases same; exact different rfl
  | field _ _ _ => cases same

theorem take_preserves_variable_field (resolved : Resolve before place source object permission)
    (taken : Take before source object after) (nonempty : (splitPlace place).2 ≠ [])
    (stored : (name, slot) ∈ before.variables) : (name, slot) ∈ after.variables := by
  obtain ⟨parent, field, rfl⟩ := resolve_source_nonempty resolved nonempty
  exact taken.stored_unchanged (place := .variable name) (by intro impossible; cases impossible) stored


end Dada.Shared.Typing
