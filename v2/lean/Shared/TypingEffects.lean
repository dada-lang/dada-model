import Shared.Typing

namespace Dada.Shared.Typing

theorem ClassTable.WellFormed.erase {classes : ClassTable} (wf : classes.WellFormed) :
    ClassesWellFormed classes.erase := by
  constructor
  · simpa [ClassTable.erase, List.map_map, Function.comp_def] using wf.1
  · intro name declaration member
    obtain ⟨⟨originalName, original⟩, present, equality⟩ := List.mem_map.mp member
    cases equality
    exact (wf.2 _ present).1

-- A move updates an existing slot's description; it never allocates a name.
theorem Environment.replace_keys (environment : Environment) (name : VariableId)
    (description : SlotDescription) :
    (environment.replace name description).map Prod.fst = environment.map Prod.fst := by
  simp only [Environment.replace, List.map_map]
  apply List.map_congr_left
  intro entry _
  by_cases same : entry.1 = name <;> simp [same]

theorem give_keys (taken : Typing.give classes before place = some (ty, after)) :
    after.map Prod.fst = before.map Prod.fst := by
  unfold give at taken
  obtain ⟨sourceSlot, _, taken⟩ := Option.bind_eq_some_iff.mp taken
  obtain ⟨source, _, taken⟩ := Option.bind_eq_some_iff.mp taken
  obtain ⟨result, _, taken⟩ := Option.bind_eq_some_iff.mp taken
  by_cases shared : result.permission = .shared
  · simp [shared] at taken
    exact congrArg (List.map Prod.fst) taken.2.symm
  · simp only [shared, ↓reduceIte] at taken
    by_cases empty : (splitPlace place).2 = []
    · simp [empty] at taken
      rcases taken with ⟨rfl, rfl⟩
      exact Environment.replace_keys _ _ _
    · simp only [empty, ↓reduceIte] at taken
      obtain ⟨remaining, _, taken⟩ := Option.bind_eq_some_iff.mp taken
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at taken
      rcases taken with ⟨rfl, rfl⟩
      exact Environment.replace_keys _ _ _

theorem ExprTyped.keys (typed : ExprTyped classes before value ty after) :
    after.map Prod.fst = before.map Prod.fst := by
  induction typed using ExprTyped.rec
    (motive_2 := fun before _ _ after _ => after.map Prod.fst = before.map Prod.fst) with
  | give _ taken _ _ => exact give_keys taken
  | giveShare _ taken _ _ => exact give_keys taken
  | new _ _ _ _ ih => exact ih
  | weaken _ _ _ ih => exact ih
  | nil => rfl
  | cons _ _ first rest => exact rest.trans first

theorem ArgsTyped.keys (typed : ArgsTyped classes before values names after) :
    after.map Prod.fst = before.map Prod.fst := by
  induction typed using ArgsTyped.rec (motive_1 := fun _ _ _ _ _ => True) with
  | give => trivial
  | giveShare => trivial
  | new => trivial
  | weaken => trivial
  | nil => rfl
  | cons first _ _ rest => exact rest.trans first.keys

theorem ExprTyped.wellFormed (typed : ExprTyped classes before value ty after) :
    before.WellFormed classes ∧ Admissible classes ty ∧ after.WellFormed classes := by
  induction typed using ExprTyped.rec
    (motive_2 := fun before _ _ after _ =>
      before.WellFormed classes ∧ after.WellFormed classes) with
  | give beforeWf _ admissible afterWf => exact ⟨beforeWf, admissible, afterWf⟩
  | giveShare beforeWf _ admissible afterWf structTy =>
    exact ⟨beforeWf, admissible.share structTy, afterWf⟩
  | new _ _ admissible _ ih => exact ⟨ih.1, admissible, ih.2⟩
  | weaken _ admissible _ ih => exact ⟨ih.1, admissible, ih.2.2⟩
  | nil wf => exact ⟨wf, wf⟩
  | cons _ _ first rest => exact ⟨first.1, rest.2⟩

theorem ArgsTyped.wellFormed (typed : ArgsTyped classes before values names after) :
    before.WellFormed classes ∧ after.WellFormed classes := by
  induction typed using ArgsTyped.rec (motive_1 := fun _ _ _ _ _ => True) with
  | give => trivial
  | giveShare => trivial
  | new => trivial
  | weaken => trivial
  | nil wf => exact ⟨wf, wf⟩
  | cons first _ _ rest => exact ⟨first.wellFormed.1, rest.2⟩

theorem BindingTyped.wellFormed (typed : BindingTyped classes before pattern ty after) :
    before.WellFormed classes ∧ Admissible classes ty ∧ after.WellFormed classes := by
  cases typed with
  | «variable» beforeWf admissible fresh =>
    refine ⟨beforeWf, admissible, ?_⟩
    simpa [Environment.WellFormed, admissible, fresh] using beforeWf
  | unpack beforeWf admissible _ _ _ _ _ _ _ afterWf =>
    exact ⟨beforeWf, admissible, afterWf⟩

theorem StatementTyped.wellFormed (typed : StatementTyped classes before statement after) :
    before.WellFormed classes ∧ after.WellFormed classes := by
  cases typed with
  | letValue expression binding => exact ⟨expression.wellFormed.1, binding.wellFormed.2.2⟩

theorem SequenceTyped.wellFormed (typed : SequenceTyped classes before statements after) :
    before.WellFormed classes ∧ after.WellFormed classes := by
  induction typed with
  | nil wf => exact ⟨wf, wf⟩
  | cons first _ rest => exact ⟨first.wellFormed.1, rest.2⟩

end Dada.Shared.Typing
