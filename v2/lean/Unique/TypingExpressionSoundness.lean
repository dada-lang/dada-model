import Unique.TypingAllocation

namespace Dada.Unique.Typing

-- These statements quantify over arbitrary heaps realizing the static input,
-- including previously evaluated arguments held outside the variable store.
def ExpressionSound (classes : ClassTable) (before : Environment) (value : Value)
    (ty : ViewType) (after : Environment) : Prop :=
  ∀ state pending, Realizes classes before state pending →
    (∃ result object, Eval classes.erase state value result object) ∧
    (∀ result object, Eval classes.erase state value result object →
      Realizes classes after result ((object, ty) :: pending))

def ArgumentsSound (classes : ClassTable) (before : Environment) (values : List Value)
    (names : List ClassName) (after : Environment) : Prop :=
  ∀ state pending, Realizes classes before state pending →
    (∃ result objects, EvalArgs classes.erase state values result objects) ∧
    (∀ result objects, EvalArgs classes.erase state values result objects →
      Realizes classes after result (objects.zip (names.map ViewType.whole) ++ pending))

-- The induction isolates the move lemma: construction and weakening need no
-- additional assumptions about how a place is represented or traversed.
theorem ExprTyped.sound_of_give
    (giveSound : ∀ before place ty after, before.WellFormed classes →
      take classes before place = some (ty, after) → Admissible classes ty →
      after.WellFormed classes → ExpressionSound classes before (.give place) ty after)
    (typed : ExprTyped classes before value ty after) :
    ExpressionSound classes before value ty after := by
  induction typed using ExprTyped.rec
    (motive_2 := fun before values names after _ => ArgumentsSound classes before values names after) with
  | give wf taken admissible afterWf => exact giveSound _ _ _ _ wf taken admissible afterWf
  | @new before after name declaration arguments declared args admissible ih =>
    intro state pending realized
    have erased : (name, Class.mk (declaration.fields.map Prod.fst)) ∈ classes.erase :=
      List.mem_map.mpr ⟨(name, declaration), declared, rfl⟩
    obtain ⟨existsArgs, allArgs⟩ := ih state pending realized
    constructor
    · obtain ⟨evaluated, objects, evaluatedArgs⟩ := existsArgs
      have current := allArgs evaluated objects evaluatedArgs
      have lengths : objects.length = declaration.fields.length := by
        have argumentLengths := args.length
        have resultLengths := evaluatedArgs.length
        simpa using resultLengths.trans argumentLengths
      exact ⟨_, _, .new erased evaluatedArgs (by simpa using lengths) current.next_fresh⟩
    · intro result object evaluation
      cases evaluation with
      | new runtimeDeclared evaluatedArgs lengths _ =>
        have same := member_value_unique realized.classesWellFormed.erase.1 runtimeDeclared erased
        cases same
        have current := allArgs _ _ evaluatedArgs
        simp only [List.map_map, Function.comp_def] at current
        apply current.allocate declared admissible
        simpa using lengths
  | @weaken before after value ty other typed admissible subtype ih =>
    intro state pending realized
    obtain ⟨existsEval, allEval⟩ := ih state pending realized
    exact ⟨existsEval, fun result object evaluated =>
      (allEval result object evaluated).weaken_pending admissible subtype⟩
  | nil wf =>
    intro state pending realized
    refine ⟨⟨state, [], .nil state⟩, ?_⟩
    intro result objects evaluation
    cases evaluation
    exact realized
  | @cons before middle after value values name names typed args first rest =>
    intro state pending realized
    obtain ⟨existsFirst, allFirst⟩ := first state pending realized
    constructor
    · obtain ⟨middleState, object, evaluatedFirst⟩ := existsFirst
      obtain ⟨⟨result, objects, evaluatedRest⟩, _⟩ :=
        rest middleState ((object, .whole name) :: pending)
          (allFirst middleState object evaluatedFirst)
      exact ⟨result, object :: objects, .cons evaluatedFirst evaluatedRest⟩
    · intro result objects evaluation
      cases evaluation with
      | cons evaluatedFirst evaluatedRest =>
        have firstRealized := allFirst _ _ evaluatedFirst
        have restRealized := (rest _ _ firstRealized).2 _ _ evaluatedRest
        exact restRealized.perm List.perm_middle

end Dada.Unique.Typing
