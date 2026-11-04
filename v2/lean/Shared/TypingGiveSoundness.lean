import Shared.TypingExpressionSoundness
import Shared.TypingPromotion

namespace Dada.Shared.Typing

theorem give_sound (beforeWf : before.WellFormed classes)
    (given : give classes before place = some (ty, after)) (admissible : Admissible classes ty)
    (afterWf : after.WellFormed classes) : ExpressionSound classes before (.give place) ty after := by
  intro state pending realized
  refine ⟨give_evaluates given realized, ?_⟩
  intro result reference evaluation
  cases evaluation with
  | give operation =>
    obtain ⟨sourceTy, found, focused, effect⟩ := give_description given
    have sourceMember := Environment.lookup_member found
    have sourceAdmissible := Environment.admissible beforeWf sourceMember
    obtain ⟨root, atRoot, satisfied⟩ := realized.initializedVariables _ _ sourceMember
    have observations := focus_observations realized.classesWellFormed sourceAdmissible.2 focused
    obtain ⟨targetReference, targetData, read, _, _⟩ := satisfied.positive _ observations.positive
    obtain ⟨destination, expectedResolve⟩ := resolve_from_readPath atRoot read
    change Resolve state (placeFrom (splitPlace place).1 (splitPlace place).2) _ _ _ at expectedResolve
    rw [placeFrom_splitPlace] at expectedResolve
    obtain ⟨actualSource, actualResolve⟩ := operation.resolved
    obtain ⟨_, sameObject, sameMode⟩ :=
      resolve_deterministic realized.ownership expectedResolve actualResolve
    have sameReference : targetReference = reference := by
      cases targetReference; cases reference; simp_all
    subst targetReference
    have targetSatisfied := satisfied.focus realized.classesWellFormed realized.ownership
      sourceAdmissible.2 focused read
    have afterOwnership := operation.preserves_pending realized.ownership
    cases operation with
    | move resolved cleared =>
      have unique : ty.permission = .given := by
        exact Perm.toMode_injective targetSatisfied.mode.symm
      rcases effect with ⟨shared, _⟩ | ⟨_, effect⟩
      · simp [unique] at shared
      · have targetAfter := targetSatisfied.take_taken realized.ownership afterOwnership cleared (route_of_resolve resolved) rfl
        rcases effect with ⟨empty, rfl⟩ | ⟨remaining, nonempty, emptied, rfl⟩
        · apply realized.give_replace resolved cleared admissible targetAfter afterWf
          have sourceIsVariable := resolve_source_empty resolved empty
          change Stored result (.variable (splitPlace place).1) none
          exact sourceIsVariable ▸ cleared.cleared
        · apply realized.give_replace resolved cleared admissible targetAfter afterWf
          exact ⟨root, take_preserves_variable_field resolved cleared nonempty atRoot,
            satisfied.emptyPath realized.ownership afterOwnership realized.classesWellFormed
              sourceAdmissible.2 (.variable atRoot) (route_of_resolve resolved) cleared read emptied⟩
    | copy resolved stored =>
      have shared : ty.permission = .shared := by
        exact Perm.toMode_injective targetSatisfied.mode.symm
      rcases effect with ⟨_, rfl⟩ | ⟨unique, _⟩
      · exact realized.copy resolved stored admissible targetSatisfied
      · simp [shared] at unique
    | promote resolved promoted =>
      have shared : ty.permission = .shared := by
        exact Perm.toMode_injective targetSatisfied.mode.symm
      rcases effect with ⟨_, rfl⟩ | ⟨unique, _⟩
      · exact realized.promote resolved promoted admissible
          (targetSatisfied.promote_target realized.ownership afterOwnership promoted (route_of_resolve resolved) rfl)
      · simp [shared] at unique

theorem ExprTyped.sound (typed : ExprTyped classes before value ty after) :
    ExpressionSound classes before value ty after :=
  typed.sound_of_give (fun _ _ _ _ => give_sound)

theorem ArgsTyped.sound (typed : ArgsTyped classes before values fields after) :
    ArgumentsSound classes before values fields after := by
  induction typed using ArgsTyped.rec (motive_1 := fun _ _ _ _ _ => True) with
  | give => trivial
  | giveShare => trivial
  | new => trivial
  | weaken => trivial
  | nil wf =>
    intro state pending realized
    refine ⟨⟨state, [], .nil state⟩, ?_⟩
    intro result objects evaluated
    cases evaluated
    exact realized
  | @cons before middle after value values field fields first rest _ ih =>
    intro state pending realized
    obtain ⟨firstExists, allFirst⟩ := first.sound state pending realized
    constructor
    · obtain ⟨middleState, object, firstEvaluation⟩ := firstExists
      obtain ⟨⟨result, objects, restEvaluation⟩, _⟩ :=
        ih middleState ((object, field.toType) :: pending)
          (allFirst middleState object firstEvaluation)
      exact ⟨result, object :: objects, .cons firstEvaluation restEvaluation⟩
    · intro result objects evaluated
      cases evaluated with
      | cons firstEvaluation restEvaluation =>
        have firstRealized := allFirst _ _ firstEvaluation
        exact ((ih _ _ firstRealized).2 _ _ restEvaluation).perm List.perm_middle

end Dada.Shared.Typing
