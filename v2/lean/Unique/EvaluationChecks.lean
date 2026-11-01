import Unique.Examples
import Unique.Soundness

namespace Dada.Unique

private def pairClasses : Classes :=
  [("Token", ⟨[]⟩), ("Pair", ⟨["left", "right"]⟩)]

-- The first argument receives identity 0, the second identity 1, and only then
-- is their containing Pair allocated as identity 2.
private def orderedPairState : State :=
  ⟨[(2, ⟨"Pair", [("left", some 0), ("right", some 1)]⟩),
    (1, ⟨"Token", []⟩), (0, ⟨"Token", []⟩)], [("p", some 2)], 3⟩

example : Step pairClasses
    ⟨State.empty, [⟨"p", .new "Pair" [.new "Token" [], .new "Token" []]⟩]⟩
    ⟨orderedPairState, []⟩ := by
  let first := State.empty.allocate "Token" [] []
  let second := first.allocate "Token" [] []
  apply Step.letValue (object := 2)
    (evaluated := second.allocate "Pair" ["left", "right"] [0, 1])
  · simp [second, first, State.allocate, State.empty]
  · apply Eval.new (declaration := ⟨["left", "right"]⟩)
      (evaluated := second) (objects := [0, 1])
    · simp [pairClasses]
    · apply EvalArgs.cons (middle := first) (object := 0)
      · exact Eval.new (by simp [pairClasses]) (.nil _) rfl (by simp [State.empty])
      · apply EvalArgs.cons (middle := second) (object := 1)
        · exact Eval.new (by simp [pairClasses]) (.nil _) rfl (by decide)
        · exact EvalArgs.nil _
    · rfl
    · decide

private def repeatedGive : Value :=
  .new "Pair" [.give (.variable "t"), .give (.variable "t")]

-- The first give empties t; the second argument has no reference left to take.
private theorem repeated_give_no_eval : ¬ Eval pairClasses tokenState repeatedGive after object := by
  intro evaluated
  cases evaluated with
  | new _ arguments _ _ =>
    cases arguments with
    | cons first rest =>
      cases first with
      | give _ taken =>
        have length := taken.references.length_eq
        have empty : References _ = [] := List.eq_nil_of_length_eq_zero (by
          simpa [References, tokenState] using length.symm)
        cases rest with
        | cons second _ =>
          cases second with
          | give resolved _ =>
            cases resolved with
            | «variable» stored =>
              have member : _ ∈ References _ := List.mem_append_left _
                (List.mem_filterMap.mpr ⟨(_, _), stored, rfl⟩)
              rw [empty] at member
              exact List.not_mem_nil member

private def repeatedGiveConfiguration : Configuration :=
  ⟨tokenState, [⟨"p", repeatedGive⟩]⟩

private theorem repeated_give_stuck : Stuck pairClasses repeatedGiveConfiguration := by
  constructor
  · simp [repeatedGiveConfiguration, Configuration.finished]
  · rintro ⟨after, step⟩
    cases step with
    | letValue _ evaluation => exact repeated_give_no_eval evaluation

example : Stuck pairClasses repeatedGiveConfiguration ∧
    ¬ ∃ after, Steps pairClasses repeatedGiveConfiguration after ∧ after.finished := by
  refine ⟨repeated_give_stuck, ?_⟩
  rintro ⟨after, execution, finished⟩
  cases execution with
  | refl => exact repeated_give_stuck.1 finished
  | step first _ => exact repeated_give_stuck.2 ⟨_, first⟩

end Dada.Unique
