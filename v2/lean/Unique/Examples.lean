import Unique.Frames
import Unique.Step

namespace Dada.Unique

-- Two ordinary classes suffice: an empty Token and a Box with one field.
def exampleClasses : Classes :=
  [("Token", ⟨[]⟩), ("Box", ⟨["value"]⟩)]

def tokenState : State :=
  ⟨[(0, ⟨"Token", []⟩)], [("t", some 0)], 1⟩

def boxState : State :=
  ⟨[(1, ⟨"Box", [("value", some 0)]⟩), (0, ⟨"Token", []⟩)],
    [("b", some 1), ("t", none)], 2⟩

def movedState : State :=
  ⟨[(1, ⟨"Box", [("value", none)]⟩), (0, ⟨"Token", []⟩)],
    [("u", some 0), ("b", some 1), ("t", none)], 2⟩

def tokenProgram : List Statement := [⟨"t", .new "Token" []⟩]

def boxProgram : List Statement := [⟨"b", .new "Box" [.give (.variable "t")]⟩]

def moveProgram : List Statement := [⟨"u", .give (.field (.variable "b") "value")⟩]

private theorem createToken (rest : List Statement) :
    Step exampleClasses ⟨State.empty, tokenProgram ++ rest⟩ ⟨tokenState, rest⟩ := by
  apply Step.letValue (object := 0) (evaluated := State.empty.allocate "Token" [] [])
  · simp [State.allocate, State.empty]
  · exact Eval.new (by simp [exampleClasses]) (.nil _) rfl (by simp [State.empty])

private theorem createBox (rest : List Statement) :
    Step exampleClasses ⟨tokenState, boxProgram ++ rest⟩ ⟨boxState, rest⟩ := by
  let cleared : State := ⟨tokenState.objects, [("t", none)], 1⟩
  apply Step.letValue (object := 1)
    (evaluated := cleared.allocate "Box" ["value"] [0])
  · simp [State.allocate, cleared]
  · apply Eval.new (declaration := ⟨["value"]⟩) (evaluated := cleared) (objects := [0])
    · simp [exampleClasses]
    · apply EvalArgs.cons (middle := cleared) (object := 0)
      · exact Eval.give (Resolve.variable (by simp [tokenState]))
          (Take.variable tokenState.objects 1 [] [] "t" 0)
      · exact EvalArgs.nil _
    · rfl
    · decide

private theorem giveField (rest : List Statement) :
    Step exampleClasses ⟨boxState, moveProgram ++ rest⟩ ⟨movedState, rest⟩ := by
  apply Step.letValue (object := 0)
    (evaluated := ⟨[(1, ⟨"Box", [("value", none)]⟩), (0, ⟨"Token", []⟩)],
      [("b", some 1), ("t", none)], 2⟩)
  · simp
  · apply Eval.give (source := .field 1 "value")
    · apply Resolve.field (data := ⟨"Box", [("value", some 0)]⟩)
      · exact Resolve.variable (by simp [boxState])
      · simp [boxState]
      · simp
    · exact Take.field [("b", some 1), ("t", none)] 2 [] [(0, ⟨"Token", []⟩)]
        1 "Box" [] [] "value" 0

-- ANCHOR: create_token
example : Step exampleClasses ⟨State.empty, tokenProgram⟩ ⟨tokenState, []⟩ := by
  exact createToken []
-- ANCHOR_END: create_token

-- ANCHOR: create_box
example : Step exampleClasses ⟨tokenState, boxProgram⟩ ⟨boxState, []⟩ := by
  exact createBox []
-- ANCHOR_END: create_box

-- ANCHOR: give_field
example : Step exampleClasses ⟨boxState, moveProgram⟩ ⟨movedState, []⟩ := by
  exact giveField []
-- ANCHOR_END: give_field

def badConfiguration : Configuration :=
  ⟨movedState, [⟨"v", .give (.field (.variable "b") "value")⟩]⟩

theorem second_give_stuck : Stuck exampleClasses badConfiguration := by
  constructor
  · simp [badConfiguration, Configuration.finished]
  · intro ⟨after, step⟩
    cases step with
    | letValue fresh evaluated =>
      cases evaluated with
      | give resolved taken =>
        cases resolved with
        | field base parentStored fieldStored =>
          cases base with
          | «variable» root =>
            simp [movedState] at root
            subst_vars
            simp [movedState] at parentStored
            rcases parentStored with rfl | ⟨_, rfl⟩ <;> simp at fieldStored

private theorem framed_second_give_stuck : Framed.Stuck (Framed.baseOperation exampleClasses)
    (.running badConfiguration.state badConfiguration.code) := by
  constructor
  · simp [Framed.Configuration.finished, Framed.Configuration.running]
  · rintro ⟨after, step⟩
    generalize equality : Framed.Configuration.running badConfiguration.state badConfiguration.code = start at step
    cases step with
    | @«local» beforeState afterState code rest operation =>
      have stateEq := congrArg Framed.Configuration.state equality
      change badConfiguration.state = beforeState at stateEq
      have codeEq := congrArg (fun c => c.frame.map Framed.Frame.code) equality
      simp only [Framed.Configuration.running, Option.map_some, Option.some.injEq] at codeEq
      rw [← stateEq, ← codeEq] at operation
      exact second_give_stuck.2 ⟨_, operation⟩
    | exit =>
      have codeEq := congrArg (fun c => c.frame.map Framed.Frame.code) equality
      simp [Framed.Configuration.running, badConfiguration] at codeEq

-- ANCHOR: second_give_fails
example : Framed.Stuck (Framed.baseOperation exampleClasses)
    (.running badConfiguration.state badConfiguration.code) ∧
    ¬ ∃ after, Framed.Steps (Framed.baseOperation exampleClasses)
      (.running badConfiguration.state badConfiguration.code) after ∧ after.finished := by
  refine ⟨framed_second_give_stuck, ?_⟩
  rintro ⟨after, ⟨_, execution⟩, finished⟩
  cases execution with
  | refl => exact framed_second_give_stuck.1 finished
  | step first _ => exact framed_second_give_stuck.2 ⟨_, first⟩
-- ANCHOR_END: second_give_fails

-- ANCHOR: give_execution
example : Framed.StepsExactly (Framed.baseOperation exampleClasses)
    (.initial (tokenProgram ++ boxProgram ++ moveProgram)) 3 (.running movedState []) := by
  have classesWf : ClassesWellFormed exampleClasses := by simp [ClassesWellFormed, exampleClasses, or_imp, and_imp, forall_and]
  have tokenWf : WellFormed exampleClasses tokenState := (createToken []).preserves_wellFormed classesWf (WellFormed.empty _)
  have boxWf : WellFormed exampleClasses boxState := (createBox []).preserves_wellFormed classesWf tokenWf
  have movedWf : WellFormed exampleClasses movedState := (giveField []).preserves_wellFormed classesWf boxWf
  exact .step (Framed.local_step (createToken _) tokenWf)
    (.step (Framed.local_step (createBox _) boxWf)
      (.step (Framed.local_step (giveField []) movedWf) (.refl _)))
-- ANCHOR_END: give_execution

def nestedState : State :=
  ⟨[(1, ⟨"Box", [("value", some 0)]⟩), (0, ⟨"Token", []⟩)], [("b", some 1)], 2⟩

private theorem nested_operation : Step exampleClasses
    ⟨State.empty, [⟨"b", .new "Box" [.new "Token" []]⟩]⟩ ⟨nestedState, []⟩ := by
  let token : State := State.empty.allocate "Token" [] []
  apply Step.letValue (object := 1)
    (evaluated := token.allocate "Box" ["value"] [0])
  · simp [State.allocate, token, State.empty]
  · apply Eval.new (declaration := ⟨["value"]⟩) (evaluated := token) (objects := [0])
    · simp [exampleClasses]
    · apply EvalArgs.cons (middle := token) (object := 0)
      · exact Eval.new (by simp [exampleClasses]) (.nil _) rfl (by simp [State.empty])
      · exact EvalArgs.nil _
    · rfl
    · decide
-- ANCHOR: nested_constructor
example : Framed.Step (Framed.baseOperation exampleClasses)
    (.initial [⟨"b", .new "Box" [.new "Token" []]⟩]) (.running nestedState []) :=
  Framed.local_step nested_operation (nested_operation.preserves_wellFormed
    (by simp [ClassesWellFormed, exampleClasses, or_imp, and_imp, forall_and]) (WellFormed.empty _))
-- ANCHOR_END: nested_constructor

end Dada.Unique
