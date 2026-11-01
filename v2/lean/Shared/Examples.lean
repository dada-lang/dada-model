import Shared.Step

namespace Dada.Shared

def exampleClasses : Classes :=
  [("Token", ⟨[]⟩), ("Box", ⟨["value"]⟩)]

def tokenState : State :=
  ⟨[(0, ⟨"Token", []⟩)], [("t", some (.owned 0))], 1⟩

def boxState : State :=
  ⟨[(1, ⟨"Box", [("value", some (.owned 0))]⟩), (0, ⟨"Token", []⟩)],
    [("b", some (.owned 1)), ("t", none)], 2⟩

def sharedBoxState : State :=
  ⟨boxState.objects, [("s", some (.shared 1)), ("b", none), ("t", none)], 2⟩

def copiedState : State :=
  ⟨[(1, ⟨"Box", [("value", some (.shared 0))]⟩), (0, ⟨"Token", []⟩)],
    [("u", some (.shared 0)), ("s", some (.shared 1)), ("b", none), ("t", none)], 2⟩

def twiceCopiedState : State := copiedState.bind "v" (.shared 0)

def sharingCode : List Statement :=
  [⟨"t", .new "Token" []⟩, ⟨"b", .new "Box" [.give (.variable "t")]⟩,
    ⟨"s", .giveShare (.variable "b")⟩,
    ⟨"u", .give (.field (.variable "s") "value")⟩,
    ⟨"v", .give (.field (.variable "s") "value")⟩]

theorem example_create_token (rest : List Statement) :
    Step exampleClasses ⟨State.empty, ⟨"t", .new "Token" []⟩ :: rest⟩ ⟨tokenState, rest⟩ := by
  apply Step.letValue (reference := .owned 0)
    (evaluated := State.empty.allocate "Token" [] [])
  · simp [State.empty, State.allocate]
  · apply Eval.new (declaration := ⟨[]⟩) (references := [])
    · simp [exampleClasses]
    · exact EvalArgs.nil _
    · rfl
    · simp [State.empty]

theorem example_create_box (rest : List Statement) :
    Step exampleClasses
      ⟨tokenState, ⟨"b", .new "Box" [.give (.variable "t")]⟩ :: rest⟩ ⟨boxState, rest⟩ := by
  apply Step.letValue (reference := .owned 1)
    (evaluated := (State.mk tokenState.objects [("t", none)] 1).allocate "Box" ["value"] [.owned 0])
  · simp [State.allocate]
  · apply Eval.new (declaration := ⟨["value"]⟩) (references := [.owned 0])
    · simp [exampleClasses]
    · apply EvalArgs.cons (reference := .owned 0)
      · apply Eval.give
        apply Give.move (source := .variable "t")
        · exact Resolve.variable (reference := .owned 0) (by simp [tokenState])
        · exact Take.variable tokenState.objects 1 [] [] "t" 0
      · exact EvalArgs.nil _
    · rfl
    · decide

theorem example_share_box (rest : List Statement) :
    Step exampleClasses ⟨boxState, ⟨"s", .giveShare (.variable "b")⟩ :: rest⟩
      ⟨sharedBoxState, rest⟩ := by
  apply Step.letValue (reference := .shared 1)
    (evaluated := ⟨boxState.objects, [("b", none), ("t", none)], 2⟩)
  · simp
  · apply Eval.giveShare (reference := .owned 1)
    apply Give.move (source := .variable "b")
    · exact Resolve.variable (reference := .owned 1) (by simp [boxState])
    · exact Take.variable boxState.objects 2 [] [("t", none)] "b" 1

theorem example_copy_field (rest : List Statement) :
    Step exampleClasses
      ⟨sharedBoxState, ⟨"u", .give (.field (.variable "s") "value")⟩ :: rest⟩
      ⟨copiedState, rest⟩ := by
  apply Step.letValue (reference := .shared 0)
    (evaluated := ⟨copiedState.objects, sharedBoxState.variables, 2⟩)
  · simp [sharedBoxState]
  · apply Eval.give
    apply Give.promote (source := .field 1 "value")
    · apply Resolve.field (permission := .shared) (reference := .owned 0) (data := ⟨"Box", [("value", some (.owned 0))]⟩)
      · exact Resolve.variable (reference := .shared 1) (by simp [sharedBoxState])
      · simp [sharedBoxState, boxState]
      · simp
    · exact Promote.field sharedBoxState.variables 2 [] [(0, ⟨"Token", []⟩)]
        1 "Box" [] [] "value" 0

theorem example_copy_again (rest : List Statement) :
    Step exampleClasses
      ⟨copiedState, ⟨"v", .give (.field (.variable "s") "value")⟩ :: rest⟩
      ⟨twiceCopiedState, rest⟩ := by
  apply Step.letValue
  · simp [copiedState]
  · apply Eval.give
    apply Give.copy (source := .field 1 "value")
    · apply Resolve.field (permission := .shared) (reference := .shared 0) (data := ⟨"Box", [("value", some (.shared 0))]⟩)
      · exact Resolve.variable (reference := .shared 1) (by simp [copiedState])
      · simp [copiedState]
      · simp
    · exact ⟨⟨"Box", [("value", some (.shared 0))]⟩, by simp [copiedState], by simp⟩

-- ANCHOR: share_value
example : Step exampleClasses
    ⟨boxState, [⟨"s", .giveShare (.variable "b")⟩]⟩ ⟨sharedBoxState, []⟩ := by
  exact example_share_box []
-- ANCHOR_END: share_value

-- ANCHOR: shared_field_copy
example : Step exampleClasses
    ⟨sharedBoxState, [⟨"u", .give (.field (.variable "s") "value")⟩]⟩ ⟨copiedState, []⟩ := by
  exact example_copy_field []
-- ANCHOR_END: shared_field_copy

-- ANCHOR: sharing_execution
example : Steps exampleClasses ⟨State.empty, sharingCode⟩ ⟨twiceCopiedState, []⟩ := by
  exact .step (example_create_token _)
    (.step (example_create_box _) (.step (example_share_box _)
      (.step (example_copy_field _) (.step (example_copy_again _) (.refl _)))))
-- ANCHOR_END: sharing_execution

-- A unique outer Box contains a shared reference to the inner Box. Therefore
-- outer.value.value crosses a shared edge even though outer itself is unique.
def nestedSharedState : State :=
  ⟨(2, ⟨"Box", [("value", some (.shared 1))]⟩) :: boxState.objects,
    ("outer", some (.owned 2)) :: sharedBoxState.variables, 3⟩

def nestedCopiedState : State :=
  ⟨(2, ⟨"Box", [("value", some (.shared 1))]⟩) :: copiedState.objects,
    ("u", some (.shared 0)) :: nestedSharedState.variables, 3⟩

-- ANCHOR: nested_shared_path
example : Steps exampleClasses
    ⟨sharedBoxState, [⟨"outer", .new "Box" [.give (.variable "s")]⟩,
      ⟨"u", .give (.field (.field (.variable "outer") "value") "value")⟩]⟩
    ⟨nestedCopiedState, []⟩ := by
  apply Steps.step (middle := ⟨nestedSharedState,
    [⟨"u", .give (.field (.field (.variable "outer") "value") "value")⟩]⟩)
  · apply Step.letValue (reference := .owned 2)
      (evaluated := sharedBoxState.allocate "Box" ["value"] [.shared 1])
    · simp [State.allocate, sharedBoxState]
    · apply Eval.new (declaration := ⟨["value"]⟩) (references := [.shared 1])
      · simp [exampleClasses]
      · apply EvalArgs.cons (reference := .shared 1)
        · apply Eval.give
          apply Give.copy (source := .variable "s")
          · exact Resolve.variable (reference := .shared 1) (by simp [sharedBoxState])
          · simp [Stored, sharedBoxState]
        · exact EvalArgs.nil _
      · rfl
      · decide
  apply Steps.step (middle := ⟨nestedCopiedState, []⟩)
  · apply Step.letValue (reference := .shared 0)
      (evaluated := ⟨nestedCopiedState.objects, nestedSharedState.variables, 3⟩)
    · simp [nestedSharedState, sharedBoxState]
    · apply Eval.give
      apply Give.promote (source := .field 1 "value")
      · apply Resolve.field (permission := .shared) (reference := .owned 0)
          (data := ⟨"Box", [("value", some (.owned 0))]⟩)
        · apply Resolve.field (permission := .unique) (reference := .shared 1)
            (data := ⟨"Box", [("value", some (.shared 1))]⟩)
          · exact Resolve.variable (reference := .owned 2) (by simp [nestedSharedState])
          · simp [nestedSharedState, Reference.owned]
          · simp
        · simp [nestedSharedState, boxState]
        · simp
      · exact Promote.field nestedSharedState.variables 3
          [(2, ⟨"Box", [("value", some (.shared 1))]⟩)] [(0, ⟨"Token", []⟩)]
          1 "Box" [] [] "value" 0
  exact Steps.refl _
-- ANCHOR_END: nested_shared_path

-- A nested constructor holds its unique result while the next argument copies
-- the same shared source. Both copies preserve the original variable.
def nestedArgumentClasses : Classes :=
  ("Pair", ⟨["first", "second"]⟩) :: exampleClasses

def nestedArgumentState : State :=
  ⟨(3, ⟨"Pair", [("first", some (.owned 2)), ("second", some (.shared 1))]⟩) ::
      (2, ⟨"Box", [("value", some (.shared 1))]⟩) :: sharedBoxState.objects,
    ("out", some (.owned 3)) :: sharedBoxState.variables, 4⟩

-- ANCHOR: nested_shared_arguments
example : Step nestedArgumentClasses
    ⟨sharedBoxState, [⟨"out", .new "Pair"
      [.new "Box" [.give (.variable "s")], .give (.variable "s")]⟩]⟩
    ⟨nestedArgumentState, []⟩ := by
  apply Step.letValue (reference := .owned 3)
    (evaluated := (sharedBoxState.allocate "Box" ["value"] [.shared 1]).allocate
      "Pair" ["first", "second"] [.owned 2, .shared 1])
  · simp [State.allocate, sharedBoxState]
  · apply Eval.new (declaration := ⟨["first", "second"]⟩)
      (references := [.owned 2, .shared 1])
    · simp [nestedArgumentClasses]
    · apply EvalArgs.cons (reference := .owned 2)
      · apply Eval.new (declaration := ⟨["value"]⟩) (references := [.shared 1])
          (evaluated := sharedBoxState)
        · simp [nestedArgumentClasses, exampleClasses]
        · apply EvalArgs.cons (reference := .shared 1)
          · apply Eval.give
            apply Give.copy (source := .variable "s")
            · exact Resolve.variable (reference := .shared 1) (by simp [sharedBoxState])
            · simp [Stored, sharedBoxState]
          · exact EvalArgs.nil _
        · rfl
        · decide
      · apply EvalArgs.cons (reference := .shared 1)
        · apply Eval.give
          apply Give.copy (source := .variable "s")
          · exact Resolve.variable (reference := .shared 1)
              (by simp [State.allocate, sharedBoxState])
          · simp [Stored, State.allocate, sharedBoxState]
        · exact EvalArgs.nil _
    · rfl
    · decide
-- ANCHOR_END: nested_shared_arguments

end Dada.Shared
