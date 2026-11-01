import Unique.Unpacking

namespace Dada.Unique.Unpacking

def exampleClasses : Classes :=
  [("Token", ⟨[]⟩), ("Pair", ⟨["left", "right"]⟩)]

def pairObject : Object :=
  ⟨"Pair", [("left", some 0), ("right", some 1)]⟩

def partialPair : Object :=
  ⟨"Pair", [("left", none), ("right", some 1)]⟩

def tokenObjects : List (ObjectId × Object) :=
  [(1, ⟨"Token", []⟩), (0, ⟨"Token", []⟩)]

def constructed : State :=
  ⟨(2, pairObject) :: tokenObjects, [("p", some 2)], 3⟩

def movedLeft : State :=
  ⟨(2, partialPair) :: tokenObjects, [("taken", some 0), ("p", some 2)], 3⟩

def takenPair : State :=
  ⟨(2, partialPair) :: tokenObjects, [("taken", some 0), ("p", none)], 3⟩

def unpacked : State :=
  ⟨tokenObjects,
    [("left", none), ("right", some 1), ("taken", some 0), ("p", none)], 3⟩

def unpackingProgram : List Statement :=
  [⟨.variable "p", .new "Pair" [.new "Token" [], .new "Token" []]⟩,
    ⟨.variable "taken", .give (.field (.variable "p") "left")⟩,
    ⟨.unpack "Pair" [("left", "left"), ("right", "right")], .give (.variable "p")⟩]

private theorem construct_pair : Eval exampleClasses State.empty
    (.new "Pair" [.new "Token" [], .new "Token" []])
    ⟨(2, pairObject) :: tokenObjects, [], 3⟩ 2 := by
  let first := State.empty.allocate "Token" [] []
  let second := first.allocate "Token" [] []
  apply Eval.new (declaration := ⟨["left", "right"]⟩)
      (evaluated := second) (objects := [0, 1])
  · simp [exampleClasses]
  · apply EvalArgs.cons (middle := first) (object := 0)
    · exact Eval.new (by simp [exampleClasses]) (.nil _) rfl (by simp [State.empty])
    · apply EvalArgs.cons (middle := second) (object := 1)
      · exact Eval.new (by simp [exampleClasses]) (.nil _) rfl (by decide)
      · exact EvalArgs.nil _
  · rfl
  · decide

private theorem move_left : Eval exampleClasses constructed
    (.give (.field (.variable "p") "left"))
    ⟨(2, partialPair) :: tokenObjects, [("p", some 2)], 3⟩ 0 := by
  apply Eval.give (source := .field 2 "left")
  · apply Resolve.field (parent := 2) (data := pairObject)
    · exact Resolve.variable (by decide)
    · decide
    · decide
  · exact Take.field [("p", some 2)] 3 [] tokenObjects 2 "Pair" []
      [("right", some 1)] "left" 0

private theorem take_pair : Eval exampleClasses movedLeft
    (.give (.variable "p")) takenPair 2 := by
  exact Eval.give (Resolve.variable (by decide))
    (Take.variable ((2, partialPair) :: tokenObjects) 3 [("taken", some 0)] [] "p" 2)

private theorem unpack_pair : Bind exampleClasses takenPair 2
    (.unpack "Pair" [("left", "left"), ("right", "right")]) unpacked := by
  apply Bind.unpack (before := []) (after := tokenObjects)
    (declaration := ⟨["left", "right"]⟩)
    (bindings := [("left", none), ("right", some 1)])
  · simp [exampleClasses]
  · rfl
  · decide
  · decide
  · decide
  · exact Transfer.cons (before := []) (Transfer.cons (before := []) .nil)

theorem unpacking_execution : Steps exampleClasses ⟨State.empty, unpackingProgram⟩
    ⟨unpacked, []⟩ := by
  apply Steps.step (middle := ⟨constructed, unpackingProgram.tail⟩)
  · exact Step.letValue construct_pair (.variable (by decide))
  · apply Steps.step (middle := ⟨movedLeft, unpackingProgram.tail.tail⟩)
    · exact Step.letValue move_left (.variable (by decide))
    · exact .step (.letValue take_pair unpack_pair) (.refl _)

theorem moved_field_has_no_value :
    ¬ ∃ after object, Eval exampleClasses unpacked (.give (.variable "left")) after object := by
  rintro ⟨after, object, evaluation⟩
  cases evaluation with
  | give resolved _ =>
    cases resolved with
    | «variable» stored => simp [unpacked] at stored

-- ANCHOR: unpack_after_move
example : Steps exampleClasses ⟨State.empty, unpackingProgram⟩ ⟨unpacked, []⟩ ∧
    (Configuration.mk unpacked []).finished ∧
    ¬ ∃ after object, Eval exampleClasses unpacked (.give (.variable "left")) after object := by
  exact ⟨unpacking_execution, rfl, moved_field_has_no_value⟩
-- ANCHOR_END: unpack_after_move

-- Reordering the names reorders the new bindings, without changing their slots.
example : Bind exampleClasses takenPair 2
    (.unpack "Pair" [("right", "r"), ("left", "l")])
    ⟨tokenObjects, [("r", some 1), ("l", none), ("taken", some 0), ("p", none)], 3⟩ := by
  apply Bind.unpack (before := []) (after := tokenObjects)
    (declaration := ⟨["left", "right"]⟩)
    (bindings := [("r", some 1), ("l", none)])
  · simp [exampleClasses]
  · rfl
  · decide
  · decide
  · decide
  · exact Transfer.cons (before := [("left", none)]) (after := [])
      (Transfer.cons (before := []) .nil)

-- A fieldless object can be consumed without producing any bindings.
example : Bind exampleClasses ⟨[(0, ⟨"Token", []⟩)], [], 1⟩ 0
    (.unpack "Token" []) ⟨[], [], 1⟩ := by
  exact Bind.unpack (before := []) (after := []) (by simp [exampleClasses])
    rfl (by decide) (by decide) (by simp) .nil

-- Empty variables remain allocated: an unpack cannot reuse p as a fresh name.
example : ¬ ∃ after, Bind exampleClasses takenPair 2
    (.unpack "Pair" [("left", "p"), ("right", "right")]) after := by
  rintro ⟨after, binding⟩
  have fresh := binding.fresh "p" (by decide)
  exact fresh (by decide)

example : WellFormed exampleClasses unpacked := by
  have classesWf : ClassesWellFormed exampleClasses := by
    simp [ClassesWellFormed, exampleClasses]
    rintro name declaration (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> decide
  exact unpacking_execution.preserves_wellFormed classesWf (WellFormed.empty _)

end Dada.Unique.Unpacking
