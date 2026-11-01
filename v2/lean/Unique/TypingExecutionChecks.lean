import Unique.TypingChecks

namespace Dada.Unique.Typing.Checks

def runtimeTokens : List (ObjectId × Object) :=
  [(1, ⟨"Token", []⟩), (0, ⟨"Token", []⟩)]
def runtimePair : Object := ⟨"Pair", [("left", some 0), ("right", some 1)]⟩
def runtimePartialPair : Object := ⟨"Pair", [("left", none), ("right", some 1)]⟩
def runtimeBox : Object := ⟨"Box", [("item", some 2)]⟩
def runtimeEmptyBox : Object := ⟨"Box", [("item", none)]⟩

def runtimeConstructed : State :=
  ⟨(3, runtimeBox) :: (2, runtimePair) :: runtimeTokens, [("b", some 3)], 4⟩
def runtimeLeft : State :=
  ⟨(3, runtimeBox) :: (2, runtimePartialPair) :: runtimeTokens,
    [("taken", some 0), ("b", some 3)], 4⟩
def runtimeItem : State :=
  ⟨(3, runtimeEmptyBox) :: (2, runtimePartialPair) :: runtimeTokens,
    [("p", some 2), ("taken", some 0), ("b", some 3)], 4⟩
def runtimeTakenPair : State :=
  { runtimeItem with variables := [("p", none), ("taken", some 0), ("b", some 3)] }
def runtimeFinal : State :=
  ⟨(3, runtimeEmptyBox) :: runtimeTokens,
    [("left", none), ("right", some 1), ("p", none), ("taken", some 0), ("b", some 3)], 4⟩

private theorem construct_runtime : Eval classes.erase State.empty
    (.new "Box" [.new "Pair" [.new "Token" [], .new "Token" []]])
    ⟨(3, runtimeBox) :: (2, runtimePair) :: runtimeTokens, [], 4⟩ 3 := by
  let first := State.empty.allocate "Token" [] []
  let second := first.allocate "Token" [] []
  let third := second.allocate "Pair" ["left", "right"] [0, 1]
  apply Eval.new (declaration := ⟨["item"]⟩) (evaluated := third) (objects := [2])
  · decide
  · apply EvalArgs.cons (middle := third) (object := 2)
    · apply Eval.new (declaration := ⟨["left", "right"]⟩)
        (evaluated := second) (objects := [0, 1])
      · decide
      · apply EvalArgs.cons (middle := first) (object := 0)
        · exact Eval.new (by decide) (.nil _) rfl (by decide)
        · apply EvalArgs.cons (middle := second) (object := 1)
          · exact Eval.new (by decide) (.nil _) rfl (by decide)
          · exact .nil _
      · rfl
      · decide
    · exact .nil _
  · rfl
  · decide

private theorem left_runtime : Eval classes.erase runtimeConstructed (.give leftPlace)
    ⟨(3, runtimeBox) :: (2, runtimePartialPair) :: runtimeTokens, [("b", some 3)], 4⟩ 0 := by
  apply Eval.give (source := .field 2 "left")
  · apply Resolve.field (parent := 2) (data := runtimePair)
    · apply Resolve.field (parent := 3) (data := runtimeBox)
      · exact .variable (by decide)
      · decide
      · decide
    · decide
    · decide
  · exact Take.field [("b", some 3)] 4 [(3, runtimeBox)] runtimeTokens 2 "Pair"
      [] [("right", some 1)] "left" 0

private theorem item_runtime : Eval classes.erase runtimeLeft (.give itemPlace)
    ⟨(3, runtimeEmptyBox) :: (2, runtimePartialPair) :: runtimeTokens,
      [("taken", some 0), ("b", some 3)], 4⟩ 2 := by
  apply Eval.give (source := .field 3 "item")
  · apply Resolve.field (parent := 3) (data := runtimeBox)
    · exact .variable (by decide)
    · decide
    · decide
  · exact Take.field [("taken", some 0), ("b", some 3)] 4 []
      ((2, runtimePartialPair) :: runtimeTokens) 3 "Box" [] [] "item" 2

private theorem unpack_runtime : Unpacking.Step classes.erase
    ⟨runtimeItem, [program[3]'(by decide)]⟩ ⟨runtimeFinal, []⟩ := by
  apply Unpacking.Step.letValue (evaluated := runtimeTakenPair) (object := 2)
  · exact Eval.give (Resolve.variable (by decide))
      (Take.variable runtimeItem.objects 4 [] [("taken", some 0), ("b", some 3)] "p" 2)
  · apply Unpacking.Bind.unpack (before := [(3, runtimeEmptyBox)]) (after := runtimeTokens)
      (declaration := ⟨["left", "right"]⟩)
      (bindings := [("left", none), ("right", some 1)])
    · decide
    · rfl
    · decide
    · decide
    · decide
    · exact .cons (before := []) (.cons (before := []) .nil)

theorem program_executes : Unpacking.Steps classes.erase ⟨State.empty, program⟩
    ⟨runtimeFinal, []⟩ := by
  apply Unpacking.Steps.step (middle := ⟨runtimeConstructed, program.tail⟩)
  · exact .letValue construct_runtime (.variable (by decide))
  · apply Unpacking.Steps.step (middle := ⟨runtimeLeft, program.tail.tail⟩)
    · exact .letValue left_runtime (.variable (by decide))
    · apply Unpacking.Steps.step (middle := ⟨runtimeItem, program.tail.tail.tail⟩)
      · exact .letValue item_runtime (.variable (by decide))
      · exact .step unpack_runtime (.refl _)

-- ANCHOR: moves_and_unpacking
example :
    StatementTyped classes [] (program[0]'(by decide)) afterConstruct ∧
    StatementTyped classes afterConstruct (program[1]'(by decide)) afterLeft ∧
    StatementTyped classes afterLeft (program[2]'(by decide)) afterItem ∧
    StatementTyped classes afterItem (program[3]'(by decide)) afterUnpack ∧
    SequenceTyped classes [] program afterUnpack ∧
    Unpacking.Steps classes.erase ⟨State.empty, program⟩ ⟨runtimeFinal, []⟩ ∧
    (Unpacking.Configuration.mk runtimeFinal []).finished ∧
    (∀ ty after, ¬ ExprTyped classes afterUnpack (.give (.variable "left")) ty after) ∧
    (∀ ty after, ¬ ExprTyped classes afterUnpack (.give (.variable "p")) ty after) := by
  exact ⟨construct_typed, left_typed, item_typed, unpack_typed, program_typed,
    program_executes, rfl, fun _ _ => failed_take_not_typed (by decide),
    fun _ _ => failed_take_not_typed (by decide)⟩
-- ANCHOR_END: moves_and_unpacking

end Dada.Unique.Typing.Checks
