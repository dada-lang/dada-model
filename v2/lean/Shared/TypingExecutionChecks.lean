import Shared.TypingChecks
import Shared.UnpackingChecks

namespace Dada.Shared.Typing.ExecutionChecks

open Checks

def boxCreated : State :=
  ⟨[(1, ⟨"Box", [("item", some (.owned 0))]⟩), (0, ⟨"Token", []⟩)],
    [("b", some (.owned 1))], 2⟩

def boxShared : State :=
  ⟨boxCreated.objects, [("s", some (.shared 1)), ("b", none)], 2⟩

def boxCopied : State :=
  ⟨[(1, ⟨"Box", [("item", some (.shared 0))]⟩), (0, ⟨"Token", []⟩)],
    [("u", some (.shared 0)), ("s", some (.shared 1)), ("b", none)], 2⟩

def boxCopiedTwice : State := boxCopied.bind "v" (.shared 0)

private theorem create_box : Eval classes.erase State.empty
    (.new "Box" [.new "Token" []])
    ⟨boxCreated.objects, [], 2⟩ (.owned 1) := by
  apply Eval.new (declaration := ⟨["item"], .structType⟩)
    (evaluated := ⟨[(0, ⟨"Token", []⟩)], [], 1⟩) (references := [.owned 0])
  · decide
  · apply EvalArgs.cons (middle := ⟨[(0, ⟨"Token", []⟩)], [], 1⟩) (reference := .owned 0)
    · exact Eval.new (declaration := ⟨[], .structType⟩) (evaluated := State.empty)
        (references := []) (by decide) (.nil _) rfl (by simp [State.empty]) (by simp [StructArguments])
    · exact .nil _
  · rfl
  · decide
  · simp [StructArguments, StructReference, classes, ClassTable.erase, Reference.owned, Kind.isStruct]

private theorem share_box : Eval classes.erase boxCreated (.giveShare (.variable "b"))
    ⟨boxCreated.objects, [("b", none)], 2⟩ (.shared 1) := by
  apply Eval.giveShare (reference := .owned 1)
  exact Give.move (source := .variable "b")
    (Resolve.variable (reference := .owned 1) (by decide))
    (.variable boxCreated.objects 2 [] [] "b" 1)
  all_goals simp [StructReference, boxCreated, classes, ClassTable.erase, Reference.owned, Kind.isStruct]

private theorem first_copy : Eval classes.erase boxShared (.give (field "s" "item"))
    ⟨boxCopied.objects, boxShared.variables, 2⟩ (.shared 0) := by
  apply Eval.give
  apply Give.promote (source := .field 1 "item")
  · exact Resolve.field (permission := .shared) (reference := .owned 0)
      (data := ⟨"Box", [("item", some (.owned 0))]⟩)
      (Resolve.variable (reference := .shared 1) (by decide)) (by decide) (by decide)
  · exact Promote.field boxShared.variables 2 [] [(0, ⟨"Token", []⟩)]
      1 "Box" [] [] "item" 0

private theorem second_copy : Eval classes.erase boxCopied (.give (field "s" "item"))
    boxCopied (.shared 0) := by
  apply Eval.give
  apply Give.copy (source := .field 1 "item")
  · exact Resolve.field (permission := .shared) (reference := .shared 0)
      (data := ⟨"Box", [("item", some (.shared 0))]⟩)
      (Resolve.variable (reference := .shared 1) (by decide)) (by decide) (by decide)
  · exact ⟨⟨"Box", [("item", some (.shared 0))]⟩, by decide, by decide⟩

theorem copy_execution : Unpacking.StepsExactly classes.erase
    ⟨State.empty, copyProgram⟩ 4 ⟨boxCopiedTwice, []⟩ := by
  apply Unpacking.StepsExactly.step (middle := ⟨boxCreated, copyProgram.tail⟩)
  · exact .letValue create_box (.variable (by decide))
  · apply Unpacking.StepsExactly.step (middle := ⟨boxShared, copyProgram.drop 2⟩)
    · exact .letValue share_box (.variable (by decide))
    · apply Unpacking.StepsExactly.step (middle := ⟨boxCopied, copyProgram.drop 3⟩)
      · exact .letValue first_copy (.variable (by decide))
      · exact .step (.letValue second_copy (.variable (by decide))) (.refl _)

-- ANCHOR: copying_through_shared
example : SequenceTyped classes [] copyProgram copyFinal ∧
    Unpacking.StepsExactly classes.erase ⟨State.empty, copyProgram⟩ 4 ⟨boxCopiedTwice, []⟩ ∧
    Eval classes.erase boxShared (.give (field "s" "item"))
      ⟨boxCopied.objects, boxShared.variables, 2⟩ (.shared 0) ∧
    Eval classes.erase boxCopied (.give (field "s" "item")) boxCopied (.shared 0) ∧
    copyFinal.lookup "b" = some none ∧
    copyFinal.lookup "s" = some (some box.shared) ∧
    copyFinal.lookup "u" = some (some token.shared) ∧
    copyFinal.lookup "v" = some (some token.shared) ∧
    (1, ⟨"Box", [("item", some (.owned 0))]⟩) ∈ boxShared.objects ∧
    (1, ⟨"Box", [("item", some (.shared 0))]⟩) ∈ boxCopied.objects ∧
    ("s", some (.shared 1)) ∈ boxCopiedTwice.variables ∧
    ("u", some (.shared 0)) ∈ boxCopiedTwice.variables ∧
    ("v", some (.shared 0)) ∈ boxCopiedTwice.variables := by
  exact ⟨copy_typed, copy_execution, first_copy, second_copy, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩
-- ANCHOR_END: copying_through_shared

-- ANCHOR: unpacking_shared_fields
example : SequenceTyped classes argumentFinal
    [⟨.unpack "Holder" [("item", "item")], .give (.variable "h")⟩,
     ⟨.variable "c", .give (.variable "item")⟩] unpackFinal ∧
    Unpacking.StepsExactly classes.erase
      ⟨State.empty, Unpacking.unpackingProgram⟩ 6 ⟨Unpacking.unpackingFinished, []⟩ ∧
    unpackFinal.lookup "h" = some none ∧
    unpackFinal.lookup "item" = some (some token.shared) ∧
    unpackFinal.lookup "a" = some (some token.shared) ∧
    unpackFinal.lookup "b" = some (some token.shared) ∧
    unpackFinal.lookup "c" = some (some token.shared) ∧
    ¬ Allocated Unpacking.unpackingFinished 1 ∧
    (∀ after, ¬ BindingTyped classes [("s", some holder.shared)]
      (.unpack "Holder" [("item", "item")]) holder.shared after) := by
  refine ⟨unpack_typed, Unpacking.unpacking_execution, by decide, by decide,
    by decide, by decide, by decide, ?_, ?_⟩
  · change (1 : ObjectId) ∉ [0]; decide
  · intro after typed
    cases typed with
    | unpack _ _ given => cases given
-- ANCHOR_END: unpacking_shared_fields


-- ANCHOR: constructor_permissions
example : SequenceTyped classes [] argumentProgram argumentFinal ∧
    Unpacking.Steps classes.erase ⟨State.empty, argumentProgram⟩ ⟨Unpacking.argumentsFinished, []⟩ ∧
    argumentFinal.lookup "t" = some none ∧
    argumentFinal.lookup "h" = some (some holder) ∧
    argumentFinal.lookup "a" = some (some token.shared) ∧
    argumentFinal.lookup "b" = some (some token.shared) ∧
    (∀ ty after, ¬ ExprTyped classes [("t", some token)]
      (.new "Holder" [.give (.variable "t")]) ty after) ∧
    (∀ ty after, ¬ ExprTyped classes argumentFinal
      (.new "Box" [.give (.variable "a")]) ty after) := by
  exact ⟨arguments_typed, Unpacking.arguments_execution, by decide, by decide, by decide, by decide,
    fun _ _ => holder_requires_sharing, fun _ _ => box_rejects_shared⟩
-- ANCHOR_END: constructor_permissions

def pairCreated : State :=
  ⟨[(2, ⟨"Pair", [("left", some (.owned 0)), ("right", some (.owned 1))]⟩),
    (1, ⟨"Token", []⟩), (0, ⟨"Token", []⟩)], [("p", some (.owned 2))], 3⟩

def pairMoved : State :=
  ⟨[(2, ⟨"Pair", [("left", none), ("right", some (.owned 1))]⟩),
    (1, ⟨"Token", []⟩), (0, ⟨"Token", []⟩)],
    [("t", some (.owned 0)), ("p", some (.owned 2))], 3⟩

def pairShared : State :=
  ⟨pairMoved.objects, [("s", some (.shared 2)), ("t", some (.owned 0)), ("p", none)], 3⟩

def pairCopied : State :=
  ⟨[(2, ⟨"Pair", [("left", none), ("right", some (.shared 1))]⟩),
    (1, ⟨"Token", []⟩), (0, ⟨"Token", []⟩)],
    [("a", some (.shared 1)), ("s", some (.shared 2)), ("t", some (.owned 0)), ("p", none)], 3⟩

def pairCopiedTwice : State := pairCopied.bind "b" (.shared 1)

private theorem create_pair : Eval classes.erase State.empty
    (.new "Pair" [.new "Token" [], .new "Token" []])
    ⟨pairCreated.objects, [], 3⟩ (.owned 2) := by
  let first := State.empty.allocate "Token" [] []
  let second := first.allocate "Token" [] []
  apply Eval.new (declaration := ⟨["left", "right"], .structType⟩)
    (evaluated := second) (references := [.owned 0, .owned 1])
  · decide
  · apply EvalArgs.cons (middle := first) (reference := .owned 0)
    · exact Eval.new (declaration := ⟨[], .structType⟩) (evaluated := State.empty)
        (references := []) (by decide) (.nil _) rfl (by simp [State.empty]) (by simp [StructArguments])
    · apply EvalArgs.cons (middle := second) (reference := .owned 1)
      · exact Eval.new (declaration := ⟨[], .structType⟩) (evaluated := first)
          (references := []) (by decide) (.nil _) rfl (by decide) (by simp [StructArguments])
      · exact .nil _
  · rfl
  · decide
  · simp +decide [StructArguments, StructReference, first, second, State.allocate, State.empty, classes, ClassTable.erase, Reference.owned, Kind.isStruct]

private theorem move_left : Eval classes.erase pairCreated (.give (field "p" "left"))
    ⟨pairMoved.objects, [("p", some (.owned 2))], 3⟩ (.owned 0) := by
  apply Eval.give
  apply Give.move (source := .field 2 "left")
  · exact Resolve.field (permission := .unique) (reference := .owned 0)
      (data := ⟨"Pair", [("left", some (.owned 0)), ("right", some (.owned 1))]⟩)
      (Resolve.variable (reference := .owned 2) (by decide)) (by decide) (by decide)
  · exact Take.field pairCreated.variables 3 [] [(1, ⟨"Token", []⟩), (0, ⟨"Token", []⟩)]
      2 "Pair" [] [("right", some (.owned 1))] "left" 0

private theorem share_pair : Eval classes.erase pairMoved (.giveShare (.variable "p"))
    ⟨pairMoved.objects, [("t", some (.owned 0)), ("p", none)], 3⟩ (.shared 2) := by
  apply Eval.giveShare (reference := .owned 2)
  exact Give.move (source := .variable "p")
    (Resolve.variable (reference := .owned 2) (by decide))
    (.variable pairMoved.objects 3 [("t", some (.owned 0))] [] "p" 2)
  all_goals simp [StructReference, pairMoved, classes, ClassTable.erase, Reference.owned, Kind.isStruct]

private theorem copy_right_first : Eval classes.erase pairShared (.give (field "s" "right"))
    ⟨pairCopied.objects, pairShared.variables, 3⟩ (.shared 1) := by
  apply Eval.give
  apply Give.promote (source := .field 2 "right")
  · exact Resolve.field (permission := .shared) (reference := .owned 1)
      (data := ⟨"Pair", [("left", none), ("right", some (.owned 1))]⟩)
      (Resolve.variable (reference := .shared 2) (by decide)) (by decide) (by decide)
  · exact Promote.field pairShared.variables 3 [] [(1, ⟨"Token", []⟩), (0, ⟨"Token", []⟩)]
      2 "Pair" [("left", none)] [] "right" 1

private theorem copy_right_again : Eval classes.erase pairCopied (.give (field "s" "right"))
    pairCopied (.shared 1) := by
  apply Eval.give
  apply Give.copy (source := .field 2 "right")
  · exact Resolve.field (permission := .shared) (reference := .shared 1)
      (data := ⟨"Pair", [("left", none), ("right", some (.shared 1))]⟩)
      (Resolve.variable (reference := .shared 2) (by decide)) (by decide) (by decide)
  · exact ⟨⟨"Pair", [("left", none), ("right", some (.shared 1))]⟩, by decide, by decide⟩

theorem partial_execution : Unpacking.StepsExactly classes.erase
    ⟨State.empty, partialProgram⟩ 5 ⟨pairCopiedTwice, []⟩ := by
  apply Unpacking.StepsExactly.step (middle := ⟨pairCreated, partialProgram.tail⟩)
  · exact .letValue create_pair (.variable (by decide))
  · apply Unpacking.StepsExactly.step (middle := ⟨pairMoved, partialProgram.drop 2⟩)
    · exact .letValue move_left (.variable (by decide))
    · apply Unpacking.StepsExactly.step (middle := ⟨pairShared, partialProgram.drop 3⟩)
      · exact .letValue share_pair (.variable (by decide))
      · apply Unpacking.StepsExactly.step (middle := ⟨pairCopied, partialProgram.drop 4⟩)
        · exact .letValue copy_right_first (.variable (by decide))
        · exact .step (.letValue copy_right_again (.variable (by decide))) (.refl _)

-- ANCHOR: sharing_partial_views
example : SequenceTyped classes [] partialProgram partialFinal ∧
    Unpacking.StepsExactly classes.erase ⟨State.empty, partialProgram⟩ 5 ⟨pairCopiedTwice, []⟩ ∧
    partialFinal.lookup "s" = some (some partialPair.shared) ∧
    partialFinal.lookup "a" = some (some token.shared) ∧
    partialFinal.lookup "b" = some (some token.shared) ∧
    (2, ⟨"Pair", [("left", none), ("right", some (.shared 1))]⟩) ∈ pairCopiedTwice.objects ∧
    ("p", none) ∈ pairCopiedTwice.variables ∧
    ("a", some (.shared 1)) ∈ pairCopiedTwice.variables ∧
    ("b", some (.shared 1)) ∈ pairCopiedTwice.variables ∧
    (∀ ty after, ¬ ExprTyped classes partialFinal (.give (field "s" "left")) ty after) := by
  exact ⟨partial_typed, partial_execution, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide,
    fun _ _ => failed_give_not_typed (by decide)⟩
-- ANCHOR_END: sharing_partial_views

end Dada.Shared.Typing.ExecutionChecks
