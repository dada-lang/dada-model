import Unique.Typing

namespace Dada.Unique.Typing.Checks

def classes : ClassTable :=
  [("Token", ⟨[]⟩), ("Pair", ⟨[("left", "Token"), ("right", "Token")]⟩),
    ("Box", ⟨[("item", "Pair")]⟩)]

def token : ViewType := .whole "Token"
def pair : ViewType := .whole "Pair"
def box : ViewType := .whole "Box"
def partialPair : ViewType := ⟨"Pair", [.negative ["left"], .positive ["right"]]⟩
def partialBox : ViewType :=
  ⟨"Box", [.negative ["item", "left"], .positive ["item", "right"]]⟩
def emptyBox : ViewType := ⟨"Box", [.negative ["item"]]⟩

def afterConstruct : Environment := [("b", some box)]
def afterLeft : Environment := [("taken", some token), ("b", some partialBox)]
def afterItem : Environment :=
  [("p", some partialPair), ("taken", some token), ("b", some emptyBox)]
def beforeUnpack : Environment :=
  [("p", none), ("taken", some token), ("b", some emptyBox)]
def afterUnpack : Environment := [("left", none), ("right", some token)] ++ beforeUnpack

def leftPlace : Place := .field (.field (.variable "b") "item") "left"
def itemPlace : Place := .field (.variable "b") "item"

def program : List Unpacking.Statement :=
  [⟨.variable "b", .new "Box" [.new "Pair" [.new "Token" [], .new "Token" []]]⟩,
   ⟨.variable "taken", .give leftPlace⟩,
   ⟨.variable "p", .give itemPlace⟩,
   ⟨.unpack "Pair" [("left", "left"), ("right", "right")], .give (.variable "p")⟩]

private theorem token_typed : ExprTyped classes [] (.new "Token" []) token [] := by
  exact .new (declaration := ⟨[]⟩) (by decide) (.nil (by decide)) (by decide)

theorem construct_typed : StatementTyped classes [] (program[0]'(by decide)) afterConstruct := by
  apply StatementTyped.letValue (ty := box) (middle := [])
  · apply ExprTyped.new (declaration := ⟨[("item", "Pair")]⟩) (by decide)
    · apply ArgsTyped.cons
      · apply ExprTyped.new (declaration := ⟨[("left", "Token"), ("right", "Token")]⟩)
          (by decide)
        · exact .cons token_typed (.cons token_typed (.nil (by decide)))
        · decide
      · exact .nil (by decide)
    · decide
  · exact .variable (by decide) (by decide) (by decide)

theorem left_typed : StatementTyped classes afterConstruct (program[1]'(by decide)) afterLeft := by
  apply StatementTyped.letValue (ty := token) (middle := [("b", some partialBox)])
  · exact .give (by decide) (by decide) (by decide) (by decide)
  · exact .variable (by decide) (by decide) (by decide)

theorem item_typed : StatementTyped classes afterLeft (program[2]'(by decide)) afterItem := by
  apply StatementTyped.letValue (ty := partialPair)
    (middle := [("taken", some token), ("b", some emptyBox)])
  · exact .give (by decide) (by decide) (by decide) (by decide)
  · exact .variable (by decide) (by decide) (by decide)

theorem unpack_typed : StatementTyped classes afterItem (program[3]'(by decide)) afterUnpack := by
  apply StatementTyped.letValue (ty := partialPair) (middle := beforeUnpack)
  · exact .give (by decide) (by decide) (by decide) (by decide)
  · apply BindingTyped.unpack (declaration := ⟨[("left", "Token"), ("right", "Token")]⟩)
      (bindings := [("left", none), ("right", some token)])
    · decide
    · decide
    · rfl
    · decide
    · exact .refl _
    · decide
    · decide
    · exact .cons (by decide) (.cons (by decide) .nil)
    · decide

theorem program_typed : SequenceTyped classes [] program afterUnpack := by
  exact .cons construct_typed (.cons left_typed (.cons item_typed
    (.cons unpack_typed (.nil (by decide)))))

theorem classes_wellFormed : classes.WellFormed := by
  unfold ClassTable.WellFormed
  decide

theorem well_typed_program : ProgramTyped classes program :=
  ⟨classes_wellFormed, afterUnpack, program_typed⟩

-- ANCHOR: moves_and_unpacking
example : SequenceTyped classes [] program afterUnpack ∧
    afterUnpack.lookup "left" = some none ∧
    afterUnpack.lookup "right" = some (some token) ∧
    afterUnpack.lookup "b" = some (some emptyBox) := by
  exact ⟨program_typed, by decide, by decide, by decide⟩
-- ANCHOR_END: moves_and_unpacking

-- ANCHOR: take_root_and_field
example :
    splitPlace (.variable "b") = ("b", []) ∧
    splitPlace leftPlace = ("b", ["item", "left"]) ∧
    take classes afterConstruct (.variable "b") = some (box, [("b", none)]) ∧
    take classes afterConstruct leftPlace = some (token, [("b", some partialBox)]) := by
  decide
-- ANCHOR_END: take_root_and_field

-- Empty slots and unknown fields both fail, without treating them as equal.
example : take classes [("p", some partialPair)] (.field (.variable "p") "left") = none := by
  decide

example : take classes [("p", some ⟨"Pair", [.positive ["right"]]⟩)]
    (.field (.variable "p") "left") = none := by
  decide

example : fieldDescription classes ⟨"Pair", [.positive ["right"]]⟩ "left" = none := by
  decide

-- These rule out every derivation, including any chain of view weakening.
example : ¬ ExprTyped classes [("p", some partialPair)]
    (.give (.field (.variable "p") "left")) ty after :=
  failed_take_not_typed (by decide)

example : ¬ ExprTyped classes [("p", some ⟨"Pair", [.positive ["right"]]⟩)]
    (.give (.field (.variable "p") "left")) ty after :=
  failed_take_not_typed (by decide)

example : ¬ ExprTyped classes afterUnpack (.give (.variable "left")) ty after :=
  failed_take_not_typed (by decide)

end Dada.Unique.Typing.Checks
