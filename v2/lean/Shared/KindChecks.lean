import Shared.TypingSafety
import Shared.KindSafety

namespace Dada.Shared.KindChecks

open Typing

def classes : ClassTable :=
  [("Token", ⟨[], .structType⟩),
   ("Box", ⟨[("value", ⟨.given, "Token"⟩)], .structType⟩),
   ("SharedBox", ⟨[("value", ⟨.given, "Token"⟩)], .sharedStruct⟩),
   ("Resource", ⟨[("token", ⟨.given, "Token"⟩)], .classType⟩),
   ("Owner", ⟨[("resource", ⟨.given, "Resource"⟩), ("box", ⟨.given, "Box"⟩)], .classType⟩)]

def badBox : TypedClass := ⟨[("resource", ⟨.given, "Resource"⟩)], .structType⟩
def badSharedBox : TypedClass := ⟨badBox.fields, .sharedStruct⟩

-- ANCHOR: declarations
example : classes.WellFormed ∧
    StructType classes (.whole "Token") ∧ StructType classes (.whole "Box") ∧
    StructType classes (.whole "SharedBox" .shared) ∧
    ¬ StructType classes (.whole "Resource") ∧
    ¬ StructType classes ⟨.given, ⟨"Resource", []⟩⟩ ∧
    ¬ ClassTable.WellFormed (("BadBox", badBox) :: classes) ∧
    ¬ ClassTable.WellFormed (("BadSharedBox", badSharedBox) :: classes) := by
  decide
-- ANCHOR_END: declarations

def token : ValueType := .whole "Token"
def sharedBox : ValueType := .whole "SharedBox" .shared

def program : List Unpacking.Statement :=
  [⟨.variable "b", .new "SharedBox" [.new "Token" []]⟩,
   ⟨.variable "c", .give (.variable "b")⟩,
   ⟨.variable "t", .give (.field (.variable "b") "value")⟩]

def finalEnvironment : Environment :=
  [("t", some token.shared), ("c", some sharedBox), ("b", some sharedBox)]

theorem program_typed : SequenceTyped classes [] program finalEnvironment := by
  apply SequenceTyped.cons (middle := [("b", some sharedBox)])
  · apply StatementTyped.letValue (ty := sharedBox) (middle := [])
    · apply ExprTyped.new (declaration := ⟨[("value", ⟨.given, "Token"⟩)], .sharedStruct⟩) (by decide)
      · exact .cons (.new (declaration := ⟨[], .structType⟩) (by decide)
          (.nil (by decide)) (by decide) (by decide)) (.nil (by decide))
      · decide
      · decide
    · exact .variable (by decide) (by decide) (by decide)
  · apply SequenceTyped.cons (middle := [("c", some sharedBox), ("b", some sharedBox)])
    · exact .letValue (.give (by decide) (by decide) (by decide) (by decide))
        (.variable (by decide) (by decide) (by decide))
    · exact .cons (.letValue (.give (by decide) (by decide) (by decide) (by decide))
        (.variable (by decide) (by decide) (by decide))) (.nil (by decide))

def constructed : State :=
  ⟨[(1, ⟨"SharedBox", [("value", some (.owned 0))]⟩), (0, ⟨"Token", []⟩)],
    [("b", some (.shared 1))], 2⟩
def copied : State := constructed.bind "c" (.shared 1)
def promoted : State :=
  ⟨[(1, ⟨"SharedBox", [("value", some (.shared 0))]⟩), (0, ⟨"Token", []⟩)],
    copied.variables, 2⟩
def finalState : State := promoted.bind "t" (.shared 0)

theorem execution : Unpacking.Steps classes.erase ⟨State.empty, program⟩ ⟨finalState, []⟩ := by
  apply Unpacking.Steps.step (middle := ⟨constructed, program.tail⟩)
  · apply Unpacking.Step.letValue (evaluated := ⟨constructed.objects, [], 2⟩) (object := .shared 1)
    · apply Eval.new (declaration := ⟨["value"], .sharedStruct⟩)
        (evaluated := ⟨[(0, ⟨"Token", []⟩)], [], 1⟩) (references := [.owned 0])
      · decide
      · exact .cons (.new (declaration := ⟨[], .structType⟩) (by decide) (.nil _)
          rfl (by decide) (by simp [StructArguments])) (.nil _)
      · rfl
      · decide
      · simp [StructArguments, StructReference, classes, ClassTable.erase, Reference.owned, Kind.isStruct]
    · exact .variable (by decide)
  apply Unpacking.Steps.step (middle := ⟨copied, program.tail.tail⟩)
  · apply Unpacking.Step.letValue (evaluated := constructed) (object := .shared 1)
    · exact .give (.copy (Resolve.variable (reference := .shared 1) (by decide)) (by simp [Stored, constructed]))
    · exact .variable (by decide)
  apply Unpacking.Steps.step (middle := ⟨finalState, []⟩)
  · apply Unpacking.Step.letValue (evaluated := promoted) (object := .shared 0)
    · apply Eval.give
      apply Give.promote (source := .field 1 "value")
      · exact .field (permission := .shared) (reference := .owned 0)
          (data := ⟨"SharedBox", [("value", some (.owned 0))]⟩)
          (Resolve.variable (reference := .shared 1) (by decide)) (by decide) (by decide)
      · exact .field copied.variables 2 [] [(0, ⟨"Token", []⟩)]
          1 "SharedBox" [] [] "value" 0
    · exact .variable (by decide)
  exact .refl _

-- ANCHOR: immediately_shared
example : SequenceTyped classes [] program finalEnvironment ∧
    Unpacking.Steps classes.erase ⟨State.empty, program⟩ ⟨finalState, []⟩ ∧
    RawType.normalize classes (.nominal (.whole "SharedBox")) = sharedBox ∧
    ¬ Admissible classes (.whole "SharedBox") ∧
    ¬ Admissible classes (.whole "Resource" .shared) ∧
    ("b", some (.shared 1)) ∈ finalState.variables ∧
    ("c", some (.shared 1)) ∈ finalState.variables ∧
    ("t", some (.shared 0)) ∈ finalState.variables := by
  exact ⟨program_typed, execution, by decide, by decide, by decide,
    by decide, by decide, by decide⟩
-- ANCHOR_END: immediately_shared

theorem class_construction : ExprTyped classes [] (.new "Resource" [.new "Token" []])
    (.whole "Resource") [] := by
  apply ExprTyped.new (declaration := ⟨[("token", ⟨.given, "Token"⟩)], .classType⟩) (by decide)
  · exact .cons (.new (declaration := ⟨[], .structType⟩) (by decide)
      (.nil (by decide)) (by decide) (by decide)) (.nil (by decide))
  · decide
  · decide

theorem class_sharing_rejected :
    ¬ ExprTyped classes [("r", some (.whole "Resource"))] (.giveShare (.variable "r")) ty after := by
  intro typed
  obtain ⟨source, taken, structTy⟩ := typed.giveShare_requires_struct _ rfl
  have operation : give classes [("r", some (.whole "Resource"))] (.variable "r") =
      some (.whole "Resource", [("r", none)]) := by decide
  rw [operation] at taken
  have same := (Prod.mk.inj (Option.some.inj taken)).1
  subst source
  exact (by decide : ¬ StructType classes (.whole "Resource")) structTy

-- ANCHOR: class_boundary
example : ExprTyped classes [] (.new "Resource" [.new "Token" []]) (.whole "Resource") [] ∧
    (∀ ty after, ¬ ExprTyped classes [("r", some (.whole "Resource"))]
      (.giveShare (.variable "r")) ty after) ∧
    (∀ after, ¬ Unpacking.Bind classes.erase constructed (.shared 1)
      (.unpack "SharedBox" [("value", "v")]) after) ∧
    give classes [("r", some (.whole "Resource"))] (.variable "r") =
      some (.whole "Resource", [("r", none)]) := by
  exact ⟨class_construction, fun _ _ => class_sharing_rejected,
    (fun _ => Unpacking.shared_cannot_unpack), by decide⟩
-- ANCHOR_END: class_boundary

end Dada.Shared.KindChecks
