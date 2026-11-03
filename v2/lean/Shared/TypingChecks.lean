import Shared.Typing

namespace Dada.Shared.Typing.Checks

def classes : ClassTable :=
  [("Token", ⟨[], .structType⟩),
   ("Box", ⟨[("item", ⟨.given, "Token"⟩)], .structType⟩),
   ("Outer", ⟨[("box", ⟨.shared, "Box"⟩)], .classType⟩),
   ("Holder", ⟨[("item", ⟨.shared, "Token"⟩)], .structType⟩),
   ("Pair", ⟨[("left", ⟨.given, "Token"⟩), ("right", ⟨.given, "Token"⟩)], .structType⟩)]

def token : ValueType := .whole "Token"
def box : ValueType := .whole "Box"
def holder : ValueType := .whole "Holder"
def pair : ValueType := .whole "Pair"
def partialPair : ValueType := ⟨.given, ⟨"Pair", [.negative ["left"], .positive ["right"]]⟩⟩

def field (root name : String) : Place := .field (.variable root) name

private theorem token_typed (wf : environment.WellFormed classes) :
    ExprTyped classes environment (.new "Token" []) token environment :=
  .new (declaration := ⟨[], .structType⟩) (by decide) (.nil wf) (by decide) (by decide)

def copyProgram : List Unpacking.Statement :=
  [⟨.variable "b", .new "Box" [.new "Token" []]⟩,
   ⟨.variable "s", .giveShare (.variable "b")⟩,
   ⟨.variable "u", .give (field "s" "item")⟩,
   ⟨.variable "v", .give (field "s" "item")⟩]

def copyFinal : Environment :=
  [("v", some token.shared), ("u", some token.shared), ("s", some box.shared), ("b", none)]

theorem copy_typed : SequenceTyped classes [] copyProgram copyFinal := by
  apply SequenceTyped.cons (middle := [("b", some box)])
  · apply StatementTyped.letValue (ty := box) (middle := [])
    · exact .new (declaration := ⟨[("item", ⟨.given, "Token"⟩)], .structType⟩) (by decide)
        (.cons (token_typed (by decide)) (.nil (by decide))) (by decide) (by decide)
    · exact .variable (by decide) (by decide) (by decide)
  · apply SequenceTyped.cons (middle := [("s", some box.shared), ("b", none)])
    · apply StatementTyped.letValue (ty := box.shared) (middle := [("b", none)])
      · exact .giveShare (ty := box) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact .variable (by decide) (by decide) (by decide)
    · apply SequenceTyped.cons
        (middle := [("u", some token.shared), ("s", some box.shared), ("b", none)])
      · apply StatementTyped.letValue (ty := token.shared)
          (middle := [("s", some box.shared), ("b", none)])
        · exact .give (by decide) (by decide) (by decide) (by decide)
        · exact .variable (by decide) (by decide) (by decide)
      · apply SequenceTyped.cons
        · apply StatementTyped.letValue (ty := token.shared)
            (middle := [("u", some token.shared), ("s", some box.shared), ("b", none)])
          · exact .give (by decide) (by decide) (by decide) (by decide)
          · exact .variable (by decide) (by decide) (by decide)
        · exact .nil (by decide)

-- ANCHOR: copying_through_shared
example : SequenceTyped classes [] copyProgram copyFinal ∧
    copyFinal.lookup "b" = some none ∧
    copyFinal.lookup "s" = some (some box.shared) ∧
    copyFinal.lookup "u" = some (some token.shared) ∧
    copyFinal.lookup "v" = some (some token.shared) :=
  ⟨copy_typed, by decide, by decide, by decide, by decide⟩
-- ANCHOR_END: copying_through_shared

-- ANCHOR: permission_paths
example :
    focus classes box ["item"] = some token ∧
    focus classes box.shared ["item"] = some token.shared ∧
    focus classes (.whole "Outer") ["box", "item"] = some token.shared ∧
    focus classes holder ["item"] = some token.shared ∧
    give classes [("b", some box)] (field "b" "item") =
      some (token, [("b", some ⟨.given, ⟨"Box", [.negative ["item"]]⟩⟩)]) ∧
    give classes [("s", some box.shared)] (field "s" "item") =
      some (token.shared, [("s", some box.shared)]) ∧
    give classes [("o", some (.whole "Outer"))] (place :=
      .field (field "o" "box") "item") =
      some (token.shared, [("o", some (.whole "Outer"))]) ∧
    give classes [("h", some holder)] (field "h" "item") =
      some (token.shared, [("h", some holder)]) := by
  exact ⟨by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
-- ANCHOR_END: permission_paths

def argumentProgram : List Unpacking.Statement :=
  [⟨.variable "t", .new "Token" []⟩,
   ⟨.variable "h", .new "Holder" [.giveShare (.variable "t")]⟩,
   ⟨.variable "a", .give (field "h" "item")⟩,
   ⟨.variable "b", .give (field "h" "item")⟩]

def argumentFinal : Environment :=
  [("b", some token.shared), ("a", some token.shared), ("h", some holder), ("t", none)]

theorem arguments_typed : SequenceTyped classes [] argumentProgram argumentFinal := by
  apply SequenceTyped.cons (middle := [("t", some token)])
  · exact .letValue (token_typed (by decide)) (.variable (by decide) (by decide) (by decide))
  · apply SequenceTyped.cons (middle := [("h", some holder), ("t", none)])
    · apply StatementTyped.letValue (ty := holder) (middle := [("t", none)])
      · apply ExprTyped.new (declaration := ⟨[("item", ⟨.shared, "Token"⟩)], .structType⟩) (by decide)
        · exact .cons (.giveShare (ty := token) (by decide) (by decide) (by decide) (by decide) (by decide))
            (.nil (by decide))
        · decide
        · decide
      · exact .variable (by decide) (by decide) (by decide)
    · apply SequenceTyped.cons
        (middle := [("a", some token.shared), ("h", some holder), ("t", none)])
      · apply StatementTyped.letValue (ty := token.shared)
          (middle := [("h", some holder), ("t", none)])
        · exact .give (by decide) (by decide) (by decide) (by decide)
        · exact .variable (by decide) (by decide) (by decide)
      · apply SequenceTyped.cons
        · apply StatementTyped.letValue (ty := token.shared)
            (middle := [("a", some token.shared), ("h", some holder), ("t", none)])
          · exact .give (by decide) (by decide) (by decide) (by decide)
          · exact .variable (by decide) (by decide) (by decide)
        · exact .nil (by decide)

theorem give_wrong_permission (taken : give classes environment place = some (result, computedAfter))
    (different : result.permission ≠ ty.permission) :
    ¬ ExprTyped classes environment (.give place) ty after := by
  intro typed
  obtain ⟨other, same, modes⟩ := typed.give_permission place rfl
  have equal := (Prod.mk.inj (Option.some.inj (taken.symm.trans same))).1
  exact different (equal ▸ modes)

theorem holder_requires_sharing :
    ¬ ExprTyped classes [("t", some token)]
      (.new "Holder" [.give (.variable "t")]) ty after := by
  intro typed
  obtain ⟨declaration, declared, arguments⟩ := typed.new_requires_arguments "Holder" _ rfl
  have same : declaration = ⟨[("item", ⟨.shared, "Token"⟩)], .structType⟩ := by
    simpa [classes] using declared
  subst declaration
  cases arguments with
  | cons first rest =>
    exact give_wrong_permission (result := token) (computedAfter := [("t", none)])
      (by decide) (by decide) first

theorem box_rejects_shared :
    ¬ ExprTyped classes argumentFinal (.new "Box" [.give (.variable "a")]) ty after := by
  intro typed
  obtain ⟨declaration, declared, arguments⟩ := typed.new_requires_arguments "Box" _ rfl
  have same : declaration = ⟨[("item", ⟨.given, "Token"⟩)], .structType⟩ := by
    simpa [classes] using declared
  subst declaration
  cases arguments with
  | cons first rest =>
    exact give_wrong_permission (result := token.shared) (computedAfter := argumentFinal)
      (by decide) (by decide) first

-- ANCHOR: constructor_permissions
example : SequenceTyped classes [] argumentProgram argumentFinal ∧
    argumentFinal.lookup "t" = some none ∧
    argumentFinal.lookup "h" = some (some holder) ∧
    argumentFinal.lookup "a" = some (some token.shared) ∧
    argumentFinal.lookup "b" = some (some token.shared) ∧
    (∀ ty after, ¬ ExprTyped classes [("t", some token)]
      (.new "Holder" [.give (.variable "t")]) ty after) ∧
    (∀ ty after, ¬ ExprTyped classes argumentFinal
      (.new "Box" [.give (.variable "a")]) ty after) := by
  exact ⟨arguments_typed, by decide, by decide, by decide, by decide,
    fun _ _ => holder_requires_sharing, fun _ _ => box_rejects_shared⟩
-- ANCHOR_END: constructor_permissions

def partialProgram : List Unpacking.Statement :=
  [⟨.variable "p", .new "Pair" [.new "Token" [], .new "Token" []]⟩,
   ⟨.variable "t", .give (field "p" "left")⟩,
   ⟨.variable "s", .giveShare (.variable "p")⟩,
   ⟨.variable "a", .give (field "s" "right")⟩,
   ⟨.variable "b", .give (field "s" "right")⟩]

def partialFinal : Environment :=
  [("b", some token.shared), ("a", some token.shared), ("s", some partialPair.shared),
   ("t", some token), ("p", none)]

theorem partial_typed : SequenceTyped classes [] partialProgram partialFinal := by
  apply SequenceTyped.cons (middle := [("p", some pair)])
  · apply StatementTyped.letValue (ty := pair) (middle := [])
    · exact .new (declaration := ⟨[("left", ⟨.given, "Token"⟩), ("right", ⟨.given, "Token"⟩)], .structType⟩)
        (by decide) (.cons (token_typed (by decide))
          (.cons (token_typed (by decide)) (.nil (by decide)))) (by decide) (by decide)
    · exact .variable (by decide) (by decide) (by decide)
  · apply SequenceTyped.cons (middle := [("t", some token), ("p", some partialPair)])
    · apply StatementTyped.letValue (ty := token) (middle := [("p", some partialPair)])
      · exact .give (by decide) (by decide) (by decide) (by decide)
      · exact .variable (by decide) (by decide) (by decide)
    · apply SequenceTyped.cons
        (middle := [("s", some partialPair.shared), ("t", some token), ("p", none)])
      · apply StatementTyped.letValue (ty := partialPair.shared)
          (middle := [("t", some token), ("p", none)])
        · exact .giveShare (ty := partialPair) (by decide) (by decide) (by decide) (by decide) (by decide)
        · exact .variable (by decide) (by decide) (by decide)
      · apply SequenceTyped.cons (middle := [("a", some token.shared),
          ("s", some partialPair.shared), ("t", some token), ("p", none)])
        · apply StatementTyped.letValue (ty := token.shared)
            (middle := [("s", some partialPair.shared), ("t", some token), ("p", none)])
          · exact .give (by decide) (by decide) (by decide) (by decide)
          · exact .variable (by decide) (by decide) (by decide)
        · apply SequenceTyped.cons
          · apply StatementTyped.letValue (ty := token.shared)
              (middle := [("a", some token.shared), ("s", some partialPair.shared),
                ("t", some token), ("p", none)])
            · exact .give (by decide) (by decide) (by decide) (by decide)
            · exact .variable (by decide) (by decide) (by decide)
          · exact .nil (by decide)

-- ANCHOR: sharing_partial_views
example : SequenceTyped classes [] partialProgram partialFinal ∧
    partialFinal.lookup "s" = some (some partialPair.shared) ∧
    partialFinal.lookup "a" = some (some token.shared) ∧
    partialFinal.lookup "b" = some (some token.shared) ∧
    (∀ ty after, ¬ ExprTyped classes partialFinal (.give (field "s" "left")) ty after) := by
  exact ⟨partial_typed, by decide, by decide, by decide,
    fun _ _ => failed_give_not_typed (by decide)⟩
-- ANCHOR_END: sharing_partial_views

def unpackFinal : Environment :=
  [("c", some token.shared), ("item", some token.shared),
   ("b", some token.shared), ("a", some token.shared), ("h", none), ("t", none)]

theorem unpack_typed : SequenceTyped classes argumentFinal
    [⟨.unpack "Holder" [("item", "item")], .give (.variable "h")⟩,
     ⟨.variable "c", .give (.variable "item")⟩] unpackFinal := by
  let emptied : Environment :=
    [("b", some token.shared), ("a", some token.shared), ("h", none), ("t", none)]
  apply SequenceTyped.cons (middle := ("item", some token.shared) :: emptied)
  · apply StatementTyped.letValue (ty := holder) (middle := emptied)
    · exact .give (by decide) (by decide) (by decide) (by decide)
    · apply BindingTyped.unpack (declaration := ⟨[("item", ⟨.shared, "Token"⟩)], .structType⟩)
        (bindings := [("item", some token.shared)])
      · decide
      · decide
      · rfl
      · rfl
      · decide
      · exact .refl _
      · decide
      · decide
      · exact .cons (by decide) .nil
      · decide
  · apply SequenceTyped.cons
    · apply StatementTyped.letValue (ty := token.shared)
        (middle := ("item", some token.shared) :: emptied)
      · exact .give (by decide) (by decide) (by decide) (by decide)
      · exact .variable (by decide) (by decide) (by decide)
    · exact .nil (by decide)

-- ANCHOR: unpacking_shared_fields
example : SequenceTyped classes argumentFinal
    [⟨.unpack "Holder" [("item", "item")], .give (.variable "h")⟩,
     ⟨.variable "c", .give (.variable "item")⟩] unpackFinal ∧
    unpackFinal.lookup "h" = some none ∧
    unpackFinal.lookup "item" = some (some token.shared) ∧
    unpackFinal.lookup "a" = some (some token.shared) ∧
    unpackFinal.lookup "b" = some (some token.shared) ∧
    unpackFinal.lookup "c" = some (some token.shared) ∧
    (∀ after, ¬ BindingTyped classes [("s", some holder.shared)]
      (.unpack "Holder" [("item", "item")]) holder.shared after) := by
  refine ⟨unpack_typed, by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro after typed
  cases typed with
  | unpack _ _ given => cases given
-- ANCHOR_END: unpacking_shared_fields

end Dada.Shared.Typing.Checks
