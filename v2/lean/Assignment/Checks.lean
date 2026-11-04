import Assignment.Typing
import Destructors.Checks

namespace Dada.Assignment.Checks
open Shared Shared.Typing

def classes : ClassTable := Destructors.Checks.classes ++
  [("Box", ⟨[("point", ⟨.given, "Point"⟩)], .structType⟩)]

def partialWrapper : ValueType := Destructors.Checks.partialWrapper
def wrapper : Context := ⟨[("w", ⟨.given, "Wrapper"⟩)], [("w", some (.whole "Wrapper"))]⟩
def partialContext : Context := wrapper.withCurrent [("w", some partialWrapper)]
def emptyResource : Context := ⟨[("r", ⟨.given, "Resource"⟩)], [("r", none)]⟩

-- ANCHOR: refill
example :
    store classes partialContext (.field (.variable "w") "resource") (.whole "Resource") = some wrapper ∧
    StatementTyped classes [] partialContext
      (.store (.field (.variable "w") "resource") (.new "Resource" [])) wrapper := by
  constructor
  · decide
  · apply StatementTyped.store (middle := partialContext) (ty := .whole "Resource")
    · exact .lift (by decide)
        (.new (declaration := ⟨[], .classType⟩) (by decide) (.nil (by decide)) (by decide) (by decide))
        (by decide)
    · decide
-- ANCHOR_END: refill

-- ANCHOR: class_replacement
example :
    store classes wrapper (.field (.variable "w") "resource") (.whole "Resource") = none ∧
    store classes emptyResource (.variable "r") (.whole "Resource") =
      some (emptyResource.withCurrent [("r", some (.whole "Resource"))]) ∧
    store classes emptyResource (.variable "r") (.whole "Token") = none := by decide
-- ANCHOR_END: class_replacement

def point : Context := ⟨[("p", ⟨.given, "Point"⟩)], [("p", some (.whole "Point"))]⟩
def sharedPoint : Context := ⟨[("s", ⟨.shared, "SharedPoint"⟩)],
  [("s", some (.whole "SharedPoint" .shared))]⟩
def box (permission : Perm) : Context := ⟨[("b", ⟨permission, "Box"⟩)],
  [("b", some (.whole "Box" permission))]⟩

-- ANCHOR: structs
example :
    store classes point (.variable "p") (.whole "Point") = some point ∧
    store classes sharedPoint (.variable "s") (.whole "SharedPoint" .shared) = some sharedPoint ∧
    store classes (box .given) (.field (.variable "b") "point") (.whole "Point") = some (box .given) ∧
    store classes (box .shared) (.field (.variable "b") "point") (.whole "Point" .shared) = none ∧
    store classes point (.variable "p") (.whole "Point" .shared) = none ∧
    layoutKey ⟨.given, "Point"⟩ = layoutKey ⟨.shared, "Point"⟩ := by decide
-- ANCHOR_END: structs

-- ANCHOR: partial_value
example :
    store classes (wrapper.withCurrent [("w", none)]) (.variable "w") partialWrapper = some partialContext ∧
    ¬ Finished classes partialContext ∧
    bindingTypes classes (.unpack "Wrapper" [("resource", "r")]) partialWrapper =
      some [("r", ⟨.given, "Resource"⟩)] := by
  refine ⟨by decide, ?_, by decide⟩
  intro finished
  exact (by decide : ¬ StructType classes partialWrapper)
    (finished "w" partialWrapper (by simp [partialContext, wrapper, Context.withCurrent]))
-- ANCHOR_END: partial_value

-- ANCHOR: rhs_first
example :
    StatementTyped classes [] wrapper (.store (.variable "w") (.give (.variable "w"))) wrapper ∧
    store classes (wrapper.withCurrent [("w", none)])
      (.field (.variable "w") "resource") (.whole "Resource") = none := by
  constructor
  · apply StatementTyped.store (middle := wrapper.withCurrent [("w", none)]) (ty := .whole "Wrapper")
    · exact .lift (by decide) (.give (by decide) (by decide) (by decide) (by decide)) (by decide)
    · decide
  · decide
-- ANCHOR_END: rhs_first

def resourceDestructor : Declaration :=
  ⟨⟨[receiver "Resource" .given], none⟩,
    ⟨[.local ⟨.unpack "Resource" [], .give (.variable "self")⟩], none⟩⟩

def declarations : Declarations := [(.destructor "Resource", resourceDestructor)]

theorem resource_body : BodyTyped classes declarations resourceDestructor.signature resourceDestructor.body := by
  let finalContext : Context := ⟨[("self", ⟨.given, "Resource"⟩)], [("self", none)]⟩
  refine ⟨finalContext, finalContext, ?_, .none (by decide), ?_⟩
  · apply SequenceTyped.cons (middle := finalContext)
    · apply StatementTyped.local
      apply LocalTyped.letValue (middle := finalContext) (ty := .whole "Resource")
      · exact .lift (by decide) (.give (by decide) (by decide) (by decide) (by decide)) (by decide)
      · apply BindingTyped.lift (fixed := []) (by decide) _ (by decide) (by decide)
        exact .unpack (declaration := ⟨[], .classType⟩) (bindings := [])
          (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) .nil (by decide)
    · exact .nil (by decide)
  · simp [Finished, Destructors.Finished, finalContext]

def replacementBefore : Context :=
  ⟨[("r", ⟨.given, "Resource"⟩), ("replacement", ⟨.given, "Resource"⟩)],
    [("r", some (.whole "Resource")), ("replacement", some (.whole "Resource"))]⟩
def replacementMiddle : Context := replacementBefore.withCurrent
  [("r", none), ("replacement", some (.whole "Resource"))]
def replacementAfter : Context := replacementBefore.withCurrent
  [("r", some (.whole "Resource")), ("replacement", none)]

-- ANCHOR: explicit_replacement
example :
    DeclarationsTyped classes declarations ∧
    SequenceTyped classes declarations replacementBefore
      [.dropClass "Resource" (.variable "r"), .store (.variable "r") (.give (.variable "replacement"))]
      replacementAfter := by
  constructor
  · refine ⟨by decide, ?_⟩
    intro entry member
    have eq : entry = (.destructor "Resource", resourceDestructor) := by simpa [declarations] using member
    cases eq
    exact ⟨⟨by decide, by decide, by decide, rfl, ⟨⟨[], .classType⟩, by decide, rfl⟩⟩, resource_body⟩
  · apply SequenceTyped.cons (middle := replacementMiddle)
    · apply StatementTyped.call (declaration := resourceDestructor) (middle := replacementMiddle)
      · simp [declarations]
      · simp
      · exact .lift (by decide)
          (.cons (.give (by decide) (by decide) (by decide) (by decide)) (.nil (by decide))) (by decide)
      · exact .none (by decide)
    · apply SequenceTyped.cons (middle := replacementAfter)
      · apply StatementTyped.store
          (middle := replacementBefore.withCurrent [("r", none), ("replacement", none)])
          (ty := .whole "Resource")
        · exact .lift (by decide) (.give (by decide) (by decide) (by decide) (by decide)) (by decide)
        · decide
      · exact .nil (by decide)
-- ANCHOR_END: explicit_replacement

end Dada.Assignment.Checks
