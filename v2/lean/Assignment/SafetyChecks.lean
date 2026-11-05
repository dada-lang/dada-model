import Assignment.Safety
import Assignment.ExecutionChecks

namespace Dada.Assignment.Checks
open Shared Shared.Typing

theorem declarations_typed : DeclarationsTyped classes declarations := by
  refine ⟨by decide, ?_⟩
  intro entry member
  have same : entry = (.destructor "Resource", resourceDestructor) := by simpa [declarations] using member
  cases same
  exact ⟨⟨by decide, by decide, by decide, rfl, ⟨⟨[], .classType⟩, by decide, rfl⟩⟩, resource_body⟩

def refillProgram : Program :=
  ⟨classes, declarations,
    [.local ⟨.variable "w", .new "Wrapper" [.new "Resource" []]⟩,
     .dropClass "Resource" (.field (.variable "w") "resource"),
     .store (.field (.variable "w") "resource") (.new "Resource" []),
     .local ⟨.unpack "Wrapper" [("resource", "r")], .give (.variable "w")⟩,
     .dropClass "Resource" (.variable "r")]⟩

def unpackedWrapper : Context :=
  ⟨[("r", ⟨.given, "Resource"⟩), ("w", ⟨.given, "Wrapper"⟩)],
    [("r", some (.whole "Resource")), ("w", none)]⟩

def consumedWrapper : Context := unpackedWrapper.withCurrent [("r", none), ("w", none)]

-- The same caller frame survives a destructor call, refills its empty field,
-- and consumes the reconstructed owner before the initial frame exits.
theorem refill_typed : ProgramTyped refillProgram := by
  refine ⟨by decide, declarations_typed, consumedWrapper, ?_, ?_⟩
  · apply SequenceTyped.cons (middle := wrapper)
    · apply StatementTyped.local
      apply LocalTyped.letValue (middle := Context.empty) (ty := .whole "Wrapper")
      · apply ExprTyped.lift (by decide) _ (by decide)
        exact .new (declaration := ⟨[("resource", ⟨.given, "Resource"⟩)], .classType⟩)
          (by decide)
          (.cons (.new (declaration := ⟨[], .classType⟩) (by decide)
            (.nil (by decide)) (by decide) (by decide)) (.nil (by decide)))
          (by decide) (by decide)
      · apply BindingTyped.lift (fixed := [("w", ⟨.given, "Wrapper"⟩)])
          (by decide) _ (by decide) (by decide)
        exact .variable (by decide) (by decide) (by decide)
    · apply SequenceTyped.cons (middle := partialContext)
      · apply StatementTyped.call (declaration := resourceDestructor) (middle := partialContext)
        · simp [refillProgram, declarations]
        · simp
        · exact .lift (by decide)
            (.cons (.give (by decide) (by decide) (by decide) (by decide)) (.nil (by decide)))
            (by decide)
        · exact .none (by decide)
      · apply SequenceTyped.cons (middle := wrapper)
        · apply StatementTyped.store (middle := partialContext) (ty := .whole "Resource")
          · exact .lift (by decide)
              (.new (declaration := ⟨[], .classType⟩) (by decide) (.nil (by decide))
                (by decide) (by decide)) (by decide)
          · decide
        · apply SequenceTyped.cons (middle := unpackedWrapper)
          · apply StatementTyped.local
            apply LocalTyped.letValue (middle := wrapper.withCurrent [("w", none)])
              (ty := .whole "Wrapper")
            · exact .lift (by decide) (.give (by decide) (by decide) (by decide) (by decide)) (by decide)
            · apply BindingTyped.lift (fixed := [("r", ⟨.given, "Resource"⟩)])
                (by decide) _ (by decide) (by decide)
              exact .unpack (declaration := ⟨[("resource", ⟨.given, "Resource"⟩)], .classType⟩)
                (bindings := [("r", some (.whole "Resource"))])
                (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
                (.cons (by decide) .nil) (by decide)
          · apply SequenceTyped.cons (middle := consumedWrapper)
            · apply StatementTyped.call (declaration := resourceDestructor) (middle := consumedWrapper)
              · simp [refillProgram, declarations]
              · simp
              · exact .lift (by decide)
                  (.cons (.give (by decide) (by decide) (by decide) (by decide)) (.nil (by decide)))
                  (by decide)
              · exact .none (by decide)
            · exact .nil (by decide)
  · simp [Finished, Destructors.Finished, consumedWrapper, unpackedWrapper, Context.withCurrent]

def overwriteProgram : Program :=
  ⟨classes, [],
    [.local ⟨.variable "s", .new "SharedPoint" []⟩,
     .store (.variable "s") (.new "SharedPoint" [])]⟩

theorem overwrite_typed : ProgramTyped overwriteProgram := by
  refine ⟨by decide, ⟨by decide, by simp [overwriteProgram]⟩, sharedPoint, ?_, ?_⟩
  · apply SequenceTyped.cons (middle := sharedPoint)
    · apply StatementTyped.local
      apply LocalTyped.letValue (middle := Context.empty) (ty := .whole "SharedPoint" .shared)
      · exact .lift (by decide)
          (.new (declaration := ⟨[], .sharedStruct⟩) (by decide) (.nil (by decide))
            (by decide) (by decide)) (by decide)
      · apply BindingTyped.lift (fixed := [("s", ⟨.shared, "SharedPoint"⟩)])
          (by decide) _ (by decide) (by decide)
        exact .variable (by decide) (by decide) (by decide)
    · apply SequenceTyped.cons (middle := sharedPoint)
      · apply StatementTyped.store (middle := sharedPoint) (ty := .whole "SharedPoint" .shared)
        · exact .lift (by decide)
            (.new (declaration := ⟨[], .sharedStruct⟩) (by decide) (.nil (by decide))
              (by decide) (by decide)) (by decide)
        · decide
      · exact .nil (by decide)
  · intro name ty member
    have same : (name, some ty) = ("s", some (.whole "SharedPoint" .shared)) := by
      simpa [sharedPoint] using member
    cases same
    decide

-- ANCHOR: refill_safety
example : ProgramTyped refillProgram ∧
    ∀ configuration,
      Steps classes.erase declarations (.initial refillProgram) configuration →
      ConfigurationTyped classes declarations configuration ∧
      ¬ Stuck classes.erase declarations configuration ∧
      (configuration.finished → configuration.objects = []) := by
  refine ⟨refill_typed, ?_⟩
  intro configuration trace
  have safe := program_safety refill_typed trace
  exact ⟨safe.1, safe.2.2, safe.1.finished_heap_empty⟩
-- ANCHOR_END: refill_safety

-- ANCHOR: overwrite_safety
example : ProgramTyped overwriteProgram ∧
    ∀ configuration,
      Steps classes.erase [] (.initial overwriteProgram) configuration →
      ConfigurationTyped classes [] configuration ∧
      ¬ Stuck classes.erase [] configuration ∧
      (configuration.finished → configuration.objects = []) := by
  refine ⟨overwrite_typed, ?_⟩
  intro configuration trace
  have safe := program_safety overwrite_typed trace
  exact ⟨safe.1, safe.2.2, safe.1.finished_heap_empty⟩
-- ANCHOR_END: overwrite_safety

end Dada.Assignment.Checks
