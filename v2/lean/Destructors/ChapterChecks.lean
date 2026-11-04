import Destructors.ExecutionChecks

namespace Dada.Destructors.Checks
open Shared Shared.Typing

-- ANCHOR: consumption
example : ProgramTyped pairProgram ∧
    ¬ Finished classes [("right",some (.whole "Token")),("left",none),("pair",none)] ∧
    ¬ Finished classes [("other",some (.whole "Token")),("right",none),("left",none),("pair",none)] ∧
    ¬ Droppable classes declarations (.whole "Token") := by
  refine ⟨pair_typed, ?_, ?_, by decide⟩
  · intro h; exact (by decide : ¬ StructType classes (.whole "Token")) (h "right" _ (by simp))
  · intro h; exact (by decide : ¬ StructType classes (.whole "Token")) (h "other" _ (by simp))
-- ANCHOR_END: consumption

-- ANCHOR: function_bodies
example : BodyTyped classes declarations finish.signature finish.body ∧
    BodyTyped classes declarations unpackFinish.signature unpackFinish.body ∧
    BodyTyped classes declarations ⟨[⟨"token",⟨.given,"Token"⟩⟩],some ⟨.given,"Token"⟩⟩
      ⟨[],some (.give (.variable "token"))⟩ := by
  refine ⟨finish_body,unpackFinish_body,[("token",some (.whole "Token"))],[("token",none)],.nil (by decide),?_,by simp [Finished]⟩
  exact .some (.give (by decide) (by decide) (by decide) (by decide))
-- ANCHOR_END: function_bodies

-- ANCHOR: boundaries
example :
    ¬ BodyTyped classes declarations resource.signature ⟨[],none⟩ ∧
    ProgramTyped recursionProgram ∧
    (∀ depth, Steps classes.erase declarations (.initial recursionProgram) (recursionState depth)) ∧
    (∀ depth, Step classes.erase declarations (recursionState depth) (recursionState (depth + 1))) ∧
    (∀ depth, ¬ (recursionState depth).finished) ∧
    ¬ Droppable classes declarations (.whole "Token") ∧
    ¬ Droppable classes declarations partialWrapper := by
  refine ⟨?_,recursion_typed,recursion_reachable,recursive_step,?_,by decide,by decide⟩
  · rintro ⟨middle,final,sequence,result,finished⟩
    cases sequence
    cases result
    have impossible := finished "self" (.whole "Resource")
      (by simp [resource,Functions.Signature.environment,receiver,FieldType.toType])
    exact (by decide : ¬ StructType classes (.whole "Resource")) impossible
  · intro depth; simp [recursionState,Configuration.finished,Configuration.running]
-- ANCHOR_END: boundaries

end Dada.Destructors.Checks
