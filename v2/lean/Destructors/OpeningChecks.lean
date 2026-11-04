import Destructors.BoundaryChecks
import Destructors.ExecutionChecks

namespace Dada.Destructors.Checks
open Shared Shared.Typing

def returningResource : Declaration :=
  ⟨⟨[⟨"token",⟨.given,"Resource"⟩⟩],some ⟨.given,"Resource"⟩⟩,
   ⟨[],some (.give (.variable "token"))⟩⟩

def returningTable : Declarations :=
  [(.function "identity",returningResource),(.destructor "Resource",resource)]

def returningProgram : Program := ⟨classes,returningTable,
  [.local ⟨.variable "original",.new "Resource" []⟩,
   .call (some "returned") (.function "identity") [.give (.variable "original")],
   .dropClass "Resource" (.variable "returned")]⟩

-- ANCHOR: ownership_return
example : ProgramTyped returningProgram ∧
    ¬ Finished classes [("returned",some (.whole "Resource")),("original",none)] := by
  constructor
  · refine ⟨by decide, ?_, [("returned",none),("original",none)], ?_, by simp [Finished]⟩
    · constructor
      · decide
      · intro entry member
        simp only [returningProgram,returningTable,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl
        · refine ⟨⟨by decide,by decide,by decide,by decide⟩, ?_⟩
          exact ⟨_,[("token",none)],.nil (by decide),
            .some (.give (by decide) (by decide) (by decide) (by decide)),by simp [Finished]⟩
        · refine ⟨⟨by decide,by decide,by decide,rfl,⟨⟨[],.classType⟩,by decide,rfl⟩⟩,?_,?_,?_,?_,?_⟩
          · exact [("self",none)]
          · exact [("self",none)]
          · apply SequenceTyped.cons
            · apply StatementTyped.local
              apply Shared.Typing.StatementTyped.letValue (middle := [("self",none)]) (ty := .whole "Resource")
              · exact .give (by decide) (by decide) (by decide) (by decide)
              · exact .unpack (declaration := ⟨[],.classType⟩) (bindings := [])
                  (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) .nil (by decide)
            · exact .nil (by decide)
          · exact .none (by decide)
          · simp [Finished]
    · apply SequenceTyped.cons (middle := [("original",some (.whole "Resource"))])
      · apply StatementTyped.local
        apply Shared.Typing.StatementTyped.letValue (middle := []) (ty := .whole "Resource")
        · exact .new (declaration := ⟨[],.classType⟩) (by decide) (.nil (by decide)) (by decide) (by decide)
        · exact .variable (by decide) (by decide) (by decide)
      · apply SequenceTyped.cons (middle := [("returned",some (.whole "Resource")),("original",none)])
        · exact .call (declaration := returningResource) (middle := [("original",none)])
            (by simp [returningProgram,returningTable]) (by decide)
            (.cons (.give (by decide) (by decide) (by decide) (by decide)) (.nil (by decide)))
            (.some (.variable (by decide) (by decide) (by decide)))
        · apply SequenceTyped.cons
          · exact .call (declaration := resource) (middle := [("returned",none),("original",none)])
              (by simp [returningProgram,returningTable]) (by simp)
              (.cons (.give (by decide) (by decide) (by decide) (by decide)) (.nil (by decide)))
              (.none (by decide))
          · exact .nil (by decide)
  · intro h
    exact (by decide : ¬ StructType classes (.whole "Resource")) (h "returned" _ (by simp))
-- ANCHOR_END: ownership_return

def structProgram : Program := ⟨classes,[],
  [.local ⟨.variable "p",.new "Point" []⟩,
   .local ⟨.variable "s",.new "SharedPoint" []⟩,
   .dropStruct (.variable "p"), .dropStruct (.variable "s")]⟩
def structFinal : Environment := [("s",some (.whole "SharedPoint" .shared)),("p",none)]

-- ANCHOR: struct_program
example : SequenceTyped classes [] [] structProgram.main structFinal ∧
    Finished classes structFinal ∧
    (∀ ty after, ¬ ExprTyped classes structFinal (.give (.variable "p")) ty after) ∧
    ExprTyped classes structFinal (.give (.variable "s")) (.whole "SharedPoint" .shared) structFinal := by
  refine ⟨?_,?_,?_,.give (by decide) (by decide) (by decide) (by decide)⟩
  · apply SequenceTyped.cons (middle := [("p",some (.whole "Point"))])
    · apply StatementTyped.local
      apply Shared.Typing.StatementTyped.letValue (middle := []) (ty := .whole "Point")
      · exact .new (declaration := ⟨[],.structType⟩) (by decide) (.nil (by decide)) (by decide) (by decide)
      · exact .variable (by decide) (by decide) (by decide)
    · apply SequenceTyped.cons (middle := [("s",some (.whole "SharedPoint" .shared)),("p",some (.whole "Point"))])
      · apply StatementTyped.local
        apply Shared.Typing.StatementTyped.letValue (middle := [("p",some (.whole "Point"))]) (ty := .whole "SharedPoint" .shared)
        · exact .new (declaration := ⟨[],.sharedStruct⟩) (by decide) (.nil (by decide)) (by decide) (by decide)
        · exact .variable (by decide) (by decide) (by decide)
      · exact .cons (middle := structFinal) (.dropStruct (ty := .whole "Point") (.give (by decide) (by decide) (by decide) (by decide)) (by decide))
          (.cons (.dropStruct (ty := .whole "SharedPoint" .shared) (.give (by decide) (by decide) (by decide) (by decide)) (by decide)) (.nil (by decide)))
  · intro name ty member
    have eq : name = "s" ∧ ty = .whole "SharedPoint" .shared := by simpa [structFinal] using member
    rcases eq with ⟨rfl,rfl⟩
    decide
  · intro ty after
    exact failed_give_not_typed (by decide)
-- ANCHOR_END: struct_program

def parcelClasses : ClassTable :=
  ("Parcel",⟨[("point",⟨.shared,"SharedPoint"⟩)],.classType⟩) :: classes

def parcel : Declaration :=
  ⟨⟨[receiver "Parcel" .given],none⟩,
   ⟨[.local ⟨.unpack "Parcel" [("point","point")],.give (.variable "self")⟩],none⟩⟩

-- ANCHOR: struct_field
example : parcelClasses.WellFormed ∧
    Signature.WellFormed parcelClasses (.destructor "Parcel") parcel.signature ∧
    BodyTyped parcelClasses [(.destructor "Parcel",parcel)] parcel.signature parcel.body := by
  refine ⟨by decide,⟨by decide,by decide,by decide,rfl,⟨⟨[("point",⟨.shared,"SharedPoint"⟩)],.classType⟩,by decide,rfl⟩⟩,?_,?_,?_,?_,?_⟩
  · exact [("point",some (.whole "SharedPoint" .shared)),("self",none)]
  · exact [("point",some (.whole "SharedPoint" .shared)),("self",none)]
  · apply SequenceTyped.cons
    · apply StatementTyped.local
      apply Shared.Typing.StatementTyped.letValue (middle := [("self",none)]) (ty := .whole "Parcel")
      · exact .give (by decide) (by decide) (by decide) (by decide)
      · exact .unpack (declaration := ⟨[("point",⟨.shared,"SharedPoint"⟩)],.classType⟩)
          (bindings := [("point",some (.whole "SharedPoint" .shared))])
          (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
          (.cons (by decide) .nil) (by decide)
    · exact .nil (by decide)
  · exact .none (by decide)
  · intro name ty member
    have eq : name = "point" ∧ ty = .whole "SharedPoint" .shared := by simpa using member
    rcases eq with ⟨rfl,rfl⟩
    decide
-- ANCHOR_END: struct_field

def consumePartial : Declaration :=
  ⟨⟨[⟨"w",⟨.given,"Wrapper"⟩⟩],none⟩,
   ⟨[.local ⟨.variable "taken",.give (.field (.variable "w") "resource")⟩,
     .local ⟨.unpack "Wrapper" [("resource","resource")],.give (.variable "w")⟩,
     .dropClass "Resource" (.variable "taken")],none⟩⟩

-- ANCHOR: partial_cleanup
example : BodyTyped classes declarations consumePartial.signature consumePartial.body ∧
    Shared.Typing.give classes [("w",some (.whole "Wrapper"))] (.field (.variable "w") "resource") =
      some (.whole "Resource",[("w",some partialWrapper)]) ∧
    ¬ Droppable classes declarations partialWrapper := by
  refine ⟨?_,by decide,by decide⟩
  refine ⟨[("resource",none),("taken",none),("w",none)],
    [("resource",none),("taken",none),("w",none)],?_,.none (by decide),by simp [Finished]⟩
  apply SequenceTyped.cons (middle := [("taken",some (.whole "Resource")),("w",some partialWrapper)])
  · apply StatementTyped.local
    apply Shared.Typing.StatementTyped.letValue (middle := [("w",some partialWrapper)]) (ty := .whole "Resource")
    · exact .give (by decide) (by decide) (by decide) (by decide)
    · exact .variable (by decide) (by decide) (by decide)
  · apply SequenceTyped.cons (middle := [("resource",none),("taken",some (.whole "Resource")),("w",none)])
    · apply StatementTyped.local
      apply Shared.Typing.StatementTyped.letValue (middle := [("taken",some (.whole "Resource")),("w",none)]) (ty := partialWrapper)
      · exact .give (by decide) (by decide) (by decide) (by decide)
      · exact .unpack (declaration := ⟨[("resource",⟨.given,"Resource"⟩)],.classType⟩)
          (bindings := [("resource",none)])
          (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
          (.cons (by decide) .nil) (by decide)
    · apply SequenceTyped.cons
      · exact .call (declaration := resource) (middle := [("resource",none),("taken",none),("w",none)])
          (by simp [declarations]) (by simp)
          (.cons (.give (by decide) (by decide) (by decide) (by decide)) (.nil (by decide))) (.none (by decide))
      · exact .nil (by decide)
-- ANCHOR_END: partial_cleanup

def finishProgram : Program := ⟨classes,declarations,
  [.local ⟨.variable "w",.new "Wrapper" [.new "Resource" []]⟩,
   .call none (.function "finish") [.give (.variable "w")]]⟩

-- ANCHOR: function_call
example : BodyTyped classes declarations finish.signature finish.body ∧
    BodyTyped classes declarations unpackFinish.signature unpackFinish.body ∧
    ProgramTyped finishProgram := by
  refine ⟨finish_body,unpackFinish_body,by decide,declarations_typed,[("w",none)],?_,by simp [Finished]⟩
  apply SequenceTyped.cons (middle := [("w",some (.whole "Wrapper"))])
  · apply StatementTyped.local
    apply Shared.Typing.StatementTyped.letValue (middle := []) (ty := .whole "Wrapper")
    · apply ExprTyped.new (declaration := ⟨[("resource",⟨.given,"Resource"⟩)],.classType⟩) (by decide)
      · exact .cons (.new (declaration := ⟨[],.classType⟩) (by decide) (.nil (by decide)) (by decide) (by decide)) (.nil (by decide))
      · decide
      · decide
    · exact .variable (by decide) (by decide) (by decide)
  · apply SequenceTyped.cons
    · exact .call (declaration := finish) (middle := [("w",none)])
        (by simp [finishProgram,declarations]) (by simp)
        (.cons (.give (by decide) (by decide) (by decide) (by decide)) (.nil (by decide))) (.none (by decide))
    · exact .nil (by decide)
-- ANCHOR_END: function_call

end Dada.Destructors.Checks
