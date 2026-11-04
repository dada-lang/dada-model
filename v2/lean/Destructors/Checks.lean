import Destructors.Safety

namespace Dada.Destructors.Checks
open Shared Shared.Typing

def classes : ClassTable :=
  [("Token", ⟨[], .classType⟩), ("Resource", ⟨[], .classType⟩),
   ("Wrapper", ⟨[("resource", ⟨.given, "Resource"⟩)], .classType⟩),
   ("Pair", ⟨[("left", ⟨.given, "Token"⟩), ("right", ⟨.given, "Token"⟩)], .classType⟩),
   ("Again", ⟨[], .classType⟩), ("Point", ⟨[], .structType⟩),
   ("SharedPoint", ⟨[], .sharedStruct⟩)]

def resource : Declaration :=
  ⟨⟨[receiver "Resource" .given], none⟩,
   ⟨[.local ⟨.unpack "Resource" [], .give (.variable "self")⟩], none⟩⟩

def wrapper : Declaration :=
  ⟨⟨[receiver "Wrapper" .given], none⟩,
   ⟨[.local ⟨.unpack "Wrapper" [("resource", "resource")], .give (.variable "self")⟩,
     .dropClass "Resource" (.variable "resource")], none⟩⟩

def again : Declaration :=
  ⟨⟨[receiver "Again" .given], none⟩,
   ⟨[.dropClass "Again" (.variable "self")], none⟩⟩

def finish : Declaration :=
  ⟨⟨[⟨"w", ⟨.given, "Wrapper"⟩⟩], none⟩,
   ⟨[.local ⟨.variable "extra", .new "Resource" []⟩,
     .dropClass "Wrapper" (.variable "w"), .dropClass "Resource" (.variable "extra")], none⟩⟩

def declarations : Declarations :=
  [(.destructor "Resource", resource), (.destructor "Wrapper", wrapper),
   (.destructor "Again", again), (.function "finish", finish)]

theorem resource_body : BodyTyped classes declarations resource.signature resource.body := by
  refine ⟨[("self", none)], [("self", none)], ?_, .none (by decide), ?_⟩
  · apply SequenceTyped.cons (middle := [("self", none)])
    · apply StatementTyped.local
      apply Shared.Typing.StatementTyped.letValue (middle := [("self", none)]) (ty := .whole "Resource")
      · exact .give (by decide) (by decide) (by decide) (by decide)
      · exact .unpack (declaration := ⟨[], .classType⟩) (bindings := [])
          (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
          .nil (by decide)
    · exact .nil (by decide)
  · simp [Finished]

theorem wrapper_body : BodyTyped classes declarations wrapper.signature wrapper.body := by
  refine ⟨[("resource", none), ("self", none)], [("resource", none), ("self", none)], ?_, .none (by decide), ?_⟩
  · apply SequenceTyped.cons (middle := [("resource", some (.whole "Resource")), ("self", none)])
    · apply StatementTyped.local
      apply Shared.Typing.StatementTyped.letValue (middle := [("self", none)]) (ty := .whole "Wrapper")
      · exact .give (by decide) (by decide) (by decide) (by decide)
      · exact .unpack (declaration := ⟨[("resource", ⟨.given, "Resource"⟩)], .classType⟩) (bindings := [("resource", some (.whole "Resource"))])
          (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
          (.cons (by decide) .nil) (by decide)
    · apply SequenceTyped.cons (middle := [("resource", none), ("self", none)])
      · apply StatementTyped.call (declaration := resource) (middle := [("resource", none), ("self", none)])
        · simp [declarations]
        · simp
        · exact .cons (.give (by decide) (by decide) (by decide) (by decide)) (.nil (by decide))
        · exact .none (by decide)
      · exact .nil (by decide)
  · simp [Finished]

theorem again_body : BodyTyped classes declarations again.signature again.body := by
  refine ⟨[("self", none)], [("self", none)], ?_, .none (by decide), ?_⟩
  · apply SequenceTyped.cons (middle := [("self", none)])
    · apply StatementTyped.call (declaration := again) (middle := [("self", none)])
      · simp [declarations]
      · simp
      · exact .cons (.give (by decide) (by decide) (by decide) (by decide)) (.nil (by decide))
      · exact .none (by decide)
    · exact .nil (by decide)
  · simp [Finished]

theorem finish_body : BodyTyped classes declarations finish.signature finish.body := by
  refine ⟨[("extra", none), ("w", none)], [("extra", none), ("w", none)], ?_, .none (by decide), ?_⟩
  · apply SequenceTyped.cons (middle := [("extra", some (.whole "Resource")), ("w", some (.whole "Wrapper"))])
    · apply StatementTyped.local
      apply Shared.Typing.StatementTyped.letValue (middle := [("w", some (.whole "Wrapper"))]) (ty := .whole "Resource")
      · exact .new (declaration := ⟨[], .classType⟩) (by decide) (.nil (by decide)) (by decide) (by decide)
      · exact .variable (by decide) (by decide) (by decide)
    · apply SequenceTyped.cons (middle := [("extra", some (.whole "Resource")), ("w", none)])
      · apply StatementTyped.call (declaration := wrapper) (middle := [("extra", some (.whole "Resource")), ("w", none)])
        · simp [declarations]
        · simp
        · exact .cons (.give (by decide) (by decide) (by decide) (by decide)) (.nil (by decide))
        · exact .none (by decide)
      · apply SequenceTyped.cons (middle := [("extra", none), ("w", none)])
        · apply StatementTyped.call (declaration := resource) (middle := [("extra", none), ("w", none)])
          · simp [declarations]
          · simp
          · exact .cons (.give (by decide) (by decide) (by decide) (by decide)) (.nil (by decide))
          · exact .none (by decide)
        · exact .nil (by decide)
  · simp [Finished]

theorem declarations_typed : DeclarationsTyped classes declarations := by
  constructor
  · decide
  · intro entry member
    simp only [declarations, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals constructor
    · exact ⟨by decide, by decide, by decide, rfl, ⟨⟨[], .classType⟩, by decide, rfl⟩⟩
    · exact resource_body
    · exact ⟨by decide, by decide, by decide, rfl, ⟨⟨[("resource", ⟨.given,"Resource"⟩)], .classType⟩, by decide, rfl⟩⟩
    · exact wrapper_body
    · exact ⟨by decide, by decide, by decide, rfl, ⟨⟨[], .classType⟩, by decide, rfl⟩⟩
    · exact again_body
    · exact ⟨by decide, by decide, by decide, by decide⟩
    · exact finish_body

-- ANCHOR: function_consumes
example : BodyTyped classes declarations finish.signature finish.body := finish_body
-- ANCHOR_END: function_consumes

-- ANCHOR: empty_destructor_rejected
example : ¬ BodyTyped classes declarations resource.signature ⟨[], none⟩ := by
  rintro ⟨middle, final, sequence, result, finished⟩
  cases sequence
  cases result
  have impossible := finished "self" (.whole "Resource") (by simp [resource, Functions.Signature.environment, receiver, FieldType.toType])
  exact (by decide : ¬ StructType classes (.whole "Resource")) impossible
-- ANCHOR_END: empty_destructor_rejected

-- ANCHOR: recursive_destructor
example : BodyTyped classes declarations again.signature again.body := again_body
-- ANCHOR_END: recursive_destructor

-- ANCHOR: finished_obligations
example :
    ¬ Finished classes [("token", some (.whole "Token"))] ∧
    ¬ Finished classes [("other", some (.whole "Token")), ("token", none)] ∧
    Finished classes [("token", none)] ∧
    Finished classes [("p", some (.whole "Point")), ("s", some (.whole "SharedPoint" .shared))] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; exact (by decide : ¬ StructType classes (.whole "Token")) (h "token" _ (by simp))
  · intro h; exact (by decide : ¬ StructType classes (.whole "Token")) (h "other" _ (by simp))
  · simp [Finished]
  · intro name ty member
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, Option.some.injEq] at member
    rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
-- ANCHOR_END: finished_obligations

-- ANCHOR: struct_drop
example :
    StatementTyped classes declarations [("p", some (.whole "Point"))]
      (.dropStruct (.variable "p")) [("p", none)] ∧
    StatementTyped classes declarations [("s", some (.whole "SharedPoint" .shared))]
      (.dropStruct (.variable "s")) [("s", some (.whole "SharedPoint" .shared))] := by
  constructor
  · exact .dropStruct (ty := .whole "Point") (.give (by decide) (by decide) (by decide) (by decide)) (by decide)
  · exact .dropStruct (ty := .whole "SharedPoint" .shared) (.give (by decide) (by decide) (by decide) (by decide)) (by decide)
-- ANCHOR_END: struct_drop

-- ANCHOR: droppable_boundaries
example :
    Droppable classes declarations (.whole "Wrapper") ∧
    ¬ Droppable classes declarations (.whole "Token") ∧
    ¬ Droppable classes declarations ⟨.given, ⟨"Wrapper", [.negative ["resource"]]⟩⟩ ∧
    Droppable classes declarations (.whole "Point") ∧
    Droppable classes declarations (.whole "SharedPoint" .shared) := by decide
-- ANCHOR_END: droppable_boundaries

-- ANCHOR: no_destructor_rejected
example (after : Environment) :
    ¬ StatementTyped classes declarations [("token", some (.whole "Token"))]
      (.dropClass "Token" (.variable "token")) after := by
  intro typed
  have member := drop_requires_declaration typed
  simp [declarations] at member
-- ANCHOR_END: no_destructor_rejected

def partialWrapper : ValueType := ⟨.given, ⟨"Wrapper", [.negative ["resource"]]⟩⟩

-- ANCHOR: partial_drop_rejected
example (after : Environment) :
    ¬ StatementTyped classes declarations [("w", some partialWrapper)]
      (.dropClass "Wrapper" (.variable "w")) after := by
  intro typed
  cases typed with
  | call declared _ args _ =>
    have same := member_value_unique declarations_typed.1 (by simp [declarations] :
      (.destructor "Wrapper", wrapper) ∈ declarations) declared
    cases same
    cases args with
    | cons expression _ =>
      obtain ⟨source, taken, subtype⟩ := give_subtype expression _ rfl
      have operation : Shared.Typing.give classes [("w", some partialWrapper)] (.variable "w") =
          some (partialWrapper, [("w", none)]) := by decide
      rw [operation] at taken
      cases taken
      have positive := subtype.2.2.1 ["resource"] (by decide)
      exact (by unfold Pos; decide : ¬ Pos classes (normalize classes partialWrapper) ["resource"]) positive
-- ANCHOR_END: partial_drop_rejected

def consumePair : Declaration :=
  ⟨⟨[⟨"pair",⟨.given,"Pair"⟩⟩],none⟩,
   ⟨[.local ⟨.unpack "Pair" [("left","left"),("right","right")],.give (.variable "pair")⟩,
     .local ⟨.unpack "Token" [],.give (.variable "left")⟩,
     .local ⟨.unpack "Token" [],.give (.variable "right")⟩],none⟩⟩

def unpackFinish : Declaration :=
  ⟨finish.signature,
   ⟨[.local ⟨.variable "extra",.new "Resource" []⟩,
     .local ⟨.unpack "Wrapper" [("resource","resource")],.give (.variable "w")⟩,
     .local ⟨.unpack "Resource" [],.give (.variable "resource")⟩,
     .local ⟨.unpack "Resource" [],.give (.variable "extra")⟩],none⟩⟩

theorem consumePair_body : BodyTyped classes declarations consumePair.signature consumePair.body := by
  refine ⟨[("left", none), ("right", none), ("pair", none)], [("left", none), ("right", none), ("pair", none)], ?_, .none (by decide), ?_⟩
  · apply SequenceTyped.cons (middle := [("left", some (.whole "Token")), ("right", some (.whole "Token")), ("pair", none)])
    · apply StatementTyped.local
      apply Shared.Typing.StatementTyped.letValue (middle := [("pair", none)]) (ty := .whole "Pair")
      · exact .give (by decide) (by decide) (by decide) (by decide)
      · exact .unpack (declaration := ⟨[("left", ⟨.given, "Token"⟩), ("right", ⟨.given, "Token"⟩)], .classType⟩) (bindings := [("left", some (.whole "Token")), ("right", some (.whole "Token"))])
          (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
          (.cons (by decide) (.cons (by decide) .nil)) (by decide)
    · apply SequenceTyped.cons (middle := [("left", none), ("right", some (.whole "Token")), ("pair", none)])
      · apply StatementTyped.local
        apply Shared.Typing.StatementTyped.letValue (middle := [("left", none), ("right", some (.whole "Token")), ("pair", none)]) (ty := .whole "Token")
        · exact .give (by decide) (by decide) (by decide) (by decide)
        · exact .unpack (declaration := ⟨[], .classType⟩) (bindings := [])
            (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
            .nil (by decide)
      · apply SequenceTyped.cons (middle := [("left", none), ("right", none), ("pair", none)])
        · apply StatementTyped.local
          apply Shared.Typing.StatementTyped.letValue (middle := [("left", none), ("right", none), ("pair", none)]) (ty := .whole "Token")
          · exact .give (by decide) (by decide) (by decide) (by decide)
          · exact .unpack (declaration := ⟨[], .classType⟩) (bindings := [])
              (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
              .nil (by decide)
        · exact .nil (by decide)
  · simp [Finished]

theorem unpackFinish_body : BodyTyped classes declarations unpackFinish.signature unpackFinish.body := by
  refine ⟨[("resource", none), ("extra", none), ("w", none)], [("resource", none), ("extra", none), ("w", none)], ?_, .none (by decide), ?_⟩
  · apply SequenceTyped.cons (middle := [("extra", some (.whole "Resource")), ("w", some (.whole "Wrapper"))])
    · apply StatementTyped.local
      apply Shared.Typing.StatementTyped.letValue (middle := [("w", some (.whole "Wrapper"))]) (ty := .whole "Resource")
      · exact .new (declaration := ⟨[], .classType⟩) (by decide) (.nil (by decide)) (by decide) (by decide)
      · exact .variable (by decide) (by decide) (by decide)
    · apply SequenceTyped.cons (middle := [("resource", some (.whole "Resource")), ("extra", some (.whole "Resource")), ("w", none)])
      · apply StatementTyped.local
        apply Shared.Typing.StatementTyped.letValue (middle := [("extra", some (.whole "Resource")), ("w", none)]) (ty := .whole "Wrapper")
        · exact .give (by decide) (by decide) (by decide) (by decide)
        · exact .unpack (declaration := ⟨[("resource", ⟨.given, "Resource"⟩)], .classType⟩) (bindings := [("resource", some (.whole "Resource"))])
            (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
            (.cons (by decide) .nil) (by decide)
      · apply SequenceTyped.cons (middle := [("resource", none), ("extra", some (.whole "Resource")), ("w", none)])
        · apply StatementTyped.local
          apply Shared.Typing.StatementTyped.letValue (middle := [("resource", none), ("extra", some (.whole "Resource")), ("w", none)]) (ty := .whole "Resource")
          · exact .give (by decide) (by decide) (by decide) (by decide)
          · exact .unpack (declaration := ⟨[], .classType⟩) (bindings := [])
              (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
              .nil (by decide)
        · apply SequenceTyped.cons (middle := [("resource", none), ("extra", none), ("w", none)])
          · apply StatementTyped.local
            apply Shared.Typing.StatementTyped.letValue (middle := [("resource", none), ("extra", none), ("w", none)]) (ty := .whole "Resource")
            · exact .give (by decide) (by decide) (by decide) (by decide)
            · exact .unpack (declaration := ⟨[], .classType⟩) (bindings := [])
                (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
                .nil (by decide)
          · exact .nil (by decide)
  · simp [Finished]

def pairProgram : Program := ⟨classes,declarations,
  .local ⟨.variable "pair",.new "Pair" [.new "Token" [],.new "Token" []]⟩ :: consumePair.body.statements⟩

theorem pair_typed : ProgramTyped pairProgram := by
  obtain ⟨middle,final,sequence,result,finished⟩ := consumePair_body
  cases result with
  | none _ =>
    refine ⟨by decide,declarations_typed,middle,?_,finished⟩
    apply SequenceTyped.cons (middle := [("pair",some (.whole "Pair"))]) _ sequence
    apply StatementTyped.local
    apply Shared.Typing.StatementTyped.letValue (middle := []) (ty := .whole "Pair")
    · apply ExprTyped.new (declaration := ⟨[("left",⟨.given,"Token"⟩),("right",⟨.given,"Token"⟩)],.classType⟩) (by decide)
      · exact .cons (.new (declaration := ⟨[],.classType⟩) (by decide) (.nil (by decide)) (by decide) (by decide))
          (.cons (.new (declaration := ⟨[],.classType⟩) (by decide) (.nil (by decide)) (by decide) (by decide)) (.nil (by decide)))
      · decide
      · decide
    · exact .variable (by decide) (by decide) (by decide)

-- ANCHOR: pair_consumed
example : ProgramTyped pairProgram := pair_typed
-- ANCHOR_END: pair_consumed

-- ANCHOR: function_unpacks
example : BodyTyped classes declarations unpackFinish.signature unpackFinish.body := unpackFinish_body
-- ANCHOR_END: function_unpacks

-- ANCHOR: return_consumes
example : BodyTyped classes declarations
    ⟨[⟨"token",⟨.given,"Token"⟩⟩],some ⟨.given,"Token"⟩⟩
    ⟨[],some (.give (.variable "token"))⟩ := by
  exact ⟨_,[("token",none)],.nil (by decide),
    .some (.give (by decide) (by decide) (by decide) (by decide)), by simp [Finished]⟩
-- ANCHOR_END: return_consumes

end Dada.Destructors.Checks
