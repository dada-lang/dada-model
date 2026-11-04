import Functions.Typing
import Correspondence.SharedFunctions

namespace Dada.Functions.Checks

open Shared Shared.Typing

def classes : ClassTable :=
  [("Token", ⟨[], .classType⟩), ("Point", ⟨[], .structType⟩),
   ("Box", ⟨[("child", ⟨.given, "Token"⟩)], .classType⟩),
   ("Pair", ⟨[("left", ⟨.given, "Token"⟩), ("right", ⟨.given, "Token"⟩)], .classType⟩)]

def ownedToken : FieldType := ⟨.given, "Token"⟩
def ownedPoint : FieldType := ⟨.given, "Point"⟩
def sharedPoint : FieldType := ⟨.shared, "Point"⟩

def identity : Declaration :=
  ⟨⟨[⟨"token", ownedToken⟩], some ownedToken⟩, ⟨[], some (.give (.variable "token"))⟩⟩

def copy : Declaration :=
  ⟨⟨[⟨"point", sharedPoint⟩], some sharedPoint⟩, ⟨[], some (.give (.variable "point"))⟩⟩

def takeMethod : Declaration :=
  ⟨⟨[receiver "Point" .given], some ownedPoint⟩, ⟨[], some (.give (.variable "self"))⟩⟩

def copyMethod : Declaration :=
  ⟨⟨[receiver "Point" .shared], some sharedPoint⟩, ⟨[], some (.give (.variable "self"))⟩⟩

def leave : Declaration := ⟨⟨[⟨"token", ownedToken⟩], none⟩, ⟨[], none⟩⟩

def consume : Declaration :=
  ⟨leave.signature, ⟨[.local ⟨.unpack "Token" [], .give (.variable "token")⟩], none⟩⟩

def declarations : Declarations :=
  [(.function "identity", identity), (.function "copy", copy),
   (.method "Point" "take", takeMethod), (.method "Point" "copy", copyMethod),
   (.function "leave", leave), (.function "consume", consume)]

private theorem token_give : ExprTyped classes [("token", some ownedToken.toType)]
    (.give (.variable "token")) ownedToken.toType [("token", none)] :=
  .give (by decide) (by decide) (by decide) (by decide)

private theorem point_copy : ExprTyped classes [("point", some sharedPoint.toType)]
    (.give (.variable "point")) sharedPoint.toType [("point", some sharedPoint.toType)] :=
  .give (by decide) (by decide) (by decide) (by decide)

private theorem identity_body : BodyTyped classes declarations identity.signature identity.body :=
  ⟨_, _, .nil (by decide), .some token_give⟩

private theorem copy_body : BodyTyped classes declarations copy.signature copy.body :=
  ⟨_, _, .nil (by decide), .some point_copy⟩

private theorem take_body : BodyTyped classes declarations takeMethod.signature takeMethod.body :=
  ⟨_, [("self", none)], .nil (by decide),
    .some (.give (by decide) (by decide) (by decide) (by decide))⟩

private theorem copy_method_body : BodyTyped classes declarations copyMethod.signature copyMethod.body :=
  ⟨_, takeMethod.signature.environment.map (fun (n, _) => (n, some sharedPoint.toType)),
    .nil (by decide), .some (.give (by decide) (by decide) (by decide) (by decide))⟩

private theorem leave_body : BodyTyped classes declarations leave.signature leave.body :=
  ⟨_, _, .nil (by decide), .none (by decide)⟩

private theorem consume_statement : Shared.Typing.StatementTyped classes leave.signature.environment
    ⟨.unpack "Token" [], .give (.variable "token")⟩ [("token", none)] := by
  apply Shared.Typing.StatementTyped.letValue token_give
  exact .unpack (declaration := ⟨[], .classType⟩) (bindings := [])
    (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
    .nil (by decide)

private theorem consume_body : BodyTyped classes declarations consume.signature consume.body :=
  ⟨_, _, .cons (.local consume_statement) (.nil (by decide)), .none (by decide)⟩

theorem declarations_typed : DeclarationsTyped classes declarations := by
  constructor
  · decide
  · intro entry member
    simp only [declarations, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, identity_body⟩
    · exact ⟨by decide, copy_body⟩
    · exact ⟨by decide, take_body⟩
    · exact ⟨by decide, copy_method_body⟩
    · exact ⟨by decide, leave_body⟩
    · exact ⟨by decide, consume_body⟩

def identityCode : List Statement :=
  [.local ⟨.variable "original", .new "Token" []⟩,
   .call (some "result") (.function "identity") [.give (.variable "original")]]

def identityProgram : Program := ⟨classes, declarations, identityCode⟩

def identityReturned : Configuration :=
  (.running ⟨[(0, ⟨"Token", []⟩)], [("result", some (.owned 0)), ("original", none)], 1⟩ ⟨[], none⟩)

private theorem identity_main : SequenceTyped classes declarations [] identityCode
    [("result", some ownedToken.toType), ("original", none)] := by
  apply SequenceTyped.cons (middle := [("original", some ownedToken.toType)])
  · apply StatementTyped.local
    apply Shared.Typing.StatementTyped.letValue (middle := []) (ty := ownedToken.toType)
    · exact .new (declaration := ⟨[], .classType⟩) (by decide) (.nil (by decide))
        (by decide) (by decide)
    · exact .variable (by decide) (by decide) (by decide)
  · apply SequenceTyped.cons
    · apply StatementTyped.call (declaration := identity) (middle := [("original", none)])
      · simp [declarations]
      · decide
      · exact .cons (.give (by decide) (by decide) (by decide) (by decide)) (.nil (by decide))
      · exact .some (.variable (by decide) (by decide) (by decide))
    · exact .nil (by decide)

private theorem new_token (variables : Store) :
    Eval classes.erase ⟨[], variables, 0⟩ (.new "Token" [])
      ⟨[(0, ⟨"Token", []⟩)], variables, 1⟩ (.owned 0) :=
  .new (declaration := ⟨[], .classType⟩) (references := []) (by decide) (.nil _)
    rfl (by simp) (by simp [StructArguments, Kind.isStruct])

private theorem move_head (objects : List (ObjectId × Object)) (nextId : Nat)
    (name : String) (object : ObjectId) (rest : Store) :
    Eval classes.erase ⟨objects, (name, some (.owned object)) :: rest, nextId⟩
      (.give (.variable name)) ⟨objects, (name, none) :: rest, nextId⟩ (.owned object) :=
  .give (.move (source := .variable name) (.variable (reference := .owned object) (by simp)) (.variable objects nextId [] rest name object))

private theorem copy_head (objects : List (ObjectId × Object)) (nextId : Nat)
    (name : String) (object : ObjectId) (rest : Store) :
    Eval classes.erase ⟨objects, (name, some (.shared object)) :: rest, nextId⟩
      (.give (.variable name)) ⟨objects, (name, some (.shared object)) :: rest, nextId⟩ (.shared object) :=
  .give (.copy (source := .variable name) (.variable (reference := .shared object) (by simp)) (by simp [Stored]))

private theorem leaf_live (id : ObjectId) (className : String) (variables : Store)
    (nextId : Nat) (object : ObjectId) :
    Live ⟨[(id, ⟨className, []⟩)], variables, nextId⟩ object ↔
      ∃ name reference, (name, some reference) ∈ variables ∧ reference.object = object := by
  constructor
  · intro live
    cases live with
    | «variable» member => exact ⟨_, _, member, rfl⟩
    | field _ stored field =>
      simp only [List.mem_singleton, Prod.mk.injEq] at stored
      rcases stored with ⟨_, rfl⟩
      simp at field
  · rintro ⟨name, reference, member, rfl⟩
    exact .variable member

private theorem collected_step {table : Classes} {functions : Declarations}
    (raw : RawStep table functions before middle)
    (collected : middle.collect = after) : Step table functions before after :=
  collected ▸ Step.collect raw

private theorem checked_step {table : Classes} {functions : Declarations}
    (raw : RawStep table functions before after)
    (collected : after.collect = after) : Step table functions before after :=
  collected_step raw collected

macro "gc" : tactic => `(tactic|
  simp +instances [Configuration.collect, State.collect, Configuration.rootState, Configuration.running,
    leaf_live, parameterStore, identity, copy, takeMethod, copyMethod, leave, receiver,
    Reference.owned, Reference.shared, State.bind, List.flatMap, Frame.variables,
    Parameter.name, List.map, List.flatten, and_assoc, exists_or, or_and_right] <;> rfl)

theorem identity_execution : Steps classes.erase declarations
    (.initial identityProgram) identityReturned := by
  apply Steps.step (middle := (.running ⟨[(0, ⟨"Token", []⟩)], [("original", some (.owned 0))], 1⟩ ⟨identityCode.tail, none⟩))
  · exact checked_step (.local (.letValue (new_token []) (.variable (by simp)))) (by gc)
  · apply Steps.step
    · exact checked_step (RawStep.call (declaration := identity) (by simp [declarations]) rfl (by decide)
        (.cons (move_head _ _ _ _ []) (.nil _)) rfl) (by gc)
    · apply Steps.step
      · exact checked_step (RawStep.return (.some (move_head _ _ "token" _ [])) (.some (by decide))) (by gc)
      · exact .refl _

-- ANCHOR: identity
example : ProgramTyped identityProgram ∧
    Steps classes.erase declarations (.initial identityProgram) identityReturned ∧
    Step classes.erase declarations identityReturned ⟨[], 1, []⟩ ∧
    ("original", none) ∈ identityReturned.rootState.variables ∧
    ("result", some (.owned 0)) ∈ identityReturned.rootState.variables :=
  ⟨⟨by decide, declarations_typed, _, identity_main⟩, identity_execution,
    by exact collected_step .exit (by simp), by decide, by decide⟩
-- ANCHOR_END: identity

def sharedCode : List Statement :=
  [.local ⟨.variable "p", .new "Point" []⟩,
   .local ⟨.variable "s", .giveShare (.variable "p")⟩,
   .call (some "t") (.function "copy") [.give (.variable "s")]]

def sharedProgram : Program := ⟨classes, declarations, sharedCode⟩

def sharedReturned : Configuration :=
  (.running ⟨[(0, ⟨"Point", []⟩)], [("t", some (.shared 0)), ("s", some (.shared 0)), ("p", none)], 1⟩ ⟨[], none⟩)

private theorem new_point (variables : Store) :
    Eval classes.erase ⟨[], variables, 0⟩ (.new "Point" [])
      ⟨[(0, ⟨"Point", []⟩)], variables, 1⟩ (.owned 0) :=
  .new (declaration := ⟨[], .structType⟩) (references := []) (by decide) (.nil _)
    rfl (by simp) (by simp [StructArguments])

private theorem shared_main : SequenceTyped classes declarations [] sharedCode
    [("t", some sharedPoint.toType), ("s", some sharedPoint.toType), ("p", none)] := by
  apply SequenceTyped.cons (middle := [("p", some ownedPoint.toType)])
  · apply StatementTyped.local
    apply Shared.Typing.StatementTyped.letValue (middle := []) (ty := ownedPoint.toType)
    · exact .new (declaration := ⟨[], .structType⟩) (by decide) (.nil (by decide))
        (by decide) (by decide)
    · exact .variable (by decide) (by decide) (by decide)
  · apply SequenceTyped.cons (middle := [("s", some sharedPoint.toType), ("p", none)])
    · apply StatementTyped.local
      apply Shared.Typing.StatementTyped.letValue (middle := [("p", none)])
        (ty := sharedPoint.toType)
      · exact .giveShare (ty := ownedPoint.toType) (by decide) (by decide) (by decide)
          (by decide) (by decide)
      · exact .variable (by decide) (by decide) (by decide)
    · apply SequenceTyped.cons
      · apply StatementTyped.call (declaration := copy)
          (middle := [("s", some sharedPoint.toType), ("p", none)])
        · simp [declarations]
        · decide
        · exact .cons (.give (by decide) (by decide) (by decide) (by decide)) (.nil (by decide))
        · exact .some (.variable (by decide) (by decide) (by decide))
      · exact .nil (by decide)

theorem shared_execution : Steps classes.erase declarations
    (.initial sharedProgram) sharedReturned := by
  apply Steps.step (middle := (.running ⟨[(0, ⟨"Point", []⟩)], [("p", some (.owned 0))], 1⟩ ⟨sharedCode.tail, none⟩))
  · exact checked_step (.local (.letValue (new_point []) (.variable (by simp)))) (by gc)
  · apply Steps.step (middle := (.running ⟨[(0, ⟨"Point", []⟩)],
      [("s", some (.shared 0)), ("p", none)], 1⟩ ⟨sharedCode.drop 2, none⟩))
    · apply checked_step
      · apply RawStep.local
        apply Unpacking.Step.letValue (object := .shared 0)
        · apply Eval.giveShare (reference := .owned 0)
          · exact .move (source := .variable "p")
              (.variable (reference := .owned 0) (by decide)) (.variable _ _ [] [] "p" 0)
          · exact ⟨⟨"Point", []⟩, ⟨[], .structType⟩, by decide, by decide, rfl⟩
        · exact .variable (by decide)
      · gc
    · apply Steps.step
      · exact checked_step (RawStep.call (declaration := copy) (by simp [declarations]) rfl (by decide)
          (.cons (copy_head _ _ _ _ _) (.nil _)) rfl) (by gc)
      · apply Steps.step
        · exact checked_step (RawStep.return (.some (copy_head _ _ "point" _ [])) (.some (by decide))) (by gc)
        · exact .refl _

-- ANCHOR: shared
example : ProgramTyped sharedProgram ∧
    Steps classes.erase declarations (.initial sharedProgram) sharedReturned ∧
    Step classes.erase declarations sharedReturned ⟨[], 1, []⟩ ∧
    ("p", none) ∈ sharedReturned.rootState.variables ∧
    ("s", some (.shared 0)) ∈ sharedReturned.rootState.variables ∧
    ("t", some (.shared 0)) ∈ sharedReturned.rootState.variables ∧
    ¬ Admissible classes (ValueType.whole "Token" .shared) :=
  ⟨⟨by decide, declarations_typed, _, shared_main⟩, shared_execution,
    by exact collected_step .exit (by simp), by decide, by decide, by decide, by decide⟩
-- ANCHOR_END: shared

def methodCode : List Statement :=
  [.local ⟨.variable "p", .new "Point" []⟩,
   .call (some "q") (.method "Point" "take") [.give (.variable "p")],
   .local ⟨.variable "s", .giveShare (.variable "q")⟩,
   .call (some "t") (.method "Point" "copy") [.give (.variable "s")]]

def methodProgram : Program := ⟨classes, declarations, methodCode⟩

def methodReturned : Configuration :=
  (.running ⟨[(0, ⟨"Point", []⟩)],
      [("t", some (.shared 0)), ("s", some (.shared 0)), ("q", none), ("p", none)], 1⟩ ⟨[], none⟩)

private theorem method_main : SequenceTyped classes declarations [] methodCode
    [("t", some sharedPoint.toType), ("s", some sharedPoint.toType), ("q", none), ("p", none)] := by
  apply SequenceTyped.cons (middle := [("p", some ownedPoint.toType)])
  · apply StatementTyped.local
    apply Shared.Typing.StatementTyped.letValue (middle := []) (ty := ownedPoint.toType)
    · exact .new (declaration := ⟨[], .structType⟩) (by decide) (.nil (by decide))
        (by decide) (by decide)
    · exact .variable (by decide) (by decide) (by decide)
  · apply SequenceTyped.cons (middle := [("q", some ownedPoint.toType), ("p", none)])
    · apply StatementTyped.call (declaration := takeMethod) (middle := [("p", none)])
      · simp [declarations]
      · decide
      · exact .cons (.give (by decide) (by decide) (by decide) (by decide)) (.nil (by decide))
      · exact .some (.variable (by decide) (by decide) (by decide))
    · apply SequenceTyped.cons (middle := [("s", some sharedPoint.toType), ("q", none), ("p", none)])
      · apply StatementTyped.local
        apply Shared.Typing.StatementTyped.letValue (middle := [("q", none), ("p", none)])
          (ty := sharedPoint.toType)
        · exact .giveShare (ty := ownedPoint.toType) (by decide) (by decide) (by decide)
            (by decide) (by decide)
        · exact .variable (by decide) (by decide) (by decide)
      · apply SequenceTyped.cons
        · apply StatementTyped.call (declaration := copyMethod)
            (middle := [("s", some sharedPoint.toType), ("q", none), ("p", none)])
          · simp [declarations]
          · decide
          · exact .cons (.give (by decide) (by decide) (by decide) (by decide)) (.nil (by decide))
          · exact .some (.variable (by decide) (by decide) (by decide))
        · exact .nil (by decide)

theorem method_execution : Steps classes.erase declarations (.initial methodProgram) methodReturned := by
  apply Steps.step (middle := (.running ⟨[(0, ⟨"Point", []⟩)], [("p", some (.owned 0))], 1⟩ ⟨methodCode.tail, none⟩))
  · exact checked_step (.local (.letValue (new_point []) (.variable (by simp)))) (by gc)
  · apply Steps.step
    · exact checked_step (RawStep.call (declaration := takeMethod) (by simp [declarations]) rfl (by decide)
        (.cons (move_head _ _ _ _ []) (.nil _)) rfl) (by gc)
    · apply Steps.step (middle := (.running ⟨[(0, ⟨"Point", []⟩)], [("q", some (.owned 0)), ("p", none)], 1⟩ ⟨methodCode.drop 2, none⟩))
      · exact checked_step (RawStep.return (.some (move_head _ _ "self" _ [])) (.some (by decide))) (by gc)
      · apply Steps.step (middle := (.running ⟨[(0, ⟨"Point", []⟩)],
          [("s", some (.shared 0)), ("q", none), ("p", none)], 1⟩ ⟨methodCode.drop 3, none⟩))
        · apply checked_step
          · apply RawStep.local
            apply Unpacking.Step.letValue (object := .shared 0)
            · apply Eval.giveShare (reference := .owned 0)
              · exact .move (source := .variable "q") (.variable (reference := .owned 0) (by decide))
                  (.variable _ _ [] [("p", none)] "q" 0)
              · exact ⟨⟨"Point", []⟩, ⟨[], .structType⟩, by decide, by decide, rfl⟩
            · exact .variable (by decide)
          · gc
        · apply Steps.step
          · exact checked_step (RawStep.call (declaration := copyMethod) (by simp [declarations]) rfl (by decide)
              (.cons (copy_head _ _ _ _ _) (.nil _)) rfl) (by gc)
          · apply Steps.step
            · exact checked_step (RawStep.return (.some (copy_head _ _ "self" _ [])) (.some (by decide))) (by gc)
            · exact .refl _

-- ANCHOR: methods
example : ProgramTyped methodProgram ∧
    Steps classes.erase declarations (.initial methodProgram) methodReturned ∧
    Step classes.erase declarations methodReturned ⟨[], 1, []⟩ ∧
    ("p", none) ∈ methodReturned.rootState.variables ∧
    ("s", some (.shared 0)) ∈ methodReturned.rootState.variables ∧
    ("t", some (.shared 0)) ∈ methodReturned.rootState.variables :=
  ⟨⟨by decide, declarations_typed, _, method_main⟩, method_execution,
    by exact collected_step .exit (by simp), by decide, by decide, by decide⟩
-- ANCHOR_END: methods

def leaveCode : List Statement :=
  [.local ⟨.variable "t", .new "Token" []⟩,
   .call none (.function "leave") [.give (.variable "t")]]

def leaveProgram : Program := ⟨classes, declarations, leaveCode⟩

def leaveReturned : Configuration :=
  (.running ⟨[], [("t", none)], 1⟩ ⟨[], none⟩)

private theorem leave_main : SequenceTyped classes declarations [] leaveCode [("t", none)] := by
  apply SequenceTyped.cons (middle := [("t", some ownedToken.toType)])
  · apply StatementTyped.local
    apply Shared.Typing.StatementTyped.letValue (middle := []) (ty := ownedToken.toType)
    · exact .new (declaration := ⟨[], .classType⟩) (by decide) (.nil (by decide))
        (by decide) (by decide)
    · exact .variable (by decide) (by decide) (by decide)
  · apply SequenceTyped.cons
    · apply StatementTyped.call (declaration := leave) (middle := [("t", none)])
      · simp [declarations]
      · simp
      · exact .cons (.give (by decide) (by decide) (by decide) (by decide)) (.nil (by decide))
      · exact .none (by decide)
    · exact .nil (by decide)

theorem leave_execution : Steps classes.erase declarations (.initial leaveProgram) leaveReturned := by
  apply Steps.step (middle := (.running ⟨[(0, ⟨"Token", []⟩)], [("t", some (.owned 0))], 1⟩ ⟨leaveCode.tail, none⟩))
  · exact checked_step (.local (.letValue (new_token []) (.variable (by simp)))) (by gc)
  · apply Steps.step
    · exact checked_step (RawStep.call (declaration := leave) (by simp [declarations]) rfl (by simp)
        (.cons (move_head _ _ _ _ []) (.nil _)) rfl) (by gc)
    · exact .step (collected_step (RawStep.return (.none _) (.none _)) (by gc)) (.refl _)

-- ANCHOR: completion
example : ProgramTyped leaveProgram ∧
    Steps classes.erase declarations (.initial leaveProgram) leaveReturned ∧
    Step classes.erase declarations leaveReturned ⟨[], 1, []⟩ ∧ leaveReturned.objects = [] ∧
    BodyTyped classes declarations consume.signature consume.body :=
  ⟨⟨by decide, declarations_typed, _, leave_main⟩, leave_execution,
    by exact collected_step .exit (by simp), rfl, consume_body⟩
-- ANCHOR_END: completion

-- ANCHOR: rejection
example :
    ¬ Signature.WellFormed classes (.function "bad") ⟨[⟨"x", ⟨.shared, "Token"⟩⟩], none⟩ ∧
    ¬ Signature.WellFormed classes (.method "Point" "bad")
      ⟨[⟨"self", ownedToken⟩], none⟩ ∧
    (∀ after, ¬ StatementTyped classes [(.function "identity", identity)] []
      (.call (some "x") (.function "identity") []) after) ∧
    (∀ after, ¬ StatementTyped classes [(.function "identity", identity)] []
      (.call none (.function "identity") [.new "Token" []]) after) := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro after typed
    obtain ⟨declaration, member, arity, _⟩ := call_arity typed
    simp only [List.mem_singleton, Prod.mk.injEq] at member
    rcases member with ⟨_, rfl⟩
    cases arity
  · intro after typed
    obtain ⟨declaration, member, _, shape⟩ := call_arity typed
    simp only [List.mem_singleton, Prod.mk.injEq] at member
    rcases member with ⟨_, rfl⟩
    cases shape

-- ANCHOR_END: rejection

def recur : Declaration :=
  ⟨⟨[], none⟩, ⟨[.call none (.function "recur") []], none⟩⟩

def recursionTable : Declarations := [(.function "recur", recur)]

def recursionProgram : Program := ⟨classes, recursionTable, recur.body.statements⟩

def recursionState (depth : Nat) : Configuration :=
  (.running State.empty recur.body (List.replicate depth ⟨[], ⟨[], none⟩, none⟩))

theorem recursive_step (depth : Nat) :
    Step classes.erase recursionTable (recursionState depth) (recursionState (depth + 1)) := by
  simpa [recursionState, recur, List.replicate_succ, parameterStore, State.empty, Configuration.running] using
    (Step.collect (RawStep.call (classes := classes.erase) (declarations := recursionTable)
      (before := State.empty) (evaluated := State.empty) (destination := none)
      (name := .function "recur") (arguments := []) (rest := []) (result := none)
      (frames := List.replicate depth ⟨[], ⟨[], none⟩, none⟩)
      (declaration := recur) (references := []) (by simp [recursionTable]) rfl
      (by simp) (.nil _) rfl))

theorem recursion_reachable (depth : Nat) :
    Steps classes.erase recursionTable (.initial recursionProgram) (recursionState depth) := by
  induction depth with
  | zero => exact .refl _
  | succ depth ih => exact ih.trans (.step (recursive_step depth) (.refl _))

private theorem recursive_statement : StatementTyped classes recursionTable []
    (.call none (.function "recur") []) [] :=
  .call (declaration := recur) (by simp [recursionTable]) (by simp)
    (.nil (by decide)) (.none (by decide))

-- ANCHOR: recursion
example : ProgramTyped recursionProgram ∧
    (∀ depth, Steps classes.erase recursionTable (.initial recursionProgram) (recursionState depth)) ∧
    (∀ depth, Step classes.erase recursionTable (recursionState depth) (recursionState (depth + 1))) ∧
    (∀ depth, ¬ (recursionState depth).finished) := by
  refine ⟨⟨by decide, ?_, [], .cons recursive_statement (.nil (by decide))⟩,
    recursion_reachable, recursive_step, ?_⟩
  · refine ⟨by decide, ?_⟩
    intro entry member
    have : entry = (.function "recur", recur) := by simpa [recursionProgram, recursionTable] using member
    subst entry
    exact ⟨by decide, [], [], .cons recursive_statement (.nil (by decide)), .none (by decide)⟩
  · intro depth
    simp [recursionState, Configuration.finished, Configuration.running]
-- ANCHOR_END: recursion

def relay : Declaration :=
  ⟨identity.signature,
    ⟨[.call (some "answer") (.function "identity") [.give (.variable "token")]],
      some (.give (.variable "answer"))⟩⟩

def nestedTable : Declarations := [(.function "identity", identity), (.function "relay", relay)]

def nestedCode : List Statement :=
  [.local ⟨.variable "token", .new "Token" []⟩,
   .call (some "result") (.function "relay") [.give (.variable "token")]]

def nestedProgram : Program := ⟨classes, nestedTable, nestedCode⟩

def nestedReturned : Configuration :=
  (.running ⟨[(0, ⟨"Token", []⟩)], [("result", some (.owned 0)), ("token", none)], 1⟩ ⟨[], none⟩)

theorem nested_typed : ProgramTyped nestedProgram := by
  refine ⟨by decide, ⟨by decide, ?_⟩,
    [("result", some ownedToken.toType), ("token", none)], ?_⟩
  · intro entry member
    simp only [nestedProgram, nestedTable, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨by decide, _, _, .nil (by decide), .some token_give⟩
    · refine ⟨by decide, [("answer", some ownedToken.toType), ("token", none)],
        [("answer", none), ("token", none)], ?_, ?_⟩
      · apply SequenceTyped.cons
        · exact .call (declaration := identity) (by simp [nestedProgram, nestedTable])
            (by decide) (.cons token_give (.nil (by decide)))
            (.some (.variable (by decide) (by decide) (by decide)))
        · exact .nil (by decide)
      · exact .some (.give (by decide) (by decide) (by decide) (by decide))
  · apply SequenceTyped.cons (middle := [("token", some ownedToken.toType)])
    · apply StatementTyped.local
      apply Shared.Typing.StatementTyped.letValue (middle := []) (ty := ownedToken.toType)
      · exact .new (declaration := ⟨[], .classType⟩) (by decide) (.nil (by decide))
          (by decide) (by decide)
      · exact .variable (by decide) (by decide) (by decide)
    · apply SequenceTyped.cons
      · exact .call (declaration := relay) (by simp [nestedProgram, nestedTable])
          (by decide) (.cons token_give (.nil (by decide)))
          (.some (.variable (by decide) (by decide) (by decide)))
      · exact .nil (by decide)

theorem nested_execution : Steps classes.erase nestedTable (.initial nestedProgram) nestedReturned := by
  apply Steps.step (middle := (.running ⟨[(0, ⟨"Token", []⟩)], [("token", some (.owned 0))], 1⟩ ⟨nestedCode.tail, none⟩))
  · exact checked_step (.local (.letValue (new_token []) (.variable (by simp)))) (by gc)
  · apply Steps.step
    · exact checked_step (RawStep.call (declaration := relay) (by simp [nestedTable]) rfl (by decide)
        (.cons (move_head _ _ _ _ []) (.nil _)) rfl) (by simp only [relay]; gc)
    · apply Steps.step
      · exact checked_step (RawStep.call (declaration := identity) (by simp [nestedTable]) rfl (by decide)
          (.cons (move_head _ _ _ _ []) (.nil _)) rfl) (by gc)
      · apply Steps.step
        · exact checked_step (RawStep.return (.some (move_head _ _ "token" _ [])) (.some (by decide))) (by gc)
        · apply Steps.step
          · exact checked_step (RawStep.return (.some (move_head _ _ "answer" _ [("token", none)])) (.some (by decide))) (by gc)
          · exact .refl _

-- ANCHOR: nested
example : ProgramTyped nestedProgram ∧
    Steps classes.erase nestedTable (.initial nestedProgram) nestedReturned ∧
    Step classes.erase nestedTable nestedReturned ⟨[], 1, []⟩ ∧
    nestedReturned.rootState.variables = [("result", some (.owned 0)), ("token", none)] ∧
    nestedReturned.frames.length = 1 :=
  ⟨nested_typed, nested_execution, by exact collected_step .exit (by simp), rfl, rfl⟩
-- ANCHOR_END: nested

-- A suspended caller roots both its container and its child while a callee runs.
def callerHeap : List (ObjectId × Object) :=
  [(1, ⟨"Box", [("child", some (.owned 0))]⟩), (0, ⟨"Token", []⟩)]

def savedFrame : Frame := ⟨[("box", some (.owned 1))], ⟨[], none⟩, none⟩

def gcBefore : Configuration :=
  .running ⟨callerHeap, [], 2⟩ ⟨[.local ⟨.variable "temporary", .new "Token" []⟩], none⟩ [savedFrame]

def gcDuring : Configuration :=
  .running ⟨(2, ⟨"Token", []⟩) :: callerHeap, [("temporary", some (.owned 2))], 3⟩
    ⟨[], none⟩ [savedFrame]

def gcAfter : Configuration :=
  .running ⟨callerHeap, savedFrame.variables, 3⟩ savedFrame.body

private theorem caller_root (heap : List (ObjectId × Object)) (nextId : Nat) :
    Live ⟨heap, savedFrame.variables, nextId⟩ 1 :=
  .variable (name := "box") (reference := .owned 1) (by simp [savedFrame])

private theorem gc_local : Step classes.erase declarations gcBefore gcDuring := by
  apply checked_step
  · apply RawStep.local
    apply Unpacking.Step.letValue
    · exact .new (declaration := ⟨[], .classType⟩) (references := [])
        (by decide) (.nil _) rfl (by decide) (by simp [StructArguments, Kind.isStruct])
    · exact .variable (by simp [State.allocate])
  · apply Configuration.collect_eq_self
    intro id data member
    simp only [gcDuring, Configuration.running, callerHeap, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .variable (name := "temporary") (reference := .owned 2) (by simp [gcDuring, Configuration.rootState,
        Configuration.running, savedFrame])
    · exact .variable (name := "box") (reference := .owned 1) (by simp [gcDuring, Configuration.rootState,
        Configuration.running, savedFrame])
    · apply Live.field (parent := 1) (data := ⟨"Box", [("child", some (.owned 0))]⟩)
        (name := "child") (reference := .owned 0)
      · exact .variable (name := "box") (reference := .owned 1) (by simp [gcDuring, Configuration.rootState,
          Configuration.running, savedFrame])
      · simp [gcDuring, Configuration.rootState, Configuration.running, callerHeap]
      · simp

private theorem remaining_live (id : ObjectId) :
    Live ⟨(2, ⟨"Token", []⟩) :: callerHeap, savedFrame.variables, 3⟩ id ↔ id = 0 ∨ id = 1 := by
  constructor
  · intro live
    cases live with
    | «variable» member =>
      simp only [savedFrame, List.mem_singleton, Prod.mk.injEq, Option.some.injEq] at member
      obtain ⟨_, rfl⟩ := member
      exact .inr rfl
    | field _ stored field =>
      simp only [callerHeap, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at stored
      rcases stored with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      · simp at field
      · simp only [List.mem_singleton, Prod.mk.injEq, Option.some.injEq] at field
        obtain ⟨_, rfl⟩ := field
        exact .inl rfl
      · simp at field
  · rintro (rfl | rfl)
    · exact .field (parent := 1) (data := ⟨"Box", [("child", some (.owned 0))]⟩)
        (name := "child") (reference := .owned 0) (caller_root _ _)
        (by simp [callerHeap]) (by simp)
    · exact caller_root _ _

private theorem gc_return : Step classes.erase declarations gcDuring gcAfter := by
  apply collected_step (RawStep.return (.none _) (.none _))
  have characterization := remaining_live
  dsimp [callerHeap, savedFrame] at characterization
  simp +instances [Configuration.collect, State.collect, Configuration.rootState, Configuration.running,
    savedFrame, gcAfter, List.flatMap, List.map, List.flatten,
    characterization, callerHeap]
  decide

-- ANCHOR: gc
example : Step classes.erase declarations gcBefore gcDuring ∧
    gcDuring.objects.length = 3 ∧
    Step classes.erase declarations gcDuring gcAfter ∧
    gcAfter.objects = callerHeap ∧
    Step classes.erase declarations gcAfter ⟨[], 3, []⟩ ∧
    (Configuration.mk [] 3 []).finished ∧
    Step classes.erase declarations (.initial ⟨classes, declarations, []⟩) ⟨[], 0, []⟩ :=
  ⟨gc_local, rfl, gc_return, rfl, collected_step .exit (by simp), rfl,
    collected_step .exit (by simp)⟩
-- ANCHOR_END: gc

end Dada.Functions.Checks
