import Destructors.Checks

namespace Dada.Destructors.Checks
open Shared Shared.Typing

private theorem move_head (objects : List (ObjectId × Object)) (nextId : Nat)
    (name : String) (object : ObjectId) (rest : Store) :
    Eval classes.erase ⟨objects, (name, some (.owned object)) :: rest, nextId⟩
      (.give (.variable name)) ⟨objects, (name, none) :: rest, nextId⟩ (.owned object) :=
  .give (.move (source := .variable name) (.variable (reference := .owned object) (by simp))
    (.variable objects nextId [] rest name object))

private theorem step_of_classes
    (typed : ConfigurationTyped classes declarations before)
    (raw : RawStep classes.erase declarations before after)
    (allClasses : ∀ id data, (id, data) ∈ after.objects → ¬ StructType classes (.whole data.className)) :
    Step classes.erase declarations before after := by
  have retained := (raw.sound typed).2
  have collected : after.collect = after := by
    apply Configuration.collect_eq_self
    intro id data member
    have kept := retained id data member (allClasses id data member)
    classical
    exact of_decide_eq_true (List.mem_filter.mp kept).2
  exact collected ▸ Step.collect raw

def wrapperCode : List Statement :=
  [.local ⟨.variable "w", .new "Wrapper" [.new "Resource" []]⟩,
   .dropClass "Wrapper" (.variable "w")]
def wrapperProgram : Program := ⟨classes, declarations, wrapperCode⟩

theorem wrapper_typed : ProgramTyped wrapperProgram := by
  refine ⟨by decide, declarations_typed, [("w",none)], ?_, by simp [Finished]⟩
  apply SequenceTyped.cons (middle := [("w",some (.whole "Wrapper"))])
  · apply StatementTyped.local
    apply Shared.Typing.StatementTyped.letValue (middle := []) (ty := .whole "Wrapper")
    · apply ExprTyped.new (declaration := ⟨[("resource",⟨.given,"Resource"⟩)],.classType⟩) (by decide)
      · exact .cons (.new (declaration := ⟨[],.classType⟩) (by decide) (.nil (by decide))
          (by decide) (by decide)) (.nil (by decide))
      · decide
      · decide
    · exact .variable (by decide) (by decide) (by decide)
  · apply SequenceTyped.cons
    · exact .call (declaration := wrapper) (middle := [("w",none)]) (by simp [wrapperProgram,declarations]) (by simp)
        (.cons (.give (by decide) (by decide) (by decide) (by decide)) (.nil (by decide)))
        (.none (by decide))
    · exact .nil (by decide)

def wrapperHeap : List (ObjectId × Object) :=
  [(1,⟨"Wrapper",[("resource",some (.owned 0))]⟩), (0,⟨"Resource",[]⟩)]
def resourceHeap : List (ObjectId × Object) := [(0,⟨"Resource",[]⟩)]
def mainCaller : Frame := ⟨[("w",none)],⟨[],none⟩,none⟩
def wrapperCaller : Frame := ⟨[("resource",none),("self",none)],⟨[],none⟩,none⟩
def w1 : Configuration := .running ⟨wrapperHeap,[("w",some (.owned 1))],2⟩
  ⟨[.dropClass "Wrapper" (.variable "w")],none⟩
def w2 : Configuration := .running ⟨wrapperHeap,[("self",some (.owned 1))],2⟩ wrapper.body [mainCaller]
def w3 : Configuration := .running ⟨resourceHeap,[("resource",some (.owned 0)),("self",none)],2⟩
  ⟨[.dropClass "Resource" (.variable "resource")],none⟩ [mainCaller]
def w4 : Configuration := .running ⟨resourceHeap,[("self",some (.owned 0))],2⟩ resource.body [wrapperCaller,mainCaller]
def w5 : Configuration := .running ⟨[],[("self",none)],2⟩ ⟨[],none⟩ [wrapperCaller,mainCaller]
def w6 : Configuration := .running ⟨[],wrapperCaller.variables,2⟩ ⟨[],none⟩ [mainCaller]
def w7 : Configuration := .running ⟨[],mainCaller.variables,2⟩ ⟨[],none⟩

private theorem wrapperHeap_classes : ∀ id data, (id,data) ∈ wrapperHeap →
    ¬ StructType classes (.whole data.className) := by
  intro id data member
  simp only [wrapperHeap,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at member
  rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide

private theorem resourceHeap_classes : ∀ id data, (id,data) ∈ resourceHeap →
    ¬ StructType classes (.whole data.className) := by
  intro id data member
  have eq : (id,data) = (0,⟨"Resource",[]⟩) := List.mem_singleton.mp member
  cases eq
  decide

theorem wrapper_execution : Steps classes.erase declarations (.initial wrapperProgram) ⟨[],2,[]⟩ := by
  have t0 := ConfigurationTyped.initial wrapper_typed
  have a : Step classes.erase declarations (.initial wrapperProgram) w1 := by
    apply step_of_classes t0 _ wrapperHeap_classes
    have allocation : Eval classes.erase State.empty (.new "Wrapper" [.new "Resource" []])
        ⟨wrapperHeap,[],2⟩ (.owned 1) := by
      exact Eval.new (classes := classes.erase) (state := State.empty) (className := "Wrapper")
        (evaluated := ⟨resourceHeap,[],1⟩) (arguments := [.new "Resource" []]) (declaration := ⟨["resource"],.classType⟩) (references := [.owned 0])
        (by decide) (.cons (Eval.new (classes := classes.erase) (state := State.empty) (evaluated := State.empty)
          (className := "Resource") (arguments := []) (declaration := ⟨[],.classType⟩) (references := [])
          (by decide) (.nil _) rfl (by simp [State.empty]) (by simp [StructArguments,Kind.isStruct])) (.nil _))
        rfl (by decide) (by simp [StructArguments,Kind.isStruct])
    exact .local (.letValue allocation (.variable (by simp)))
  have t1 := t0.preservation a
  have b : Step classes.erase declarations w1 w2 := by
    apply step_of_classes t1 _ wrapperHeap_classes
    exact .call (declaration := wrapper) (evaluated := ⟨wrapperHeap,[("w",none)],2⟩)
      (references := [.owned 1]) (by simp [declarations]) rfl (by simp)
      (.cons (move_head _ _ _ _ []) (.nil _)) rfl
  have t2 := t1.preservation b
  have c : Step classes.erase declarations w2 w3 := by
    apply step_of_classes t2 _ resourceHeap_classes
    apply RawStep.local
    apply Unpacking.Step.letValue (move_head _ _ _ _ [])
    exact .unpack (before := []) (after := resourceHeap) (declaration := ⟨["resource"],.classType⟩)
      (by decide) rfl (by decide) (by decide) (by decide)
      (.cons (before := []) (after := []) .nil)
  have t3 := t2.preservation c
  have d : Step classes.erase declarations w3 w4 := by
    apply step_of_classes t3 _ resourceHeap_classes
    exact .call (declaration := resource) (evaluated := ⟨resourceHeap,wrapperCaller.variables,2⟩)
      (references := [.owned 0]) (by simp [declarations]) rfl (by simp)
      (.cons (move_head _ _ _ _ [("self",none)]) (.nil _)) rfl
  have t4 := t3.preservation d
  have e : Step classes.erase declarations w4 w5 := by
    apply step_of_classes t4 _ (by simp [w5,Configuration.running])
    apply RawStep.local
    apply Unpacking.Step.letValue (move_head _ _ _ _ [])
    exact .unpack (before := []) (after := []) (declaration := ⟨[],.classType⟩)
      (by decide) rfl (by decide) (by decide) (by decide) .nil
  have t5 := t4.preservation e
  have f : Step classes.erase declarations w5 w6 := by
    apply step_of_classes t5 _ (by simp [w6,Configuration.running])
    exact .return (evaluated := ⟨[],[("self",none)],2⟩) (.none _) (.none _)
      (by simp [StoreFinished])
  have t6 := t5.preservation f
  have g : Step classes.erase declarations w6 w7 := by
    apply step_of_classes t6 _ (by simp [w7,Configuration.running])
    exact .return (evaluated := ⟨[],wrapperCaller.variables,2⟩) (.none _) (.none _)
      (by simp [StoreFinished,wrapperCaller])
  have t7 := t6.preservation g
  have h : Step classes.erase declarations w7 ⟨[],2,[]⟩ := by
    apply step_of_classes t7 _ (by simp)
    exact .exit (by simp [StoreFinished,mainCaller])
  exact .step a (.step b (.step c (.step d (.step e (.step f (.step g (.step h (.refl _))))))))

-- ANCHOR: wrapper_consumed
example : ProgramTyped wrapperProgram ∧
    Steps classes.erase declarations (.initial wrapperProgram) ⟨[],2,[]⟩ :=
  ⟨wrapper_typed, wrapper_execution⟩
-- ANCHOR_END: wrapper_consumed

def recursionState (depth : Nat) : Configuration :=
  .running ⟨[(0,⟨"Again",[]⟩)],[("self",some (.owned 0))],1⟩ again.body
    (List.replicate depth ⟨[("self",none)],⟨[],none⟩,none⟩)

theorem recursive_step (depth : Nat) :
    Step classes.erase declarations (recursionState depth) (recursionState (depth + 1)) := by
  have collected : (recursionState (depth + 1)).collect = recursionState (depth + 1) := by
    apply Configuration.collect_eq_self
    intro id data member
    have eq : (id,data) = (0,⟨"Again",[]⟩) := List.mem_singleton.mp member
    cases eq
    exact .variable (name := "self") (reference := .owned 0)
      (by simp [recursionState,Configuration.rootState,Configuration.running])
  rw [← collected]
  apply Step.collect
  simpa only [recursionState,again,Statement.dropClass,List.replicate_succ,
    Configuration.running,parameterStore,receiver,List.map,List.zip,List.zipWith] using
    (RawStep.call (classes := classes.erase) (declarations := declarations)
      (before := ⟨[(0,⟨"Again",[]⟩)],[("self",some (.owned 0))],1⟩)
      (evaluated := ⟨[(0,⟨"Again",[]⟩)],[("self",none)],1⟩)
      (destination := none) (name := .destructor "Again")
      (arguments := [.give (.variable "self")]) (rest := []) (result := none)
      (frames := List.replicate depth ⟨[("self",none)],⟨[],none⟩,none⟩) (returnTo := none)
      (declaration := again) (references := [.owned 0]) (by simp [declarations]) rfl
      (by simp) (.cons (move_head _ _ _ _ []) (.nil _)) rfl)

theorem recursive_prefix (depth : Nat) :
    Steps classes.erase declarations (recursionState 0) (recursionState depth) := by
  induction depth with
  | zero => exact .refl _
  | succ depth ih => exact ih.trans (.step (recursive_step depth) (.refl _))

def recursionProgram : Program := ⟨classes,declarations,
  .local ⟨.variable "self",.new "Again" []⟩ :: again.body.statements⟩

theorem recursion_typed : ProgramTyped recursionProgram := by
  obtain ⟨middle,final,sequence,result,finished⟩ := again_body
  cases result with
  | none _ =>
    refine ⟨by decide,declarations_typed,middle,?_,finished⟩
    apply SequenceTyped.cons (middle := [("self",some (.whole "Again"))]) _ sequence
    apply StatementTyped.local
    apply Shared.Typing.StatementTyped.letValue (middle := []) (ty := .whole "Again")
    · exact .new (declaration := ⟨[],.classType⟩) (by decide) (.nil (by decide)) (by decide) (by decide)
    · exact .variable (by decide) (by decide) (by decide)

theorem recursion_enter : Step classes.erase declarations (.initial recursionProgram) (recursionState 0) := by
  apply step_of_classes (ConfigurationTyped.initial recursion_typed)
  · have allocation : Eval classes.erase State.empty (.new "Again" [])
        ⟨[(0,⟨"Again",[]⟩)],[],1⟩ (.owned 0) :=
      Eval.new (classes := classes.erase) (state := State.empty) (evaluated := State.empty)
        (className := "Again") (arguments := []) (declaration := ⟨[],.classType⟩)
        (references := []) (by decide) (.nil _) rfl (by simp [State.empty])
        (by simp [StructArguments,Kind.isStruct])
    exact .local (.letValue allocation (.variable (by simp)))
  · intro id data member
    have eq : (id,data) = (0,⟨"Again",[]⟩) := List.mem_singleton.mp member
    cases eq
    decide

theorem recursion_reachable (depth : Nat) :
    Steps classes.erase declarations (.initial recursionProgram) (recursionState depth) :=
  .step recursion_enter (recursive_prefix depth)

-- ANCHOR: recursive_execution
example : BodyTyped classes declarations again.signature again.body ∧
    (∀ depth, Steps classes.erase declarations (recursionState 0) (recursionState depth)) ∧
    (∀ depth, Step classes.erase declarations (recursionState depth) (recursionState (depth + 1))) ∧
    (∀ depth, ¬ (recursionState depth).finished) := by
  refine ⟨again_body, recursive_prefix, recursive_step, ?_⟩
  intro depth
  simp [recursionState,Configuration.finished,Configuration.running]
-- ANCHOR_END: recursive_execution

end Dada.Destructors.Checks
