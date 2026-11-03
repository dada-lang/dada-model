import Shared.Unpacking

namespace Dada.Shared.Unpacking

def exampleClasses : Classes :=
  [("Token", ⟨[], .structType⟩), ("Box", ⟨["item"], .structType⟩), ("Outer", ⟨["box"], .classType⟩),
    ("Holder", ⟨["item"], .structType⟩), ("Pair", ⟨["left", "right"], .structType⟩)]

def tokenObject : Object := ⟨"Token", []⟩
def holderObject : Object := ⟨"Holder", [("item", some (.shared 0))]⟩

def tokenCreated : State :=
  ⟨[(0, tokenObject)], [("t", some (.owned 0))], 1⟩

def holderCreated : State :=
  ⟨[(1, holderObject), (0, tokenObject)], [("h", some (.owned 1)), ("t", none)], 2⟩

def copiedOnce : State := holderCreated.bind "a" (.shared 0)
def argumentsFinished : State := copiedOnce.bind "b" (.shared 0)

def holderTaken : State :=
  ⟨[(1, holderObject), (0, tokenObject)],
    [("b", some (.shared 0)), ("a", some (.shared 0)), ("h", none), ("t", none)], 2⟩

def holderUnpacked : State :=
  ⟨[(0, tokenObject)],
    [("item", some (.shared 0)), ("b", some (.shared 0)), ("a", some (.shared 0)),
      ("h", none), ("t", none)], 2⟩

def unpackingFinished : State := holderUnpacked.bind "c" (.shared 0)

def unpackingProgram : List Statement :=
  [⟨.variable "t", .new "Token" []⟩,
    ⟨.variable "h", .new "Holder" [.giveShare (.variable "t")]⟩,
    ⟨.variable "a", .give (.field (.variable "h") "item")⟩,
    ⟨.variable "b", .give (.field (.variable "h") "item")⟩,
    ⟨.unpack "Holder" [("item", "item")], .give (.variable "h")⟩,
    ⟨.variable "c", .give (.variable "item")⟩]

private theorem new_token : Eval exampleClasses State.empty (.new "Token" [])
    ⟨[(0, tokenObject)], [], 1⟩ (.owned 0) := by
  exact Eval.new (state := State.empty) (evaluated := State.empty)
    (declaration := ⟨[], .structType⟩) (references := [])
    (by simp [exampleClasses]) (.nil _) rfl (by simp [State.empty])
    (by simp [StructArguments])

private theorem new_holder : Eval exampleClasses tokenCreated
    (.new "Holder" [.giveShare (.variable "t")])
    ⟨[(1, holderObject), (0, tokenObject)], [("t", none)], 2⟩ (.owned 1) := by
  apply Eval.new (declaration := ⟨["item"], .structType⟩)
    (evaluated := ⟨[(0, tokenObject)], [("t", none)], 1⟩)
    (references := [.shared 0])
  · simp [exampleClasses]
  · apply EvalArgs.cons (middle := ⟨[(0, tokenObject)], [("t", none)], 1⟩)
      (reference := .shared 0)
    · exact Eval.giveShare (reference := .owned 0) (Give.move (source := .variable "t")
        (Resolve.variable (reference := .owned 0) (by decide))
        (.variable [(0, tokenObject)] 1 [] [] "t" 0))
        (by simp [StructReference, tokenObject, exampleClasses, Reference.owned, Kind.isStruct])
    · exact .nil _
  · rfl
  · decide
  · simp [StructArguments, StructReference, tokenObject, exampleClasses, Reference.shared, Kind.isStruct]

private theorem copy_item {state : State}
    (holder : ("h", some (.owned 1)) ∈ state.variables)
    (allocated : (1, holderObject) ∈ state.objects) :
    Eval exampleClasses state (.give (.field (.variable "h") "item")) state (.shared 0) := by
  apply Eval.give
  apply Give.copy (source := .field 1 "item")
  · exact Resolve.field (reference := .shared 0) (.variable holder) allocated (by decide)
  · exact ⟨holderObject, allocated, by decide⟩

private theorem take_holder : Eval exampleClasses argumentsFinished
    (.give (.variable "h")) holderTaken (.owned 1) := by
  exact Eval.give (Give.move (source := .variable "h")
    (Resolve.variable (reference := .owned 1) (by decide))
    (.variable [(1, holderObject), (0, tokenObject)] 2
      [("b", some (.shared 0)), ("a", some (.shared 0))] [("t", none)] "h" 1))

private theorem unpack_holder : Bind exampleClasses holderTaken (.owned 1)
    (.unpack "Holder" [("item", "item")]) holderUnpacked := by
  apply Bind.unpack (before := []) (after := [(0, tokenObject)])
    (declaration := ⟨["item"], .structType⟩)
    (bindings := [("item", some (.shared 0))])
  · simp [exampleClasses]
  · rfl
  · decide
  · decide
  · decide
  · exact Transfer.cons (before := []) .nil

private theorem copy_unpacked : Eval exampleClasses holderUnpacked
    (.give (.variable "item")) holderUnpacked (.shared 0) := by
  exact Eval.give (Give.copy (source := .variable "item")
    (Resolve.variable (reference := .shared 0) (by decide))
    (by change ("item", some (.shared 0)) ∈ holderUnpacked.variables; decide))

theorem arguments_execution : Steps exampleClasses
    ⟨State.empty, unpackingProgram.take 4⟩ ⟨argumentsFinished, []⟩ := by
  apply Steps.step (middle := ⟨tokenCreated, (unpackingProgram.take 4).tail⟩)
  · exact .letValue new_token (.variable (by decide))
  · apply Steps.step (middle := ⟨holderCreated, (unpackingProgram.take 4).tail.tail⟩)
    · exact .letValue new_holder (.variable (by decide))
    · apply Steps.step (middle := ⟨copiedOnce, (unpackingProgram.take 4).tail.tail.tail⟩)
      · exact .letValue (copy_item (by decide) (by decide)) (.variable (by decide))
      · exact .step (.letValue (copy_item (by decide) (by decide)) (.variable (by decide))) (.refl _)

theorem unpacking_execution : StepsExactly exampleClasses
    ⟨State.empty, unpackingProgram⟩ 6 ⟨unpackingFinished, []⟩ := by
  apply StepsExactly.step (middle := ⟨tokenCreated, unpackingProgram.tail⟩)
  · exact .letValue new_token (.variable (by decide))
  · apply StepsExactly.step (middle := ⟨holderCreated, unpackingProgram.tail.tail⟩)
    · exact .letValue new_holder (.variable (by decide))
    · apply StepsExactly.step (middle := ⟨copiedOnce, unpackingProgram.drop 3⟩)
      · exact .letValue (copy_item (by decide) (by decide)) (.variable (by decide))
      · apply StepsExactly.step (middle := ⟨argumentsFinished, unpackingProgram.drop 4⟩)
        · exact .letValue (copy_item (by decide) (by decide)) (.variable (by decide))
        · apply StepsExactly.step (middle := ⟨holderUnpacked, unpackingProgram.drop 5⟩)
          · exact .letValue take_holder unpack_holder
          · exact .step (.letValue copy_unpacked (.variable (by decide))) (.refl _)

-- ANCHOR: shared_fields_survive_unpacking
example : StepsExactly exampleClasses ⟨State.empty, unpackingProgram⟩ 6
      ⟨unpackingFinished, []⟩ ∧
    ("h", none) ∈ unpackingFinished.variables ∧
    ("item", some (.shared 0)) ∈ unpackingFinished.variables ∧
    ("a", some (.shared 0)) ∈ unpackingFinished.variables ∧
    ("b", some (.shared 0)) ∈ unpackingFinished.variables ∧
    ("c", some (.shared 0)) ∈ unpackingFinished.variables ∧
    ¬ Allocated unpackingFinished 1 ∧
    ∀ state after object,
      ¬ Bind exampleClasses state (.shared object) (.unpack "Holder" [("item", "item")]) after := by
  refine ⟨unpacking_execution, by decide, by decide, by decide, by decide, by decide,
    by change (1 : ObjectId) ∉ [0]; decide, ?_⟩
  intro state after object
  exact shared_cannot_unpack
-- ANCHOR_END: shared_fields_survive_unpacking

-- Field order may differ, and empty slots transfer without inventing a value.
example : Bind exampleClasses
    ⟨[(1, ⟨"Pair", [("left", none), ("right", some (.shared 0))]⟩), (0, tokenObject)], [], 2⟩
    (.owned 1) (.unpack "Pair" [("right", "r"), ("left", "l")])
    ⟨[(0, tokenObject)], [("r", some (.shared 0)), ("l", none)], 2⟩ := by
  apply Bind.unpack (before := []) (after := [(0, tokenObject)])
    (declaration := ⟨["left", "right"], .structType⟩)
    (bindings := [("r", some (.shared 0)), ("l", none)])
  · simp [exampleClasses]
  · rfl
  · decide
  · decide
  · decide
  · exact Transfer.cons (before := [("left", none)]) (after := [])
      (Transfer.cons (before := []) .nil)

-- Even a fieldless object needs a unique reference to be consumed.
example : Bind exampleClasses ⟨[(0, tokenObject)], [], 1⟩ (.owned 0)
    (.unpack "Token" []) ⟨[], [], 1⟩ := by
  exact Bind.unpack (declaration := ⟨[], .structType⟩) (before := []) (after := []) (by simp [exampleClasses])
    rfl (by decide) (by decide) (by simp) .nil

end Dada.Shared.Unpacking
