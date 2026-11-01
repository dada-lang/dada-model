import Unique.TypingExecutionChecks
import Unique.TypingRealization
import Unique.TypingEffects

namespace Dada.Unique.Typing.RejectionChecks

open Checks

def hiddenPair : ViewType := ⟨"Pair", [.positive ["right"]]⟩
def partialEnvironment : Environment := [("p", some partialPair)]
def hiddenEnvironment : Environment := [("p", some hiddenPair)]
def left : Place := .field (.variable "p") "left"
def root : Place := .variable "p"

private theorem give_result (typed : ExprTyped table before value ty after) :
    ∀ place, value = .give place →
      ∃ source, take table before place = some (source, after) ∧ Subtype table source ty := by
  induction typed using ExprTyped.rec (motive_2 := fun _ _ _ _ _ => True) with
  | give _ taken _ _ =>
    intro place equality
    cases equality
    exact ⟨_, taken, .refl _ _⟩
  | new => intro place equality; cases equality
  | weaken _ _ subtype ih =>
    intro place equality
    obtain ⟨source, taken, previous⟩ := ih place equality
    exact ⟨source, taken, previous.trans subtype⟩
  | nil => trivial
  | cons => trivial

private theorem new_arguments (typed : ExprTyped table before value ty after) :
    ∀ name arguments, value = .new name arguments →
      ∃ declaration, (name, declaration) ∈ table ∧
        ArgsTyped table before arguments (declaration.fields.map Prod.snd) after := by
  induction typed using ExprTyped.rec (motive_2 := fun _ _ _ _ _ => True) with
  | give => intro name arguments equality; cases equality
  | new declared typed _ _ =>
    intro name arguments equality
    cases equality
    exact ⟨_, declared, typed⟩
  | weaken _ _ _ ih => exact ih
  | nil => trivial
  | cons => trivial

theorem partial_give : ExprTyped classes partialEnvironment (.give root) partialPair [("p", none)] :=
  .give (by decide) (by decide) (by decide) (by decide)

theorem partial_not_whole : ¬ ExprTyped classes partialEnvironment (.give root) pair after := by
  intro typed
  obtain ⟨source, taken, subtype⟩ := give_result typed root rfl
  have actual : take classes partialEnvironment root = some (partialPair, [("p", none)]) := by decide
  rw [actual] at taken
  cases taken
  have positive : Pos classes (normalize classes pair) ["left"] := by decide
  have impossible := subtype.2.1 ["left"] positive
  have absent : ¬ Pos classes (normalize classes partialPair) ["left"] := by decide
  exact absent impossible

theorem partial_constructor_rejected :
    ¬ ExprTyped classes partialEnvironment (.new "Box" [.give root]) ty after := by
  intro typed
  obtain ⟨declaration, declared, arguments⟩ := new_arguments typed "Box" [.give root] rfl
  have actual : declaration = ⟨[("item", "Pair")]⟩ := by
    simpa [classes] using declared
  subst declaration
  cases arguments with
  | cons first _ => exact partial_not_whole first

private theorem description_for_pattern
    (typed : FieldBindings table ty pattern bindings) (member : (field, name) ∈ pattern) :
    ∃ description, fieldDescription table ty field = some description := by
  induction typed with
  | nil => simp at member
  | cons described _ ih =>
    rcases List.mem_cons.mp member with same | later
    · cases same; exact ⟨_, described⟩
    · exact ih later

theorem hidden_unpack_rejected :
    ¬ BindingTyped classes before (.unpack "Pair" pattern) hiddenPair after := by
  intro typed
  cases typed with
  | @unpack _ _ declaration _ _ _ _ _ declared fields _ _ descriptions _ =>
    have actual : declaration = (⟨[("left", "Token"), ("right", "Token")]⟩ : TypedClass) := by
      simpa [classes] using declared
    subst actual
    have present : "left" ∈ pattern.map Prod.fst := fields.mem_iff.mpr (by simp)
    obtain ⟨⟨_, destination⟩, member, equal⟩ := List.mem_map.mp present
    simp only at equal
    subst equal
    obtain ⟨description, described⟩ := description_for_pattern descriptions member
    have absent : fieldDescription classes hiddenPair "left" = none := by decide
    rw [absent] at described
    contradiction

def runtimePartial : State :=
  ⟨(2, runtimePartialPair) :: runtimeTokens, [("p", some 2), ("taken", some 0)], 3⟩
def runtimeAfterTake : State :=
  { runtimePartial with variables := [("p", none), ("taken", some 0)] }

theorem partial_constructor_executes :
    Eval classes.erase runtimePartial (.new "Box" [.give root])
      (runtimeAfterTake.allocate "Box" ["item"] [2]) 3 := by
  apply Eval.new (declaration := ⟨["item"]⟩) (evaluated := runtimeAfterTake) (objects := [2])
  · decide
  · apply EvalArgs.cons (middle := runtimeAfterTake) (object := 2)
    · exact Eval.give (.variable (by decide))
        (Take.variable runtimePartial.objects 3 [] [("taken", some 0)] "p" 2)
    · exact .nil _
  · rfl
  · decide

def twoClasses : ClassTable := [("Two", ⟨[("a", "Token"), ("b", "Token")]⟩)] ++ classes
def tokenEnvironment : Environment := [("t", some token)]
def tokenGive : Value := .give (.variable "t")

theorem first_argument_moves :
    ExprTyped twoClasses tokenEnvironment tokenGive token [("t", none)] :=
  .give (by decide) (by decide) (by decide) (by decide)

theorem repeated_argument_rejected :
    ¬ ExprTyped twoClasses tokenEnvironment (.new "Two" [tokenGive, tokenGive]) ty after := by
  intro typed
  obtain ⟨declaration, declared, arguments⟩ :=
    new_arguments typed "Two" [tokenGive, tokenGive] rfl
  have actual : declaration = ⟨[("a", "Token"), ("b", "Token")]⟩ := by
    simpa [twoClasses, classes] using declared
  subst declaration
  cases arguments with
  | cons first rest =>
    obtain ⟨source, taken⟩ := first.give_requires_take (.variable "t") rfl
    have actual : take twoClasses tokenEnvironment (.variable "t") =
        some (token, [("t", none)]) := by decide
    rw [actual] at taken
    cases taken
    cases rest with
    | cons second _ => exact failed_take_not_typed (by decide) second

private theorem hidden_positive_paths (known : Pos classes hiddenPair path) :
    path = [] ∨ path = ["right"] := by
  cases path with
  | nil => exact Or.inl rfl
  | cons field rest =>
    have valid := known.valid
    have right : field = "right" := by
      simp [Pos, positive, hiddenPair, Entry.path, List.isPrefixOf_cons_cons] at known
      exact known.2.symm
    subst field
    cases rest with
    | nil => exact Or.inr rfl
    | cons next rest => simp [classAt, classes, hiddenPair, List.lookup] at valid

def runtimeFull : State :=
  ⟨(2, runtimePair) :: runtimeTokens, [("p", some 2)], 3⟩
def runtimeGivenLeft : State :=
  { runtimeFull with objects := (2, runtimePartialPair) :: runtimeTokens }

theorem initialized_hidden_field : Satisfies classes runtimeFull 2 hiddenPair ∧
    Eval classes.erase runtimeFull (.give left) runtimeGivenLeft 0 := by
  constructor
  · constructor
    · exact ⟨runtimePair, by decide, rfl⟩
    · intro path positive
      rcases hidden_positive_paths positive with rfl | rfl
      · exact ⟨2, runtimePair, by decide, by decide, rfl⟩
      · exact ⟨1, ⟨"Token", []⟩, by decide, by decide, by decide⟩
    · intro path negative
      change false = true at negative
      contradiction
  · exact Eval.give (.field (parent := 2) (data := runtimePair)
      (.variable (by decide)) (by decide) (by decide))
      (Take.field [("p", some 2)] 3 [] runtimeTokens 2 "Pair" []
        [("right", some 1)] "left" 0)

-- ANCHOR: rejected_moves
example :
    (∀ ty after, ¬ ExprTyped classes partialEnvironment (.give left) ty after) ∧
    (∀ ty after, ¬ ExprTyped classes hiddenEnvironment (.give left) ty after) ∧
    Satisfies classes runtimeFull 2 hiddenPair ∧
    Eval classes.erase runtimeFull (.give left) runtimeGivenLeft 0 ∧
    ExprTyped classes partialEnvironment (.give root) partialPair [("p", none)] ∧
    (∀ after, ¬ ExprTyped classes partialEnvironment (.give root) pair after) ∧
    (∀ ty after, ¬ ExprTyped classes partialEnvironment (.new "Box" [.give root]) ty after) ∧
    Eval classes.erase runtimePartial (.new "Box" [.give root])
      (runtimeAfterTake.allocate "Box" ["item"] [2]) 3 ∧
    (∀ before pattern after, ¬ BindingTyped classes before
      (.unpack "Pair" pattern) hiddenPair after) ∧
    ExprTyped twoClasses tokenEnvironment tokenGive token [("t", none)] ∧
    (∀ ty after, ¬ ExprTyped twoClasses [("t", none)] tokenGive ty after) ∧
    (∀ ty after, ¬ ExprTyped twoClasses tokenEnvironment
      (.new "Two" [tokenGive, tokenGive]) ty after) := by
  exact ⟨fun _ _ => failed_take_not_typed (by decide),
    fun _ _ => failed_take_not_typed (by decide), initialized_hidden_field.1,
    initialized_hidden_field.2, partial_give, fun _ => partial_not_whole,
    fun _ _ => partial_constructor_rejected, partial_constructor_executes,
    fun _ _ _ => hidden_unpack_rejected, first_argument_moves,
    fun _ _ => failed_take_not_typed (by decide), fun _ _ => repeated_argument_rejected⟩
-- ANCHOR_END: rejected_moves

end Dada.Unique.Typing.RejectionChecks
