import Assignment.Typing
import Shared.TypingGiveSoundness
import Shared.TypingBindingPending

namespace Dada.Assignment
open Shared Shared.Typing

theorem ExprTyped.erase (typed : ExprTyped classes before value ty after) :
    Shared.Typing.ExprTyped classes before.current value ty after.current := by
  cases typed with
  | lift _ expression _ => exact expression

theorem ExprTyped.wellFormed (typed : ExprTyped classes before value ty after) :
    before.WellFormed classes ∧ Admissible classes ty ∧ after.WellFormed classes := by
  cases typed with
  | lift beforeWf expression afterWf => exact ⟨beforeWf,expression.wellFormed.2.1,afterWf⟩

theorem ExprTyped.keys (typed : ExprTyped classes before value ty after) :
    after.current.map Prod.fst = before.current.map Prod.fst := typed.erase.keys

theorem ExprTyped.sound (typed : ExprTyped classes before value ty after) :
    ExpressionSound classes before.current value ty after.current := typed.erase.sound

theorem ExprTyped.singletonArgs (typed : ExprTyped classes before value field.toType after) :
    ArgsTyped classes before [value] [field] after := by
  cases typed with
  | lift beforeWf expression afterWf =>
    exact .lift beforeWf (.cons expression (.nil afterWf.1)) afterWf

theorem ArgsTyped.erase (typed : ArgsTyped classes before values types after) :
    Shared.Typing.ArgsTyped classes before.current values types after.current := by
  cases typed with
  | lift _ arguments _ => exact arguments

theorem ArgsTyped.wellFormed (typed : ArgsTyped classes before values types after) :
    before.WellFormed classes ∧ after.WellFormed classes := by
  cases typed with
  | lift beforeWf _ afterWf => exact ⟨beforeWf,afterWf⟩

theorem ArgsTyped.keys (typed : ArgsTyped classes before values types after) :
    after.current.map Prod.fst = before.current.map Prod.fst := typed.erase.keys

theorem ArgsTyped.length (typed : ArgsTyped classes before values types after) :
    values.length = types.length := typed.erase.length

theorem ArgsTyped.sound (typed : ArgsTyped classes before values types after) :
    ArgumentsSound classes before.current values types after.current := typed.erase.sound

theorem BindingTyped.erase (typed : BindingTyped classes before pattern ty after) :
    Shared.Typing.BindingTyped classes before.current pattern ty after.current := by
  cases typed with
  | lift _ binding _ _ => exact binding

theorem BindingTyped.wellFormed (typed : BindingTyped classes before pattern ty after) :
    before.WellFormed classes ∧ after.WellFormed classes := by
  cases typed with
  | lift beforeWf _ _ afterWf => exact ⟨beforeWf,afterWf⟩

theorem BindingTyped.exists_bind_pending
    (typed : BindingTyped classes before pattern ty after)
    (realized : Realizes classes before.current state ((reference,ty) :: pending)) :
    ∃ result, Unpacking.Bind classes.erase state reference pattern result :=
  typed.erase.exists_bind_pending realized

theorem BindingTyped.preserves_realization_pending
    (typed : BindingTyped classes before pattern ty after)
    (realized : Realizes classes before.current state ((reference,ty) :: pending))
    (operation : Unpacking.Bind classes.erase state reference pattern result) :
    Realizes classes after.current result pending :=
  typed.erase.preserves_realization_pending realized operation

theorem LocalTyped.wellFormed (typed : LocalTyped classes before statement after) :
    before.WellFormed classes ∧ after.WellFormed classes := by
  cases typed with
  | letValue expression binding => exact ⟨expression.wellFormed.1,binding.wellFormed.2⟩

theorem DestinationTyped.shape
    (typed : DestinationTyped classes before destination result after) :
    DestinationMatches destination result := by
  cases typed <;> rfl

theorem DestinationTyped.wellFormed
    (typed : DestinationTyped classes before destination result after) :
    before.WellFormed classes ∧ after.WellFormed classes := by
  cases typed with
  | none wf => exact ⟨wf,wf⟩
  | some binding => exact binding.wellFormed

theorem store_keys (beforeWf : before.WellFormed classes)
    (stored : store classes before place ty = some after) :
    after.current.map Prod.fst = before.current.map Prod.fst := by
  rw [← (store_wellFormed stored).2.1, store_preserves_bindings stored]
  exact beforeWf.2.1

theorem SequenceTyped.wellFormed (typed : SequenceTyped classes declarations before code after) :
    before.WellFormed classes ∧ after.WellFormed classes := by
  induction typed with
  | nil wf => exact ⟨wf,wf⟩
  | cons first _ ih =>
    refine ⟨?_,ih.2⟩
    cases first with
    | «local» typed => exact typed.wellFormed.1
    | call _ _ args _ => exact args.wellFormed.1
    | store expression _ => exact expression.wellFormed.1
    | dropStruct expression _ => exact expression.wellFormed.1

end Dada.Assignment
