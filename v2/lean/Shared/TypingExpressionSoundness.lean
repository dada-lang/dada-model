import Shared.TypingAllocation

namespace Dada.Shared.Typing

-- These statements quantify over arbitrary heaps realizing the static input,
-- including previously evaluated arguments held outside the variable store.
def ExpressionSound (classes : ClassTable) (before : Environment) (value : Value)
    (ty : ValueType) (after : Environment) : Prop :=
  ∀ state pending, Realizes classes before state pending →
    (∃ result object, Eval classes.erase state value result object) ∧
    (∀ result object, Eval classes.erase state value result object →
      Realizes classes after result ((object, ty) :: pending))

def ArgumentsSound (classes : ClassTable) (before : Environment) (values : List Value)
    (fields : List FieldType) (after : Environment) : Prop :=
  ∀ state pending, Realizes classes before state pending →
    (∃ result objects, EvalArgs classes.erase state values result objects) ∧
    (∀ result objects, EvalArgs classes.erase state values result objects →
      Realizes classes after result (objects.zip (fields.map FieldType.toType) ++ pending))

-- The induction isolates the move lemma: construction and weakening need no
-- additional assumptions about how a place is represented or traversed.
theorem ExprTyped.sound_of_give
    (giveSound : ∀ before place ty after, before.WellFormed classes →
      Typing.give classes before place = some (ty, after) → Admissible classes ty →
      after.WellFormed classes → ExpressionSound classes before (.give place) ty after)
    (typed : ExprTyped classes before value ty after) :
    ExpressionSound classes before value ty after := by
  induction typed using ExprTyped.rec
    (motive_2 := fun before values fields after _ => ArgumentsSound classes before values fields after) with
  | give wf taken admissible afterWf => exact giveSound _ _ _ _ wf taken admissible afterWf
  | @giveShare before after place ty wf taken admissible afterWf structTy =>
    intro state pending realized
    obtain ⟨existsGive, allGive⟩ := giveSound _ _ _ _ wf taken admissible afterWf state pending realized
    constructor
    · obtain ⟨result, reference, evaluated⟩ := existsGive
      cases evaluated with
      | give given =>
        have sat := (allGive result reference (.give given)).pendingValues reference ty (by simp)
        obtain ⟨data, stored, name⟩ := sat.root
        obtain ⟨declaration, declared, kind⟩ := structTy.declaration
        exact ⟨result, .shared reference.object, .giveShare given
          ⟨data, ⟨declaration.fields.map Prod.fst, declaration.kind⟩, stored,
            List.mem_map.mpr ⟨(ty.base, declaration), lookup_member declared, by simp [ValueType.base, name]⟩,
            kind⟩⟩
    · intro result reference evaluation
      cases evaluation with
      | giveShare given _ =>
        exact (allGive result _ (.give given)).share_pending structTy
  | @new before after name declaration arguments declared args admissible structFields ih =>
    intro state pending realized
    have erased : (name, Class.mk (declaration.fields.map Prod.fst) declaration.kind) ∈ classes.erase :=
      List.mem_map.mpr ⟨(name, declaration), declared, rfl⟩
    obtain ⟨existsArgs, allArgs⟩ := ih state pending realized
    constructor
    · obtain ⟨evaluated, objects, evaluatedArgs⟩ := existsArgs
      have current := allArgs evaluated objects evaluatedArgs
      have lengths : objects.length = declaration.fields.length := by
        have argumentLengths := args.length
        have resultLengths := evaluatedArgs.length
        simpa using resultLengths.trans argumentLengths
      exact ⟨_, _, .new erased evaluatedArgs (by simpa using lengths) current.next_fresh (by
        intro isStruct reference member
        have views : ArgumentsSatisfy classes evaluated declaration.fields objects :=
          ArgumentsSatisfy.of_pending lengths (fun object ty pair =>
            current.pendingValues object ty (List.mem_append_left _ (by
              simpa only [List.map_map, Function.comp_def] using pair)))
        obtain ⟨entry, entryMember, sat⟩ := views.reference member
        obtain ⟨data, stored, nameEq⟩ := sat.root
        obtain ⟨target, targetDeclared, targetKind⟩ := (structFields isStruct entry entryMember).declaration
        exact ⟨data, ⟨target.fields.map Prod.fst, target.kind⟩, stored,
          List.mem_map.mpr ⟨(_, target), lookup_member targetDeclared, by simp [ValueType.base, FieldType.toType, ValueType.whole] at nameEq ⊢; exact nameEq.symm⟩,
          targetKind⟩)⟩
    · intro result object evaluation
      cases evaluation with
      | new runtimeDeclared evaluatedArgs lengths _ _ =>
        have same := member_value_unique realized.classesWellFormed.erase.1 runtimeDeclared erased
        cases same
        have current := allArgs _ _ evaluatedArgs
        simp only [List.map_map, Function.comp_def] at current
        exact current.allocate declared admissible (by simpa using lengths)
  | @weaken before after value ty other typed admissible subtype ih =>
    intro state pending realized
    obtain ⟨existsEval, allEval⟩ := ih state pending realized
    exact ⟨existsEval, fun result object evaluated =>
      (allEval result object evaluated).weaken_pending admissible subtype⟩
  | nil wf =>
    intro state pending realized
    refine ⟨⟨state, [], .nil state⟩, ?_⟩
    intro result objects evaluation
    cases evaluation
    exact realized
  | @cons before middle after value values field fields typed args first rest =>
    intro state pending realized
    obtain ⟨existsFirst, allFirst⟩ := first state pending realized
    constructor
    · obtain ⟨middleState, object, evaluatedFirst⟩ := existsFirst
      obtain ⟨⟨result, objects, evaluatedRest⟩, _⟩ :=
        rest middleState ((object, field.toType) :: pending)
          (allFirst middleState object evaluatedFirst)
      exact ⟨result, object :: objects, .cons evaluatedFirst evaluatedRest⟩
    · intro result objects evaluation
      cases evaluation with
      | cons evaluatedFirst evaluatedRest =>
        have firstRealized := allFirst _ _ evaluatedFirst
        have restRealized := (rest _ _ firstRealized).2 _ _ evaluatedRest
        exact restRealized.perm List.perm_middle

end Dada.Shared.Typing
