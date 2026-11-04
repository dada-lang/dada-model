import Destructors.Collection
import Functions.Safety

namespace Dada.Destructors
open Shared Shared.Typing
open Functions (Slots heapState from_heap to_heap realized_slots)

theorem DropTyped.statement (typed : DropTyped classes declarations before place core after) :
    StatementTyped classes declarations before core after := by
  cases typed with
  | struct expression structTy => exact .dropStruct expression structTy
  | «class» expression declared signature =>
    apply StatementTyped.call declared (by simp)
    · simpa only [signature, receiver, List.map, FieldType.toType] using
        ArgsTyped.cons expression (.nil expression.wellFormed.2.2)
    · simpa only [signature] using DestinationTyped.none expression.wellFormed.2.2

theorem Satisfies_struct (satisfied : Satisfies classes state reference ty)
    (structTy : StructType classes ty) : StructReference classes.erase state reference := by
  obtain ⟨data, stored, name⟩ := satisfied.root
  obtain ⟨declaration, declared, kind⟩ := structTy.declaration
  exact ⟨data, ⟨declaration.fields.map Prod.fst, declaration.kind⟩, stored,
    List.mem_map.mpr ⟨(ty.base, declaration), lookup_member declared,
      by simp [ValueType.base, name]⟩, kind⟩

theorem Finished.store (finished : Finished classes environment)
    (slots : Slots environment state.variables roots)
    (realized : Realizes classes environment state pending) : StoreFinished classes.erase state := by
  intro name reference member
  have rootMember : reference ∈ roots.map Prod.fst := by
    rw [slots.references]
    exact List.mem_filterMap.mpr ⟨(name, some reference), member, rfl⟩
  obtain ⟨⟨ref, ty⟩, typedMember, equality⟩ := List.mem_map.mp rootMember
  dsimp at equality
  subst ref
  obtain ⟨x, envMember, _⟩ := slots.root typedMember
  have sat := (to_heap realized slots).pendingValues reference ty (List.mem_append_left _ typedMember)
  simpa only [StructReference, heapState] using Satisfies_struct sat (finished x ty envMember)

def RetainsClasses (classes : ClassTable) (before after : Configuration) : Prop :=
  ∀ id data, (id, data) ∈ before.objects →
    ¬ StructType classes (.whole data.className) → (id, data) ∈ after.objects

theorem collect_safely {configuration : Configuration}
    (discardable : ∀ reference ty, (reference, ty) ∈ garbage → StructType classes ty)
    (classesWf : classes.WellFormed) (declarationsWf : DeclarationsTyped classes declarations)
    (shape : StackShape classes declarations configuration.frames roots)
    (realized : Realizes classes [] (heapState configuration.rootState) (roots ++ garbage)) :
    ConfigurationTyped classes declarations configuration.collect ∧
      RetainsClasses classes configuration configuration.collect := by
  refine ⟨collect_typed classesWf declarationsWf shape realized, ?_⟩
  intro id data stored classObject
  have retained := collectPending_retains_classes realized discardable stored classObject
  rwa [collect_heap shape] at retained

theorem ResultTyped.exists_eval (typed : ResultTyped classes environment value result final)
    (realized : Realizes classes environment state pending) :
    ∃ evaluated reference, ResultEval classes.erase state value evaluated reference ∧
      reference.isSome = result.isSome := by
  cases typed with
  | none _ => exact ⟨state,Option.none,.none _,rfl⟩
  | some expression =>
    obtain ⟨evaluated,reference,evaluation⟩ := (expression.sound _ _ realized).1
    exact ⟨evaluated,Option.some reference,.some evaluation,rfl⟩

theorem DestinationTyped.exists_deliver
    (typed : DestinationTyped classes environment destination result after)
    (slots : Slots environment variables roots)
    (shape : reference.isSome = result.isSome) :
    ∃ delivered, Deliver variables destination reference delivered := by
  cases typed with
  | none _ => cases reference <;> simp at shape; exact ⟨variables,.none _⟩
  | some binding =>
    cases reference with
    | none => cases shape
    | some reference =>
      cases binding with
      | «variable» _ _ fresh =>
        exact ⟨_,.some (slots.keys ▸ fresh)⟩

theorem binding_keys (typed : BindingTyped classes before pattern ty after)
    (operation : Unpacking.Bind classes.erase state reference pattern result)
    (keys : before.map Prod.fst = state.variables.map Prod.fst) :
    after.map Prod.fst = result.variables.map Prod.fst := by
  cases typed with
  | «variable» _ _ _ => cases operation; simp [State.bind, keys]
  | unpack _ _ _ _ _ _ _ _ fields _ =>
    cases operation with
    | unpack _ _ _ _ _ transfer => simp [List.map_append, fields.keys, transfer.keys, keys]

theorem parameter_slots (parameters : List Parameter) (references : List Reference)
    (lengths : references.length = parameters.length) :
    Slots (Functions.Signature.environment ⟨parameters,result⟩) (parameterStore parameters references)
      (references.zip (parameters.map (fun p => p.type.toType))) := by
  induction parameters generalizing references with
  | nil => have : references = [] := List.length_eq_zero_iff.mp lengths; subst references; exact .nil
  | cons parameter parameters ih =>
    cases references with
    | nil => simp at lengths
    | cons reference references =>
      exact .value parameter.name reference parameter.type.toType (ih references (Nat.succ.inj lengths))

def resultRoots (reference : Option Reference) (result : Option FieldType) : PendingValues :=
  reference.toList.zip (result.toList.map FieldType.toType)

theorem ResultTyped.preserves (typed : ResultTyped classes before value result after)
    (realized : Realizes classes before state pending)
    (evaluation : ResultEval classes.erase state value evaluated reference) :
    Realizes classes after evaluated (resultRoots reference result ++ pending) ∧
      after.map Prod.fst = before.map Prod.fst ∧ evaluated.variables.map Prod.fst = state.variables.map Prod.fst := by
  cases typed with
  | none _ => cases evaluation; exact ⟨realized,rfl,rfl⟩
  | some expression =>
    cases evaluation with
    | some evaluation => exact ⟨(expression.sound _ _ realized).2 _ _ evaluation,expression.keys,evaluation.variable_keys⟩

theorem DestinationTyped.preserves (typed : DestinationTyped classes before destination result after)
    (realized : Realizes classes before ⟨objects,variables,nextId⟩ (resultRoots reference result ++ pending))
    (keys : before.map Prod.fst = variables.map Prod.fst)
    (delivery : Deliver variables destination reference delivered) :
    Realizes classes after ⟨objects,delivered,nextId⟩ pending ∧ after.map Prod.fst = delivered.map Prod.fst := by
  cases typed with
  | none _ => cases delivery; exact ⟨realized,keys⟩
  | some binding =>
    cases delivery with
    | some fresh =>
      exact ⟨binding.preserves_realization_pending realized (.variable fresh),
        by simpa [State.bind] using (binding_keys (state := ⟨objects,variables,nextId⟩)
          (reference := .owned 0) binding (.variable fresh) keys)⟩

theorem ConfigurationTyped.progress {configuration : Configuration}
    (typed : ConfigurationTyped classes declarations configuration) :
    configuration.finished ∨ ∃ after, Step classes.erase declarations configuration after := by
  rcases configuration with ⟨objects,nextId,frames⟩
  obtain ⟨classesWf,declarationsWf,roots,shape,heap⟩ := typed
  cases shape with
  | done => exact .inl rfl
  | @active frame rest environment localRoots laterRoots result slots envWf body continuation =>
    have realized := from_heap heap slots envWf
    rcases frame with ⟨variables,frameBody,destination⟩
    rcases frameBody with ⟨code,returnValue⟩
    obtain ⟨middle,final,sequence,returned,finished⟩ := body
    right
    cases code with
    | cons first restCode =>
      cases sequence with
      | cons firstTyped tail =>
        cases firstTyped with
        | «local» localTyped =>
          cases localTyped with
          | letValue expression binding =>
            obtain ⟨evaluated,reference,evaluation⟩ := (expression.sound _ _ realized).1
            have evaluatedRealized := (expression.sound _ _ realized).2 _ _ evaluation
            obtain ⟨after,operation⟩ := binding.exists_bind_pending evaluatedRealized
            exact ⟨_,.collect (.local (.letValue evaluation operation))⟩
        | call declared fresh args dest =>
          obtain ⟨evaluated,references,evaluation⟩ := (args.sound _ _ realized).1
          exact ⟨_,.collect (.call declared dest.shape
            (fun x member occupied => fresh x member ((realized.variableDomain x).mpr occupied))
            evaluation (by simpa using evaluation.length.trans args.length))⟩
        | dropStruct expression structTy =>
          obtain ⟨evaluated,reference,evaluation⟩ := (expression.sound _ _ realized).1
          have evaluatedRealized := (expression.sound _ _ realized).2 _ _ evaluation
          exact ⟨_, .collect (.dropStruct evaluation
            (Satisfies_struct (evaluatedRealized.pendingValues _ _ (by simp)) structTy))⟩
    | nil =>
      cases sequence with
      | nil _ =>
        obtain ⟨evaluated,reference,evaluation,resultShape⟩ := returned.exists_eval realized
        cases continuation with
        | done =>
          cases returned with
          | none _ => exact ⟨_,.collect (.exit (finished.store slots realized))⟩
        | caller callerSlots _ delivery _ _ =>
          obtain ⟨variables,delivered⟩ := delivery.exists_deliver callerSlots resultShape
          obtain ⟨evaluatedRealized,staticKeys,runtimeKeys⟩ := returned.preserves realized evaluation
          obtain ⟨discarded,discardedSlots⟩ := realized_slots evaluatedRealized
            (staticKeys.trans (slots.keys.trans runtimeKeys.symm))
          exact ⟨_,.collect (.return evaluation delivered (finished.store discardedSlots evaluatedRealized))⟩

theorem evalArgs_keys (evaluation : EvalArgs classes before arguments after references) :
    after.variables.map Prod.fst = before.variables.map Prod.fst := by
  induction evaluation using EvalArgs.rec (motive_1 := fun _ _ _ _ _ => True) with
  | give => trivial
  | giveShare => trivial
  | new => trivial
  | nil => rfl
  | cons first _ _ ih => exact ih.trans first.variable_keys

theorem RawStep.sound {before after : Configuration}
    (typed : ConfigurationTyped classes declarations before)
    (step : RawStep classes.erase declarations before after) :
    ConfigurationTyped classes declarations after.collect ∧ RetainsClasses classes after after.collect := by
  obtain ⟨classesWf,declarationsWf,roots,shape,heap⟩ := typed
  cases step with
  | @«local» beforeState afterState statement rest result frames destination operation =>
    cases shape with
    | active slots envWf body continuation =>
      obtain ⟨middle,final,sequence,returned,finished⟩ := body
      cases sequence with
      | cons first tail =>
        cases first with
        | «local» localTyped =>
          cases localTyped with
          | letValue expression binding =>
            cases operation with
            | letValue evaluation bound =>
              have realized := from_heap heap slots envWf
              have evaluated := (expression.sound _ _ realized).2 _ _ evaluation
              have afterRealized := binding.preserves_realization_pending evaluated bound
              have keys := binding_keys binding bound
                (expression.keys.trans (slots.keys.trans evaluation.variable_keys.symm))
              obtain ⟨afterRoots,afterSlots⟩ := realized_slots afterRealized keys
              have afterHeap := to_heap afterRealized afterSlots
              apply collect_safely (garbage := []) (by simp) classesWf declarationsWf
                (.active (frame := ⟨afterState.variables,⟨rest,result⟩,destination⟩) afterSlots afterRealized.environmentWellFormed ⟨middle,final,tail,returned,finished⟩ continuation)
              simpa only [List.append_nil,heapState,Configuration.rootState,Configuration.running] using afterHeap
  | @call beforeState evaluated destination name arguments rest result frames returnTo declaration references
      declared resultShape fresh evaluation lengths =>
    cases shape with
    | active slots envWf body continuation =>
      obtain ⟨middle,final,sequence,returned,finished⟩ := body
      cases sequence with
      | cons first tail =>
        cases first with
        | call expectedMember _ args delivery =>
          have same := member_value_unique declarationsWf.1 expectedMember declared
          cases same
          have realized := from_heap heap slots envWf
          have evaluatedRealized := (args.sound _ _ realized).2 _ _ evaluation
          have keys := args.keys.trans (slots.keys.trans (evalArgs_keys evaluation).symm)
          obtain ⟨callerRoots,callerSlots⟩ := realized_slots evaluatedRealized keys
          have callerHeap := to_heap evaluatedRealized callerSlots
          obtain ⟨signatureWf,calleeBody⟩ := declarationsWf.2 _ declared
          have calleeSlots := parameter_slots (result := declaration.signature.result) declaration.signature.parameters references lengths
          have calleeWf := (BodyFrom.of_declaration calleeBody).sequence_wf
          apply collect_safely (garbage := []) (by simp) classesWf declarationsWf
            (.active (frame := ⟨parameterStore declaration.signature.parameters references,declaration.body,destination⟩) calleeSlots calleeWf calleeBody
              (.caller (caller := ⟨evaluated.variables,⟨rest,result⟩,returnTo⟩) callerSlots evaluatedRealized.environmentWellFormed delivery
                ⟨middle,final,tail,returned,finished⟩ continuation))
          apply callerHeap.perm
          simp only [List.map_map, Function.comp_def, List.append_nil]
          apply List.Perm.trans (List.Perm.of_eq (List.append_assoc _ _ _).symm)
          apply List.Perm.trans (List.perm_append_comm.append_right _)
          exact List.Perm.of_eq (List.append_assoc _ _ _)
  | @dropStruct beforeState evaluated place reference rest result frames destination evaluation _ =>
    cases shape with
    | active slots envWf body continuation =>
      obtain ⟨middle,final,sequence,returned,finished⟩ := body
      cases sequence with
      | cons first tail =>
        cases first with
        | dropStruct expression structTy =>
          have realized := from_heap heap slots envWf
          have evaluatedRealized := (expression.sound _ _ realized).2 _ _ evaluation
          have keys := expression.keys.trans (slots.keys.trans evaluation.variable_keys.symm)
          obtain ⟨afterRoots,afterSlots⟩ := realized_slots evaluatedRealized keys
          have afterHeap := to_heap evaluatedRealized afterSlots
          apply collect_safely (garbage := [(reference, _)]) (by
            intro ref ty member; cases List.mem_singleton.mp member; exact structTy) classesWf declarationsWf
            (.active (frame := ⟨evaluated.variables,⟨rest,result⟩,destination⟩) afterSlots
              evaluatedRealized.environmentWellFormed ⟨middle,final,tail,returned,finished⟩ continuation)
          apply afterHeap.perm
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using
            (List.perm_append_comm (l₁ := [(reference, _)])).append_left afterRoots
  | @«return» beforeState evaluated result reference caller frames destination variables evaluation delivered _ =>
    cases shape with
    | active slots envWf body continuation =>
      obtain ⟨middle,final,sequence,returned,finished⟩ := body
      cases sequence with
      | nil _ =>
        cases continuation with
        | @caller _ _ _ _ callerEnvironment resumed callerRoots laterRoots callerResult callerSlots callerWf delivery callerBody rest =>
          have realized := from_heap heap slots envWf
          obtain ⟨evaluatedRealized,staticKeys,runtimeKeys⟩ := returned.preserves realized evaluation
          obtain ⟨discarded,discardedSlots⟩ := realized_slots evaluatedRealized
            (staticKeys.trans (slots.keys.trans runtimeKeys.symm))
          have calleeHeap := to_heap evaluatedRealized discardedSlots
          have callerHeap := calleeHeap.perm (show
              (discarded ++ (resultRoots reference _ ++ (callerRoots ++ laterRoots))).Perm
              (callerRoots ++ (resultRoots reference _ ++ (laterRoots ++ discarded))) from by
            exact List.perm_append_comm.trans (by
              simpa only [List.append_assoc] using
                (List.perm_append_comm (l₁ := resultRoots reference _) (l₂ := callerRoots)).append_right (laterRoots ++ discarded)))
          have callerRealized := from_heap callerHeap callerSlots callerWf
          obtain ⟨resumedRealized,resumedKeys⟩ := delivery.preserves callerRealized callerSlots.keys delivered
          obtain ⟨resumedRoots,resumedSlots⟩ := realized_slots resumedRealized resumedKeys
          have resumedHeap := to_heap resumedRealized resumedSlots
          apply collect_safely (fun ref ty member => by
            obtain ⟨name, envMember, _⟩ := discardedSlots.root member
            exact finished name ty envMember) classesWf declarationsWf (.active (frame := ⟨variables,caller.body,caller.destination⟩) resumedSlots resumedRealized.environmentWellFormed callerBody rest)
          simpa only [List.append_assoc,heapState,Configuration.rootState,Configuration.running] using resumedHeap
  | exit _ =>
    cases shape with
    | active slots envWf body continuation =>
      cases continuation with
      | done =>
        obtain ⟨middle,final,sequence,returned,finished⟩ := body
        cases sequence with
        | nil _ =>
          cases returned with
          | none _ =>
            apply collect_safely (roots := []) (fun ref ty member => by
              obtain ⟨name, envMember, _⟩ := slots.root (by simpa only [List.append_nil] using member)
              exact finished name ty envMember) classesWf declarationsWf .done
            simpa only [List.append_nil, List.nil_append, heapState, Configuration.rootState, Configuration.running] using heap

theorem ConfigurationTyped.preservation {before after : Configuration}
    (typed : ConfigurationTyped classes declarations before)
    (step : Step classes.erase declarations before after) :
    ConfigurationTyped classes declarations after := by
  cases step with
  | collect raw => exact (raw.sound typed).1

theorem ConfigurationTyped.trace {before after : Configuration}
    (typed : ConfigurationTyped classes declarations before)
    (trace : Steps classes.erase declarations before after) :
    ConfigurationTyped classes declarations after := by
  induction trace with
  | refl => exact typed
  | step first _ ih => exact ih (typed.preservation first)

theorem ConfigurationTyped.finished_heap_empty {configuration : Configuration}
    (typed : ConfigurationTyped classes declarations configuration)
    (finished : configuration.finished) : configuration.objects = [] := by
  rcases configuration with ⟨objects,nextId,frames⟩
  change frames = [] at finished
  subst frames
  obtain ⟨_,_,roots,shape,heap⟩ := typed
  cases shape
  have same := State.collect_eq_self heap.ownership.no_pending
  rw [heapState,State.collect_no_variables] at same
  exact (congrArg State.objects same).symm

-- Owners retain their multiplicity: two distinct slots holding the same
-- shared reference count twice. Frame-local names need not be globally unique.
theorem ConfigurationTyped.ownership {configuration : Configuration}
    (typed : ConfigurationTyped classes declarations configuration) :
    (Owners configuration.rootState).Pairwise Compatible ∧
    (∀ id, id ∈ References configuration.rootState ↔ Allocated configuration.rootState id) := by
  obtain ⟨_,_,roots,shape,heap⟩ := typed
  have refs := shape.references
  constructor
  · simpa only [Owners,heapState,List.filterMap_nil,List.nil_append,refs,
      Configuration.rootState] using heap.ownership.ownersCompatible
  · intro id
    have complete := heap.ownership.referencesComplete id
    simpa only [heapState,References,List.filterMap_nil,List.nil_append,refs,
      Configuration.rootState,Allocated,List.map_append,List.map_filterMap,Function.comp_def] using complete

theorem program_safety (typed : ProgramTyped program)
    (trace : Steps program.classes.erase program.declarations (.initial program) configuration) :
    ConfigurationTyped program.classes program.declarations configuration ∧
    (configuration.finished ∨ ∃ after, Step program.classes.erase program.declarations configuration after) ∧
    ¬ Stuck program.classes.erase program.declarations configuration := by
  have preserved := (ConfigurationTyped.initial typed).trace trace
  have progress := preserved.progress
  refine ⟨preserved,progress,?_⟩
  intro stuck
  rcases progress with finished | successor
  · exact stuck.1 finished
  · exact stuck.2 successor

end Dada.Destructors
