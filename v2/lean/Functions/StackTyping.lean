import Functions.Realization

namespace Dada.Functions
open Shared Shared.Typing

-- The active body's final expression has this result type; no termination
-- condition is imposed on recursive calls.
def BodyFrom (classes : ClassTable) (declarations : Declarations) (environment : Environment)
    (body : Body) (result : Option FieldType) : Prop :=
  ∃ middle final, SequenceTyped classes declarations environment body.statements middle ∧
    ResultTyped classes middle body.result result final

-- A suspended caller is checked starting with the environment that delivery
-- will produce, while its stored locals realize the environment before delivery.
inductive ContinuationTyped (classes : ClassTable) (declarations : Declarations) : Option VariableId → Option FieldType → List Frame → PendingValues → Prop where
  | done : ContinuationTyped classes declarations none none [] []
  | caller {destination result caller rest environment resumed roots laterRoots callerResult} :
      Slots environment caller.variables roots → environment.WellFormed classes →
      DestinationTyped classes environment destination result resumed →
      BodyFrom classes declarations resumed caller.body callerResult →
      ContinuationTyped classes declarations caller.destination callerResult rest laterRoots →
      ContinuationTyped classes declarations destination result (caller :: rest) (roots ++ laterRoots)

inductive StackShape (classes : ClassTable) (declarations : Declarations) : List Frame → PendingValues → Prop where
  | done : StackShape classes declarations [] []
  | active {frame rest environment roots laterRoots result} :
      Slots environment frame.variables roots → environment.WellFormed classes →
      BodyFrom classes declarations environment frame.body result →
      ContinuationTyped classes declarations frame.destination result rest laterRoots →
      StackShape classes declarations (frame :: rest) (roots ++ laterRoots)

def ConfigurationTyped (classes : ClassTable) (declarations : Declarations) (configuration : Configuration) : Prop :=
  classes.WellFormed ∧ DeclarationsTyped classes declarations ∧
  ∃ roots, StackShape classes declarations configuration.frames roots ∧
    Realizes classes [] (heapState configuration.rootState) roots

theorem ContinuationTyped.references (typed : ContinuationTyped classes declarations destination result frames roots) :
    roots.map Prod.fst = (frames.flatMap Frame.variables).filterMap Prod.snd := by
  induction typed with
  | done => rfl
  | caller slots _ _ _ _ ih => simp [List.filterMap_append, slots.references, ih]

theorem StackShape.references (typed : StackShape classes declarations frames roots) :
    roots.map Prod.fst = (frames.flatMap Frame.variables).filterMap Prod.snd := by
  cases typed with
  | done => rfl
  | active slots _ _ continuation => simp [List.filterMap_append, slots.references, continuation.references]

theorem reachable_iff_live (state : State) (roots : List Reference)
    (same : roots = state.variables.filterMap Prod.snd) :
    Reachable state.objects roots object ↔ Live state object := by
  constructor
  · intro reached
    induction reached with
    | root member =>
      rw [same] at member
      obtain ⟨⟨name,slot⟩,stored,value⟩ := List.mem_filterMap.mp member
      change slot = some _ at value
      subst slot; exact .variable stored
    | field _ stored field ih => exact .field ih stored field
  · intro live
    induction live with
    | «variable» stored => exact .root (same ▸ List.mem_filterMap.mpr ⟨_,stored,rfl⟩)
    | field _ stored field ih => exact .field ih stored field

theorem collect_heap {configuration : Configuration} (shape : StackShape classes declarations configuration.frames roots) :
    collectPending (heapState configuration.rootState) roots = heapState configuration.collect.rootState := by
  classical
  have live (id : ObjectId) :
      Reachable configuration.objects (roots.map Prod.fst) id ↔ Live configuration.rootState id :=
    reachable_iff_live (object := id) configuration.rootState (roots.map Prod.fst) shape.references
  simp only [collectPending, heapState, rootReferences, List.filterMap_nil, List.append_nil,
    Configuration.collect, Configuration.rootState, State.collect]
  congr 1
  apply List.filter_congr
  intro entry member
  exact propext (live entry.1) ▸ rfl

theorem collect_typed {configuration : Configuration} (classesWf : classes.WellFormed) (declarationsWf : DeclarationsTyped classes declarations)
    (shape : StackShape classes declarations configuration.frames roots)
    (realized : Realizes classes [] (heapState configuration.rootState) (roots ++ garbage)) :
    ConfigurationTyped classes declarations configuration.collect := by
  refine ⟨classesWf,declarationsWf,roots,?_,?_⟩
  · simpa using shape
  · have kept := realized.collect_pending (List.sublist_append_left roots garbage)
    rwa [collect_heap shape] at kept

theorem BodyFrom.of_declaration (typed : BodyTyped classes declarations signature body) :
    BodyFrom classes declarations signature.environment body signature.result := typed

theorem SequenceTyped.wellFormed (typed : SequenceTyped classes declarations before code after) :
    before.WellFormed classes ∧ after.WellFormed classes := by
  induction typed with
  | nil wf => exact ⟨wf,wf⟩
  | cons first _ ih =>
    constructor
    · cases first with
      | «local» t => exact t.wellFormed.1
      | call _ _ args _ => exact args.wellFormed.1
    · exact ih.2

theorem BodyFrom.sequence_wf (typed : BodyFrom classes declarations environment body result) :
    environment.WellFormed classes := by
  obtain ⟨middle,final,sequence,_⟩ := typed
  exact sequence.wellFormed.1

theorem ConfigurationTyped.initial (typed : ProgramTyped program) :
    ConfigurationTyped program.classes program.declarations (.initial program) := by
  obtain ⟨classesWf,declarationsWf,final,sequence⟩ := typed
  have finalWf := sequence.wellFormed.2
  refine ⟨classesWf,declarationsWf,[],?_,Realizes.empty classesWf⟩
  exact .active (frame := ⟨[], ⟨program.main,none⟩,none⟩) .nil (by simp [Environment.WellFormed])
    ⟨final,final,sequence,.none finalWf⟩ .done

end Dada.Functions
