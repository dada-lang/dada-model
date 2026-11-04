import Functions.Typing
import Shared.TypingSafety
import Shared.TypingCollection

namespace Dada.Functions
open Shared Shared.Typing

-- A store and its environment describe the same ordered slots. The third
-- index lists exactly the initialized references, decorated with their types.
inductive Slots : Environment → Store → PendingValues → Prop where
  | nil : Slots [] [] []
  | empty {environment variables roots} (name) : Slots environment variables roots →
      Slots ((name, none) :: environment) ((name, none) :: variables) roots
  | value {environment variables roots} (name reference ty) : Slots environment variables roots →
      Slots ((name, some ty) :: environment) ((name, some reference) :: variables) ((reference, ty) :: roots)

theorem Slots.keys (slots : Slots environment variables roots) :
    environment.map Prod.fst = variables.map Prod.fst := by
  induction slots <;> simp_all

theorem Slots.references (slots : Slots environment variables roots) :
    roots.map Prod.fst = variables.filterMap Prod.snd := by
  induction slots <;> simp_all

theorem Slots.root (slots : Slots environment variables roots) (member : (reference, ty) ∈ roots) :
    ∃ name, (name, some ty) ∈ environment ∧ (name, some reference) ∈ variables := by
  induction slots with
  | nil => simp at member
  | empty name _ ih =>
    obtain ⟨name', e, v⟩ := ih member
    exact ⟨name', List.mem_cons_of_mem _ e, List.mem_cons_of_mem _ v⟩
  | value name ref type _ ih =>
    rcases List.mem_cons.mp member with same | later
    · cases same; exact ⟨name, by simp, by simp⟩
    · obtain ⟨name', e, v⟩ := ih later
      exact ⟨name', List.mem_cons_of_mem _ e, List.mem_cons_of_mem _ v⟩

theorem Slots.empty_slot (slots : Slots environment variables roots) (member : (name, none) ∈ environment) :
    (name, none) ∈ variables := by
  induction slots with
  | nil => simp at member
  | empty x _ ih =>
    rcases List.mem_cons.mp member with same | later
    · cases same; simp
    · exact List.mem_cons_of_mem _ (ih later)
  | value x ref ty _ ih =>
    rcases List.mem_cons.mp member with same | later
    · cases same
    · exact List.mem_cons_of_mem _ (ih later)

theorem Slots.initialized (slots : Slots environment variables roots) (member : (name, some ty) ∈ environment) :
    ∃ reference, (name, some reference) ∈ variables ∧ (reference, ty) ∈ roots := by
  induction slots with
  | nil => simp at member
  | empty x _ ih =>
    rcases List.mem_cons.mp member with same | later
    · cases same
    · obtain ⟨r,v,p⟩ := ih later; exact ⟨r,List.mem_cons_of_mem _ v,p⟩
  | value x ref type _ ih =>
    rcases List.mem_cons.mp member with same | later
    · cases same; exact ⟨ref,by simp,by simp⟩
    · obtain ⟨r,v,p⟩ := ih later
      exact ⟨r,List.mem_cons_of_mem _ v,List.mem_cons_of_mem _ p⟩

inductive Paired (R : A → B → Prop) : List A → List B → Prop where
  | nil : Paired R [] []
  | cons {a b as bs} : R a b → Paired R as bs → Paired R (a :: as) (b :: bs)

theorem Slots.exists_of_matches
    (keys : environment.map Prod.fst = variables.map Prod.fst)
    (matchedSlots : Paired (fun e v => e.1 = v.1 ∧ SlotMatches classes state v.2 e.2) environment variables) :
    ∃ roots, Slots environment variables roots := by
  induction matchedSlots with
  | nil => exact ⟨[], .nil⟩
  | @cons e v es vs first rest ih =>
    obtain ⟨same, matched⟩ := first
    obtain ⟨roots, tail⟩ := ih (List.cons.inj keys).2
    rcases e with ⟨name,ty⟩; rcases v with ⟨name',ref⟩
    simp only at same; subst name'
    cases ty <;> cases ref <;> simp only [SlotMatches] at matched
    · exact ⟨roots, .empty name tail⟩
    · exact ⟨_, .value _ _ _ tail⟩

theorem realized_slots (realized : Realizes classes environment state pending)
    (keys : environment.map Prod.fst = state.variables.map Prod.fst) :
    ∃ roots, Slots environment state.variables roots := by
  apply Slots.exists_of_matches keys
  have paired : ∀ (es : Environment) (vs : Store),
      es.map Prod.fst = vs.map Prod.fst →
      (∀ entry ∈ es, entry ∈ environment) → (∀ entry ∈ vs, entry ∈ state.variables) →
      Paired (fun e v => e.1 = v.1 ∧ SlotMatches classes state v.2 e.2) es vs := by
    intro es
    induction es with
    | nil => intro vs key _ _; have : vs = [] := List.length_eq_zero_iff.mp (by simpa using congrArg List.length key.symm); subst vs; exact .nil
    | cons e es ih =>
      intro vs key subE subV
      cases vs with
      | nil => simp at key
      | cons v vs =>
        have same := (List.cons.inj key).1
        refine .cons ⟨same, ?_⟩ (ih vs (List.cons.inj key).2
          (fun entry h => subE entry (List.mem_cons_of_mem _ h))
          (fun entry h => subV entry (List.mem_cons_of_mem _ h)))
        rcases e with ⟨name,ty⟩; rcases v with ⟨name',ref⟩
        simp only at same; subst name'
        have em := subE _ (List.mem_cons_self ..)
        have vm := subV _ (List.mem_cons_self ..)
        cases ty with
        | none =>
          have eq := member_value_unique realized.ownership.variableKeys vm (realized.emptyVariables _ em)
          subst ref; trivial
        | some ty =>
          obtain ⟨r,stored,sat⟩ := realized.initializedVariables _ _ em
          have eq := member_value_unique realized.ownership.variableKeys vm stored
          subst ref; exact sat
  exact paired _ _ keys (fun _ h => h) (fun _ h => h)

private theorem compatible_symm {first second : Reference} (h : Compatible first second) : Compatible second first := by
  rcases h with different | shared
  · exact .inl (Ne.symm different)
  · exact .inr ⟨shared.2,shared.1⟩

private theorem owners_targets (state : State) : (Owners state).map Reference.object = References state := by
  simp [Owners, References, List.map_filterMap, List.map_flatMap]

-- Repartitioning the roots between locals and pending references does not
-- change the heap, ownership occurrences, or any view observations.
theorem reroot (realized : Realizes classes oldEnvironment oldState oldPending)
    (objects : newState.objects = oldState.objects) (counter : newState.nextId = oldState.nextId)
    (environmentWf : newEnvironment.WellFormed classes)
    (variableKeys : (newState.variables.map Prod.fst).Nodup)
    (owners : (oldPending.map Prod.fst ++ Owners oldState).Perm (newPending.map Prod.fst ++ Owners newState))
    (pendingTypes : ∀ r t, (r,t) ∈ newPending → Admissible classes t)
    (domain : ∀ name, name ∈ newEnvironment.map Prod.fst ↔ name ∈ newState.variables.map Prod.fst)
    (empty : ∀ name, (name,none) ∈ newEnvironment → (name,none) ∈ newState.variables)
    (initialized : ∀ name ty, (name,some ty) ∈ newEnvironment →
      ∃ r, (name,some r) ∈ newState.variables ∧ Satisfies classes oldState r ty)
    (pendingValues : ∀ r t, (r,t) ∈ newPending → Satisfies classes oldState r t) :
    Realizes classes newEnvironment newState newPending := by
  constructor
  · exact realized.classesWellFormed
  · exact environmentWf
  · exact pendingTypes
  · constructor
    · simpa [objects] using realized.ownership.objectKeys
    · exact variableKeys
    · simpa [objects] using realized.ownership.shapes
    · simpa [objects,counter] using realized.ownership.bounds
    · have roots : (oldPending.map Prod.fst ++ oldState.variables.filterMap Prod.snd).Perm
          (newPending.map Prod.fst ++ newState.variables.filterMap Prod.snd) := by
        apply (List.perm_append_right_iff (oldState.objects.flatMap (fun e => e.2.fields.filterMap Prod.snd))).mp
        simpa only [Owners, ← List.append_assoc, objects] using owners
      have moveRoot {reference : Reference}
          (member : reference ∈ oldPending.map Prod.fst ++ oldState.variables.filterMap Prod.snd) :
          LiveWith newState (newPending.map Prod.fst) reference.object := by
        rcases List.mem_append.mp (roots.mem_iff.mp member) with p | v
        · exact .pending p
        · obtain ⟨⟨name, slot⟩, stored, value⟩ := List.mem_filterMap.mp v
          change slot = some reference at value
          subst slot
          exact .variable stored
      intro id allocated
      have live := realized.ownership.rooted id (by simpa [Allocated,objects] using allocated)
      clear allocated
      induction live with
      | pending member => exact moveRoot (List.mem_append_left _ member)
      | «variable» member => exact moveRoot (List.mem_append_right _ (List.mem_filterMap.mpr ⟨_,member,rfl⟩))
      | field _ stored field ih => exact .field ih (by simpa [objects] using stored) field
    · exact owners.pairwise realized.ownership.ownersCompatible compatible_symm
    · intro id
      have eq := (owners.map Reference.object).mem_iff (a := id)
      simp only [List.map_append, owners_targets] at eq
      exact eq.symm.trans ((realized.ownership.referencesComplete id).trans (by simp [Allocated,objects]))
  · simpa [FieldsMatchClasses,objects] using realized.fields
  · exact domain
  · exact empty
  · intro name ty member
    obtain ⟨r,stored,sat⟩ := initialized _ _ member
    exact ⟨r,stored,sat.same_objects objects.symm⟩
  · intro r t member; exact (pendingValues _ _ member).same_objects objects.symm

def heapState (state : State) : State := ⟨state.objects,[],state.nextId⟩

theorem to_heap (realized : Realizes classes environment state pending)
    (slots : Slots environment state.variables roots) :
    Realizes classes [] (heapState state) (roots ++ pending) := by
  apply reroot (newState := heapState state) (newPending := roots ++ pending) realized rfl rfl (by simp [Environment.WellFormed]) (by simp [heapState])
  · simp only [List.map_append, Owners, heapState, List.filterMap_nil, List.nil_append, ← slots.references]
    simpa only [List.append_assoc] using (List.perm_append_comm (l₁ := pending.map Prod.fst) (l₂ := roots.map Prod.fst)).append_right (state.objects.flatMap (fun entry => entry.2.fields.filterMap Prod.snd))
  · intro r t member
    rcases List.mem_append.mp member with localRoot | p
    · obtain ⟨name,e,_⟩ := slots.root localRoot
      exact Environment.admissible realized.environmentWellFormed e
    · exact realized.pendingTypes _ _ p
  · simp [heapState]
  · simp
  · simp
  · intro r t member
    rcases List.mem_append.mp member with localRoot | p
    · obtain ⟨name,e,v⟩ := slots.root localRoot
      obtain ⟨r',v',sat⟩ := realized.initializedVariables _ _ e
      have eq := member_value_unique realized.ownership.variableKeys v v'
      cases eq; exact sat
    · exact realized.pendingValues _ _ p

theorem from_heap (realized : Realizes classes [] (heapState state) (roots ++ pending))
    (slots : Slots environment variables roots) (wf : environment.WellFormed classes) :
    Realizes classes environment ⟨state.objects,variables,state.nextId⟩ pending := by
  apply reroot (newState := ⟨state.objects,variables,state.nextId⟩) (newPending := pending) realized rfl rfl wf (slots.keys ▸ wf.1)
  · simp only [List.map_append, Owners, heapState, List.filterMap_nil, List.nil_append, ← slots.references]
    simpa only [List.append_assoc] using (List.perm_append_comm (l₁ := roots.map Prod.fst) (l₂ := pending.map Prod.fst)).append_right (state.objects.flatMap (fun entry => entry.2.fields.filterMap Prod.snd))
  · intro r t member; exact realized.pendingTypes _ _ (List.mem_append_right _ member)
  · intro name; rw [slots.keys]
  · intro name member; exact slots.empty_slot member
  · intro name ty member
    obtain ⟨r,v,p⟩ := slots.initialized member
    exact ⟨r,v,realized.pendingValues _ _ (List.mem_append_left _ p)⟩
  · intro r t member; exact realized.pendingValues _ _ (List.mem_append_right _ member)

end Dada.Functions
