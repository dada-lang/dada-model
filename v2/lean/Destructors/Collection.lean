import Destructors.StackTyping

namespace Dada.Destructors
open Shared Shared.Typing
open Functions (heapState Slots)

-- Reachability remembers where a discarded root came from; no view is used
-- to infer that an unmentioned field is empty.
theorem Realizes.reachable {id : ObjectId} (realized : Realizes classes environment state pending)
    (stored : (id, data) ∈ state.objects) :
    Reachable state.objects (rootReferences state pending) id := by
  have live := realized.ownership.rooted id (List.mem_map.mpr ⟨(id, data), stored, rfl⟩)
  clear stored
  induction live with
  | pending member => exact .root (List.mem_append_left _ member)
  | «variable» member => exact .root (List.mem_append_right _ (List.mem_filterMap.mpr ⟨_, member, rfl⟩))
  | field _ stored field ih => exact .field ih stored field

theorem struct_field (realized : Realizes classes environment state pending)
    (stored : (parent, data) ∈ state.objects)
    (structParent : StructType classes (.whole data.className))
    (field : (name, some reference) ∈ data.fields) :
    ∃ target, (reference.object, target) ∈ state.objects ∧
      StructType classes (.whole target.className) := by
  obtain ⟨declaration, fieldType, target, declared, described, targetStored, targetName⟩ :=
    realized.fields _ _ _ _ stored field
  obtain ⟨structDecl, found, kind⟩ := structParent.declaration
  have same := member_value_unique realized.classesWellFormed.1
    (lookup_member found) declared
  cases same
  have structField := (realized.classesWellFormed.2 _ declared).2 _ described |>.2.2 kind
  exact ⟨target, targetStored, by simpa only [StructType, ValueType.base,
    ValueType.whole, Unique.Typing.ViewType.whole, FieldType.toType, targetName] using structField⟩

-- The roots removed by collection may have arbitrary views, but must all be
-- structs. Field nominal correctness covers even fields omitted by those views.
theorem collectPending_retains_classes {id : ObjectId}
    (realized : Realizes classes environment state (kept ++ garbage))
    (discardable : ∀ reference ty, (reference, ty) ∈ garbage → StructType classes ty)
    (stored : (id, data) ∈ state.objects)
    (classObject : ¬ StructType classes (.whole data.className)) :
    (id, data) ∈ (collectPending state kept).objects := by
  have reached := Realizes.reachable realized stored
  have split : Reachable state.objects (rootReferences state kept) id ∨
      ∃ target, (id, target) ∈ state.objects ∧ StructType classes (.whole target.className) := by
    clear stored classObject
    induction reached with
    | root member =>
      simp only [rootReferences, List.map_append, List.mem_append] at member
      rcases member with (keptMember | garbageMember) | variableMember
      · exact .inl (.root (List.mem_append_left _ keptMember))
      · obtain ⟨⟨reference,ty⟩, typedMember, equality⟩ := List.mem_map.mp garbageMember
        dsimp at equality
        subst equality
        obtain ⟨target, targetStored, targetName⟩ :=
          (realized.pendingValues _ _ (List.mem_append_right _ typedMember)).root
        exact .inr ⟨target, targetStored, by
          simpa only [StructType, ValueType.base, ValueType.whole,
            Unique.Typing.ViewType.whole, targetName] using discardable _ _ typedMember⟩
      · exact .inl (.root (List.mem_append_right _ variableMember))
    | field _ parentStored field ih =>
      rcases ih with live | ⟨parentData, parentMember, structParent⟩
      · exact .inl (.field live parentStored field)
      · have same := member_value_unique realized.ownership.objectKeys parentMember parentStored
        cases same
        exact .inr (struct_field realized parentStored structParent field)
  apply collectPending_member.mpr
  refine ⟨stored, ?_⟩
  rcases split with live | ⟨target, targetStored, structTarget⟩
  · exact live
  · have same := member_value_unique realized.ownership.objectKeys targetStored stored
    cases same
    exact False.elim (classObject structTarget)

end Dada.Destructors
