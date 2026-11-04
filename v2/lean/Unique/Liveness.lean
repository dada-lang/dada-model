import Unique.Soundness
import Common.Rooted

namespace Dada.Unique

-- Reachability is explicit in the invariant, independent of allocation order.
theorem WellFormed.allocated_live (wf : WellFormed classes state)
    (allocated : Allocated state object) : Live state object := wf.rooted object allocated

theorem WellFormed.live_allocated (wf : WellFormed classes state)
    (live : Live state object) : Allocated state object := by
  apply (wf.referencesComplete object).mp
  cases live with
  | «variable» stored =>
    exact List.mem_append_left _ (List.mem_filterMap.mpr ⟨(_, some object), stored, rfl⟩)
  | field _ stored field =>
    exact List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨(_, _), stored, List.mem_filterMap.mpr ⟨(_, some object), field, rfl⟩⟩)

-- Liveness is a graph property, independent of the transition relation.
theorem WellFormed.live_iff_allocated (wf : WellFormed classes state) :
    Live state object ↔ Allocated state object :=
  ⟨wf.live_allocated, wf.allocated_live⟩

-- There is exactly one owning occurrence of each allocated object, counted
-- across both variables and object fields.
theorem WellFormed.owner_count (wf : WellFormed classes state)
    (allocated : Allocated state object) : (References state).count object = 1 := by
  exact wf.referencesUnique.count_of_mem ((wf.referencesComplete object).mpr allocated)

end Dada.Unique
