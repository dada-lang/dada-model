import Std

namespace Dada.Common

-- A finite ordered list of entries with no duplicate keys.
structure FiniteMap (Key Value : Type) where
  entries : List (Key × Value)
  uniqueKeys : (entries.map Prod.fst).Nodup

def FiniteMap.empty : FiniteMap Key Value where
  entries := []
  uniqueKeys := List.nodup_nil

theorem FiniteMap.value_unique (map : FiniteMap Key Value)
    {key : Key} {value value' : Value}
    (member : (key, value) ∈ map.entries)
    (member' : (key, value') ∈ map.entries) : value = value' := by
  obtain ⟨i, hi, entry⟩ := List.getElem_of_mem member
  obtain ⟨j, hj, entry'⟩ := List.getElem_of_mem member'
  have same_index : i = j := map.uniqueKeys.eq_of_getElem_eq
    (by simpa using hi) (by simpa using hj) (by simp [entry, entry'])
  subst j
  have same_entry : (key, value) = (key, value') := entry.symm.trans entry'
  exact (Prod.mk.inj same_entry).2

end Dada.Common
