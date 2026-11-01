import Common.FiniteMap

open Dada.Common

-- ANCHOR: empty_map
example : (FiniteMap.empty : FiniteMap Nat Nat).entries = [] := by
  rfl
-- ANCHOR_END: empty_map
