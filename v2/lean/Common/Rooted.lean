import Std

namespace Dada.Common

-- A graph is rooted when a node is reached from a root by finitely many edges.
inductive Rooted {Node : Type} (root : Node → Prop) (edge : Node → Node → Prop) :
    Node → Prop where
  | root (atRoot : root node) : Rooted root edge node
  | field (parent : Rooted root edge node) (stored : edge node target) :
      Rooted root edge target

-- If every allocated node has an owner, following owners backwards must reach a
-- root: each backwards field edge strictly increases a bounded allocation rank.
theorem rooted_of_covered {Node : Type} {root : Node → Prop}
    {edge : Node → Node → Prop} {allocated : Node → Prop}
    (rank : Node → Nat) (bound : Nat)
    (bounded : ∀ node, allocated node → rank node < bound)
    (covered : ∀ node, allocated node →
      root node ∨ ∃ parent, allocated parent ∧ edge parent node)
    (descending : ∀ parent node, allocated parent → edge parent node →
      rank node < rank parent) :
    ∀ node, allocated node → Rooted root edge node := by
  have byDistance : ∀ distance node, bound - rank node = distance →
      allocated node → Rooted root edge node := by
    intro distance
    induction distance using Nat.strongRecOn with
    | ind distance ih =>
      intro node measure live
      rcases covered node live with atRoot | ⟨parent, parentLive, stored⟩
      · exact .root atRoot
      · have parentBound := bounded parent parentLive
        have decrease := descending parent node parentLive stored
        have smaller : bound - rank parent < distance := by omega
        exact .field (ih (bound - rank parent) smaller parent rfl parentLive) stored
  intro node live
  exact byDistance (bound - rank node) node rfl live

end Dada.Common
