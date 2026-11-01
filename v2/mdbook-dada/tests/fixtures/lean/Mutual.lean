namespace Fixtures

inductive Token where
  | token

mutual
inductive Eval : Nat → Prop where
  | arguments {n : Nat} : Args n → Eval n

inductive Args : Nat → Prop where
  | nil : Args 0
  | cons {n : Nat} : Eval n → Args n
end

inductive Step : Prop where
  | evaluated : Eval 0 → Step

theorem finished : True := by
  trivial

end Fixtures
