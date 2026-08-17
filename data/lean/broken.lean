import Mathlib

/-!
Meant to fail. The goal is `S_le_S_succ`, and the step lemma underneath it
cites `Nat.sum_range_succ_of_triangle`, which does not exist in mathlib.
-/

namespace DemoBroken

/-- The sum of the first `n` positive integers. -/
def S (n : ℕ) : ℕ := n * (n + 1) / 2

/-- A step lemma that appeals to a lemma that does not exist. -/
lemma S_succ (n : ℕ) : S (n + 1) = S n + (n + 1) := by
  simpa [S] using Nat.sum_range_succ_of_triangle n

/-- The running total never decreases. -/
theorem S_le_S_succ (n : ℕ) : S n ≤ S (n + 1) := by
  rw [S_succ]; omega

end DemoBroken
