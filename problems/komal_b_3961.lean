import Mathlib.SetTheory.Cardinal.Basic

/-!
# Komal problem B.3961
Let `a` and `b` positive integers, so that for any `n` positive integer `a^n + n ∣ b^n + n`.
Show that `a = b`.
-/

namespace KomalB3961

/-- The answer 2 is to be determined by the solver of the original problem. -/
theorem komal_b_3961 :
    ∀ a b : ℕ+, (∀ n : ℕ+, ((a : ℕ) ^ (n : ℕ) + n ∣ (b : ℕ) ^ (n : ℕ) + n)) → a = b := by
  sorry

end KomalB3961
