/-
Copyright (c) 2025 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Schweitzer 2014 Q2
Let `1 ≤ k` integer, and `I_1, I_2, ..., I_k` not degenerate intervals of `[0, 1]`.
Prove that `k^2 ≤ ∑ (1 / |I_i ∪ I_j|)`, where we are summing on all `(i, j)` index pairs where
`I_i` and `I_j` are not disjoint.
-/

namespace Schweitzer2014Q2

open scoped BigOperators

/-- A non-degenerate interval in [0,1] is represented by its endpoints. -/
structure Interval where
  a : ℝ
  b : ℝ
  ha : 0 ≤ a
  hb : b ≤ 1
  hab : a < b

/-- The interval as a set. -/
def Interval.toSet (I : Interval) : Set ℝ := Set.Ioo I.a I.b

/-- The length (measure) of an interval. -/
def Interval.length (I : Interval) : ℝ := I.b - I.a

/-- Two intervals are disjoint. -/
noncomputable def Interval.disjoint (I J : Interval) : Bool :=
  I.b ≤ J.a || J.b ≤ I.a

/-- The length of the union of two intervals (when not disjoint). -/
def Interval.unionLength (I J : Interval) : ℝ :=
  max I.b J.b - min I.a J.a

/-- The answer 2 is to be determined by the solver of the original problem. -/
theorem _root_.schweizer2014q2 (k : ℕ) (hk : 1 ≤ k) (I : Fin k → Interval) :
    (k : ℝ) ^ 2 ≤ ∑ i : Fin k, ∑ j : Fin k,
      if ¬(I i).disjoint (I j) then 1 / (I i).unionLength (I j) else 0 := by
  sorry

end Schweitzer2014Q2
