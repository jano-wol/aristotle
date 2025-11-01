import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Card

/-!
# Permutations and Pigeonhole Principle (Easy Version)

## Problem Statement

Let n ≥ 2 and let P be a set of permutations acting on [n] = {0, 1, 2, ..., n-1}.

**Assumptions:**
1. **Transitivity:** The set P acts transitively on [n], meaning that for any two elements
i, j ∈ [n], there exists a finite composition of permutations from P that maps i to j.
2. **Majority coloring:** More than half of the elements of [n] are colored red.

**Goal:** Show that for any two distinct elements a, b ∈ [n], there exists a finite composition
of permutations from P that simultaneously maps both a and b to red-colored positions.

## Main results

* `pppeasy`: Given a transitive set of permutations on a finite set with more than half
  the elements colored red, any pair of distinct elements can be moved by a composition of
  permutations to positions where both elements land on red.
-/

namespace PPPEasy
/--
  PROVIDED SOLUTION:
  Take any edge, and consider the graph consisting of all edges to which this edge can be moved.
  By transitivity, every vertex has the same degree, so the graph is regular.
  Consider the red vertices; since more than half of all vertices are red, there are many of them.
  If every edge starting from a red vertex ended at a blue vertex, then each blue vertex would receive more edges than any red vertex sends.
  This would contradict the regularity of the graph, because all vertices must have the same degree.
  Therefore, there must be an edge connecting two red vertices, which proves the claim.
-/
theorem pppeasy (n : ℕ) (hn : 2 ≤ n) (P : Set (Equiv.Perm (Fin n)))
    (h_trans : ∀ i j : Fin n, ∃ (σ : Equiv.Perm (Fin n)),
      (∃ (perms : List (Equiv.Perm (Fin n))), (∀ p ∈ perms, p ∈ P) ∧ σ = perms.foldl (· * ·) 1) ∧
      σ i = j)
    (red : Set (Fin n)) (h_red : (n : ℚ) / 2 < (red.ncard : ℚ))
    (a b : Fin n) (hab : a ≠ b) :
    ∃ (σ : Equiv.Perm (Fin n)),
      (∃ (perms : List (Equiv.Perm (Fin n))), (∀ p ∈ perms, p ∈ P) ∧ σ = perms.foldl (· * ·) 1) ∧
      σ a ∈ red ∧ σ b ∈ red := by
  sorry

end PPPEasy
