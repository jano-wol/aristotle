/-
Copyright (c) 2025 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
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
