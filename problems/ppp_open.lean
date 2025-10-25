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
# Permutations and Pigeonhole Principle (Open Problem - Bounded Steps)

## Problem Statement

Let n ≥ 2 and let P be a set of permutations acting on [n] = {0, 1, 2, ..., n-1}.

**Assumptions:**
1. **Transitivity:** The set P acts transitively on [n], meaning that for any two elements
   i, j ∈ [n], there exists a finite composition of permutations from P that maps i to j.
2. **Majority coloring:** More than half of the elements of [n] are colored red.

**Goal:** Show that for any two distinct elements a, b ∈ [n], there exists a composition
of **at most n-1 permutations** from P that simultaneously maps both a and b to red-colored
positions.

This is a strengthening of the "easy version" which only asks for existence of such a composition
(without bounding the number of steps). The bound of n-1 steps is conjectured to be optimal.

## Relation to the Easy Version

The easy version (see `Archive.Imo.ppp_easy`) proves that such a composition exists, but does
not bound the number of steps required. This open problem asks: can we always do it quickly,
in at most n-1 steps?

## Main results

* `pppopen`: Given a transitive set of permutations on a finite set with more than half
  the elements colored red, any pair of distinct elements can be moved by a composition of
  **at most n-1 permutations** from P to positions where both elements land on red.
-/

namespace PPPOpen

/-- Open problem: The easy version with a bound of at most n-1 steps. -/
theorem pppopen (n : ℕ) (hn : 2 ≤ n) (P : Set (Equiv.Perm (Fin n)))
    (h_trans : ∀ i j : Fin n, ∃ (σ : Equiv.Perm (Fin n)),
      (∃ (perms : List (Equiv.Perm (Fin n))), (∀ p ∈ perms, p ∈ P) ∧ σ = perms.foldl (· * ·) 1) ∧
      σ i = j)
    (red : Set (Fin n)) (h_red : (n : ℚ) / 2 < (red.ncard : ℚ))
    (a b : Fin n) (hab : a ≠ b) :
    ∃ (σ : Equiv.Perm (Fin n)),
      (∃ (perms : List (Equiv.Perm (Fin n))),
        perms.length ≤ n - 1 ∧
        (∀ p ∈ perms, p ∈ P) ∧
        σ = perms.foldl (· * ·) 1) ∧
      σ a ∈ red ∧ σ b ∈ red := by
  sorry

end PPPOpen
