/-
Copyright (c) 2025 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Log

/-!
# Schweitzer 2014 Q1

## Problem Statement

Let n be a positive integer. Let F be a family of sets that contains more than half of all
subsets of an n-element set X. Prove that we can always select ⌈log₂ n⌉ + 1 sets from F
such that together they separate the elements of X, meaning that for any two distinct elements
of X, there exists a selected set that contains exactly one of the two elements.

## Definitions

A family F of subsets **separates** elements x, y ∈ X if there exists S ∈ F such that
(x ∈ S ∧ y ∉ S) or (x ∉ S ∧ y ∈ S).

A family F **separates all pairs** in X if it separates every pair of distinct elements.

## Main result

* `schweitzer2014q1`: If F contains more than 2^(n-1) subsets of an n-element set,
  then we can select ⌈log₂ n⌉ + 1 sets from F that separate all pairs.
-/

namespace Schweitzer2014Q1

/-- A family of sets F separates two distinct elements x and y if some set in F
contains exactly one of them. -/
def separates {α : Type*} (F : Set (Set α)) (x y : α) : Prop :=
  ∃ S ∈ F, (x ∈ S ∧ y ∉ S) ∨ (x ∉ S ∧ y ∈ S)

/-- A family of sets F separates all pairs if it separates every pair of distinct elements. -/
def separatesAllPairs {α : Type*} (F : Set (Set α)) (X : Set α) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → separates F x y

/-- Schweitzer 2014 Q2: If F contains more than half of all subsets of an n-element set,
then we can select ⌈log₂ n⌉ + 1 sets from F that separate all pairs. -/
theorem schweitzer2014q1 (n : ℕ) (hn : 0 < n) (X : Finset (Fin n))
    (hX : X.card = n)
    (F : Set (Set (Fin n)))
    (hF : (2 ^ (n - 1) : ℕ) < F.ncard) :
    ∃ (G : Finset (Set (Fin n))),
      (∀ S ∈ G, S ∈ F) ∧
      G.card ≤ Nat.clog 2 n + 1 ∧
      separatesAllPairs (G : Set (Set (Fin n))) X := by
  sorry

end Schweitzer2014Q1
