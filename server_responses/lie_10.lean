/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b54a4275-f2e7-48ca-acb3-bf8aa572233c

The following was proved by Aristotle:

- open Module in
lemma invtRootSubmodule.eq_top_iff {K : Type*} [Field K] [NeZero (2 : K)]
    [Module K M] [Module K N] {P : RootPairing ι K M N} [P.IsRootSystem]
    (q : P.invtRootSubmodule) :
    q = ⊤ ↔ ∀ i, P.root i ∈ (q : Submodule K M)
-/

/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.RootSystem.RootPositive
import Mathlib.LinearAlgebra.RootSystem.WeylGroup
import Mathlib.RepresentationTheory.Submodule


@[expose] public section

open Function Set

open Submodule (span span_le)

open LinearMap (ker)

open MulAction (orbit mem_orbit_self mem_orbit_iff)

open Module.End (invtSubmodule)

open scoped MonoidAlgebra

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

class IsRootSystem : Prop where
  span_root_eq_top : span R (range P.root) = ⊤
  span_coroot_eq_top : span R (range P.coroot) = ⊤

/-- The sublattice of invariant submodules of the root space. -/
def invtRootSubmodule : Sublattice (Submodule R M) :=
  ⨅ i, invtSubmodule (P.reflection i)

lemma mem_invtRootSubmodule_iff {q : Submodule R M} :
    q ∈ P.invtRootSubmodule ↔ ∀ i, q ∈ Module.End.invtSubmodule (P.reflection i) := by
  simp [invtRootSubmodule]

@[simp] protected lemma invtRootSubmodule.top_mem : ⊤ ∈ P.invtRootSubmodule := by
  simp [invtRootSubmodule]

@[simp] protected lemma invtRootSubmodule.bot_mem : ⊥ ∈ P.invtRootSubmodule := by
  simp [invtRootSubmodule]

instance : BoundedOrder P.invtRootSubmodule where
  top := ⟨⊤, invtRootSubmodule.top_mem P⟩
  bot := ⟨⊥, invtRootSubmodule.bot_mem P⟩
  le_top := fun ⟨p, hp⟩ ↦ by simp
  bot_le := fun ⟨p, hp⟩ ↦ by simp

instance [Nontrivial M] : Nontrivial P.invtRootSubmodule where
  exists_pair_ne := ⟨⊥, ⊤, by rw [ne_eq, Subtype.ext_iff]; exact bot_ne_top⟩

@[simp] lemma coe_bot : ((⊥ : P.invtRootSubmodule) : Submodule R M) = ⊥ := rfl

@[simp] lemma coe_top : ((⊤ : P.invtRootSubmodule) : Submodule R M) = ⊤ := rfl

open Module in
lemma invtRootSubmodule.eq_top_iff {K : Type*} [Field K] [NeZero (2 : K)]
    [Module K M] [Module K N] {P : RootPairing ι K M N} [P.IsRootSystem]
    (q : P.invtRootSubmodule) :
    q = ⊤ ↔ ∀ i, P.root i ∈ (q : Submodule K M) := by
  -- The top submodule is the entire space M, so if q is the top submodule, then every element of M is in q. Since the roots are in M, they must be in q.
  have h_top : (⊤ : Submodule K M) = Submodule.span K (Set.range P.root) := by
    exact Eq.symm ( by exact? );
  -- If $q$ is the top submodule, then by definition, it contains all elements of $M$, which includes all the roots.
  apply Iff.intro;
  · aesop;
  · -- If every root is in q, then the span of the roots is contained in q. Since the top submodule is the span of the roots, this implies q is the top submodule.
    intro hq
    have h_span : Submodule.span K (Set.range P.root) ≤ q.val := by
      exact Submodule.span_le.mpr ( Set.range_subset_iff.mpr hq );
    -- Since the top submodule is equal to the span of the roots, and we have h_span which states that the span of the roots is contained in q, we can conclude that q is the top submodule.
    have h_top_eq : (⊤ : Submodule K M) ≤ q.val := by
      exact h_top ▸ h_span;
    exact Subtype.ext ( le_antisymm ( le_top ) h_top_eq )