/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d23d888a-ef59-4098-a933-280fc65bafa1

The following was proved by Aristotle:

- lemma invtRootSubmodule.eq_top_iff {K : Type*} [Field K] [NeZero (2 : K)]
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

/--
  A proof for a similar statement.
open Module in
lemma invtRootSubmodule.eq_bot_iff {K : Type*} [Field K] [NeZero (2 : K)]
    [Module K M] [Module K N] {P : RootPairing ι K M N} [P.IsRootSystem]
    (q : P.invtRootSubmodule) :
    q = ⊥ ↔ ∀ i, P.root i ∉ (q : Submodule K M) := by
  have : IsReflexive K M := .of_isPerfPair P.toLinearMap
  refine ⟨fun h ↦ by simp [h, P.ne_zero], fun h ↦ ?_⟩
  rw [Subtype.mk_eq_bot_iff (by simp), Submodule.eq_bot_iff]
  intro x hx
  by_contra hx₀
  obtain ⟨i, hi⟩ : ∃ i, P.coroot' i x ≠ 0 := by
    contrapose! hx₀
    suffices Dual.eval K M x = 0 from
      ((Dual.eval K M).map_eq_zero_iff (bijective_dual_eval K M).injective).mp this
    exact LinearMap.ext_on_range P.span_coroot'_eq_top hx₀
  replace h : P.reflection i x ∉ (q : Submodule K M) := by
    specialize h i
    contrapose! h
    rw [reflection_apply, LinearMap.flip_apply, Submodule.sub_mem_iff_right _ hx] at h
    exact (Submodule.smul_mem_iff _ hi).mp h
  have h' : P.reflection i x ∈ (q : Submodule K M) := P.mem_invtRootSubmodule_iff.mp q.property i hx
  contradiction
-/
lemma invtRootSubmodule.eq_top_iff {K : Type*} [Field K] [NeZero (2 : K)]
    [Module K M] [Module K N] {P : RootPairing ι K M N} [P.IsRootSystem]
    (q : P.invtRootSubmodule) :
    q = ⊤ ↔ ∀ i, P.root i ∈ (q : Submodule K M) := by
  have : Module.IsReflexive K M := .of_isPerfPair P.toLinearMap
  refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
  rw [Subtype.mk_eq_top_iff (by simp), Submodule.eq_top_iff']
  intro x
  by_contra hx₀
  have h' : x ∈ Submodule.span K (Set.range P.root) := by
    have := ‹P.IsRootSystem›.span_root_eq_top;
    aesop;
  exact hx₀ ( Submodule.span_le.mpr ( Set.range_subset_iff.mpr h ) h' )
