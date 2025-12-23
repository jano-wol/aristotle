/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b22d52fe-f177-46b1-bb81-2607181777d7

The following was proved by Aristotle:

- @[simp] lemma invtSubmoduleToLieIdeal_top :
    invtSubmoduleToLieIdeal (⊤ : Submodule K (Module.Dual K H)) (by simp) = ⊤
-/

import Mathlib.Algebra.Lie.Weights.IsSimple
import Mathlib.LinearAlgebra.RootSystem.RootPositive
import Mathlib.LinearAlgebra.RootSystem.WeylGroup
import Mathlib.RepresentationTheory.Submodule
import Mathlib.Algebra.Lie.Weights.IsSimple
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas


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

@[deprecated (since := "2025-12-14")] alias RootSystem := IsRootSystem

attribute [simp] IsRootSystem.span_root_eq_top

attribute [simp] IsRootSystem.span_coroot_eq_top

@[simp] lemma coe_bot : ((⊥ : P.invtRootSubmodule) : Submodule R M) = ⊥ := rfl

@[simp] lemma coe_top : ((⊤ : P.invtRootSubmodule) : Submodule R M) = ⊤ := rfl

open Module in
lemma invtRootSubmodule.eq_top_iff {K : Type*} [Field K] [NeZero (2 : K)]
    [Module K M] [Module K N] {P : RootPairing ι K M N} [P.IsRootSystem]
    (q : P.invtRootSubmodule) :
    q = ⊤ ↔ ∀ i, P.root i ∈ (q : Submodule K M) := by
  admit

end RootPairing

namespace LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]

variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

variable [LieAlgebra.IsKilling K L] [LieModule.IsTriangularizable K H L]

lemma span_coroot_eq_top :
    Submodule.span K (Set.range (coroot : LieModule.Weight K H L → H)) = ⊤ := by
  admit

lemma rootSpace_le_sl2SubmoduleOfRoot (α : LieModule.Weight K H L) (hα : α.IsNonZero) :
    LieAlgebra.rootSpace H α ≤ sl2SubmoduleOfRoot hα := by
  rw [sl2SubmoduleOfRoot_eq_sup]; exact le_sup_of_le_left le_sup_left

lemma H_le_iSup_sl2SubmoduleOfRoot :
    H.toLieSubmodule ≤
      ⨆ (α : LieModule.Weight K H L) (hα : α.IsNonZero), sl2SubmoduleOfRoot hα := by
  intro x hx
  obtain ⟨c, hc⟩ : ∃ c : LieModule.Weight K H L →₀ K,
      (c.sum fun α r => r • coroot α) = ⟨x, hx⟩ := by
    have h_span := span_coroot_eq_top (H := H)
    rw [Submodule.eq_top_iff'] at h_span
    exact Finsupp.mem_span_range_iff_exists_finsupp.mp (h_span ⟨x, hx⟩)
  have hx_sum : x = ∑ α ∈ c.support, c α • (coroot α : L) := by
    have : (⟨x, hx⟩ : H.toLieSubmodule) = c.sum fun α r => r • coroot α := hc.symm
    calc x = ↑(⟨x, hx⟩ : H.toLieSubmodule) := rfl
      _ = ↑(c.sum fun α r => r • coroot α) := congrArg Subtype.val this
      _ = _ := by rw [Finsupp.sum, AddSubmonoidClass.coe_finset_sum]; rfl
  rw [hx_sum]
  refine Submodule.sum_mem _ fun α hα => Submodule.smul_mem _ _ ?_
  by_cases hα_zero : α.IsNonZero
  · rw [LieSubmodule.mem_toSubmodule]
    apply LieSubmodule.mem_iSup_of_mem α
    apply LieSubmodule.mem_iSup_of_mem hα_zero
    rw [sl2SubmoduleOfRoot_eq_sup]
    exact Submodule.mem_sup_right (Submodule.mem_map_of_mem
      (coe_corootSpace_eq_span_singleton α ▸ Submodule.subset_span (Set.mem_singleton _)))
  · simp only [LieModule.Weight.IsNonZero, not_not] at hα_zero
    simp only [coroot_eq_zero_iff.mpr hα_zero, ZeroMemClass.coe_zero, Submodule.zero_mem]

lemma iSup_rootSpace_eq_top :
    H.toLieSubmodule ⊔ ⨆ α : H.root, rootSpace H α = ⊤ := by
  by_contra h_contra
  apply h_contra (eq_top_iff.mpr _)
  rw [← LieModule.iSup_genWeightSpace_eq_top']
  simp only [iSup_le_iff]
  intro α
  by_cases hα : α.IsZero
  · simp [hα]
  · apply le_sup_of_le_right
    apply le_iSup_of_le ⟨α, (Finset.mem_filter_univ α).mpr hα⟩
    exact le_rfl

/--
  PROVIDED SOLUTION:
  Use iSup_rootSpace_eq_top, and rootSpace_le_sl2SubmoduleOfRoot and H_le_iSup_sl2SubmoduleOfRoot
-/
@[simp] lemma invtSubmoduleToLieIdeal_top :
    invtSubmoduleToLieIdeal (⊤ : Submodule K (Module.Dual K H)) (by simp) = ⊤ := by
  rw [← LieSubmodule.toSubmodule_inj, invtSubmoduleToLieIdeal, LieSubmodule.iSup_toSubmodule,
    LieSubmodule.top_toSubmodule]
  -- Since each sl2SubmoduleOfRoot is a submodule of L and the union is the supremum of these submodules, the supremum should be the entire L.
  have h_sup : ⨆ (α : LieModule.Weight K H L) (hα : α.IsNonZero), sl2SubmoduleOfRoot hα = ⊤ := by
    -- Since $H$ is contained in the supremum of the $sl2SubmoduleOfRoot$'s and the supremum of the $rootSpace$'s is $L$, the supremum of the $sl2SubmoduleOfRoot$'s must be $L$.
    have h_sup : H.toLieSubmodule ⊔ ⨆ (α : LieModule.Weight K H L), rootSpace H α ≤ ⨆ (α : LieModule.Weight K H L), ⨆ (hα : α.IsNonZero), sl2SubmoduleOfRoot hα := by
      refine' sup_le _ _;
      · exact?;
      · refine' iSup_le fun α => _;
        by_cases hα : α.IsNonZero <;> simp_all +decide [ LieAlgebra.rootSpace ];
        · exact le_iSup₂_of_le α hα ( by exact? );
        · exact?;
    simp_all +decide [ Submodule.eq_top_iff' ];
    refine' eq_top_iff.mpr _;
    have := iSup_rootSpace_eq_top ( L := L ) ( H := H );
    rw [ ← this ];
    exact sup_le h_sup.1 ( iSup_le fun α => h_sup.2 α );
  convert h_sup.ge;
  simp +decide [ Submodule.mem_iSup ];
  simp +decide [ Submodule.eq_top_iff', iSup_subtype ]

end LieAlgebra.IsKilling