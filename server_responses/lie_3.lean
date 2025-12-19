/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e1973a3b-0b1e-4e76-a5b1-38c081de6174

The following was proved by Aristotle:

- @[simp] lemma invtSubmoduleToLieIdeal_top :
    invtSubmoduleToLieIdeal (⊤ : Submodule K (Module.Dual K H)) (by simp) = ⊤
-/

import Mathlib.Algebra.Lie.Weights.IsSimple
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas


variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]

variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

variable [LieAlgebra.IsKilling K L] [LieModule.IsTriangularizable K H L]

namespace LieAlgebra.IsKilling

noncomputable section AristotleLemmas

#check LieModule.Weight
#check LieAlgebra.IsKilling.coroot

lemma span_coroot_eq_top : Submodule.span K (Set.range (coroot : LieModule.Weight K H L → H)) = ⊤ := by
  have h_span_dual : Submodule.span K (Set.range (LieModule.Weight.toLinear K H L)) = ⊤ := by
    exact?;
  have h_span_dual : Submodule.span K (Set.range (fun α : LieModule.Weight K H L => (LieAlgebra.IsKilling.cartanEquivDual H).symm (LieModule.Weight.toLinear K H L α))) = ⊤ := by
    have h_iso : ∀ (f : Module.Dual K H →ₗ[K] H), Function.Surjective f → Submodule.span K (Set.range (f ∘ LieModule.Weight.toLinear K H L)) = ⊤ := by
      simp_all +decide [ Function.Surjective, Set.range_comp ];
      exact fun f hf => LinearMap.range_eq_top.mpr fun x => by obtain ⟨ y, hy ⟩ := hf x x.2; exact ⟨ y, hy ⟩ ;
    exact h_iso _ ( LinearEquiv.surjective _ );
  -- Since the coroots are scalar multiples of the inverse images of the roots, and the span of the roots is the entire dual space, multiplying by non-zero scalars preserves the span.
  have h_coroot_span : Submodule.span K (Set.range (fun α : LieModule.Weight K H L => (LieAlgebra.IsKilling.coroot α))) = Submodule.span K (Set.range (fun α : LieModule.Weight K H L => (LieAlgebra.IsKilling.cartanEquivDual H).symm (LieModule.Weight.toLinear K H L α))) := by
    refine' le_antisymm _ _ <;> rw [ Submodule.span_le ] <;> simp +decide [ Set.range_subset_iff ];
    · intro α; by_cases hα : α.IsNonZero <;> simp_all +decide [ LieAlgebra.IsKilling.coroot ] ;
    · intro α; by_cases hα : α.IsNonZero <;> simp_all +decide [ LieAlgebra.IsKilling.coroot ] ;
      · have := LieAlgebra.IsKilling.root_apply_cartanEquivDual_symm_ne_zero hα; simp_all +decide [ two_smul ] ;
        rw [ Submodule.mem_span ] at *; aesop;
        have := a ⟨ α, rfl ⟩ ; simp_all +decide [ ← two_smul K ] ;
        convert p.smul_mem ( ( α ( ( LieAlgebra.IsKilling.cartanEquivDual H ).symm ( LieModule.Weight.toLinear K H L α ) ) ) / 2 ) this using 1 ; simp +decide [ div_eq_inv_mul, smul_smul ] ; ring!; aesop;
      · convert Submodule.zero_mem _ using 1 ; aesop;
  exact h_coroot_span.trans h_span_dual

lemma H_le_iSup_sl2SubmoduleOfRoot :
    H.toLieSubmodule ≤ ⨆ (α : LieModule.Weight K H L) (hα : α.IsNonZero), sl2SubmoduleOfRoot hα := by
      intro x hx; specialize @hx ; aesop;
      -- Since $x \in H$, we can write $x$ as a linear combination of coroots.
      obtain ⟨αs, hαs⟩ : ∃ αs : Finset (LieModule.Weight K H L), ∃ (c : LieModule.Weight K H L → K), x = ∑ α ∈ αs, c α • coroot α := by
        have h_span : Submodule.span K (Set.range (coroot : LieModule.Weight K H L → H)) = ⊤ := by
          exact?;
        rw [ Submodule.eq_top_iff' ] at h_span;
        have := h_span ⟨ x, hx ⟩;
        rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at this;
        obtain ⟨ c, hc ⟩ := this; use c.support, c; simp_all +decide [ Finsupp.sum ] ;
      aesop;
      refine' Submodule.sum_mem _ fun α hα => _;
      by_cases hα_zero : α.IsNonZero <;> aesop;
      · refine' Submodule.smul_mem _ _ ( Submodule.mem_iSup_of_mem α ( Submodule.mem_iSup_of_mem hα_zero _ ) );
        rw [ LieAlgebra.IsKilling.sl2SubmoduleOfRoot_eq_sup ];
        exact Submodule.mem_sup_right ( Submodule.mem_map_of_mem ( LieAlgebra.IsKilling.coe_corootSpace_eq_span_singleton α ▸ Submodule.subset_span ( Set.mem_singleton _ ) ) );
      · simp_all +decide [ LieAlgebra.IsKilling.coroot ]

end AristotleLemmas

@[simp] lemma invtSubmoduleToLieIdeal_top :
    invtSubmoduleToLieIdeal (⊤ : Submodule K (Module.Dual K H)) (by simp) = ⊤ := by
  rw [← LieSubmodule.toSubmodule_inj, invtSubmoduleToLieIdeal, LieSubmodule.iSup_toSubmodule,
    LieSubmodule.top_toSubmodule, Submodule.eq_top_iff']
  -- For any non-zero root α, the sl2 submodule of α contains the root space L_α.
  have h_sl2_submodule_contains_root_space : ∀ (α : LieModule.Weight K H L) (hα : α.IsNonZero), LieAlgebra.rootSpace H α ≤ LieAlgebra.IsKilling.sl2SubmoduleOfRoot hα := by
    intro α hα
    have h_sl2_submodule_contains_root_space : LieModule.genWeightSpace L α ≤ LieAlgebra.IsKilling.sl2SubmoduleOfRoot hα := by
      rw [ LieAlgebra.IsKilling.sl2SubmoduleOfRoot_eq_sup ];
      exact le_sup_of_le_left ( le_sup_left );
    exact?;
  -- Since `⨆ α, genWeightSpace L α = ⊤` (by `LieModule.iSup_genWeightSpace_eq_top'`), we have `⨆ α, genWeightSpace L α ≤ ⨆ α, sl2SubmoduleOfRoot α`.
  have h_sup_le_sup : ⨆ (α : LieModule.Weight K H L), LieAlgebra.rootSpace H α ≤ ⨆ (α : LieModule.Weight K H L) (hα : α.IsNonZero), LieAlgebra.IsKilling.sl2SubmoduleOfRoot hα := by
    refine' iSup_le fun α => _;
    by_cases hα : α.IsNonZero;
    · exact le_iSup₂_of_le α hα ( h_sl2_submodule_contains_root_space α hα );
    · simp_all +decide [ LieModule.Weight.IsNonZero ];
      convert H_le_iSup_sl2SubmoduleOfRoot;
  -- Since `⨆ α, genWeightSpace L α = ⊤` (by `LieModule.iSup_genWeightSpace_eq_top'`), we have `⨆ α, genWeightSpace L α ≤ ⨆ α, sl2SubmoduleOfRoot α` implies `⊤ ≤ ⨆ α, sl2SubmoduleOfRoot α`.
  have h_top_le_sup : (⊤ : Submodule K L) ≤ ⨆ (α : LieModule.Weight K H L) (hα : α.IsNonZero), LieAlgebra.IsKilling.sl2SubmoduleOfRoot hα := by
    have h_top_le_sup : (⨆ (α : LieModule.Weight K H L), LieAlgebra.rootSpace H α) = ⊤ := by
      exact?;
    aesop;
  simp_all +decide [ Submodule.eq_top_iff' ];
  convert h_top_le_sup using 1;
  simp +decide [ Submodule.mem_iSup ]

end LieAlgebra.IsKilling