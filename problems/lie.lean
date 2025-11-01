/-
Copyright (c) 2025 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
import Mathlib.Algebra.Lie.Killing

/-!
# Simple Lie algebras

We show the irreducibility of root systems of simple Lie algebras.

## Main definitions
* `LieAlgebra.IsKilling.invtSubmoduleToLieIdeal`: constructs a Lie ideal from an invariant
  submodule of the dual space

## Main results
* `LieAlgebra.IsKilling.instIsIrreducible`: the root system of a simple Lie algebra is irreducible
-/


namespace Submodule

variable [Semiring R] [AddCommMonoid M] [Module R M]
variable {x : M} (p p' : Submodule R M)
variable [Semiring R₂] {σ₁₂ : R →+* R₂}
variable [AddCommMonoid M₂] [Module R₂ M₂]
variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F σ₁₂ M M₂]

theorem mem_span_triple {w x y z : M} :
    w ∈ span R ({x, y, z} : Set M) ↔ ∃ a b c : R, a • x + b • y + c • z = w := by
  rw [mem_span_insert]
  simp_rw [mem_span_pair]
  refine exists_congr fun a ↦ ⟨?_, ?_⟩
  · rintro ⟨u, ⟨b, c, rfl⟩, rfl⟩
    exact ⟨b, c, by rw [add_assoc]⟩
  · rintro ⟨b, c, rfl⟩
    exact ⟨b • y + c • z, ⟨b, c, rfl⟩, by rw [add_assoc]⟩

end Submodule

namespace IsSl2Triple

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

open LieModule Set

variable {L M}
variable {h e f : L}
variable {R}

variable (R) in
open Submodule in
/-- The subalgebra associated to an `sl₂` triple. -/
def toLieSubalgebra (t : IsSl2Triple h e f) :
    LieSubalgebra R L where
  __ := span R {e, f, h}
  lie_mem' {x y} hx hy := by
    simp only [carrier_eq_coe, SetLike.mem_coe] at hx hy ⊢
    induction hx using span_induction with
    | zero => simp
    | add u v hu hv hu' hv' => simpa only [add_lie] using add_mem hu' hv'
    | smul t u hu hu' => simpa only [smul_lie] using smul_mem _ t hu'
    | mem u hu =>
      induction hy using span_induction with
      | zero => simp
      | add u v hu hv hu' hv' => simpa only [lie_add] using add_mem hu' hv'
      | smul t u hv hv' => simpa only [lie_smul] using smul_mem _ t hv'
      | mem v hv =>
        simp only [mem_insert_iff, mem_singleton_iff] at hu hv
        rcases hu with rfl | rfl | rfl <;>
        rcases hv with rfl | rfl | rfl <;> (try simp only [lie_self, zero_mem])
        · rw [t.lie_e_f]
          apply subset_span
          simp
        · rw [← lie_skew, t.lie_h_e_nsmul, neg_mem_iff]
          apply nsmul_mem <| subset_span _
          simp
        · rw [← lie_skew, t.lie_e_f, neg_mem_iff]
          apply subset_span
          simp
        · rw [← lie_skew, t.lie_h_f_nsmul, neg_neg]
          apply nsmul_mem <| subset_span _
          simp
        · rw [t.lie_h_e_nsmul]
          apply nsmul_mem <| subset_span _
          simp
        · rw [t.lie_h_f_nsmul, neg_mem_iff]
          apply nsmul_mem <| subset_span _
          simp

lemma mem_toLieSubalgebra_iff {x : L} {t : IsSl2Triple h e f} :
    x ∈ t.toLieSubalgebra R ↔ ∃ c₁ c₂ c₃ : R, x = c₁ • e + c₂ • f + c₃ • ⁅e, f⁆ := by
  simp_rw [t.lie_e_f, toLieSubalgebra, ← LieSubalgebra.mem_toSubmodule, Submodule.mem_span_triple,
    eq_comm]

end IsSl2Triple


namespace LieAlgebra

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

open Module LieModule Set
open Submodule renaming span → span
open Submodule renaming subset_span → subset_span

namespace IsKilling

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
variable [IsKilling K L]
variable {K L H}
variable [IsTriangularizable K H L]

section CharZero

variable [CharZero K]

/-- The embedded `sl₂` associated to a root. -/
noncomputable def sl2SubalgebraOfRoot {α : Weight K H L} (hα : α.IsNonZero) :
    LieSubalgebra K L := by
  choose h e f t ht using exists_isSl2Triple_of_weight_isNonZero hα
  exact t.toLieSubalgebra K

lemma mem_sl2SubalgebraOfRoot_iff {α : Weight K H L} (hα : α.IsNonZero) {h e f : L}
    (t : IsSl2Triple h e f) (hte : e ∈ rootSpace H α) (htf : f ∈ rootSpace H (-α)) {x : L} :
    x ∈ sl2SubalgebraOfRoot hα ↔ ∃ c₁ c₂ c₃ : K, x = c₁ • e + c₂ • f + c₃ • ⁅e, f⁆ := by
  simp only [sl2SubalgebraOfRoot, IsSl2Triple.mem_toLieSubalgebra_iff]
  generalize_proofs _ _ _ he hf
  obtain ⟨ce, hce⟩ : ∃ c : K, he.choose = c • e := by
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨e, hte⟩ (by simpa using t.e_ne_zero)).mp
      (finrank_rootSpace_eq_one α hα) ⟨_, he.choose_spec.choose_spec.2.1⟩
    exact ⟨c, by simpa using hc.symm⟩
  obtain ⟨cf, hcf⟩ : ∃ c : K, hf.choose = c • f := by
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨f, htf⟩ (by simpa using t.f_ne_zero)).mp
      (finrank_rootSpace_eq_one (-α) (by simpa)) ⟨_, hf.choose_spec.2.2⟩
    exact ⟨c, by simpa using hc.symm⟩
  have hce₀ : ce ≠ 0 := by
    rintro rfl
    simp only [zero_smul] at hce
    exact he.choose_spec.choose_spec.1.e_ne_zero hce
  have hcf₀ : cf ≠ 0 := by
    rintro rfl
    simp only [zero_smul] at hcf
    exact he.choose_spec.choose_spec.1.f_ne_zero hcf
  simp_rw [hcf, hce]
  refine ⟨fun ⟨c₁, c₂, c₃, hx⟩ ↦ ⟨c₁ * ce, c₂ * cf, c₃ * cf * ce, ?_⟩,
    fun ⟨c₁, c₂, c₃, hx⟩ ↦ ⟨c₁ * ce⁻¹, c₂ * cf⁻¹, c₃ * ce⁻¹ * cf⁻¹, ?_⟩⟩
  · simp [hx, mul_smul]
  · simp [hx, mul_smul, hce₀, hcf₀]

/-- The `sl₂` subalgebra associated to a root, regarded as a Lie submodule over the Cartan
subalgebra. -/
noncomputable def sl2SubmoduleOfRoot {α : Weight K H L} (hα : α.IsNonZero) :
    LieSubmodule K H L where
  __ := sl2SubalgebraOfRoot hα
  lie_mem {h} x hx := by
    suffices ⁅(h : L), x⁆ ∈ sl2SubalgebraOfRoot hα by simpa
    obtain ⟨h', e, f, ht, heα, hfα⟩ := exists_isSl2Triple_of_weight_isNonZero hα
    replace hx : x ∈ sl2SubalgebraOfRoot hα := hx
    obtain ⟨c₁, c₂, c₃, rfl⟩ := (mem_sl2SubalgebraOfRoot_iff hα ht heα hfα).mp hx
    rw [mem_sl2SubalgebraOfRoot_iff hα ht heα hfα, lie_add, lie_add, lie_smul, lie_smul, lie_smul]
    have he_wt : ⁅(h : L), e⁆ = α h • e := lie_eq_smul_of_mem_rootSpace heα h
    have hf_wt : ⁅(h : L), f⁆ = (-α) h • f := lie_eq_smul_of_mem_rootSpace hfα h
    have hef_zero : ⁅(h : L), ⁅e, f⁆⁆ = 0 := by
      suffices h_coroot_in_zero : ⁅e, f⁆ ∈ rootSpace H (0 : H → K) from
        lie_eq_smul_of_mem_rootSpace h_coroot_in_zero h ▸ (zero_smul K ⁅e, f⁆)
      rw [ht.lie_e_f, IsSl2Triple.h_eq_coroot hα ht heα hfα, rootSpace_zero_eq K L H]
      exact (coroot α).property
    exact ⟨c₁ * α h, c₂ * (-α h), 0, by simp [he_wt, hf_wt, hef_zero, smul_smul]⟩

/-- The coroot space of `α` viewed as a submodule of the ambient Lie algebra `L`.
This represents the image of the coroot space under the inclusion `H ↪ L`. -/
noncomputable abbrev corootSubmodule (α : Weight K H L) : LieSubmodule K H L :=
  LieSubmodule.map H.toLieSubmodule.incl (corootSpace α)

open Submodule in
lemma sl2SubmoduleOfRoot_eq_sup (α : Weight K H L) (hα : α.IsNonZero) :
    sl2SubmoduleOfRoot hα = genWeightSpace L α ⊔ genWeightSpace L (-α) ⊔ corootSubmodule α := by
  ext x
  obtain ⟨h', e, f, ht, heα, hfα⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · replace hx : x ∈ sl2SubalgebraOfRoot hα := hx
    obtain ⟨c₁, c₂, c₃, rfl⟩ := (mem_sl2SubalgebraOfRoot_iff hα ht heα hfα).mp hx
    refine add_mem (add_mem ?_ ?_) ?_
    · exact mem_sup_left <| mem_sup_left <| smul_mem _ _ heα
    · exact mem_sup_left <| mem_sup_right <| smul_mem _ _ hfα
    · suffices ∃ y ∈ corootSpace α, H.subtype y = c₃ • h' from
        mem_sup_right <| by simpa [ht.lie_e_f, -Subtype.exists]
      obtain ⟨ y, hy ⟩ : ∃ y ∈ LieAlgebra.corootSpace α, (H.subtype : ↥H.toSubmodule → L) y = h' := by
        norm_num +zetaDelta at ⊢;
        use by
          have h_h'_in_H : h' ∈ H := by
            have := ht
            cases this;
            have h'_in_H : h' ∈ H := by
              have h'_root : ⁅e, f⁆ = h' := by
                assumption
              rw [ ← h'_root ];
              have h'_root : ⁅e, f⁆ ∈ rootSpace H (α + (-α)) := by
                exact lie_mem_genWeightSpace_of_mem_genWeightSpace heα hfα;
              simp +zetaDelta at h'_root;
              exact h'_root
            exact h'_in_H;
          exact h_h'_in_H
        rw [ LieAlgebra.mem_corootSpace ];
        rw [ Submodule.mem_span ];
        intro p hp;
        convert hp ⟨ e, heα, f, hfα, ?_ ⟩ using 1
        exact ht.lie_e_f;
      use c₃ • y;
      simp_all only [subtype_apply, map_smul, and_true]
      obtain ⟨val, property⟩ := y
      obtain ⟨left, right⟩ := hy
      subst right
      apply SMulMemClass.smul_mem
      simp_all only
  · have aux {β : Weight K H L} (hβ : β.IsNonZero) {y g : L}
        (hy : y ∈ genWeightSpace L β) (hg : g ∈ rootSpace H β) (hg_ne_zero : g ≠ 0) :
        ∃ c : K, y = c • g := by
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨g, hg⟩
        (by rwa [ne_eq, LieSubmodule.mk_eq_zero])).mp (finrank_rootSpace_eq_one β hβ) ⟨y, hy⟩
      exact ⟨c, by simpa using hc.symm⟩
    obtain ⟨x_αneg, hx_αneg, x_h, ⟨y, hy_coroot, rfl⟩, rfl⟩ := mem_sup.mp hx
    obtain ⟨x_pos, hx_pos, x_neg, hx_neg, rfl⟩ := mem_sup.mp hx_αneg
    obtain ⟨c₁, rfl⟩ := aux hα hx_pos heα ht.e_ne_zero
    obtain ⟨c₂, rfl⟩ := aux (Weight.IsNonZero.neg hα) hx_neg hfα ht.f_ne_zero
    obtain ⟨c₃, rfl⟩ : ∃ c₃ : K, c₃ • coroot α = y := by
      simpa [← mem_span_singleton, ← coe_corootSpace_eq_span_singleton α]
    change _ ∈ sl2SubalgebraOfRoot hα
    rw [mem_sl2SubalgebraOfRoot_iff hα ht heα hfα]
    use c₁, c₂, c₃
    simp [ht.lie_e_f, IsSl2Triple.h_eq_coroot hα ht heα hfα, -LieSubmodule.incl_coe]



end CharZero

end IsKilling

end LieAlgebra


namespace LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
open LieAlgebra LieModule Module
variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

-- Note that after https://github.com/leanprover-community/mathlib4/issues/10068 (Cartan's criterion) is complete we can omit `[IsKilling K L]`
variable [IsKilling K L] [IsTriangularizable K H L]

section aux

variable (q : Submodule K (Dual K H))
  (hq : ∀ i, q ∈ End.invtSubmodule ((rootSystem H).reflection i))
  (χ : Weight K H L)
  (x_χ m_α : L) (hx_χ : x_χ ∈ genWeightSpace L χ)
  (α : Weight K H L) (hαq : ↑α ∈ q) (hα₀ : α.IsNonZero)

section

variable
  (w_plus : χ.toLinear + α.toLinear ≠ 0)
  (w_minus : χ.toLinear - α.toLinear ≠ 0)
  (w_chi : χ.toLinear ≠ 0)
  (m_pos m_neg : L)
  (y : H) (hy : y ∈ corootSpace α)
  (h_bracket_sum : ⁅x_χ, m_α⁆ = ⁅x_χ, m_pos⁆ + ⁅x_χ, m_neg⁆ + ⁅x_χ, (y : L)⁆)
  (h_pos_containment : ⁅x_χ, m_pos⁆ ∈ genWeightSpace L (⇑χ + ⇑α))
  (h_neg_containment : ⁅x_χ, m_neg⁆ ∈ genWeightSpace L (⇑χ - ⇑α))

include hx_χ w_plus w_minus w_chi h_bracket_sum h_pos_containment h_neg_containment hαq

private theorem chi_in_q_aux (h_chi_in_q : ↑χ ∈ q) :
    ⁅x_χ, m_α⁆ ∈ ⨆ α : {α : Weight K H L // ↑α ∈ q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2 := by
  sorry
