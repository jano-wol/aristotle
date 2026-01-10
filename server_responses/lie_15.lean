/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 51ba86c9-3bd7-45ad-80ad-12ba3efb4691

The following was proved by Aristotle:

- theorem isSimple_of_isIrreducible (hIrr : (rootSystem H).IsIrreducible) : IsSimple K L
-/

import Mathlib.Algebra.Lie.Weights.IsSimple
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas


namespace LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]

open LieAlgebra LieModule Module

variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

variable [IsKilling K L] [IsTriangularizable K H L]

lemma cartan_sup_iSup_rootSpace_eq_top :
    H.toLieSubmodule ⊔ ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), rootSpace H α = ⊤ := by
  admit

lemma exists_rootSet_lieIdeal_eq (I : LieIdeal K L) :
    ∃ Φ : Set H.root, I.toSubmodule = (I.toSubmodule ⊓ H.toSubmodule) ⊔
      ⨆ α ∈ Φ, (rootSpace H α.1).toSubmodule := by
  admit

theorem isCompl_killingCompl (I : LieIdeal K L) :
    IsCompl I I.killingCompl := by
  admit

theorem compl_eq_killingCompl (I : LieIdeal K L) :
    Iᶜ = I.killingCompl := by
  admit

noncomputable section AristotleLemmas

#check RootPairing.IsIrreducible
#print RootSystem

#check IsLieAbelian

lemma cartan_is_abelian : IsLieAbelian H := by
  constructor ; aesop

lemma cartan_eq_sup_inf_ideal (I : LieIdeal K L) (hI : IsCompl I I.killingCompl) :
    H.toSubmodule = (I.toSubmodule ⊓ H.toSubmodule) ⊔ (I.killingCompl.toSubmodule ⊓ H.toSubmodule) := by
  -- Since $I$ and $J$ are complementary ideals, we have $H \subseteq (H \cap I) + (H \cap J)$.
  have h_le : H.toSubmodule ≤ (I : Submodule K L) ⊓ H.toSubmodule ⊔ (LieIdeal.killingCompl K L I : Submodule K L) ⊓ H.toSubmodule := by
    intro x hx;
    -- Since $I$ and $J$ are complementary, $x$ can be written as $x = i + j$ with $i \in I$ and $j \in J$.
    obtain ⟨i, j, hi, hj, hx_eq⟩ : ∃ i j : L, i ∈ I ∧ j ∈ LieIdeal.killingCompl K L I ∧ x = i + j := by
      have := hI.sup_eq_top;
      replace this := Submodule.mem_sup.mp ( this.symm ▸ Submodule.mem_top : x ∈ I ⊔ LieIdeal.killingCompl K L I ) ; aesop;
    -- Since $H$ is abelian, we have $[i, x] = 0$ and $[j, x] = 0$ for all $x \in H$.
    have h_comm : ∀ x ∈ H, ⁅i, x⁆ = 0 ∧ ⁅j, x⁆ = 0 := by
      intro x hx
      have h_comm_i : ⁅i, x⁆ ∈ I := by
        exact?
      have h_comm_j : ⁅j, x⁆ ∈ LieIdeal.killingCompl K L I := by
        exact?
      have h_comm_zero : ⁅i, x⁆ + ⁅j, x⁆ = 0 := by
        have h_comm_zero : ⁅x, i + j⁆ = 0 := by
          have h_comm_zero : ∀ x ∈ H, ∀ y ∈ H, ⁅x, y⁆ = 0 := by
            have h_comm_zero : IsLieAbelian H := by
              exact?;
            intro x hx y hy; exact (by
            have := h_comm_zero.1 ⟨ x, hx ⟩ ⟨ y, hy ⟩;
            exact Subtype.ext_iff.mp this);
          aesop;
        rw [ ← neg_eq_zero, ← lie_skew, ← lie_skew ];
        simp_all +decide [ lie_add, add_comm ];
      have h_comm_zero : ⁅i, x⁆ ∈ I ⊓ LieIdeal.killingCompl K L I := by
        simp_all +decide [ add_eq_zero_iff_eq_neg ];
        intro y hy; specialize h_comm_j y hy; simp_all +decide [ killingForm, lie_skew ] ;
        simp_all +decide [ LieModule.traceForm, lie_skew ];
        simp_all +decide [ LieRing.of_associative_ring_bracket, mul_assoc ];
        simp_all +decide [ mul_sub, sub_mul, mul_assoc ];
        rw [ sub_eq_zero ] at * ; aesop;
      have := hI.disjoint.le_bot h_comm_zero; aesop;
    -- Since $i$ and $j$ are in the centralizer of $H$, they are in $H$.
    have h_i_j_in_H : i ∈ H ∧ j ∈ H := by
      have h_i_j_in_H : ∀ x : L, (∀ y ∈ H, ⁅x, y⁆ = 0) → x ∈ H := by
        intro x hx_comm
        have h_normalizer : x ∈ LieSubalgebra.normalizer H := by
          simp +decide [ LieSubalgebra.mem_normalizer_iff, hx_comm ];
          exact fun y hy => by rw [ hx_comm y hy ] ; exact H.zero_mem;
        have h_self_normalizing : H.normalizer = H := by
          exact?;
        exact h_self_normalizing ▸ h_normalizer;
      exact ⟨ h_i_j_in_H i fun y hy => h_comm y hy |>.1, h_i_j_in_H j fun y hy => h_comm y hy |>.2 ⟩;
    exact Submodule.mem_sup.mpr ⟨ i, ⟨ hi, h_i_j_in_H.1 ⟩, j, ⟨ hj, h_i_j_in_H.2 ⟩, by simp +decide [ hx_eq ] ⟩;
  exact le_antisymm h_le ( sup_le ( inf_le_right ) ( inf_le_right ) )

def RootSystem.IsIrreducible {ι R M N} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (P : RootSystem ι R M N) : Prop := RootPairing.IsIrreducible P.toRootPairing

end AristotleLemmas

theorem isSimple_of_isIrreducible (hIrr : (rootSystem H).IsIrreducible) : IsSimple K L := by
  by_contra h_not_simple
  obtain ⟨I, hI_ne_bot, hI_ne_top⟩ : ∃ I : LieIdeal K L, I ≠ ⊥ ∧ I ≠ ⊤ := by
    have h_not_simple_def : ¬LieAlgebra.IsSimple K L → ∃ I : LieIdeal K L, I ≠ ⊥ ∧ I ≠ ⊤ := by
      intro h_not_simple_def
      simp [LieAlgebra.IsSimple] at h_not_simple_def;
      contrapose! h_not_simple_def;
      constructor;
      · exact fun I => Classical.or_iff_not_imp_left.2 fun h => h_not_simple_def I h;
      · cases subsingleton_or_nontrivial L <;> simp_all +decide [ LieAlgebra.IsKilling ];
        · have := hIrr.1; simp_all +decide [ LieAlgebra.IsKilling.rootSystem ] ;
          exact False.elim ( this.exists_pair_ne.elim fun x hx => hx.elim fun y hy => hy <| Subsingleton.elim _ _ );
        · intro h_abelian
          have h_center : LieAlgebra.center K L = ⊤ := by
            exact?
          have h_center_eq_bot : LieAlgebra.center K L = ⊥ := by
            exact?
          exact absurd h_center_eq_bot (by
          simp +decide [ h_center ];
          exact absurd ( h_center_eq_bot ▸ h_center ) ( by simp +decide [ LieSubmodule.eq_bot_iff ] ));
    exact h_not_simple_def h_not_simple
  let J := I.killingCompl
  obtain ⟨Φ₁, hΦ₁⟩ := exists_rootSet_lieIdeal_eq (H := H) I
  obtain ⟨Φ₂, hΦ₂⟩ := exists_rootSet_lieIdeal_eq (H := H) J

  have s1 : H.toSubmodule = (I.toSubmodule ⊓ H.toSubmodule) ⊔ (J.toSubmodule ⊓ H.toSubmodule) := by
    have h_cartan_decomp : H.toSubmodule = (I.toSubmodule ⊓ H.toSubmodule) ⊔ (J.toSubmodule ⊓ H.toSubmodule) := by
      have h_compl : IsCompl I J := by
        exact?
      exact?;
    exact h_cartan_decomp
/-
  have s2 : Φ₁ ∩ Φ₂ = ∅ := by
    sorry
  have s3 : Φ₁ ∪ Φ₂ = Set.univ := by
    sorry
  have s4 : Φ₁ ≠ ∅ := by
    sorry
--/
  admit

end LieAlgebra.IsKilling
