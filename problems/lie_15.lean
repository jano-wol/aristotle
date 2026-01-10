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
    sorry
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
