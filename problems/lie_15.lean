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
    sorry
  let J := I.killingCompl
  obtain ⟨Φ₁, hΦ₁⟩ := exists_rootSet_lieIdeal_eq (H := H) I
  obtain ⟨Φ₂, hΦ₂⟩ := exists_rootSet_lieIdeal_eq (H := H) J

  have s1 : H.toSubmodule = (I.toSubmodule ⊓ H.toSubmodule) ⊔ (J.toSubmodule ⊓ H.toSubmodule) := by
    sorry
  have s2 : Φ₁ ∩ Φ₂ = ∅ := by
    sorry
  have s3 : Φ₁ ∪ Φ₂ = Set.univ := by
    sorry
  have s4 : Φ₁ ≠ ∅ := by
    sorry
  admit

end LieAlgebra.IsKilling
