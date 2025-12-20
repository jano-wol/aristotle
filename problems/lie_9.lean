import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

namespace LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
open LieAlgebra LieModule Module
variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
variable [IsKilling K L] [IsTriangularizable K H L]

/--
  PROVIDED SOLUTION:
  Since I is an ideal, H acts on I via ad. Elements of H act semisimply, so I has a basis of
  common eigenvectors for ad H. These lie in genWeightSpace since for semisimple operators,
  generalized eigenspaces equal eigenspaces.

  KEY LEMMAS:
  - `LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra`:
      For x ∈ H, `(ad K L x).IsSemisimple`
  - `Module.End.IsSemisimple.genEigenspace_eq_eigenspace`:
      For semisimple f, generalized eigenspaces = eigenspaces
  - `LieModule.genWeightSpace`: defined as `⨅ x, genWeightSpaceOf M (χ x) x`
-/
lemma exists_lieIdeal_generating_set_mem_genWeightSpace (I : LieIdeal K L) :
    ∃ S : Set L, Submodule.span K S = I.toSubmodule ∧
      ∀ x ∈ S, ∃ χ : Weight K H L, x ∈ genWeightSpace L χ := by
  sorry

end LieAlgebra.IsKilling
