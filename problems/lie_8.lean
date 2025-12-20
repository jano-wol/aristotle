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
  common eigenvectors for ad H. These are weight vectors, so I is spanned by I ∩ (weight spaces).

  KEY LEMMAS:
  - `LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra`:
      For x ∈ H, `(ad K L x).IsSemisimple`
  - `LieModule.iSup_genWeightSpace_eq_top'`: Weight spaces span L
  - `LieModule.iSupIndep_genWeightSpace'`: Weight spaces are independent
-/
lemma lieIdeal_eq_iSup_inf_genWeightSpace (I : LieIdeal K L) :
    I.toSubmodule = ⨆ χ : Weight K H L, I.toSubmodule ⊓ (genWeightSpace L χ).toSubmodule := by
  sorry

end LieAlgebra.IsKilling
