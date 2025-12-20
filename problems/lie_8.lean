import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

namespace LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
open LieAlgebra LieModule Module
variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
variable [IsKilling K L] [IsTriangularizable K H L]

/--
  PROVIDED SOLUTION:
  Since H consists of semisimple elements, it acts diagonalisably on I, and so I has a basis of common
  eigenvectors for the elements of ad H. As we know that each root space L α is 1-dimensional by
  LieAlgebra.IsKilling.finrank_rootSpace_eq_one, this implies lieIdeal_eq_iSup_inf.

  KEY LEMMAS:
  - `LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra`:
      For x ∈ H, `(ad K L x).IsSemisimple` (H consists of semisimple elements)
  - `LieModule.iSup_genWeightSpace_eq_top'`:
      Weight spaces span L
  - `LieAlgebra.rootSpace_zero_eq`:
      The zero root space equals H
  - `LieModule.iSupIndep_genWeightSpace'`:
      Weight spaces are independent
  - `LieAlgebra.IsKilling.finrank_rootSpace_eq_one`:
      Each nonzero root space is 1-dimensional
-/
lemma lieIdeal_eq_iSup_inf_genWeightSpace (I : LieIdeal K L) :
    I.toSubmodule = ⨆ χ : Weight K H L, I.toSubmodule ⊓ (genWeightSpace L χ).toSubmodule := by
  sorry

end LieAlgebra.IsKilling
