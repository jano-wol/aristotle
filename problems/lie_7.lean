import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

namespace LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
open LieAlgebra LieModule Module
variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
variable [IsKilling K L] [IsTriangularizable K H L]


lemma lieIdeal_eq_iSup_inf_genWeightSpace (I : LieIdeal K L) :
    I.toSubmodule = ⨆ χ : Weight K H L, I.toSubmodule ⊓ (genWeightSpace L χ).toSubmodule := by admit

/--
  PROVIDED SOLUTION:
  Use `lieIdeal_eq_iSup_inf_genWeightSpace` and split the sup into zero and nonzero weights.
  For the zero weight, `genWeightSpace L 0 = H` by `rootSpace_zero_eq`.

  KEY LEMMAS:
  - `lieIdeal_eq_iSup_inf_genWeightSpace`: I = ⨆ χ, I ⊓ genWeightSpace L χ
  - `LieAlgebra.rootSpace_zero_eq`: genWeightSpace L 0 = H
-/
lemma lieIdeal_eq_iSup_inf (I : LieIdeal K L) :
    I.toSubmodule = (I.toSubmodule ⊓ H.toLieSubmodule.toSubmodule) ⊔
      ⨆ α : {α : Weight K H L // α.IsNonZero}, I.toSubmodule ⊓ (genWeightSpace L α.1).toSubmodule := by
  sorry

end LieAlgebra.IsKilling
