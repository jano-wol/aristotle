import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

namespace LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
open LieAlgebra LieModule Module
variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
variable [IsKilling K L] [IsTriangularizable K H L]


lemma iSup_rootSpace_eq_top :
    H.toLieSubmodule ⊔ ⨆ α : {α : Weight K H L // α.IsNonZero}, genWeightSpace L α = ⊤ := by
  admit

lemma lieIdeal_eq_iSup_inf (I : LieIdeal K L) :
    I.toSubmodule = (I.toSubmodule ⊓ H.toLieSubmodule.toSubmodule) ⊔
      ⨆ α : {α : Weight K H L // α.IsNonZero}, I.toSubmodule ⊓ (genWeightSpace L α.1).toSubmodule := by
  sorry

end LieAlgebra.IsKilling
