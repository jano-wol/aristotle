import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

namespace LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
open LieAlgebra LieModule Module
variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
variable [IsKilling K L] [IsTriangularizable K H L]

/-- The root space decomposition: L decomposes as the Cartan subalgebra H
together with the sum of all nonzero root spaces. -/
lemma iSup_rootSpace_eq_top :
    H.toLieSubmodule ⊔ ⨆ α : {α : Weight K H L // α.IsNonZero}, genWeightSpace L α = ⊤ := by
  sorry

end LieAlgebra.IsKilling
