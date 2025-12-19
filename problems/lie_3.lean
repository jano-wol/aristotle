import Mathlib.Algebra.Lie.Weights.IsSimple
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
variable [LieAlgebra.IsKilling K L] [LieModule.IsTriangularizable K H L]

namespace LieAlgebra.IsKilling

@[simp] lemma invtSubmoduleToLieIdeal_top :
    invtSubmoduleToLieIdeal (⊤ : Submodule K (Module.Dual K H)) (by simp) = ⊤ := by
  rw [← LieSubmodule.toSubmodule_inj, invtSubmoduleToLieIdeal, LieSubmodule.iSup_toSubmodule,
    LieSubmodule.top_toSubmodule, Submodule.eq_top_iff']
  sorry

end LieAlgebra.IsKilling
