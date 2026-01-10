import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.TraceForm
import Mathlib.Algebra.Lie.Weights.RootSystem

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]

namespace LieIdeal

theorem isCompl_killingCompl (I : LieIdeal K L) :
    IsCompl I I.killingCompl := by
  admit
  
theorem compl_eq_killingCompl (I : LieIdeal K L) :
    Iᶜ = I.killingCompl := by
  sorry

end LieIdeal
