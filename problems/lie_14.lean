import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

namespace LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
open LieAlgebra LieModule Module
variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
variable [IsKilling K L] [IsTriangularizable K H L]


lemma lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace (I : LieIdeal K L) :
    I.toSubmodule = (I.toSubmodule ⊓ H.toSubmodule) ⊔
      ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), I.toSubmodule ⊓ (genWeightSpace L α.1).toSubmodule := by
  admit

/--
  PROVIDED SOLUTION:
  A Lie ideal decomposes as its intersection with the Cartan subalgebra plus a direct sum of
  root spaces corresponding to some subset Φ of roots. This follows from the fact that root spaces
  are 1-dimensional, so the intersection of I with each root space is either trivial or the full
  root space.
-/
lemma exists_rootSet_lieIdeal_eq (I : LieIdeal K L) :
    ∃ Φ : Set H.root, I.toSubmodule = (I.toSubmodule ⊓ H.toSubmodule) ⊔
      ⨆ α ∈ Φ, (rootSpace H α.1).toSubmodule := by
  sorry

end LieAlgebra.IsKilling
