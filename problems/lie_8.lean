import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

namespace LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
open LieAlgebra LieModule Module
variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
variable [IsKilling K L] [IsTriangularizable K H L]

lemma exists_lieIdeal_generating_set_mem_genWeightSpace (I : LieIdeal K L) :
    ∃ S : Set L, Submodule.span K S = I.toSubmodule ∧ ∀ x ∈ S, ∃ χ : Weight K H L, x ∈ genWeightSpace L χ := by admit

/--
  PROVIDED SOLUTION:
  Use `exists_lieIdeal_generating_set_mem_genWeightSpace`: I has a generating set S where each
  element lies in some weight space. Each s ∈ S satisfies s ∈ I ⊓ genWeightSpace L χ for some χ,
  so Span S ≤ ⨆ χ, I ⊓ genWeightSpace L χ. The reverse inclusion is trivial.

  KEY LEMMAS:
  - `exists_lieIdeal_generating_set_mem_genWeightSpace`: I has generators in weight spaces
-/
lemma lieIdeal_eq_iSup_inf_genWeightSpace (I : LieIdeal K L) :
    I.toSubmodule = ⨆ χ : Weight K H L, I.toSubmodule ⊓ (genWeightSpace L χ).toSubmodule := by
  sorry

end LieAlgebra.IsKilling
