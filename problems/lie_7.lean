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

/--
  PROVIDED SOLUTION::
  Since H consists of semisimple elements, it acts diagonalisably on I, and so I has a basis of common
  eigenvectors for the elements of ad H. As we know that each root space L α is 1-dimensional by
  LieAlgebra.IsKilling.finrank_rootSpace_eq_one, this implies lieIdeal_eq_iSup_inf.
-/
lemma lieIdeal_eq_iSup_inf (I : LieIdeal K L) :
    I.toSubmodule = (I.toSubmodule ⊓ H.toLieSubmodule.toSubmodule) ⊔
      ⨆ α : {α : Weight K H L // α.IsNonZero}, I.toSubmodule ⊓ (genWeightSpace L α.1).toSubmodule := by
  sorry

end LieAlgebra.IsKilling
