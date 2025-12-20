/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2eb11bda-6e25-40c9-9e5c-b3e3c732f90f

The following was proved by Aristotle:

- lemma iSup_rootSpace_eq_top :
    H.toLieSubmodule ⊔ ⨆ α : {α : Weight K H L // α.IsNonZero}, genWeightSpace L α = ⊤
-/

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
  by_contra h_contra;
  -- Since $L$ is decomposed into the sum of the zero weight space and the nonzero weight spaces, and $H$ is the Cartan subalgebra, it must be that $L$ is equal to the sum of $H$ and the nonzero weight spaces.
  have h_decomp : (⨆ (α : LieModule.Weight K H L), (LieModule.genWeightSpace L α)) = ⊤ := by
    exact?;
  refine' h_contra ( eq_top_iff.mpr _ );
  rw [ ← h_decomp ];
  simp +decide [ iSup_le_iff ];
  intro α;
  by_cases hα : α.IsZero;
  · simp [hα];
  · exact le_sup_of_le_right ( le_iSup_of_le ⟨ α, hα ⟩ le_rfl )

end LieAlgebra.IsKilling