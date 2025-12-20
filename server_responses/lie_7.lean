/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9623f432-3abd-473f-86e5-77482da1c842

The following was proved by Aristotle:

- lemma lieIdeal_eq_iSup_inf (I : LieIdeal K L) :
    I.toSubmodule = (I.toSubmodule ⊓ H.toLieSubmodule.toSubmodule) ⊔
      ⨆ α : {α : Weight K H L // α.IsNonZero}, I.toSubmodule ⊓ (genWeightSpace L α.1).toSubmodule
-/

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
  -- Apply the hypothesis `h_split` to rewrite the right-hand side of the equation.
  apply le_antisymm;
  · have h_split : I.toSubmodule ≤ ⨆ (χ : Weight K H L), I.toSubmodule ⊓ (genWeightSpace L χ).toSubmodule := by
      convert lieIdeal_eq_iSup_inf_genWeightSpace I |> le_of_eq;
      · infer_instance;
      · infer_instance;
    refine' le_trans h_split _;
    refine' iSup_le _;
    intro χ;
    by_cases hχ : χ.IsZero;
    · simp +decide [ hχ ];
    · exact le_sup_of_le_right ( le_iSup_of_le ⟨ χ, hχ ⟩ le_rfl );
  · aesop

end LieAlgebra.IsKilling