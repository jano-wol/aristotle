/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 96e9f439-dafe-4235-ae56-31db33ff50e4

The following was proved by Aristotle:

- lemma lieIdeal_eq_iSup_inf_genWeightSpace (I : LieIdeal K L) :
    I.toSubmodule = ⨆ χ : Weight K H L, I.toSubmodule ⊓ (genWeightSpace L χ).toSubmodule
-/

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
  rw [ eq_comm ];
  -- By definition of LieModule.IsTriangularizable, there exists a generating set S such that each element of S lies in some generalized weight space.
  obtain ⟨S, hS⟩ : ∃ S : Set L, Submodule.span K S = I.toSubmodule ∧ ∀ x ∈ S, ∃ χ : Weight K H L, x ∈ genWeightSpace L χ := by
    exact?;
  refine' le_antisymm _ _;
  · exact iSup_le fun χ => inf_le_left;
  · rw [ ← hS.1, Submodule.span_le ];
    intro x hx;
    obtain ⟨ χ, hχ ⟩ := hS.2 x hx;
    exact Submodule.mem_iSup_of_mem χ ( Submodule.mem_inf.mpr ⟨ Submodule.subset_span hx, hχ ⟩ )

end LieAlgebra.IsKilling