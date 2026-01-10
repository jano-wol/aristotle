/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f15090ca-e7c5-410d-aef3-6b2c3e48b746

The following was proved by Aristotle:

- theorem compl_eq_killingCompl (I : LieIdeal K L) :
    Iᶜ = I.killingCompl
-/

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
  -- Since the Lie algebra is semisimple, the orthogonal complement of a submodule is the same as its complement in the algebra.
  have h_semisimple : IsCompl I (LieIdeal.killingCompl K L I) := by
    -- Apply the hypothesis that the Lie algebra is semisimple to conclude the proof.
    apply isCompl_killingCompl;
  exact?

end LieIdeal