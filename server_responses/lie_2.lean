/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 211c7d16-4c18-4317-a033-6615ade2680a

The following was proved by Aristotle:

- theorem isCompl_killingCompl (I : LieIdeal K L) :
    IsCompl I I.killingCompl
-/

import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.TraceForm
import Mathlib.Algebra.Lie.Weights.RootSystem


variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]

namespace LieIdeal

noncomputable section AristotleLemmas

#check LieAlgebra.IsKilling.instSemisimple

/-
The lattice complement of an ideal in a semisimple Lie algebra is contained in its Killing orthogonal complement.
-/
theorem compl_le_killingCompl (I : LieIdeal K L) : Iᶜ ≤ I.killingCompl := by
  haveI : LieAlgebra.IsSemisimple K L := LieAlgebra.IsKilling.instSemisimple K L
  intro y;
  aesop;
  -- Since $I$ and $J$ are ideals, $[I, J] \leq I \cap J = 0$.
  have h_comm : ∀ x ∈ I, ∀ y ∈ Iᶜ, ⁅x, y⁆ = 0 := by
    have h_comm : ⁅I, Iᶜ⁆ ≤ I ⊓ Iᶜ := by
      exact le_inf ( LieSubmodule.lie_le_left _ _ ) ( LieSubmodule.lie_le_right _ _ );
    simp_all +decide [ LieSubmodule.lie_eq_bot_iff ];
  -- Since $⁅x, y⁆ = 0$ for all $x \in I$ and $y \in Iᶜ$, we have that $\text{ad } x \circ \text{ad } y = 0$.
  have h_ad_zero : ∀ x ∈ I, ∀ y ∈ Iᶜ, LinearMap.comp (LieAlgebra.ad K L x) (LieAlgebra.ad K L y) = 0 := by
    intro x hx y hy; ext z; simp +decide [ h_comm x hx y hy ] ;
    convert h_comm x hx ( ⁅y, z⁆ ) _ using 1;
    exact?;
  -- Since $\text{ad } x \circ \text{ad } y = 0$, its trace is zero.
  have h_trace_zero : ∀ x ∈ I, ∀ y ∈ Iᶜ, LinearMap.trace K L (LinearMap.comp (LieAlgebra.ad K L x) (LieAlgebra.ad K L y)) = 0 := by
    aesop;
  exact h_trace_zero _ a_1 _ a

#print killingForm
#check LieModule.traceForm_apply_lie_apply
#check LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot

/-
The bracket of two elements in the intersection of an ideal and its Killing orthogonal complement is zero.
-/
theorem lie_mem_inf_killingCompl_eq_zero (I : LieIdeal K L) (x y : L) (hx : x ∈ I ⊓ I.killingCompl) (hy : y ∈ I ⊓ I.killingCompl) : ⁅x, y⁆ = 0 := by
  -- Since $y \in I \cap I^\perp \subseteq I$ and $I$ is an ideal, $[y, z] \in I$.
  have h_yz : ∀ z : L, ⁅y, z⁆ ∈ I := by
    aesop;
    exact?;
  have h_zero : ∀ z : L, (LieModule.traceForm K L L) ⁅x, y⁆ z = 0 := by
    -- Since $x \in I \cap I^\perp \subseteq I^\perp$, $\kappa(x, w) = 0$ for all $w \in I$.
    have h_xw : ∀ w ∈ I, (LieModule.traceForm K L L) x w = 0 := by
      aesop;
      rw [ ← right _ a, ← LieModule.traceForm_comm ];
    intro z
    have h_kappa_zero_step : LieModule.traceForm K L L ⁅x, y⁆ z = LieModule.traceForm K L L x ⁅y, z⁆ := by
      exact?;
    rw [ h_kappa_zero_step, h_xw _ ( h_yz z ) ];
  -- Since the Killing form is non-degenerate, if $\kappa([x, y], z) = 0$ for all $z \in L$, then $[x, y] = 0$.
  have h_nondeg : LinearMap.BilinForm.Nondegenerate (LieModule.traceForm K L L) := by
    exact?;
  exact?

#print IsLieAbelian
#check LieAlgebra.IsKilling.ideal_eq_bot_of_isLieAbelian

#print LieModule.IsTrivial

#check LieSubmodule.lie_abelian_iff_lie_self_eq_bot

#check LieSubmodule.lie_eq_bot_iff

/-
An ideal in a semisimple Lie algebra is disjoint from its Killing orthogonal complement.
-/
theorem disjoint_killingCompl (I : LieIdeal K L) : Disjoint I I.killingCompl := by
  -- Let $J = I \cap I^\perp$. We have shown that for any $x, y \in J$, $[x, y] = 0$. Thus $J$ is an abelian ideal.
  set J := I ⊓ I.killingCompl with hJ;
  -- Since $J$ is an abelian ideal, we have $J = 0$.
  have hJ_zero : J = ⊥ := by
    have h_abelian : IsLieAbelian J := by
      refine' ⟨ fun x y => _ ⟩;
      exact Subtype.ext ( lie_mem_inf_killingCompl_eq_zero I x y x.2 y.2 )
    exact?;
  exact disjoint_iff.mpr hJ_zero

#check Module.finrank

#check LieSubmodule.sup_toSubmodule
#check LieSubmodule.inf_toSubmodule
#check LieSubmodule.toSubmodule_eq_top
#check LieIdeal.toSubmodule_killingCompl

#check LieSubmodule.bot_toSubmodule
#check LinearMap.IsSymm.isRefl

/-
An ideal in a semisimple Lie algebra is codisjoint from its Killing orthogonal complement.
-/
theorem codisjoint_killingCompl (I : LieIdeal K L) : Codisjoint I I.killingCompl := by
  have h_compl_le_killingCompl : Iᶜ ≤ I.killingCompl := by
    exact?;
  -- Since $Iᶜ \leq I.killingCompl$, we have $I \⊔ Iᶜ = \top$.
  have h_union : I ⊔ Iᶜ = ⊤ := by
    exact?;
  rw [ codisjoint_iff_le_sup ];
  exact h_union ▸ sup_le_sup_left h_compl_le_killingCompl _

#check LieSubmodule.toSubmodule_inj

#check LieIdeal.codisjoint_killingCompl

end AristotleLemmas

theorem isCompl_killingCompl (I : LieIdeal K L) :
    IsCompl I I.killingCompl := by
  constructor;
  · exact?;
  · apply_rules [ codisjoint_killingCompl ]

end LieIdeal