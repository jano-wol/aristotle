/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a07cc4b0-f9d6-43ff-8af7-2f5bcbd08131

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

noncomputable section AristotleLemmas

-- Check for HasCompl instance
#synth HasCompl (LieIdeal K L)

-- Check for BooleanAlgebra instance
#synth BooleanAlgebra (LieIdeal K L)

-- Check for IsSemisimple instance
#synth LieAlgebra.IsSemisimple K L

#check LieAlgebra.radical
#check LieAlgebra.HasTrivialRadical
#check LieAlgebra.HasTrivialRadical.radical_eq_bot
#check LieAlgebra.IsSolvable

#check LieAlgebra.IsSolvable
#check LieAlgebra.derivedSeries
#check LieAlgebra.radical

lemma killingForm_eq_zero_of_disjoint (I J : LieIdeal K L) (h : Disjoint I J) (x : I) (y : J) :
    killingForm K L x y = 0 := by
      -- Since $I$ and $J$ are disjoint, their intersection is trivial. Therefore, for any $x \in I$ and $y \in J$, the trace of the linear map $ad(x)ad(y)$ is zero.
      have h_trace_zero : ∀ x : L, ∀ y : L, x ∈ I → y ∈ J → (killingForm K L) x y = 0 := by
        -- Since $I$ and $J$ are ideals, for any $x \in I$ and $y \in J$, the linear map $ad(x)ad(y)$ maps $L$ into $I \cap J$.
        have h_map : ∀ x : L, ∀ y : L, x ∈ I → y ∈ J → ∀ z : L, (LieAlgebra.ad K L x) ((LieAlgebra.ad K L y) z) ∈ I ⊓ J := by
          aesop;
          · exact?;
          · -- Since $J$ is an ideal, we have $⁅y_1, z⁆ \in J$.
            have h_yz : ⁅y_1, z⁆ ∈ J := by
              exact?;
            exact?;
        -- Since the image of the map $ad(x)ad(y)$ is contained in $I \cap J$, and $I$ and $J$ are disjoint, this image must be zero.
        have h_zero_image : ∀ x : L, ∀ y : L, x ∈ I → y ∈ J → ∀ z : L, (LieAlgebra.ad K L x) ((LieAlgebra.ad K L y) z) = 0 := by
          simp_all +decide [ disjoint_iff_inf_le ];
        -- Since the linear map $ad(x)ad(y)$ is zero for all $z \in L$, its trace must also be zero.
        have h_trace_zero : ∀ x : L, ∀ y : L, x ∈ I → y ∈ J → LinearMap.trace K L (LieAlgebra.ad K L x ∘ₗ LieAlgebra.ad K L y) = 0 := by
          intro x y hx hy; rw [ show ( LieAlgebra.ad K L x ∘ₗ LieAlgebra.ad K L y ) = 0 from LinearMap.ext fun z => h_zero_image x y hx hy z ] ; simp +decide ;
        exact?;
      exact h_trace_zero _ _ x.2 y.2

-- Check IsNoetherian instance
example : IsNoetherian K L := inferInstance

-- Check solvability criterion
-- We expect something like:
-- theorem LieAlgebra.isSolvable_of_trace_ad_eq_zero ...

#check LieAlgebra.IsSolvable
variable (I : LieIdeal K L)
#check LieAlgebra.IsSolvable I

lemma isSolvable_of_killing_zero (I : LieIdeal K L) (h : ∀ x ∈ I, ∀ y ∈ I, killingForm K L x y = 0) :
    LieAlgebra.IsSolvable I := by
  -- We know that killingForm K I is the restriction of killingForm K L
  have h_res : killingForm K I = 0 := by
    ext ⟨x, hx⟩ ⟨y, hy⟩
    rw [LieIdeal.killingForm_eq]
    simp
    exact h x hx y hy
  -- Now we need to show that if the Killing form is zero, the Lie algebra is solvable.
  -- This is true in characteristic 0.
  -- We can use `LieAlgebra.isSolvable_of_traceForm_eq_zero` if it exists, or similar.
  -- Since we can't find the exact lemma, we will leave this as sorry for now,
  -- but we hope the ATP can find it or we can find it later.
  -- Actually, let's try to use `LieAlgebra.isSolvable_of_isNilpotent` if we can show it's nilpotent.
  -- But zero Killing form doesn't imply nilpotent in general, only solvable.
  use 1;
  simp_all +decide [ LieSubmodule.lie_eq_bot_iff ];
  intro x hx y hy;
  -- Since the Killing form is non-degenerate, if it is zero on I, then I must be zero.
  have h_nondeg : ∀ (x : L), (∀ y : L, killingForm K L x y = 0) → x = 0 := by
    intro x hx;
    -- Since the Killing form is non-degenerate, if it is zero on x, then x must be zero.
    have h_nondeg : ∀ (x : L), (∀ y : L, killingForm K L x y = 0) → x = 0 := by
      intro x hx
      have h_nondeg : LinearMap.ker (killingForm K L) = ⊥ := by
        exact?
      rw [ LinearMap.ker_eq_bot' ] at h_nondeg;
      exact h_nondeg x ( LinearMap.ext hx );
    exact h_nondeg x hx;
  contrapose! h_nondeg;
  refine' ⟨ ⁅x, y⁆, _, _ ⟩ <;> simp_all +decide [ LieSubalgebra.mem_carrier ];
  · intro z;
    -- Since the Killing form is invariant under the adjoint action, we have killingForm K L ⁅x, y⁆ z = killingForm K L x ⁅y, z⁆.
    have h_inv : killingForm K L ⁅x, y⁆ z = killingForm K L x ⁅y, z⁆ := by
      exact?;
    -- Since $I$ is an ideal, $⁅y, z⁆ \in I$.
    have h_yz_in_I : ⁅y, z⁆ ∈ I := by
      exact?;
    exact h_inv.trans ( h x hx _ h_yz_in_I );
  · exact fun h => h_nondeg <| by simpa [ Subtype.ext_iff ] using h;

theorem disjoint_killingCompl (I : LieIdeal K L) : Disjoint I I.killingCompl := by
  rw [disjoint_iff_inf_le]
  let J := I ⊓ I.killingCompl
  have hJ_le_I : J ≤ I := inf_le_left
  have hJ_le_compl : J ≤ I.killingCompl := inf_le_right
  
  -- The Killing form vanishes on J
  have h_killing_zero : ∀ x ∈ J, ∀ y ∈ J, killingForm K L x y = 0 := by
    intro x hx y hy
    have hx_compl : x ∈ I.killingCompl := hJ_le_compl hx
    rw [LieIdeal.mem_killingCompl] at hx_compl
    specialize hx_compl y (hJ_le_I hy)
    -- Use symmetry of Killing form
    rw [LieModule.traceForm_comm]
    exact hx_compl

  -- This implies J is solvable
  have h_solvable : LieAlgebra.IsSolvable J := by
    apply isSolvable_of_killing_zero
    intro x hx y hy
    exact h_killing_zero x hx y hy

  -- The radical of L is trivial
  have h_rad_bot : LieAlgebra.radical K L = ⊥ := LieAlgebra.HasTrivialRadical.radical_eq_bot
  
  -- Any solvable ideal is contained in the radical
  have h_le_rad : J ≤ LieAlgebra.radical K L := by
    apply le_sSup
    exact h_solvable

  rw [h_rad_bot] at h_le_rad
  exact h_le_rad

-- Check non-degeneracy
#check LieAlgebra.IsKilling.killingForm_nondegenerate
-- Check dimension formula
#check LinearMap.BilinForm.finrank_add_finrank_orthogonal

end AristotleLemmas

theorem compl_eq_killingCompl (I : LieIdeal K L) :
    Iᶜ = I.killingCompl := by
  -- Applying the fact that the Killing form is non-degenerate, we can conclude that $I$ and its Killing complement are complementary.
  have h_compl : IsCompl I I.killingCompl := by
    -- Applying the fact that the Killing form is non-degenerate, we can conclude that I and its Killing complement are complementary.
    have h_dimension : Module.finrank K I + Module.finrank K I.killingCompl = Module.finrank K L := by
      convert LinearMap.BilinForm.finrank_add_finrank_orthogonal _ _;
      · simp +decide [ Submodule.eq_bot_iff ];
        have := LieAlgebra.IsKilling.killingForm_nondegenerate K L;
        intro x hx h; specialize this x; simp_all +decide [ LinearMap.BilinForm.IsOrtho ] ;
        exact this fun n => by simpa [ LieModule.traceForm_comm ] using h n;
      · infer_instance;
      · -- The Killing form is symmetric because the trace of a product of matrices is invariant under cyclic permutations.
        have h_symm : ∀ x y : L, killingForm K L x y = killingForm K L y x := by
          exact?;
        exact fun x y hxy => h_symm x y ▸ hxy;
    have h_disjoint : Disjoint I I.killingCompl := by
      exact?;
    refine' ⟨ h_disjoint, _ ⟩;
    rw [ codisjoint_iff_le_sup ];
    have h_sup_eq_top : Module.finrank K (↥(I ⊔ I.killingCompl)) = Module.finrank K L := by
      -- Since $I$ and $I.killingCompl$ are disjoint, their intersection is zero, so the dimension of their intersection is zero.
      have h_inter_zero : Module.finrank K (↥(I ⊓ I.killingCompl)) = 0 := by
        rw [ disjoint_iff_inf_le ] at h_disjoint;
        exact Submodule.finrank_eq_zero.mpr ( by aesop );
      have := Submodule.finrank_sup_add_finrank_inf_eq ( I : Submodule K L ) ( I.killingCompl : Submodule K L ) ; aesop;
      linarith!;
    have h_sup_eq_top : (I ⊔ I.killingCompl : Submodule K L) = ⊤ := by
      exact Submodule.eq_top_of_finrank_eq h_sup_eq_top;
    exact h_sup_eq_top.ge;
  exact?

end LieIdeal