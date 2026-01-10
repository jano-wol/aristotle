/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8af9b509-38d7-453b-a30a-7eccd6a97b71

The following was proved by Aristotle:

- lemma exists_rootSet_lieIdeal_eq (I : LieIdeal K L) :
    ∃ Φ : Set H.root, I.toSubmodule = (I.toSubmodule ⊓ H.toSubmodule) ⊔
      ⨆ α ∈ Φ, (rootSpace H α.1).toSubmodule
-/

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
  refine' ⟨ _, _ ⟩;
  exact { x | ( I : Submodule K L ) ⊓ ( LieAlgebra.rootSpace H ( ⇑ ( x : LieModule.Weight K H L ) ) : Submodule K L ) ≠ ⊥ };
  refine' le_antisymm _ _;
  · intro x hx
    have hx_decomp : x ∈ (I.toSubmodule ⊓ H.toSubmodule) ⊔ ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), I.toSubmodule ⊓ (genWeightSpace L α.1).toSubmodule := by
      convert lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace I |> fun h => h ▸ hx;
      · infer_instance;
      · infer_instance;
    simp_all +decide [ Submodule.mem_sup, Submodule.mem_iSup ];
    obtain ⟨ y, hy, z, hz, rfl ⟩ := hx_decomp;
    refine' ⟨ y, hy, z, _, rfl ⟩;
    intro N hN;
    refine' hz N fun α hα => _;
    by_cases h : ( I : Submodule K L ) ⊓ ( LieAlgebra.rootSpace H α.toFun : Submodule K L ) = ⊥ <;> simp_all +decide [ Submodule.eq_bot_iff ];
    · intro x hx; specialize h x; aesop;
    · intro x hx;
      obtain ⟨ y, hy ⟩ := h;
      exact hN α hα y hy.1 hy.2.1 hy.2.2 ( hx.2 );
  · simp +decide [ Submodule.mem_sup, Submodule.mem_iSup ];
    intro α hα hα';
    -- Since $\alpha$ is a root, the root space $\mathfrak{g}_\alpha$ is 1-dimensional.
    have h_root_space_dim : Module.finrank K (LieAlgebra.rootSpace H α) = 1 := by
      exact?;
    -- Since $\alpha$ is a root, the root space $\mathfrak{g}_\alpha$ is 1-dimensional, so any non-zero element in $\mathfrak{g}_\alpha$ generates the entire space.
    obtain ⟨x, hx⟩ : ∃ x : L, x ∈ LieAlgebra.rootSpace H α ∧ x ≠ 0 ∧ x ∈ I := by
      simp_all +decide [ Submodule.eq_bot_iff ];
      tauto;
    have h_root_space_gen : ∀ y ∈ LieAlgebra.rootSpace H α, ∃ c : K, y = c • x := by
      have := finrank_eq_one_iff'.mp h_root_space_dim;
      norm_num +zetaDelta at *;
      obtain ⟨ y, hy, hy', hy'' ⟩ := this; intro z hz; obtain ⟨ c, hc ⟩ := hy'' z hz; obtain ⟨ d, hd ⟩ := hy'' x hx.1; use c / d; simp_all +decide [ div_eq_inv_mul, smul_smul ] ;
      rw [ ← hc, ← hd, smul_smul, mul_comm ];
      by_cases hd : d = 0 <;> simp_all +decide [ mul_assoc ];
    exact fun y hy => by obtain ⟨ c, rfl ⟩ := h_root_space_gen y hy; exact I.smul_mem c hx.2.2;

end LieAlgebra.IsKilling