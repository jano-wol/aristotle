/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 793f972e-d103-44b7-a791-ba9af237e654

The following was proved by Aristotle:

- @[simp] lemma invtSubmoduleToLieIdeal_top :
    invtSubmoduleToLieIdeal (⊤ : Submodule K (Module.Dual K H)) (by simp) = ⊤
-/

import Mathlib.Algebra.Lie.Weights.IsSimple
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas


variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]

variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

variable [LieAlgebra.IsKilling K L] [LieModule.IsTriangularizable K H L]

namespace LieAlgebra.IsKilling

noncomputable section AristotleLemmas

#print LieAlgebra.IsKilling.invtSubmoduleToLieIdeal
#print LieAlgebra.IsKilling.sl2SubmoduleOfRoot
#print LieAlgebra.IsKilling.sl2SubalgebraOfRoot

lemma span_singleton_eq_rootSpace (α : LieModule.Weight K H L) (hα : α.IsNonZero) (x : L) (hx : x ∈ LieAlgebra.rootSpace H α) (hx0 : x ≠ 0) :
    Submodule.span K {x} = LieAlgebra.rootSpace H α := by
  -- Since the root space is one-dimensional and $x$ is a non-zero element of it, the span of $x$ must be the entire root space.
  have h_span : Submodule.span K {x} ≤ LieAlgebra.rootSpace H α ∧ Module.finrank K (Submodule.span K {x}) = 1 := by
    exact ⟨ Submodule.span_le.mpr ( Set.singleton_subset_iff.mpr hx ), finrank_span_singleton hx0 ⟩;
  refine' Submodule.eq_of_le_of_finrank_eq h_span.1 _;
  convert h_span.2;
  convert LieAlgebra.IsKilling.finrank_rootSpace_eq_one α hα

#print LieAlgebra.IsKilling.mem_sl2SubalgebraOfRoot_iff
#print IsSl2Triple.mem_toLieSubalgebra_iff

lemma rootSpace_le_sl2SubmoduleOfRoot (α : LieModule.Weight K H L) (hα : α.IsNonZero) :
    LieAlgebra.rootSpace H α ≤ (LieAlgebra.IsKilling.sl2SubmoduleOfRoot hα).toSubmodule := by
      -- Let `x` be an element of `rootSpace H α`.
      intro x hx;
      -- By `mem_sl2SubalgebraOfRoot_iff` applied to this triple, an element is in `sl2SubalgebraOfRoot hα` if and only if it is in the span of `{e, f, [e, f]}`.
      obtain ⟨e, he, f, hf, ht⟩ : ∃ e f : L, (∃ h : L, IsSl2Triple h e f) ∧ e ∈ LieAlgebra.rootSpace H α ∧ f ∈ LieAlgebra.rootSpace H (-α) := by
        by_cases hα_zero : α.IsZero;
        · cases hα hα_zero;
        · have := LieAlgebra.IsKilling.sl2SubalgebraOfRoot hα;
          obtain ⟨h, e, f, ht⟩ : ∃ h e f : L, IsSl2Triple h e f ∧ e ∈ LieAlgebra.rootSpace H α ∧ f ∈ LieAlgebra.rootSpace H (-α) := by
            exact?;
          exact ⟨ e, f, ⟨ h, ht.1 ⟩, ht.2.1, ht.2.2 ⟩;
      have hx_span : x ∈ Submodule.span K {e} := by
        have hx_span : Submodule.span K {e} = LieAlgebra.rootSpace H α := by
          apply span_singleton_eq_rootSpace α hα e hf;
          intro he0;
          obtain ⟨ h, hh ⟩ := f;
          cases hh ; aesop;
        exact hx_span.symm ▸ hx;
      rw [ Submodule.mem_span_singleton ] at hx_span;
      rcases hx_span with ⟨ a, rfl ⟩;
      obtain ⟨ h, hh ⟩ := f;
      exact LieAlgebra.IsKilling.mem_sl2SubalgebraOfRoot_iff hα hh ( by simpa using hf ) ( by simpa using ht ) |>.2 ⟨ a, 0, 0, by simp +decide ⟩

lemma rootSpace_le_invtSubmoduleToLieIdeal (α : LieModule.Weight K H L) (hα : α.IsNonZero) :
    LieAlgebra.rootSpace H α ≤ (invtSubmoduleToLieIdeal (⊤ : Submodule K (Module.Dual K H)) (by simp)).toSubmodule := by
  refine' le_trans ( rootSpace_le_sl2SubmoduleOfRoot α hα ) _;
  -- By definition of `invtSubmoduleToLieIdeal`, we know that it is the supremum of `sl2SubmoduleOfRoot β` for all `β` in the root system.
  simp [LieAlgebra.IsKilling.invtSubmoduleToLieIdeal];
  exact le_iSup_of_le ⟨ α, trivial, hα ⟩ le_rfl

#check LieAlgebra.IsKilling.rootSystem

lemma coroot_mem_sl2SubmoduleOfRoot (α : LieModule.Weight K H L) (hα : α.IsNonZero) :
    ((LieAlgebra.IsKilling.rootSystem H).coroot ⟨α, by
      cases α ; aesop⟩ : L) ∈ (LieAlgebra.IsKilling.sl2SubmoduleOfRoot hα).toSubmodule := by
  all_goals generalize_proofs at *;
  -- Let's choose any sl2-triple $(e, f, h)$ such that $e \in \text{rootSpace } H \alpha$ and $f \in \text{rootSpace } H (-\alpha)$.
  obtain ⟨h, e, f, ht, he, hf⟩ : ∃ (h e f : L), IsSl2Triple h e f ∧ e ∈ LieAlgebra.rootSpace H α ∧ f ∈ LieAlgebra.rootSpace H (-α) := by
    exact?;
  have h_coroot : h = (LieAlgebra.IsKilling.rootSystem H).coroot ⟨α, by
    assumption⟩ := by
    apply IsSl2Triple.h_eq_coroot hα ht he hf
  generalize_proofs at *;
  have h_in_sl2 : h ∈ LieAlgebra.IsKilling.sl2SubalgebraOfRoot hα := by
    have h_in_sl2 : h = ⁅e, f⁆ := by
      exact?;
    exact h_in_sl2.symm ▸ LieSubalgebra.lie_mem _ ( LieAlgebra.IsKilling.mem_sl2SubalgebraOfRoot_iff hα ht he hf |>.2 ⟨ 1, 0, 0, by simp +decide ⟩ ) ( LieAlgebra.IsKilling.mem_sl2SubalgebraOfRoot_iff hα ht he hf |>.2 ⟨ 0, 1, 0, by simp +decide ⟩ );
  exact h_coroot ▸ h_in_sl2

lemma coroot_mem_sl2SubmoduleOfRoot' (α : LieModule.Weight K H L) (hα : α.IsNonZero) :
    ((LieAlgebra.IsKilling.rootSystem H).coroot ⟨α, by cases α; aesop⟩ : L) ∈ (LieAlgebra.IsKilling.sl2SubmoduleOfRoot hα).toSubmodule := by
  exact?

lemma cartan_le_invtSubmoduleToLieIdeal :
    H.toSubmodule ≤ (invtSubmoduleToLieIdeal (⊤ : Submodule K (Module.Dual K H)) (by simp)).toSubmodule := by
  intro x;
  intro hx;
  have h_span : H.toSubmodule ≤ Submodule.span K (Set.range (fun α : { α : LieModule.Weight K H L // α ∈ LieSubalgebra.root } => (LieAlgebra.IsKilling.rootSystem H).coroot α : { α : LieModule.Weight K H L // α ∈ LieSubalgebra.root } → L)) := by
    have := (LieAlgebra.IsKilling.rootSystem H).span_coroot_eq_top;
    rw [ Submodule.eq_top_iff' ] at this;
    intro x hx;
    specialize this ⟨ x, hx ⟩;
    rw [ Submodule.mem_span ] at this ⊢;
    intro p hp;
    specialize this ( Submodule.comap ( Submodule.subtype H.toSubmodule ) p );
    exact this ( by rintro _ ⟨ α, rfl ⟩ ; exact hp ⟨ α, rfl ⟩ );
  refine' h_span hx |> fun hx' => _;
  refine' Submodule.span_induction _ _ _ _ hx' <;> simp +decide [ LieAlgebra.IsKilling.invtSubmoduleToLieIdeal ];
  · intro α hα;
    exact Submodule.mem_iSup_of_mem ⟨ α, trivial, hα ⟩ ( LieAlgebra.IsKilling.coroot_mem_sl2SubmoduleOfRoot' α hα );
  · exact fun x y hx hy hx' hy' => Submodule.add_mem _ hx' hy';
  · exact fun a x hx hx' => Submodule.smul_mem _ _ hx'

lemma genWeightSpace_le_invtSubmoduleToLieIdeal (χ : LieModule.Weight K H L) :
    (LieModule.genWeightSpace L χ).toSubmodule ≤ (invtSubmoduleToLieIdeal (⊤ : Submodule K (Module.Dual K H)) (by simp)).toSubmodule := by
  rcases eq_or_ne ( χ : H → K ) 0 with h | h <;> aesop
  all_goals generalize_proofs at *;
  · exact?;
  · convert LieAlgebra.IsKilling.rootSpace_le_invtSubmoduleToLieIdeal χ h using 1

end AristotleLemmas

@[simp] lemma invtSubmoduleToLieIdeal_top :
    invtSubmoduleToLieIdeal (⊤ : Submodule K (Module.Dual K H)) (by simp) = ⊤ := by
  rw [← LieSubmodule.toSubmodule_inj, invtSubmoduleToLieIdeal, LieSubmodule.iSup_toSubmodule,
    LieSubmodule.top_toSubmodule]
  refine' eq_top_iff.mpr fun x hx => _;
  have : x ∈ ⨆ (χ : LieModule.Weight K H L), (LieModule.genWeightSpace L χ).toSubmodule := by
    convert Submodule.mem_top;
    convert LieModule.iSup_genWeightSpace_eq_top';
    constructor <;> intro h;
    swap;
    simp +zetaDelta at *;
    convert h K H L;
    intro K L M _ _ _ _ _ _ _ _ _ _; exact?;
  rw [ Submodule.mem_iSup ] at this ⊢;
  intro N hN
  apply this N
  intro χ
  apply le_trans (genWeightSpace_le_invtSubmoduleToLieIdeal χ) (by
  simp +decide [ LieAlgebra.IsKilling.invtSubmoduleToLieIdeal ];
  exact fun α hα => hN ⟨ α, trivial, hα ⟩)

end LieAlgebra.IsKilling