/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b1cf6867-48c4-487b-8dd9-dc9e6dfd45cc

The following was proved by Aristotle:

- @[simp] lemma invtSubmoduleToLieIdeal_apply_eq_bot_iff (q : Submodule K (Module.Dual K H))
    (hq : ∀ i, q ∈ Module.End.invtSubmodule ((rootSystem H).reflection i)) :
    invtSubmoduleToLieIdeal q (by exact hq) = ⊥ ↔ q = ⊥
-/

import Mathlib.Algebra.Lie.Weights.IsSimple
import Mathlib.LinearAlgebra.RootSystem.RootPositive
import Mathlib.LinearAlgebra.RootSystem.WeylGroup
import Mathlib.RepresentationTheory.Submodule
import Mathlib.Algebra.Lie.Weights.IsSimple
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas


open Function Set

open Submodule (span span_le)

open LinearMap (ker)

open MulAction (orbit mem_orbit_self mem_orbit_iff)

open Module.End (invtSubmodule)

open scoped MonoidAlgebra

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

class IsRootSystem : Prop where
  span_root_eq_top : span R (range P.root) = ⊤
  span_coroot_eq_top : span R (range P.coroot) = ⊤

@[deprecated (since := "2025-12-14")] alias RootSystem := IsRootSystem

attribute [simp] IsRootSystem.span_root_eq_top

attribute [simp] IsRootSystem.span_coroot_eq_top

@[simp] lemma coe_bot : ((⊥ : P.invtRootSubmodule) : Submodule R M) = ⊥ := rfl

@[simp] lemma coe_top : ((⊤ : P.invtRootSubmodule) : Submodule R M) = ⊤ := rfl

open Module in
lemma invtRootSubmodule.eq_bot_iff {K : Type*} [Field K] [NeZero (2 : K)]
    [Module K M] [Module K N] {P : RootPairing ι K M N} [P.IsRootSystem]
    (q : P.invtRootSubmodule) :
    q = ⊥ ↔ ∀ i, P.root i ∉ (q : Submodule K M) := by
  admit

end RootPairing

namespace LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]

variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

variable [LieAlgebra.IsKilling K L] [LieModule.IsTriangularizable K H L]

noncomputable section AristotleLemmas

/-
The sl2 submodule associated to a non-zero root is not the bottom submodule.
-/
lemma LieAlgebra.IsKilling.sl2SubmoduleOfRoot_ne_bot
    {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
    {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
    [LieAlgebra.IsKilling K L] [LieModule.IsTriangularizable K H L]
    {α : LieModule.Weight K H L} (hα : α.IsNonZero) :
    sl2SubmoduleOfRoot hα ≠ ⊥ := by
      have h_nonzero : ∃ x ∈ LieAlgebra.IsKilling.corootSubmodule α, x ≠ 0 := by
        -- Since α is non-zero, the coroot space is non-zero. The coroot itself is in the coroot space, and when mapped into L via the inclusion, it should still be non-zero.
        obtain ⟨x, hx⟩ : ∃ x ∈ LieAlgebra.corootSpace (⇑α : ↥H → K), x ≠ 0 := by
          have h_nonzero : ∃ x ∈ LieAlgebra.corootSpace (⇑α : ↥H → K), x ≠ 0 := by
            have h_nonzero : LieAlgebra.corootSpace (⇑α : ↥H → K) ≠ ⊥ := by
              aesop
            contrapose! h_nonzero;
            exact eq_bot_iff.mpr h_nonzero;
          exact h_nonzero;
        exact ⟨ x, ⟨ x, hx.1, rfl ⟩, by simpa using hx.2 ⟩;
      obtain ⟨ x, hx₁, hx₂ ⟩ := h_nonzero;
      contrapose! hx₂; aesop;
      rw [ LieAlgebra.IsKilling.sl2SubmoduleOfRoot_eq_sup ] at hx₂;
      simp_all +decide [ LieSubmodule.eq_bot_iff ]

/-
The root pairing associated with the root system of a Killing Lie algebra satisfies the `IsRootSystem` typeclass.
-/
instance LieAlgebra.IsKilling.rootSystem_isRootSystem
    {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
    {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
    [LieAlgebra.IsKilling K L] [LieModule.IsTriangularizable K H L] :
    RootPairing.IsRootSystem (rootSystem H).toRootPairing := by
  constructor
  · exact (rootSystem H).span_root_eq_top
  · exact (rootSystem H).span_coroot_eq_top

end AristotleLemmas

@[simp] lemma invtSubmoduleToLieIdeal_apply_eq_bot_iff (q : Submodule K (Module.Dual K H))
    (hq : ∀ i, q ∈ Module.End.invtSubmodule ((rootSystem H).reflection i)) :
    invtSubmoduleToLieIdeal q (by exact hq) = ⊥ ↔ q = ⊥ := by
  refine' ⟨ fun h => _, fun h => _ ⟩;
  · by_contra hq_nonzero
    obtain ⟨i, hi⟩ : ∃ i : { x : LieModule.Weight K (↥H) L // x ∈ LieSubalgebra.root }, (LieAlgebra.IsKilling.rootSystem H).toRootPairing.root i ∈ q := by
      have := @RootPairing.invtRootSubmodule.eq_bot_iff;
      contrapose! this;
      refine' ⟨ _, _, _, _, _, K, _, _, _, _, _ ⟩;
      exact { x : LieModule.Weight K (↥H) L // x ∈ LieSubalgebra.root };
      exact Module.Dual K H;
      exact ↥H;
      all_goals try infer_instance;
      refine' ⟨ _, _, ⟨ ⟨ q, _ ⟩, _ ⟩ ⟩;
      exact ( LieAlgebra.IsKilling.rootSystem H ).toRootPairing;
      exact?;
      exact?;
      exact Or.inr ⟨ by simpa using hq_nonzero, this ⟩;
    have h_sl2_nonzero : sl2SubmoduleOfRoot (by
    aesop : i.val.IsNonZero) ≠ ⊥ := by
      all_goals generalize_proofs at *;
      exact?
    generalize_proofs at *;
    refine' h_sl2_nonzero ( le_bot_iff.mp _ );
    convert h.le using 1;
    simp +decide [ LieAlgebra.IsKilling.invtSubmoduleToLieIdeal ];
    exact?;
  · simp +decide [ h, Submodule.map_zero, LieAlgebra.IsKilling.invtSubmoduleToLieIdeal ]

end LieAlgebra.IsKilling
