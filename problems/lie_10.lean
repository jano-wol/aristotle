/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.RootSystem.RootPositive
import Mathlib.LinearAlgebra.RootSystem.WeylGroup
import Mathlib.RepresentationTheory.Submodule

@[expose] public section

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

/-- The sublattice of invariant submodules of the root space. -/
def invtRootSubmodule : Sublattice (Submodule R M) :=
  ⨅ i, invtSubmodule (P.reflection i)

lemma mem_invtRootSubmodule_iff {q : Submodule R M} :
    q ∈ P.invtRootSubmodule ↔ ∀ i, q ∈ Module.End.invtSubmodule (P.reflection i) := by
  simp [invtRootSubmodule]

@[simp] protected lemma invtRootSubmodule.top_mem : ⊤ ∈ P.invtRootSubmodule := by
  simp [invtRootSubmodule]

@[simp] protected lemma invtRootSubmodule.bot_mem : ⊥ ∈ P.invtRootSubmodule := by
  simp [invtRootSubmodule]

instance : BoundedOrder P.invtRootSubmodule where
  top := ⟨⊤, invtRootSubmodule.top_mem P⟩
  bot := ⟨⊥, invtRootSubmodule.bot_mem P⟩
  le_top := fun ⟨p, hp⟩ ↦ by simp
  bot_le := fun ⟨p, hp⟩ ↦ by simp

instance [Nontrivial M] : Nontrivial P.invtRootSubmodule where
  exists_pair_ne := ⟨⊥, ⊤, by rw [ne_eq, Subtype.ext_iff]; exact bot_ne_top⟩

@[simp] lemma coe_bot : ((⊥ : P.invtRootSubmodule) : Submodule R M) = ⊥ := rfl

@[simp] lemma coe_top : ((⊤ : P.invtRootSubmodule) : Submodule R M) = ⊤ := rfl

open Module in
lemma invtRootSubmodule.eq_top_iff {K : Type*} [Field K] [NeZero (2 : K)]
    [Module K M] [Module K N] {P : RootPairing ι K M N} [P.IsRootSystem]
    (q : P.invtRootSubmodule) :
    q = ⊤ ↔ ∀ i, P.root i ∈ (q : Submodule K M) := by
  sorry
