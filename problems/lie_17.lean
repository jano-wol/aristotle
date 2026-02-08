/-
This file defines the forward direction of the order isomorphism between Lie ideals
of a Killing Lie algebra and invariant root submodules of the associated root system.

The main construction is `lieIdealToInvtRootSubmodule`, which maps a Lie ideal `I` to
the submodule of `Dual K H` spanned by the roots whose root spaces lie in `I`.

The full order isomorphism `lieIdealOrderIso` is sketched with sorry'd proofs.
-/

import Mathlib.Algebra.Lie.Weights.IsSimple

namespace LieAlgebra.IsKilling

open LieAlgebra LieModule Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsKilling K L] [IsTriangularizable K H L]

noncomputable section

/-! ### Lie ideal decomposition (sorry'd; proved in Lemma1) -/

/-- A Lie ideal decomposes as its intersection with the Cartan subalgebra plus a direct sum of
root spaces corresponding to some subset Φ of roots. -/
lemma exists_rootSet_lieIdeal_eq (I : LieIdeal K L) :
    ∃ Φ : Set H.root, I.toSubmodule = (I.toSubmodule ⊓ H.toSubmodule) ⊔
      ⨆ α ∈ Φ, (rootSpace H α.1).toSubmodule := by admit

/-! ### Root set of a Lie ideal -/

/-- The set of roots whose root space is contained in a given Lie ideal. -/
def lieIdealRootSet (I : LieIdeal K L) : Set H.root :=
  { α | (rootSpace H α.1).toSubmodule ≤ I.toSubmodule }

/-! ### Forward map: Lie ideal → invariant root submodule -/

/-- The submodule of `Dual K H` spanned by the roots associated to a Lie ideal.
This maps each root `α ∈ Φ_I` (where `g_α ⊆ I`) to its weight functional `α : H →ₗ[K] K`,
and takes their span. -/
def lieIdealToSubmodule (I : LieIdeal K L) : Submodule K (Dual K H) :=
  Submodule.span K ((↑) '' lieIdealRootSet (H := H) I)

/-! ### Weyl reflection invariance -/

/-- In a root chain, bracketing with `g_{-β}` maps `g_{k•β + α}` to a nonzero subspace of
`g_{(k-1)•β + α}` when `k` is strictly above the chain bottom.

The chain `⨁_{-b ≤ k ≤ t} g_{k•β+α}` is an irreducible sl₂(β)-module because
each weight space is 1-dimensional and the weights form a consecutive string. The lowering
operator (bracket with `f_β`) is therefore nonzero on all weight spaces except the lowest. -/
lemma exists_bracket_ne_zero_of_neg_lt_chainBotCoeff
    {α β : Weight K H L} (hβ : β.IsNonZero)
    {k : ℤ} (hk_top : k ≤ chainTopCoeff β α) (hk_bot : -k < chainBotCoeff β α) :
    ∃ x ∈ rootSpace H (-β), ∃ y ∈ rootSpace H (k • β + α),
      ⁅(x : L), (y : L)⁆ ≠ 0 := by
  -- Get sl₂ triple for β
  obtain ⟨_, e, f, isSl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hβ
  obtain rfl := isSl2.h_eq_coroot hβ he hf
  -- Get primitive vector at chain top
  obtain ⟨v, hv, v_ne0⟩ := (chainTop β α).exists_ne_zero
  have prim : isSl2.HasPrimitiveVectorWith v (chainLength β α : K) :=
    have := lie_mem_genWeightSpace_of_mem_genWeightSpace he hv
    ⟨v_ne0, (chainLength_smul _ _ hv).symm, by rwa [genWeightSpace_add_chainTop _ _ hβ] at this⟩
  -- Define chain index n = chainTopCoeff β α - k (as ℕ)
  have h_nn : (0 : ℤ) ≤ chainTopCoeff β α - k := by omega
  set n := (chainTopCoeff β α - k).toNat with hn_def
  have hn : (n : ℤ) = chainTopCoeff β α - k := Int.toNat_of_nonneg h_nn
  -- f^n v is in the root space g_{k•β+α}
  have hfnv_mem : ((toEnd K L L f) ^ n) v ∈
      genWeightSpace L (k • (β : H → K) + (α : H → K)) := by
    have h1 := toEnd_pow_apply_mem hf hv n
    suffices n • (-(β : H → K)) + (chainTop (β : H → K) α : H → K) =
        k • (β : H → K) + (α : H → K) by rwa [this] at h1
    rw [← Nat.cast_smul_eq_nsmul ℤ, smul_neg, coe_chainTop, hn]
    simp [sub_eq_add_neg]
    grind
  -- f^n v is nonzero
  have hn_le : n ≤ chainLength β α := by
    suffices (n : ℤ) ≤ chainLength β α by exact Int.le_of_ofNat_le_ofNat this
    rw [← chainBotCoeff_add_chainTopCoeff]; push_cast; omega
  -- ⁅f, f^n v⁆ = f^(n+1) v is nonzero since n+1 ≤ chainLength
  have hn1_le : n + 1 ≤ chainLength β α := by
    suffices (n : ℤ) + 1 ≤ chainLength β α by exact Int.le_of_ofNat_le_ofNat this
    rw [← chainBotCoeff_add_chainTopCoeff]; push_cast; omega
  refine ⟨f, hf, _, hfnv_mem, ?_⟩
  rw [prim.lie_f_pow_toEnd_f n]
  exact prim.pow_toEnd_f_ne_zero_of_eq_nat rfl hn1_le

/-- In a root chain, bracketing with `g_β` maps `g_{k•β + α}` to a nonzero subspace of
`g_{(k+1)•β + α}` when `k` is strictly below the chain top. This follows from
`exists_bracket_ne_zero_of_neg_lt_chainBotCoeff` by the symmetry `β ↦ -β`. -/
lemma exists_bracket_ne_zero_of_lt_chainTopCoeff
    {α β : Weight K H L} (hβ : β.IsNonZero)
    {k : ℤ} (hk_bot : -k ≤ chainBotCoeff β α) (hk_top : k < chainTopCoeff β α) :
    ∃ x ∈ rootSpace H β, ∃ y ∈ rootSpace H (k • β + α),
      ⁅(x : L), (y : L)⁆ ≠ 0 := by
  have h := exists_bracket_ne_zero_of_neg_lt_chainBotCoeff (α := α) (β := -β) hβ.neg
    (k := -k) (by simp [chainTopCoeff_neg]; omega) (by simp [chainBotCoeff_neg]; omega)
  convert h using 2
  simp

/--
PROVIDED SOLUTION:
The root set of a Lie ideal is closed under Weyl reflections: if `g_α ⊆ I` and `i` is any
root, then `g_{s_i(α)} ⊆ I`.

Proof sketch: The reflected root `s_i(α) = α + m•i` (where `m = chainTopCoeff i α -
chainBotCoeff i α`) lies in the i-chain through α. We show all chain members are in `I`
by induction: starting from `g_α ⊆ I` (given), each step uses:
1. `[g_i, g_{k•i+α}] ⊆ g_{(k+1)•i+α}` (weight space product) and `⊆ I` (ideal property)
2. `[g_i, g_{k•i+α}] ≠ 0` (`exists_bracket_ne_zero_of_lt_chainTopCoeff`)
3. `g_{(k+1)•i+α}` is 1-dimensional (`finrank_rootSpace_eq_one`)
Together these give `g_{(k+1)•i+α} ⊆ I`. The downward direction uses `g_{-i}` analogously.
-/
lemma lieIdealRootSet_reflectionPerm_invariant (I : LieIdeal K L) (i : H.root)
    {α : H.root} (hα : α ∈ lieIdealRootSet (H := H) I) :
    (rootSystem H).reflectionPerm i α ∈ lieIdealRootSet (H := H) I :=
  sorry

/-- The submodule spanned by roots of a Lie ideal is invariant under all root reflections. -/
lemma lieIdealToSubmodule_mem_invtRootSubmodule (I : LieIdeal K L) :
    lieIdealToSubmodule (H := H) I ∈ (rootSystem H).invtRootSubmodule := by
  rw [RootPairing.mem_invtRootSubmodule_iff]
  intro i
  rw [Module.End.mem_invtSubmodule]
  apply Submodule.span_le.mpr
  rintro _ ⟨α, hα, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap]
  rw [show (↑((rootSystem H).reflection i) : Dual K H →ₗ[K] Dual K H)
    (Weight.toLinear K H L ↑α) = (rootSystem H).reflection i ((rootSystem H).root α) from rfl]
  rw [← (rootSystem H).root_reflectionPerm i α]
  exact Submodule.subset_span ⟨_, lieIdealRootSet_reflectionPerm_invariant I i hα, rfl⟩

/-- Maps a Lie ideal to its corresponding invariant root submodule. -/
def lieIdealToInvtRootSubmodule (I : LieIdeal K L) :
    (rootSystem H).invtRootSubmodule :=
  ⟨lieIdealToSubmodule (H := H) I, lieIdealToSubmodule_mem_invtRootSubmodule I⟩

/-! ### Monotonicity -/

/-- The forward map is monotone: if `I ≤ J` then the root set of `I` is contained in that of `J`,
hence the spanned submodule is smaller. -/
lemma lieIdealToInvtRootSubmodule_mono {I J : LieIdeal K L} (h : I ≤ J) :
    lieIdealToInvtRootSubmodule (H := H) I ≤ lieIdealToInvtRootSubmodule J := by
  apply Submodule.span_mono
  apply Set.image_mono
  intro α (hα : (rootSpace H α.1).toSubmodule ≤ I.toSubmodule)
  exact hα.trans h


end

end LieAlgebra.IsKilling
