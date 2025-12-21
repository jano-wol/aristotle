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
lemma invtRootSubmodule.eq_top_iff {K : Type*} [Field K] [NeZero (2 : K)]
    [Module K M] [Module K N] {P : RootPairing ι K M N} [P.IsRootSystem]
    (q : P.invtRootSubmodule) :
    q = ⊤ ↔ ∀ i, P.root i ∈ (q : Submodule K M) := by
  admit

end RootPairing

namespace LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
variable [LieAlgebra.IsKilling K L] [LieModule.IsTriangularizable K H L]

/--
  Try to use invtRootSubmodule.eq_top_iff
-/
@[simp] lemma invtSubmoduleToLieIdeal_apply_eq_top_iff (q : Submodule K (Module.Dual K H))
    (hq : ∀ i, q ∈ Module.End.invtSubmodule ((rootSystem H).reflection i)) :
    invtSubmoduleToLieIdeal q (by exact hq) = ⊤ ↔ q = ⊤ := by
  sorry

end LieAlgebra.IsKilling
