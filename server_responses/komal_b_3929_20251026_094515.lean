/-
This file was edited by Aristotle.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

Your Lean code is run in a custom environment, which uses these headers:

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

The following was proved by Aristotle:

- theorem komal_b_3929 :
    Set.Infinite {triple : ℚ × ℚ × ℚ |
      let (x, y, z)
-/

import Mathlib.Data.Rat.Floor
import Mathlib.Data.Finite.Defs


/-!
# Komal problem B.3929
Prove that the equation {x³}+{y³}={z³} has infinitely many solutions where x, y and z are
rational numbers, but none of them are integers. ({r} denotes the fractional part of r.)
-/

namespace KomalB3929

/-- A rational number is an integer. -/
def IsInt (x : ℚ) : Prop := x.den = 1

theorem komal_b_3929 :
    Set.Infinite {triple : ℚ × ℚ × ℚ |
      let (x, y, z) := triple
      ¬IsInt x ∧ ¬IsInt y ∧ ¬IsInt z ∧
      Int.fract (x ^ 3) + Int.fract (y ^ 3) = Int.fract (z ^ 3)} := by
  set S := {triple : ℚ × ℚ × ℚ | ¬triple.1.den = 1 ∧ ¬triple.2.1.den = 1 ∧ ¬triple.2.2.den = 1 ∧ Int.fract (triple.1^3) + Int.fract (triple.2.1^3) = Int.fract (triple.2.2^3)} with hS_def;
  -- For any natural number $n$, let's construct the triple $(x, y, z) = \left(\frac{3}{5}(125n+1), \frac{4}{5}(125n+1), \frac{6}{5}(125n+1)\right)$.
  have h_triples (n : ℕ) : ( (3/5 : ℚ)*(125*n + 1), (4/5 : ℚ)*(125*n + 1), (6/5 : ℚ)*(125*n + 1) ) ∈ S := by
    -- Let's calculate the fractional parts of the cubes of the components.
    have h_frac_parts : Int.fract ((3 / 5 * (125 * n + 1) : ℚ) ^ 3) + Int.fract ((4 / 5 * (125 * n + 1) : ℚ) ^ 3) = Int.fract ((6 / 5 * (125 * n + 1) : ℚ) ^ 3) := by
      ring_nf;
      rw [ Int.fract, Int.fract, Int.fract ];
      norm_num [ show ⌊ ( 27:ℚ ) / 125 + n * 81 + n ^ 2 * 10125 + n ^ 3 * 421875⌋ = n * 81 + n ^ 2 * 10125 + n ^ 3 * 421875 by exact Int.floor_eq_iff.mpr ⟨ by push_cast; nlinarith, by push_cast; nlinarith ⟩, show ⌊ ( 64:ℚ ) / 125 + n * 192 + n ^ 2 * 24000 + n ^ 3 * 1000000⌋ = n * 192 + n ^ 2 * 24000 + n ^ 3 * 1000000 by exact Int.floor_eq_iff.mpr ⟨ by push_cast; nlinarith, by push_cast; nlinarith ⟩, show ⌊ ( 216:ℚ ) / 125 + n * 648 + n ^ 2 * 81000 + n ^ 3 * 3375000⌋ = n * 648 + n ^ 2 * 81000 + n ^ 3 * 3375000 + 1 by exact Int.floor_eq_iff.mpr ⟨ by push_cast; nlinarith, by push_cast; nlinarith ⟩ ] ; ring;
    norm_num [ Rat.mul_den ] at h_frac_parts ⊢ ; aesop;
    · rw [ Rat.den_eq_one_iff ] at a;
      rw [ div_mul_eq_mul_div, eq_div_iff ] at * <;> norm_cast at * ; have := congr_arg ( · % 5 ) a ; norm_num [ Int.add_emod, Int.mul_emod ] at this ⊢;
    · rw [ Rat.den_eq_one_iff ] at a;
      field_simp at a;
      norm_cast at a ; have := congr_arg ( · % 5 ) a ; norm_num [ Int.add_emod, Int.mul_emod ] at this;
    · rw [ Rat.den_eq_one_iff ] at a ; norm_num [ field_simps ] at a ; norm_cast at a ; have := congr_arg ( · % 5 ) a ; norm_num [ Nat.add_mod, Nat.mul_mod ] at this;
      grind;
  exact Set.infinite_of_injective_forall_mem ( fun n m hnm => by norm_num at hnm; linarith ) h_triples

end KomalB3929