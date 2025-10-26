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
  sorry

end KomalB3929
