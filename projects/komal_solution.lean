/-
This file was edited by Aristotle.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

The following was proved by Aristotle:

- theorem _root_.komal :
    ∀ a b : ℕ+, (∀ n : ℕ+, ((a : ℕ) ^ (n : ℕ) + n ∣ (b : ℕ) ^ (n : ℕ) + n)) → a = b
-/

/-
Copyright (c) 2025 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Aesop


/-!
# Komal problem
Let `a` and `b` positive integers, so that for any `n` positive integer `a^n + n ∣ b^n + n`.
Show that `a = b`.
-/

namespace Komal

/-- The answer 2 is to be determined by the solver of the original problem. -/
theorem _root_.komal :
    ∀ a b : ℕ+, (∀ n : ℕ+, ((a : ℕ) ^ (n : ℕ) + n ∣ (b : ℕ) ^ (n : ℕ) + n)) → a = b := by
  -- If $a \neq b$, then we can assume that $a > b$ without loss of generality.
  intro a b h_div
  by_cases h_eq : a = b;
  · exact h_eq;
  · -- Then $a^n + n \leq b^n + n$, which implies $a^n \leq b^n$, and so $a \leq b$.
    have h_le : a ≤ b := by
      -- By contradiction, assume $a > b$.
      by_contra h_contra;
      exact absurd ( h_div 1 ) ( Nat.not_dvd_of_pos_of_lt ( by norm_num ) ( by simpa using not_le.mp h_contra ) );
    -- Let $p$ be a prime number greater than $b$.
    obtain ⟨p, hp⟩ : ∃ p : ℕ, Nat.Prime p ∧ b < p := by
      exact Exists.imp ( by tauto ) ( Nat.exists_infinite_primes _ );
    -- Choose $n$ such that $n \equiv 1 \pmod{p-1}$ and $n \equiv -a \pmod{p}$.
    obtain ⟨n, hn⟩ : ∃ n : ℕ+, n ≡ 1 [MOD (p - 1)] ∧ n ≡ -a [ZMOD p] := by
      -- By the Chinese Remainder Theorem, such an $n$ exists since $p-1$ and $p$ are coprime.
      have h_crt : ∃ n : ℕ, n ≡ 1 [MOD p - 1] ∧ n ≡ p - a [MOD p] := by
        have h_crt : Nat.gcd (p - 1) p = 1 := by
          simp +decide [ hp.1.one_lt.le ];
        have := Nat.chineseRemainder h_crt;
        exact ⟨ _, this 1 ( p - a ) |> Subtype.property ⟩;
      cases' h_crt with n hn
      use ⟨ n + p * ( p - 1 ), Nat.add_pos_right n (Nat.mul_pos hp.1.pos (Nat.sub_pos_of_lt hp.1.one_lt)) ⟩
      constructor
      · simpa [ Nat.ModEq, Nat.add_mod, Nat.mul_mod ] using hn.1
      · simp_all +decide [ ← Int.natCast_modEq_iff, Nat.cast_sub hp.1.pos ];
        simp_all +decide [ ← ZMod.intCast_eq_intCast_iff, Nat.cast_sub ( show ( a : ℕ ) ≤ p from le_trans h_le hp.2.le ) ];
    -- Then $a^n + n \equiv a + n \equiv 0 \pmod{p}$ and $b^n + n \equiv b + n \equiv b - a \pmod{p}$.
    have h_mod : (a ^ (n : ℕ) + n : ℤ) ≡ 0 [ZMOD p] ∧ (b ^ (n : ℕ) + n : ℤ) ≡ b - a [ZMOD p] := by
      -- By Fermat's Little Theorem, we have $a^n \equiv a \pmod{p}$ and $b^n \equiv b \pmod{p}$.
      have h_fermat : (a ^ (n : ℕ) : ℤ) ≡ a [ZMOD p] ∧ (b ^ (n : ℕ) : ℤ) ≡ b [ZMOD p] := by
        -- Since $n \equiv 1 \pmod{p-1}$, we have $n = k(p-1) + 1$ for some integer $k$.
        obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k * (p - 1) + 1 := by
          exact ⟨ ( n - 1 ) / ( p - 1 ), by rw [ Nat.div_mul_cancel ( by rw [ ← Int.natCast_dvd_natCast ] ; simpa [ Nat.cast_sub ( show 1 ≤ ( n : ℕ ) from PNat.pos n ) ] using hn.1.symm.dvd ), Nat.sub_add_cancel ( show 1 ≤ ( n : ℕ ) from PNat.pos n ) ] ⟩;
        haveI := Fact.mk hp.1; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff, pow_add, pow_mul' ] ;
        by_cases ha : ( a : ZMod p ) = 0 <;> by_cases hb : ( b : ZMod p ) = 0 <;> simp_all +decide [ ZMod.pow_card_sub_one_eq_one ];
      exact ⟨ by simpa using h_fermat.1.add hn.2, by simpa using h_fermat.2.add hn.2 ⟩;
    -- Since $a^n + n \mid b^n + n$, we have $p \mid b - a$.
    have h_div_p : (p : ℤ) ∣ b - a := by
      exact Int.dvd_of_emod_eq_zero ( h_mod.2.symm ▸ Int.emod_eq_zero_of_dvd ( Int.dvd_trans ( Int.dvd_of_emod_eq_zero h_mod.1 ) ( mod_cast h_div n ) ) );
    contrapose! h_div_p;
    exact fun h => by have := Int.le_of_dvd ( Int.sub_pos_of_lt <| mod_cast lt_of_le_of_ne h_le h_div_p ) h; linarith [ show ( a : ℕ ) < b from mod_cast lt_of_le_of_ne h_le h_div_p ] ;
end Komal
