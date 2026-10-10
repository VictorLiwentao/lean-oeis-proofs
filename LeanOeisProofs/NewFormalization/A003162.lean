/-
Copyright 2026 The Formal Conjectures Authors.
Copyright (c) 2026 Wentao Li.
Authors: Wentao Li

The original statements and Wentao Li's contributions are licensed under Apache 2.0.
The binomial helper and its refinement are adapted from Epoch Research's
LeanOpenProblems-results; their provenance is recorded at the relevant sections
and in the accompanying SOURCE.md. No new license is asserted for those portions.
-/
import LeanOeisProofs.NewFormalization.A003161

namespace OeisA3162

/-- A binomial coefficient summation: $a(n) = S(3, n) / S(1, n)$. -/
def a (n : ℕ) : ℚ :=
  let numerator : ℚ := ∑ k ∈ Finset.range (n / 2 + 1),
    let diff : ℚ := (n.choose k : ℚ) - (if k = 0 then 0 else (n.choose (k - 1) : ℚ))
    diff ^ 3
  let denominator : ℚ := (n.choose (n / 2) : ℚ)
  numerator / denominator

/-- Auxiliary sequence $b(n) = a(2n-1)$. -/
def b (n : ℕ) : ℚ :=
  a (2 * n - 1)

end OeisA3162

/-!
# A003162: exact supercongruence and integrality

The identity is due to Miana, Ohtsuka and Romero (2016), with the underlying
binomial identity of Ohtsuka and Tauraso proved by Amdeberhan and Ekhad's
certificates. This file uses no upstream admitted integrality theorem.
The full supercongruence uses the proved arithmetic towers shared with A003161.

Lean development: Wentao Li, with AI assistance.
-/

namespace B02R2A003162

open Finset B02R2Ballot

/-- The explicit integer quotient supplied by the cubic ballot identity. -/
def integerQuotient (m : ℕ) : ℤ :=
  4 * (m.choose (m / 2) : ℤ) ^ 2 - 3 *
    ∑ j ∈ range (m + 1), (j.choose (m / 2) : ℤ) * (j.choose (m - m / 2) : ℤ)

/-- Express the rational source numerator as the cast of the integer ballot sum. -/
theorem a_eq_div (m : ℕ) :
    OeisA3162.a m =
      ((∑ k ∈ range (m / 2 + 1), ballotTerm m k ^ 3 : ℤ) : ℚ) /
        (m.choose (m / 2) : ℚ) := by
  unfold OeisA3162.a
  push_cast
  apply congrArg (fun q : ℚ => q / (m.choose (m / 2) : ℚ))
  apply sum_congr rfl
  intro k _hk
  by_cases hk : k = 0 <;> simp [ballotTerm, hk]

/-- The exact rational sequence is the cast of an explicit integer expression. -/
theorem a_eq_integerQuotient (m : ℕ) : OeisA3162.a m = (integerQuotient m : ℚ) := by
  rw [a_eq_div, cubic_identity (Nat.div_le_self m 2)]
  have hH : (m.choose (m / 2) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (Nat.div_le_self m 2)
  apply (div_eq_iff hH).2
  simp only [integerQuotient]
  push_cast
  ring

/-- The exact source integrality statement, proved without its admitted source theorem. -/
theorem a_is_integer (m : ℕ) : (OeisA3162.a m).den = 1 := by
  rw [a_eq_integerQuotient]
  exact Rat.den_intCast _

/-- The odd-index rational source equals the integer normalization formula. -/
theorem b_odd_eq (n : ℕ) :
    OeisA3162.b (n + 1) = ((4 * halfCentral n ^ 2 - 3 * crossSum n : ℤ) : ℚ) := by
  rw [OeisA3162.b, show 2 * (n + 1) - 1 = 2 * n + 1 by omega, a_eq_integerQuotient]
  simp only [integerQuotient, show (2 * n + 1) / 2 = n by omega,
    show 2 * n + 1 - n = n + 1 by omega]
  rfl

/-- The source's reduced numerator is the integer quotient itself. -/
theorem b_num_odd (n : ℕ) :
    (OeisA3162.b (n + 1)).num = 4 * halfCentral n ^ 2 - 3 * crossSum n := by
  rw [b_odd_eq, Rat.num_intCast]

/-- The unconditional identity required to transfer Coster's congruences. -/
theorem normalized_normalization (n : ℕ) :
    2 * (OeisA3162.b (n + 1)).num = 3 * shiftedSquares n - halfCentral n ^ 2 := by
  rw [b_num_odd]
  have hh := crossSum_normalization n
  linear_combination -3 * hh

/-- Rewrite the exact numerator identity at every positive source index. -/
theorem normalized_normalization_pos (N : ℕ) (hN : 0 < N) :
    2 * (OeisA3162.b N).num =
      3 * shiftedSquares (N - 1) - halfCentral (N - 1) ^ 2 := by
  simpa [Nat.sub_add_cancel (by omega : 1 ≤ N)] using normalized_normalization (N - 1)

/-- Two arithmetic towers imply the exact A003162 conclusion. -/
theorem conjecture_of_coster
    (hs : B02R2A003161.CubicTower (fun N => shiftedSquares (N - 1)))
    (hc : B02R2A003161.CubicTower (fun N => halfCentral (N - 1))) :
    B02R2A003161.CubicTower (fun N => (OeisA3162.b N).num) := by
  intro n k p hn hk hp hp5
  have hu : 0 < n * p ^ k := Nat.mul_pos hn (pow_pos hp.pos _)
  have hl : 0 < n * p ^ (k - 1) := Nat.mul_pos hn (pow_pos hp.pos _)
  apply B02R2A003161.cancel_two hp hp5
  rw [normalized_normalization_pos _ hu, normalized_normalization_pos _ hl]
  exact ((hs n k p hn hk hp hp5).mul_left 3).sub ((hc n k p hn hk hp hp5).pow 2)

/-- The exact reduced-numerator supercongruence holds at every positive multiplier and level. -/
theorem conjecture (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (OeisA3162.b (n * p ^ k)).num ≡ (OeisA3162.b (n * p ^ (k - 1))).num
      [ZMOD (p : ℤ) ^ (3 * k)] :=
  conjecture_of_coster B02R2ShiftedCongruence.shiftedSquares_tower
    B02R2Central.halfCentral_tower n k p hn hk hp hp_ge


end B02R2A003162
