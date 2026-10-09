/-
Copyright (c) 2026 AI4Math Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
import Mathlib

/-!
# OEIS A361033, conjecture C1

OEIS defines `a(n) = 3 * (4*n)! / (n! * ((n+1)!)^3)` for `n ≥ 0`, and
conjectures that `a(n)` is odd if and only if `n = 2^k - 1` for some
`k ≥ 0`.

This file uses that exact factorial formula as the definition (after
proving the denominator divides the numerator) and proves the
conjecture. The 2-adic valuation is identified exactly as
`v₂(a(n)) = 3 (s₂(n+1) - 1)`, where `s₂` is the sum of binary digits.
-/

open Finset Nat

namespace A361033

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-! ## Binary digit sums -/

lemma list_sum_eq_zero {l : List ℕ} (h : l.sum = 0) : ∀ x ∈ l, x = 0 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx : x = 0 ∧ xs.sum = 0 := by
      have : x + xs.sum = 0 := by simpa using h
      exact Nat.eq_zero_of_add_eq_zero this
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hx.1
    · exact ih hx.2 y hy

lemma ofDigits_eq_zero_of_eq_zero {b : ℕ} {l : List ℕ}
    (h : ∀ x ∈ l, x = 0) : ofDigits b l = 0 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx : x = 0 := h x (by simp)
    rw [ofDigits_cons, hx, zero_add,
      ih (fun y hy => h y (by simp [hy])), mul_zero]

lemma exists_split_of_sum_eq_one {l : List ℕ}
    (h01 : ∀ x ∈ l, x ≤ 1) (hs : l.sum = 1) :
    ∃ a b, l = a ++ 1 :: b ∧ (∀ x ∈ a, x = 0) ∧ (∀ x ∈ b, x = 0) := by
  induction l with
  | nil => simp at hs
  | cons x xs ih =>
    have hx : x = 0 ∨ x = 1 := by
      have := h01 x (by simp)
      omega
    rcases hx with rfl | rfl
    · have hxs : xs.sum = 1 := by simpa using hs
      obtain ⟨a, b, rfl, ha, hb⟩ :=
        ih (fun y hy => h01 y (by simp [hy])) hxs
      refine ⟨0 :: a, b, by simp, ?_, hb⟩
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · rfl
      · exact ha y hy
    · have hxs : xs.sum = 0 := by simpa using hs
      exact ⟨[], xs, by simp, by simp, list_sum_eq_zero hxs⟩

/-- The sum of binary digits is `1` if and only if the number is a power of two. -/
lemma digits_two_sum_eq_one_iff (n : ℕ) :
    ((digits 2 n).sum = 1) ↔ ∃ k, n = 2 ^ k := by
  constructor
  · intro h
    have h01 : ∀ x ∈ digits 2 n, x ≤ 1 := fun x hx =>
      (Nat.lt_succ_iff.mp (digits_lt_base one_lt_two hx))
    obtain ⟨a, b, hsplit, ha, hb⟩ := exists_split_of_sum_eq_one h01 h
    have hn : n = ofDigits 2 (digits 2 n) := (ofDigits_digits 2 n).symm
    rw [hsplit, ofDigits_append, ofDigits_cons,
      ofDigits_eq_zero_of_eq_zero ha, ofDigits_eq_zero_of_eq_zero hb] at hn
    exact ⟨a.length, by simpa using hn⟩
  · rintro ⟨k, rfl⟩
    rw [← mul_one (2 ^ k), digits_base_pow_mul one_lt_two (by decide : (0 : ℕ) < 1),
      digits_of_lt 2 1 (by decide) (by decide)]
    simp [List.sum_replicate]

lemma sum_digits_two_four_mul (n : ℕ) :
    (digits 2 (4 * n)).sum = (digits 2 n).sum := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have h4 : 4 * n = 2 ^ 2 * n := by ring
    rw [h4, digits_base_pow_mul one_lt_two (Nat.pos_of_ne_zero hn)]
    simp

lemma digits_two_sum_pos {n : ℕ} (hn : n ≠ 0) : 1 ≤ (digits 2 n).sum := by
  have hnil : digits 2 n ≠ [] := digits_ne_nil_iff_ne_zero.mpr hn
  exact (List.sum_pos_iff_exists_pos_nat).mpr
    ⟨_, List.getLast_mem hnil,
      Nat.pos_of_ne_zero (getLast_digit_ne_zero 2 hn)⟩

lemma mersenne_iff (n : ℕ) :
    (∃ k, n + 1 = 2 ^ k) ↔ ∃ k, n = 2 ^ k - 1 := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    omega
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
    omega

/-! ## Legendre's formula helpers -/

lemma v2_factorial_add (n : ℕ) :
    padicValNat 2 n.factorial + (digits 2 n).sum = n := by
  have h : padicValNat 2 n.factorial = n - (digits 2 n).sum := by
    simpa [Nat.reduceSub, one_mul] using
      sub_one_mul_padicValNat_factorial (p := 2) n
  rw [h, Nat.sub_add_cancel (digit_sum_le 2 n)]

lemma log_lt_of_lt_two_pow {p m b : ℕ} [hp : Fact p.Prime]
    (hb : 0 < b) (hm : m < 2 ^ b) : log p m < b := by
  rcases eq_or_ne m 0 with rfl | hm0
  · simpa [log_zero_right] using hb
  · exact log_lt_of_lt_pow hm0
      (hm.trans_le (Nat.pow_le_pow_left hp.out.two_le b))

lemma lt_two_pow_bound (n m : ℕ) (hm : m ≤ 4 * n + 1) :
    m < 2 ^ (4 * n + 2) :=
  (Nat.lt_pow_self one_lt_two).trans_le
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ))
      (hm.trans (by omega : 4 * n + 1 ≤ 4 * n + 2)))

lemma log_lt_bound (p n m : ℕ) [hp : Fact p.Prime] (hm : m ≤ 4 * n + 1) :
    log p m < 4 * n + 2 :=
  log_lt_of_lt_two_pow (by omega) (lt_two_pow_bound n m hm)

lemma padicValNat_factorial_bound (p n m : ℕ) [hp : Fact p.Prime]
    (hm : m ≤ 4 * n + 1) :
    padicValNat p m.factorial =
      ∑ i ∈ Ico 1 (4 * n + 2), m / p ^ i :=
  padicValNat_factorial (log_lt_bound p n m hm)

/-! ## Floor comparison for odd primes -/

lemma add_one_div (n q : ℕ) (hq : 0 < q) :
    (n + 1) / q = n / q + if n % q + 1 = q then 1 else 0 := by
  have hmod := Nat.mod_lt n hq
  have : n + 1 = (n % q + 1) + q * (n / q) := by
    conv_lhs => rw [← Nat.div_add_mod n q]
    ring
  rw [this, Nat.add_mul_div_left (n % q + 1) (n / q) hq]
  split_ifs with h
  · rw [h, Nat.div_self hq]
    omega
  · have : n % q + 1 < q := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hmod) h
    rw [Nat.div_eq_of_lt this]
    omega

lemma four_mul_div (n q : ℕ) (hq : 0 < q) :
    (4 * n) / q = 4 * (n / q) + (4 * (n % q)) / q := by
  have hrew : 4 * n = q * (4 * (n / q)) + 4 * (n % q) := by
    conv_lhs => rw [← Nat.div_add_mod n q]
    ring
  rw [hrew, Nat.mul_add_div hq]

/-- For `q ≥ 4`, each Legendre summand is nonnegative. -/
lemma term_nonneg {q n : ℕ} (hq : 4 ≤ q) :
    n / q + 3 * ((n + 1) / q) ≤ (4 * n) / q := by
  have hq0 : 0 < q := by omega
  rw [add_one_div n q hq0, four_mul_div n q hq0]
  by_cases h : n % q + 1 = q
  · have hr : n % q = q - 1 := by omega
    have hdiv : (4 * (q - 1)) / q = 3 := by
      apply Nat.div_eq_of_lt_le
      · have : 3 * q ≤ 4 * (q - 1) := by omega
        simpa [hr] using this
      · have : 4 * (q - 1) < (3 + 1) * q := by omega
        simpa [hr] using this
    have hite : (if n % q + 1 = q then 1 else 0) = 1 := by simp [h]
    rw [hite, hr, hdiv]
    omega
  · have hite : (if n % q + 1 = q then 1 else 0) = 0 := by simp [h]
    rw [hite, add_zero]
    have : n / q + 3 * (n / q) = 4 * (n / q) := by ring
    rw [this]
    exact Nat.le_add_right _ _

lemma term_three (n : ℕ) :
    n / 3 + 3 * ((n + 1) / 3) ≤ (4 * n) / 3 + 1 := by
  have hq0 : (0 : ℕ) < 3 := by decide
  rw [add_one_div n 3 hq0, four_mul_div n 3 hq0]
  by_cases h : n % 3 + 1 = 3
  · have hr : n % 3 = 2 := by omega
    have hite : (if n % 3 + 1 = 3 then 1 else 0) = 1 := by simp [h]
    rw [hite, hr]
    omega
  · have hite : (if n % 3 + 1 = 3 then 1 else 0) = 0 := by simp [h]
    rw [hite]
    omega

lemma padicValNat_three_of_odd_prime {p : ℕ} [hp : Fact p.Prime] (_h2 : p ≠ 2) :
    padicValNat p 3 = if p = 3 then 1 else 0 := by
  by_cases h3 : p = 3
  · subst h3
    simp
  · have : ¬ p ∣ 3 := by
      intro hdvd
      exact h3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp hdvd)
    simp [h3, padicValNat.eq_zero_of_not_dvd this]

/-- Integrality at an odd prime, via Legendre's floor-sum formula. -/
lemma odd_prime_le (p n : ℕ) [hp : Fact p.Prime] (h2 : p ≠ 2) :
    padicValNat p (n.factorial * (n + 1).factorial ^ 3) ≤
      padicValNat p (3 * (4 * n).factorial) := by
  have h3ne : (3 : ℕ) ≠ 0 := by decide
  have hf : (4 * n).factorial ≠ 0 := factorial_ne_zero _
  have hn0 : n.factorial ≠ 0 := factorial_ne_zero _
  have hn1 : (n + 1).factorial ≠ 0 := factorial_ne_zero _
  rw [padicValNat.mul hn0 (pow_ne_zero _ hn1), padicValNat.pow,
    padicValNat.mul h3ne hf]
  have hn_le : n ≤ 4 * n + 1 := by omega
  have hn1_le : n + 1 ≤ 4 * n + 1 := by omega
  have h4_le : 4 * n ≤ 4 * n + 1 := by omega
  rw [padicValNat_factorial_bound p n n hn_le,
    padicValNat_factorial_bound p n (n + 1) hn1_le,
    padicValNat_factorial_bound p n (4 * n) h4_le]
  by_cases h3 : p = 3
  · subst h3
    have hself : padicValNat 3 3 = 1 := padicValNat_self
    rw [hself]
    have hdisj : (1 : ℕ) ∉ Ico 2 (4 * n + 2) := by
      simp [mem_Ico]
    have hsplit :
        Ico (1 : ℕ) (4 * n + 2) = insert 1 (Ico 2 (4 * n + 2)) := by
      ext x
      simp only [mem_insert, mem_Ico]
      omega
    rw [hsplit, sum_insert hdisj, sum_insert hdisj, sum_insert hdisj, mul_add]
    have hhead : n / 3 ^ 1 + 3 * ((n + 1) / 3 ^ 1) ≤ (4 * n) / 3 ^ 1 + 1 := by
      simpa using term_three n
    have htail :
        ∑ i ∈ Ico 2 (4 * n + 2), n / 3 ^ i +
            3 * ∑ i ∈ Ico 2 (4 * n + 2), (n + 1) / 3 ^ i ≤
          ∑ i ∈ Ico 2 (4 * n + 2), (4 * n) / 3 ^ i := by
      have hmul :
          3 * ∑ i ∈ Ico 2 (4 * n + 2), (n + 1) / 3 ^ i =
            ∑ i ∈ Ico 2 (4 * n + 2), 3 * ((n + 1) / 3 ^ i) := by
        rw [mul_sum]
      rw [hmul, ← sum_add_distrib]
      refine sum_le_sum fun i hi => ?_
      have hi' : 2 ≤ i := (mem_Ico.mp hi).1
      have : 4 ≤ 3 ^ i := by
        have : 3 ^ 2 ≤ 3 ^ i := Nat.pow_le_pow_right (by decide) hi'
        omega
      exact term_nonneg this
    linarith [hhead, htail]
  · have hp3 : padicValNat p 3 = 0 := by
      simpa [h3] using padicValNat_three_of_odd_prime (p := p) h2
    rw [hp3, zero_add]
    have hmul :
        3 * ∑ i ∈ Ico 1 (4 * n + 2), (n + 1) / p ^ i =
          ∑ i ∈ Ico 1 (4 * n + 2), 3 * ((n + 1) / p ^ i) := by
      rw [mul_sum]
    rw [hmul, ← sum_add_distrib]
    refine sum_le_sum fun i hi => ?_
    have hi0 : 0 < i := lt_of_lt_of_le (by decide : (0 : ℕ) < 1) (mem_Ico.mp hi).1
    have hnot4 : ¬ Nat.Prime 4 := by
      simpa using Nat.not_prime_mul (a := 2) (b := 2)
        (by decide : (2 : ℕ) ≠ 1) (by decide : (2 : ℕ) ≠ 1)
    have hp5 : 5 ≤ p := by
      have : 2 ≤ p := hp.out.two_le
      have hp4 : p ≠ 4 := fun h => hnot4 (h ▸ hp.out)
      omega
    have : 4 ≤ p ^ i := by
      have : p ≤ p ^ i := Nat.le_self_pow (Nat.ne_zero_of_lt hi0) p
      omega
    exact term_nonneg this

/-! ## 2-adic comparison -/

lemma v2_num (n : ℕ) :
    padicValNat 2 (3 * (4 * n).factorial) + (digits 2 n).sum = 4 * n := by
  have h3 : padicValNat 2 3 = 0 :=
    padicValNat.eq_zero_of_not_dvd (by decide : ¬ (2 : ℕ) ∣ 3)
  rw [padicValNat.mul (by decide : (3 : ℕ) ≠ 0) (factorial_ne_zero _), h3,
    zero_add]
  have h := v2_factorial_add (4 * n)
  rwa [sum_digits_two_four_mul] at h

lemma v2_den (n : ℕ) :
    padicValNat 2 (n.factorial * (n + 1).factorial ^ 3) +
        (digits 2 n).sum + 3 * (digits 2 (n + 1)).sum =
      4 * n + 3 := by
  have hn0 : n.factorial ≠ 0 := factorial_ne_zero _
  have hn1 : (n + 1).factorial ≠ 0 := factorial_ne_zero _
  rw [padicValNat.mul hn0 (pow_ne_zero _ hn1), padicValNat.pow]
  have hA := v2_factorial_add n
  have hB := v2_factorial_add (n + 1)
  have hB3 :
      3 * padicValNat 2 (n + 1).factorial + 3 * (digits 2 (n + 1)).sum =
        3 * (n + 1) := by
    rw [← mul_add, hB]
  omega

lemma two_le (n : ℕ) :
    padicValNat 2 (n.factorial * (n + 1).factorial ^ 3) ≤
      padicValNat 2 (3 * (4 * n).factorial) := by
  have hnum := v2_num n
  have hden := v2_den n
  have hs : 1 ≤ (digits 2 (n + 1)).sum := digits_two_sum_pos (succ_ne_zero n)
  omega

/-! ## Integrality of the OEIS formula -/

lemma denom_dvd_num (n : ℕ) :
    n.factorial * (n + 1).factorial ^ 3 ∣ 3 * (4 * n).factorial := by
  have hd : n.factorial * (n + 1).factorial ^ 3 ≠ 0 :=
    mul_ne_zero (factorial_ne_zero _) (pow_ne_zero _ (factorial_ne_zero _))
  have hn : 3 * (4 * n).factorial ≠ 0 :=
    mul_ne_zero (by decide) (factorial_ne_zero _)
  rw [← factorization_le_iff_dvd hd hn]
  intro p
  by_cases hp : p.Prime
  · rw [factorization_def _ hp, factorization_def _ hp]
    by_cases h2 : p = 2
    · subst h2
      exact two_le n
    · exact odd_prime_le (hp := ⟨hp⟩) p n h2
  · simp [factorization_eq_zero_of_not_prime _ hp]

/-- OEIS A361033: `a(n) = 3*(4*n)! / (n! * ((n+1)!)^3)`, as a natural number. -/
def a (n : ℕ) : ℕ :=
  3 * (4 * n).factorial / (n.factorial * (n + 1).factorial ^ 3)

lemma a_mul_denom (n : ℕ) :
    a n * (n.factorial * (n + 1).factorial ^ 3) = 3 * (4 * n).factorial := by
  rw [a, Nat.div_mul_cancel (denom_dvd_num n)]

lemma a_ne_zero (n : ℕ) : a n ≠ 0 := by
  intro h
  have hmul := a_mul_denom n
  rw [h, zero_mul] at hmul
  exact (mul_ne_zero (by decide : (3 : ℕ) ≠ 0) (factorial_ne_zero _)) hmul.symm

lemma odd_iff_not_two_dvd {m : ℕ} : Odd m ↔ ¬ 2 ∣ m := by
  constructor
  · exact Odd.not_two_dvd_nat
  · intro h
    rw [← not_even_iff_odd, even_iff_two_dvd]
    exact h

lemma odd_iff_padicValNat_two {m : ℕ} (hm : m ≠ 0) :
    Odd m ↔ padicValNat 2 m = 0 := by
  constructor
  · intro h
    exact padicValNat.eq_zero_of_not_dvd (odd_iff_not_two_dvd.mp h)
  · intro h
    rw [odd_iff_not_two_dvd]
    intro hdvd
    have hpow : (2 : ℕ) ^ 1 ∣ m := by simpa using hdvd
    have : 1 ≤ padicValNat 2 m := (padicValNat_dvd_iff_le hm).mp hpow
    omega

lemma v2_a (n : ℕ) :
    padicValNat 2 (a n) = 3 * ((digits 2 (n + 1)).sum - 1) := by
  have hdiv := denom_dvd_num n
  have hn0 : n.factorial * (n + 1).factorial ^ 3 ≠ 0 :=
    mul_ne_zero (factorial_ne_zero _) (pow_ne_zero _ (factorial_ne_zero _))
  rw [a, padicValNat.div_of_dvd hdiv]
  have hnum := v2_num n
  have hden := v2_den n
  have hs : 1 ≤ (digits 2 (n + 1)).sum := digits_two_sum_pos (succ_ne_zero n)
  omega

/-- OEIS A361033 conjecture C1. -/
theorem a_odd_iff (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  have hs : 1 ≤ (digits 2 (n + 1)).sum := digits_two_sum_pos (succ_ne_zero n)
  have hval : padicValNat 2 (a n) = 0 ↔ (digits 2 (n + 1)).sum = 1 := by
    rw [v2_a]
    constructor
    · intro h
      omega
    · intro h
      rw [h, Nat.sub_self, mul_zero]
  rw [odd_iff_padicValNat_two (a_ne_zero n), hval, digits_two_sum_eq_one_iff,
    mersenne_iff]

/-! ## Source-fidelity checks against the OEIS data line -/

lemma a_zero : a 0 = 3 := by
  simp [a]

lemma a_one : a 1 = 9 := by
  simp [a]
  norm_num

lemma a_two : a 2 = 280 := by
  simp [a]
  norm_num

lemma a_three : a 3 = 17325 := by
  simp [a]
  norm_num

end A361033

#print axioms A361033.a_odd_iff
#print axioms A361033.denom_dvd_num
#print axioms A361033.v2_a
