/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
import Mathlib

/-!
# OEIS A375439

OEIS name: expansion of the g.f. `A(x)` satisfying
`A(x) = x + x^2 + (2*A(x)^3 + A(x^3))/3`, offset 1.

Comment (Hanna): **Conjecture**: `a(n)` is odd iff `n` is in A038754,
i.e. `n = 3^k` or `n = 2 * 3^k`.

Clearing the denominator, the NAME is the integer coefficient relation
`3 a(n) = 2 [x^n] A^3 + [x^n] A(x^3)` for `n ≥ 3`, with `a(1) = a(2) = 1`
and the dummy value `a(0) = 0`. Divisibility by 3 holds for an arbitrary
sequence, by the freshman-dream identity in characteristic 3.

This file defines that recurrence and proves the parity conjecture.
The `𝔽₂` shadow is `A ≡ x + x^2 + A(x^3)`, not Catalan.
-/

open Finset Nat Polynomial

namespace A375439

/-- Convolution square. -/
def conv2 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), b k * b (n - k)

/-- Convolution cube `[x^n] B^3`. -/
def conv3 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), conv2 b k * b (n - k)

/-- Coefficient `[x^n] B(x^3)`. -/
def subst3 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  if 3 ∣ n then b (n / 3) else 0

/-- Numerator `2 [x^n] B^3 + [x^n] B(x^3)`. -/
def rhs (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  2 * conv3 b n + subst3 b n

/-- Coefficient recurrence of OEIS A375439 (`a 0` is a dummy zero). -/
def a : ℕ → ℕ :=
  Nat.strongRec fun n ih =>
    if n = 0 then 0
    else if n = 1 then 1
    else if n = 2 then 1
    else
      let b : ℕ → ℕ := fun m => if h : m < n then ih m h else 0
      rhs b n / 3

lemma a_zero : a 0 = 0 := by
  rw [a, strongRec_eq]
  simp

lemma a_one : a 1 = 1 := by
  rw [a, strongRec_eq]
  simp

lemma a_two : a 2 = 1 := by
  rw [a, strongRec_eq]
  simp

lemma conv2_congr {b c : ℕ → ℕ} {n : ℕ} (h : ∀ k ≤ n, b k = c k) :
    conv2 b n = conv2 c n := by
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hnk : n - k ≤ n := Nat.sub_le _ _
  rw [h k hk', h (n - k) hnk]

lemma conv3_eq_of_eq_lt {b c : ℕ → ℕ} {n : ℕ} (h0b : b 0 = 0) (h0c : c 0 = 0)
    (h : ∀ k < n, b k = c k) : conv3 b n = conv3 c n := by
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  by_cases hk0 : k = 0
  · subst hk0
    simp [conv2, h0b, h0c]
  by_cases hkn : k = n
  · subst hkn
    simp [h0b, h0c]
  have hkl : k < n := Nat.lt_of_le_of_ne hk' hkn
  have hnl : n - k < n := by omega
  have hconv : conv2 b k = conv2 c k :=
    conv2_congr fun i hi => h i (Nat.lt_of_le_of_lt hi hkl)
  rw [hconv, h (n - k) hnl]

lemma subst3_eq_of_eq_lt {b c : ℕ → ℕ} {n : ℕ} (hn : 0 < n)
    (h : ∀ k < n, b k = c k) : subst3 b n = subst3 c n := by
  unfold subst3
  split_ifs with hd
  · have : n / 3 < n := Nat.div_lt_self hn (by decide : 1 < 3)
    rw [h _ this]
  · rfl

lemma a_of_ge_three {n : ℕ} (hn : 3 ≤ n) : a n = rhs a n / 3 := by
  have hne0 : n ≠ 0 := by omega
  have hne1 : n ≠ 1 := by omega
  have hne2 : n ≠ 2 := by omega
  have hrec :
      a n = rhs (fun m => if h : m < n then a m else 0) n / 3 := by
    rw [a, strongRec_eq]
    simp [hne0, hne1, hne2, a]
  rw [hrec]
  congr 1
  unfold rhs
  have hpos : 0 < n := by omega
  have hb0 : (fun m => if h : m < n then a m else 0) 0 = 0 := by
    simp [hpos, a_zero]
  have hconv :
      conv3 (fun m => if h : m < n then a m else 0) n = conv3 a n :=
    conv3_eq_of_eq_lt hb0 a_zero fun k hk => by simp [hk]
  have hsub :
      subst3 (fun m => if h : m < n then a m else 0) n = subst3 a n :=
    subst3_eq_of_eq_lt hpos fun k hk => by simp [hk]
  rw [hconv, hsub]

/-- Truncated generating polynomial over `𝔽₃`. -/
noncomputable def trunc (f : ℕ → ZMod 3) (N : ℕ) : (ZMod 3)[X] :=
  ∑ i ∈ range (N + 1), C (f i) * X ^ i

lemma trunc_coeff (f : ℕ → ZMod 3) (N i : ℕ) :
    (trunc f N).coeff i = if i ≤ N then f i else 0 := by
  unfold trunc
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [sum_ite_eq]
  simp [mem_range]

lemma trunc_pow_three (f : ℕ → ZMod 3) (N : ℕ) :
    trunc f N ^ 3 = ∑ i ∈ range (N + 1), C (f i ^ 3) * X ^ (3 * i) := by
  unfold trunc
  rw [sum_pow_char (R := (ZMod 3)[X]) 3]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_pow, ← C_pow, ← pow_mul, mul_comm i 3]

lemma coeff_sq {R : Type*} [CommSemiring R] (p : R[X]) (m : ℕ) :
    (p ^ 2).coeff m = ∑ k ∈ range (m + 1), p.coeff k * p.coeff (m - k) := by
  rw [pow_two, coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => p.coeff i * p.coeff j) m

lemma coeff_cube {R : Type*} [CommSemiring R] (p : R[X]) (m : ℕ) :
    (p ^ 3).coeff m =
      ∑ k ∈ range (m + 1),
        (∑ i ∈ range (k + 1), p.coeff i * p.coeff (k - i)) * p.coeff (m - k) := by
  have hpow : p ^ 3 = p ^ 2 * p := by rw [pow_succ]
  rw [hpow, coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (p ^ 2).coeff i * p.coeff j)]
  refine sum_congr rfl fun k _ => ?_
  rw [coeff_sq]

lemma trunc_cube_coeff (f : ℕ → ZMod 3) (n : ℕ) :
    (trunc f n ^ 3).coeff n =
      ∑ k ∈ range (n + 1),
        (∑ i ∈ range (k + 1), f i * f (k - i)) * f (n - k) := by
  rw [coeff_cube]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hnk : n - k ≤ n := Nat.sub_le _ _
  have hf_le {i : ℕ} (hi : i ≤ n) : (trunc f n).coeff i = f i := by
    rw [trunc_coeff]
    simp [hi]
  have hsum :
      ∑ i ∈ range (k + 1), (trunc f n).coeff i * (trunc f n).coeff (k - i) =
        ∑ i ∈ range (k + 1), f i * f (k - i) := by
    refine sum_congr rfl fun i hi => ?_
    have hi' : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hik : k - i ≤ k := Nat.sub_le _ _
    rw [hf_le (le_trans hi' hk'), hf_le (le_trans hik hk')]
  rw [hsum, hf_le hnk]

lemma trunc_cube_freshman (f : ℕ → ZMod 3) (n : ℕ) :
    (trunc f n ^ 3).coeff n = if 3 ∣ n then f (n / 3) ^ 3 else 0 := by
  rw [trunc_pow_three, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases hd : 3 ∣ n
  · have ⟨k, hk⟩ := hd
    have hkmem : k ∈ range (n + 1) := by
      simp [mem_range, hk]
      omega
    have hdiv : n / 3 = k := by
      rw [hk, Nat.mul_div_cancel_left k (by decide : 0 < 3)]
    have hite : (if 3 ∣ n then f (n / 3) ^ 3 else 0) = f k ^ 3 := by
      simp [hd, hdiv]
    rw [hite, sum_eq_single k]
    · have : n = 3 * k := hk
      simp [this]
    · intro i _ hi_ne
      have hne : n ≠ 3 * i := by
        intro hni
        exact hi_ne (by omega)
      simp [hne]
    · intro hnot
      exact (hnot hkmem).elim
  · have hite : (if 3 ∣ n then f (n / 3) ^ 3 else 0) = 0 := by simp [hd]
    rw [hite]
    refine sum_eq_zero fun i _ => ?_
    have hne : n ≠ 3 * i := fun hni => hd ⟨i, hni⟩
    simp [hne]

lemma conv3_mod3 (b : ℕ → ℕ) (n : ℕ) :
    (conv3 b n : ZMod 3) = if 3 ∣ n then (b (n / 3) : ZMod 3) ^ 3 else 0 := by
  have hcast :
      (conv3 b n : ZMod 3) =
        ∑ k ∈ range (n + 1),
          (∑ i ∈ range (k + 1), (b i : ZMod 3) * (b (k - i) : ZMod 3)) *
            (b (n - k) : ZMod 3) := by
    simp [conv3, conv2, Nat.cast_sum, Nat.cast_mul]
  rw [hcast, ← trunc_cube_coeff, trunc_cube_freshman]

lemma subst3_mod3 (b : ℕ → ℕ) (n : ℕ) :
    (subst3 b n : ZMod 3) = if 3 ∣ n then (b (n / 3) : ZMod 3) else 0 := by
  unfold subst3
  split_ifs <;> simp

lemma two_mul_cube_add (x : ZMod 3) : 2 * x ^ 3 + x = 0 := by
  have hx : x ^ 3 = x := ZMod.pow_card x
  have h3 : (3 : ZMod 3) = 0 := by decide
  rw [hx]
  have : (2 : ZMod 3) * x + x = (3 : ZMod 3) * x := by ring
  rw [this, h3, zero_mul]

/-- Integrality: `2 [x^n] B^3 + [x^n] B(x^3)` is divisible by 3 for every sequence. -/
lemma three_dvd_rhs (b : ℕ → ℕ) (n : ℕ) : 3 ∣ rhs b n := by
  rw [← CharP.cast_eq_zero_iff (ZMod 3) 3]
  have hsum :
      (rhs b n : ZMod 3) =
        2 * (if 3 ∣ n then (b (n / 3) : ZMod 3) ^ 3 else 0) +
          if 3 ∣ n then (b (n / 3) : ZMod 3) else 0 := by
    simp [rhs, Nat.cast_add, Nat.cast_mul, conv3_mod3, subst3_mod3]
  rw [hsum]
  split_ifs
  · exact two_mul_cube_add _
  · simp

lemma three_mul_a_of_ge {n : ℕ} (hn : 3 ≤ n) : 3 * a n = rhs a n := by
  rw [a_of_ge_three hn, Nat.mul_div_cancel']
  exact three_dvd_rhs a n

lemma conv2_zero : conv2 a 0 = 0 := by
  simp [conv2, a_zero]

lemma conv2_one : conv2 a 1 = 0 := by
  rw [conv2, sum_range_succ, sum_range_succ]
  simp [a_zero, a_one]

lemma conv3_zero : conv3 a 0 = 0 := by
  simp [conv3, a_zero]

lemma conv3_one : conv3 a 1 = 0 := by
  rw [conv3, sum_range_succ, sum_range_succ]
  simp [conv2_zero, conv2_one, a_zero, a_one]

lemma conv3_two : conv3 a 2 = 0 := by
  rw [conv3, sum_range_succ, sum_range_succ, sum_range_succ]
  simp [conv2_zero, conv2_one, a_zero]

lemma subst3_zero : subst3 a 0 = 0 := by simp [subst3, a_zero]

lemma subst3_one : subst3 a 1 = 0 := by
  have : ¬ (3 ∣ (1 : ℕ)) := by decide
  simp [subst3, this]

lemma subst3_two : subst3 a 2 = 0 := by
  have : ¬ (3 ∣ (2 : ℕ)) := by decide
  simp [subst3, this]

/-- Cleared NAME: `3A = 3x + 3x^2 + 2A^3 + A(x^3)` on coefficients. -/
lemma three_mul_a (n : ℕ) :
    3 * a n =
      (if n = 1 then 3 else 0) + (if n = 2 then 3 else 0) + rhs a n := by
  rcases lt_or_ge n 3 with hn | hn
  · interval_cases n
    · simp [a_zero, rhs, conv3_zero, subst3_zero]
    · simp [a_one, rhs, conv3_one, subst3_one]
    · simp [a_two, rhs, conv3_two, subst3_two]
  · simp [show n ≠ 1 by omega, show n ≠ 2 by omega, three_mul_a_of_ge hn]

lemma a_mod2_of_ge {n : ℕ} (hn : 3 ≤ n) :
    (a n : ZMod 2) = if 3 ∣ n then (a (n / 3) : ZMod 2) else 0 := by
  have h3 : ((3 : ℕ) : ZMod 2) = 1 := by decide
  have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
  have hcast : ((3 * a n : ℕ) : ZMod 2) = (rhs a n : ZMod 2) := by
    rw [three_mul_a_of_ge hn]
  have ha : (a n : ZMod 2) = (rhs a n : ZMod 2) := by
    have : ((3 * a n : ℕ) : ZMod 2) = (a n : ZMod 2) := by
      rw [Nat.cast_mul, h3, one_mul]
    rw [← this, hcast]
  rw [ha]
  have hrhs : (rhs a n : ZMod 2) = (subst3 a n : ZMod 2) := by
    unfold rhs
    rw [Nat.cast_add, Nat.cast_mul, h2, zero_mul, zero_add]
  rw [hrhs]
  unfold subst3
  split_ifs <;> simp

/-- `n` is of the form `3^k` or `2 * 3^k` (OEIS A038754). -/
def IsA038754 (n : ℕ) : Prop := ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k

lemma isA038754_one : IsA038754 1 := ⟨0, Or.inl (by simp)⟩

lemma isA038754_two : IsA038754 2 := ⟨0, Or.inr (by simp)⟩

lemma not_isA038754_zero : ¬ IsA038754 0 := by
  rintro ⟨k, hk⟩
  cases hk with
  | inl h =>
    exact (pow_ne_zero k (by decide : (3 : ℕ) ≠ 0)) h.symm
  | inr h =>
    have : 2 * 3 ^ k ≠ 0 := by positivity
    exact this h.symm

lemma isA038754_iff_div {n : ℕ} (hd : 3 ∣ n) :
    IsA038754 n ↔ IsA038754 (n / 3) := by
  constructor
  · rintro ⟨k, hk⟩
    cases hk with
    | inl h =>
      cases k with
      | zero =>
        have hn1 : n = 1 := h.trans (pow_zero 3)
        exact absurd (hn1 ▸ hd) (by decide : ¬ (3 : ℕ) ∣ 1)
      | succ k =>
        refine ⟨k, Or.inl ?_⟩
        rw [h, pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 3)]
    | inr h =>
      cases k with
      | zero =>
        have hn2 : n = 2 := by
          rw [h, pow_zero, mul_one]
        exact absurd (hn2 ▸ hd) (by decide : ¬ (3 : ℕ) ∣ 2)
      | succ k =>
        refine ⟨k, Or.inr ?_⟩
        have hmul : 2 * 3 ^ (k + 1) = (2 * 3 ^ k) * 3 := by
          rw [pow_succ]
          ring
        rw [h, hmul, Nat.mul_div_cancel _ (by decide : 0 < 3)]
  · rintro ⟨k, hk⟩
    cases hk with
    | inl h =>
      refine ⟨k + 1, Or.inl ?_⟩
      rw [← Nat.mul_div_cancel' hd, h, pow_succ, mul_comm]
    | inr h =>
      refine ⟨k + 1, Or.inr ?_⟩
      have hmul : 3 * (2 * 3 ^ k) = 2 * 3 ^ (k + 1) := by
        rw [pow_succ]
        ring
      rw [← Nat.mul_div_cancel' hd, h, hmul]

lemma not_isA038754_of_not_dvd {n : ℕ} (hn : 3 ≤ n) (hd : ¬ 3 ∣ n) :
    ¬ IsA038754 n := by
  rintro ⟨k, hk⟩
  cases hk with
  | inl h =>
    cases k with
    | zero =>
      have : n = 1 := h.trans (pow_zero 3)
      omega
    | succ k =>
      apply hd
      rw [h, pow_succ, mul_comm]
      exact dvd_mul_right (3 : ℕ) (3 ^ k)
  | inr h =>
    cases k with
    | zero =>
      have : n = 2 := by
        rw [h, pow_zero, mul_one]
      omega
    | succ k =>
      apply hd
      have hmul : 2 * 3 ^ (k + 1) = 3 * (2 * 3 ^ k) := by
        rw [pow_succ]
        ring
      rw [h, hmul]
      exact dvd_mul_right (3 : ℕ) (2 * 3 ^ k)

/-- OEIS A375439: `a(n)` is odd iff `n = 3^k` or `n = 2 * 3^k`. -/
theorem a_odd_iff_A038754 (n : ℕ) : Odd (a n) ↔ IsA038754 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases lt_or_ge n 3 with hn | hn
    · interval_cases n
      · constructor
        · intro hodd
          have : Even (a 0) := by simp [a_zero]
          exact (Nat.not_odd_iff_even.2 this hodd).elim
        · intro hA
          exact (not_isA038754_zero hA).elim
      · constructor
        · intro
          exact isA038754_one
        · intro
          simp [a_one]
      · constructor
        · intro
          exact isA038754_two
        · intro
          simp [a_two]
    · by_cases hd : 3 ∣ n
      · have hlt : n / 3 < n := Nat.div_lt_self (by omega) (by decide : 1 < 3)
        have hparity : Odd (a n) ↔ Odd (a (n / 3)) := by
          have hcast : (a n : ZMod 2) = (a (n / 3) : ZMod 2) := by
            rw [a_mod2_of_ge hn]
            simp [hd]
          rw [← ZMod.natCast_eq_one_iff_odd, hcast, ZMod.natCast_eq_one_iff_odd]
        rw [hparity, ih (n / 3) hlt, isA038754_iff_div hd]
      · constructor
        · intro hodd
          have : Even (a n) :=
            (ZMod.natCast_eq_zero_iff_even).1 (by
              rw [a_mod2_of_ge hn]
              simp [hd])
          exact (Nat.not_odd_iff_even.2 this hodd).elim
        · intro hA
          exact (not_isA038754_of_not_dvd hn hd hA).elim

example : a 0 = 0 := a_zero
example : a 1 = 1 := a_one
example : a 2 = 1 := a_two

#print axioms a_odd_iff_A038754
#print axioms three_mul_a
#print axioms three_dvd_rhs

end A375439
