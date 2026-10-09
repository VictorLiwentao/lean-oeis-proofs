/-
Copyright (c) 2026 AI4Math Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
import Mathlib

/-!
# OEIS A368633, conjecture C1

OEIS name: expansion of the g.f. `A(x)` satisfying
`A(x) = 1 + 2*x*A(x)^2 - x*A(-x)^2`.

Comment (Hanna): **Conjecture**: `a(n)` is odd when `n = 2^k - 1` for
`k ≥ 0` and even elsewhere.

Coefficient extraction of the functional equation yields the recurrence
`a 0 = 1` and, for `n ≥ 0`,

`a (n+1) = (if Even (n+1) then 3 else 1) * ∑_{k=0}^n a k * a (n-k)`.

This file defines that recurrence, proves it is equivalent to Hanna's
equation over `ℤ`, and proves the parity conjecture.
-/

open Finset Nat PowerSeries

namespace A368633

/-- Convolution square. -/
def conv2 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), b k * b (n - k)

/-- Coefficient recurrence of OEIS A368633. -/
def a : ℕ → ℕ :=
  Nat.strongRec fun n ih =>
    if n = 0 then 1
    else
      let b : ℕ → ℕ := fun m => if h : m < n then ih m h else 0
      (if Even n then 3 else 1) * conv2 b (n - 1)

lemma a_zero : a 0 = 1 := by
  rw [a, strongRec_eq]
  simp

lemma conv2_congr {b c : ℕ → ℕ} {n : ℕ} (h : ∀ k ≤ n, b k = c k) :
    conv2 b n = conv2 c n := by
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hnk : n - k ≤ n := Nat.sub_le _ _
  rw [h k hk', h (n - k) hnk]

lemma a_of_pos {n : ℕ} (hn : 0 < n) :
    a n = (if Even n then 3 else 1) * conv2 a (n - 1) := by
  have hne : n ≠ 0 := hn.ne'
  have hrec :
      a n =
        (if Even n then 3 else 1) *
          conv2 (fun m => if h : m < n then a m else 0) (n - 1) := by
    rw [a, strongRec_eq]
    simp [hne, a]
  rw [hrec]
  refine congrArg (fun t => (if Even n then 3 else 1) * t) ?_
  refine conv2_congr fun k hk => ?_
  have hlt : k < n := Nat.lt_of_le_of_lt hk (Nat.sub_one_lt hne)
  simp [hlt]

lemma a_succ (n : ℕ) :
    a (n + 1) = (if Even (n + 1) then 3 else 1) * conv2 a n :=
  a_of_pos (Nat.succ_pos _)

lemma a_succ_mod2 (n : ℕ) :
    (a (n + 1) : ZMod 2) =
      ∑ k ∈ range (n + 1), (a k : ZMod 2) * (a (n - k) : ZMod 2) := by
  have h3 : ((3 : ℕ) : ZMod 2) = 1 := by decide
  rw [a_succ, conv2, Nat.cast_mul, Nat.cast_sum]
  simp_rw [Nat.cast_mul]
  split_ifs
  · rw [h3, one_mul]
  · rw [Nat.cast_one, one_mul]

lemma conv2_odd_eq_zero (f : ℕ → ZMod 2) (m : ℕ) :
    ∑ k ∈ range (2 * m + 2), f k * f (2 * m + 1 - k) = 0 := by
  apply sum_involution (fun k _ => 2 * m + 1 - k)
  · intro k hk
    have hlt : k < 2 * m + 2 := mem_range.mp hk
    rw [show 2 * m + 1 - (2 * m + 1 - k) = k by omega, mul_comm]
    exact CharTwo.add_self_eq_zero _
  · intro k hk _
    have hlt : k < 2 * m + 2 := mem_range.mp hk
    intro hfix
    omega
  · intro k hk
    have hlt : k < 2 * m + 2 := mem_range.mp hk
    simp [mem_range]
    omega
  · intro k hk
    have hlt : k < 2 * m + 2 := mem_range.mp hk
    omega

lemma conv2_even_square (f : ℕ → ZMod 2) (m : ℕ) :
    ∑ k ∈ range (2 * m + 1), f k * f (2 * m - k) = f m ^ 2 := by
  classical
  let s := range (2 * m + 1)
  have hm : m ∈ s := by
    simp [s, mem_range]
    omega
  have hcancel : ∑ k ∈ s.erase m, f k * f (2 * m - k) = 0 := by
    apply sum_involution (fun k _ => 2 * m - k)
    · intro k hk
      have hk' := mem_erase.mp hk
      have hlt : k < 2 * m + 1 := mem_range.mp hk'.2
      rw [show 2 * m - (2 * m - k) = k by omega, mul_comm (f (2 * m - k))]
      exact CharTwo.add_self_eq_zero _
    · intro k hk _
      have hk' := mem_erase.mp hk
      have hlt : k < 2 * m + 1 := mem_range.mp hk'.2
      omega
    · intro k hk
      have hk' := mem_erase.mp hk
      have hlt : k < 2 * m + 1 := mem_range.mp hk'.2
      refine mem_erase.mpr ⟨?_, mem_range.mpr ?_⟩
      · intro hkm
        have : k = m := by omega
        exact hk'.1 this
      · omega
    · intro k hk
      have hk' := mem_erase.mp hk
      have hlt : k < 2 * m + 1 := mem_range.mp hk'.2
      omega
  rw [← sum_erase_add _ _ hm, hcancel, zero_add]
  have : 2 * m - m = m := by omega
  simp [pow_two, this]

lemma sq_eq_self_zmod2 (x : ZMod 2) : x ^ 2 = x :=
  (by decide : ∀ y : ZMod 2, y ^ 2 = y) x

lemma a_even_succ_even (m : ℕ) : Even (a (2 * m + 2)) := by
  have hcast : (a (2 * m + 2) : ZMod 2) = 0 := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, a_succ_mod2]
    simpa using conv2_odd_eq_zero (fun k => (a k : ZMod 2)) m
  exact (ZMod.natCast_eq_zero_iff_even).1 hcast

lemma a_odd_succ_iff {m : ℕ} : Odd (a (2 * m + 1)) ↔ Odd (a m) := by
  have hcast : (a (2 * m + 1) : ZMod 2) = (a m : ZMod 2) := by
    rw [a_succ_mod2, conv2_even_square (fun k => (a k : ZMod 2)) m, sq_eq_self_zmod2]
  rw [← ZMod.natCast_eq_one_iff_odd, hcast, ZMod.natCast_eq_one_iff_odd]

/-- `n` is of the form `2^k - 1`. -/
def IsMersenne (n : ℕ) : Prop := ∃ k : ℕ, n + 1 = 2 ^ k

lemma not_mersenne_even_succ (m : ℕ) : ¬ IsMersenne (2 * m + 2) := by
  rintro ⟨k, hk⟩
  have hodd : Odd (2 * m + 3) := odd_two_mul_add_one (m + 1)
  have : Odd (2 ^ k) := by
    have : 2 * m + 3 = 2 * m + 2 + 1 := by omega
    simpa [this, ← hk] using hodd
  cases k with
  | zero =>
    simp at hk
  | succ k =>
    have : Even (2 ^ (k + 1)) := even_pow.2 ⟨even_two, succ_ne_zero k⟩
    exact (not_odd_iff_even.2 this) ‹Odd (2 ^ (k + 1))›

/-- OEIS A368633-C1: `a(n)` is odd iff `n = 2^k - 1`. -/
theorem a_odd_iff_mersenne (n : ℕ) : Odd (a n) ↔ IsMersenne n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · constructor
      · intro
        exact ⟨0, by simp⟩
      · intro
        simp [a_zero]
    obtain ⟨m, rfl | rfl⟩ := even_or_odd' n
    · rw [a_odd_succ_iff, ih m (by omega)]
      constructor
      · rintro ⟨t, ht⟩
        refine ⟨t + 1, ?_⟩
        omega
      · rintro ⟨t, ht⟩
        cases t with
        | zero =>
          simp at ht
        | succ t =>
          refine ⟨t, ?_⟩
          omega
    · constructor
      · intro hodd
        exact (not_odd_iff_even.2 (a_even_succ_even m) hodd).elim
      · intro hM
        exact (not_mersenne_even_succ m hM).elim

/-! ## Generating-function equation over `ℤ` -/

def A : ℤ⟦X⟧ := mk fun n => (a n : ℤ)

def Aneg : ℤ⟦X⟧ := mk fun n => (-1 : ℤ) ^ n * (a n : ℤ)

lemma coeff_A (n : ℕ) : coeff n A = (a n : ℤ) := by simp [A, coeff_mk]

lemma coeff_Aneg (n : ℕ) : coeff n Aneg = (-1 : ℤ) ^ n * (a n : ℤ) := by
  simp [Aneg, coeff_mk]

lemma coeff_sq_int (F : ℤ⟦X⟧) (n : ℕ) :
    coeff n (F ^ 2) = ∑ k ∈ range (n + 1), coeff k F * coeff (n - k) F := by
  rw [pow_two, coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i F * coeff j F) n

lemma coeff_A_sq (n : ℕ) : coeff n (A ^ 2) = (conv2 a n : ℤ) := by
  rw [coeff_sq_int, conv2]
  simp [coeff_A, Nat.cast_sum, Nat.cast_mul]

lemma coeff_Aneg_sq (n : ℕ) :
    coeff n (Aneg ^ 2) = (-1 : ℤ) ^ n * (conv2 a n : ℤ) := by
  rw [coeff_sq_int]
  simp only [coeff_Aneg]
  have :
      ∑ k ∈ range (n + 1),
        ((-1 : ℤ) ^ k * (a k : ℤ)) * ((-1 : ℤ) ^ (n - k) * (a (n - k) : ℤ)) =
        (-1 : ℤ) ^ n * ∑ k ∈ range (n + 1), (a k : ℤ) * (a (n - k) : ℤ) := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hsign : (-1 : ℤ) ^ k * (-1 : ℤ) ^ (n - k) = (-1 : ℤ) ^ n := by
      rw [← pow_add, Nat.add_sub_cancel' hk']
    simp [hsign, mul_left_comm, mul_assoc, mul_comm]
  simpa [conv2, Nat.cast_sum, Nat.cast_mul] using this

lemma coeff_X_mul' (F : ℤ⟦X⟧) (n : ℕ) : coeff (n + 1) (X * F) = coeff n F :=
  coeff_succ_X_mul n F

lemma coeff_factor (n : ℕ) :
    ((if Even (n + 1) then 3 else 1 : ℕ) : ℤ) = 2 - (-1 : ℤ) ^ n := by
  by_cases h : Even n
  · have hnp : ¬ Even (n + 1) := fun h' => Nat.even_add_one.mp h' h
    rw [Even.neg_one_pow (α := ℤ) h]
    simp [hnp]
  · have hnp : Even (n + 1) := Nat.even_add_one.mpr h
    have hodd : Odd n := Nat.not_even_iff_odd.mp h
    rw [Odd.neg_one_pow (α := ℤ) hodd]
    simp [hnp]

/-- The recurrence generating function satisfies Hanna's equation. -/
theorem mk_a_satisfiesHanna : A = 1 + 2 * X * A ^ 2 - X * Aneg ^ 2 := by
  refine PowerSeries.ext fun n => ?_
  rcases n with _ | n
  · simp [coeff_A, a_zero, coeff_one]
  · have hx1 : coeff (n + 1) (1 : ℤ⟦X⟧) = 0 := by simp [coeff_one]
    have h2 : coeff (n + 1) (2 * X * A ^ 2) = 2 * coeff n (A ^ 2) := by
      rw [show 2 * X * A ^ 2 = C (2 : ℤ) * (X * A ^ 2) by simp [mul_assoc],
        coeff_C_mul, coeff_X_mul']
    have hneg : coeff (n + 1) (X * Aneg ^ 2) = coeff n (Aneg ^ 2) := coeff_X_mul' _ _
    rw [coeff_A, map_sub, map_add, hx1, zero_add, h2, hneg, coeff_A_sq, coeff_Aneg_sq, a_succ]
    have hfac := coeff_factor n
    trans (2 - (-1 : ℤ) ^ n) * (conv2 a n : ℤ)
    · have : ((if Even (n + 1) then 3 else 1 : ℕ) : ℤ) * (conv2 a n : ℤ) =
          (2 - (-1 : ℤ) ^ n) * (conv2 a n : ℤ) := by
        rw [hfac]
      simpa using this
    · ring

example : a 0 = 1 := a_zero
example : a 1 = 1 := by
  rw [a_succ]
  simp [conv2, a_zero]

#print axioms a_odd_iff_mersenne
#print axioms mk_a_satisfiesHanna

end A368633
