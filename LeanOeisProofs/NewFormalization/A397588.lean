/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
import Mathlib

/-!
# OEIS A397588

The ordinary generating function is defined by Hanna's equation

$$
A(x) = x + \bigl(x A(x)^2\bigr)'.
$$

OEIS also records Manyama's coefficient recurrence `a 1 = 1` and, for `n > 1`,
`a n = (n+1) ∑_{k=1}^{n-1} a k * a (n-k)`.

This file defines that recurrence (with `a 0 = 0`), proves it is equivalent to
Hanna's equation over `ℕ`, proves the OEIS parity comment: for `n ≥ 1`,
`a n` is odd if and only if `n` is a power of two, and proves the OEIS comment
that `a n` is divisible by 3 for `n > 1`. It also identifies the weighted
convolution with Manyama's formula and the product-rule expansion of Hanna's
equation.
-/

open Finset Nat PowerSeries

namespace A397588

/-! ## Recurrence sequence -/

/-- OEIS A397588 coefficients via Manyama's formula, extended by `a 0 = 0`. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    (n + 3) * ∑ k ∈ (Icc 1 (n + 1)).attach, a k.1 * a (n + 2 - k.1)
termination_by n => n
decreasing_by
  · exact Nat.lt_succ_of_le (mem_Icc.mp k.2).2
  · exact Nat.sub_lt (Nat.succ_pos _) (mem_Icc.mp k.2).1

lemma a_zero : a 0 = 0 := by simp only [a]

lemma a_one : a 1 = 1 := by simp only [a]

lemma a_succ_succ (n : ℕ) :
    a (n + 2) = (n + 3) * ∑ k ∈ Icc 1 (n + 1), a k * a (n + 2 - k) := by
  simp only [a]
  exact congrArg (fun t => (n + 3) * t)
    (sum_attach (Icc 1 (n + 1)) (fun k => a k * a (n + 2 - k)))

lemma a_of_gt_one {n : ℕ} (hn : 1 < n) :
    a n = (n + 1) * ∑ k ∈ Icc 1 (n - 1), a k * a (n - k) := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ n =>
      simp [a_succ_succ]

lemma a_two : a 2 = 3 := by
  rw [a_of_gt_one (by decide : 1 < 2)]
  simp [a_one]

lemma a_three : a 3 = 24 := by
  have hI : Icc (1 : ℕ) (3 - 1) = {1, 2} := by decide
  rw [a_of_gt_one (by decide : 1 < 3), hI]
  simp [a_one, a_two]

lemma a_four : a 4 = 285 := by
  have hI : Icc (1 : ℕ) (4 - 1) = {1, 2, 3} := by decide
  rw [a_of_gt_one (by decide : 1 < 4), hI]
  simp [a_one, a_two, a_three]

/-! ## Convolution pairing modulo 2 -/

lemma mem_Icc_midpoint {m : ℕ} (hm : 0 < m) :
    m ∈ Icc 1 (2 * m - 1) := by
  simp [mem_Icc]
  omega

lemma two_mul_sub_mem_Icc {m k : ℕ} (hm : 0 < m)
    (hk : k ∈ Icc 1 (2 * m - 1)) :
    2 * m - k ∈ Icc 1 (2 * m - 1) := by
  have hb := mem_Icc.mp hk
  have h2m : 1 ≤ 2 * m := by
    have : 1 ≤ m := hm
    omega
  have hk1 : k + 1 ≤ 2 * m := by omega
  refine mem_Icc.mpr ⟨?_, ?_⟩
  · exact le_sub_of_add_le (by omega)
  · exact Nat.sub_le_sub_left hb.1 _

lemma two_mul_sub_involutive {m k : ℕ}
    (hk : k ∈ Icc 1 (2 * m - 1)) :
    2 * m - (2 * m - k) = k := by
  have hb := mem_Icc.mp hk
  have : k ≤ 2 * m := le_trans hb.2 (Nat.sub_le _ _)
  exact Nat.sub_sub_self this

lemma two_mul_sub_mem_erase {m k : ℕ} (hm : 0 < m)
    (hk : k ∈ (Icc 1 (2 * m - 1)).erase m) :
    2 * m - k ∈ (Icc 1 (2 * m - 1)).erase m := by
  have hk' := mem_erase.mp hk
  refine mem_erase.mpr ⟨?_, two_mul_sub_mem_Icc hm hk'.2⟩
  intro h
  have := two_mul_sub_involutive hk'.2
  omega

/-- Off-diagonal convolution terms cancel in characteristic two. -/
lemma convolution_pairing (f : ℕ → ZMod 2) {m : ℕ} (hm : 0 < m) :
    ∑ k ∈ Icc 1 (2 * m - 1), f k * f (2 * m - k) = f m ^ 2 := by
  classical
  let s := Icc 1 (2 * m - 1)
  have hmem : m ∈ s := mem_Icc_midpoint hm
  have hcancel :
      ∑ k ∈ s.erase m, f k * f (2 * m - k) = 0 := by
    apply sum_involution (fun k _ => 2 * m - k)
    · intro k hk
      rw [two_mul_sub_involutive (mem_erase.mp hk).2, mul_comm (f (2 * m - k))]
      exact CharTwo.add_self_eq_zero _
    · intro k hk _
      have hk' := mem_erase.mp hk
      have hb := mem_Icc.mp hk'.2
      omega
    · intro k hk
      exact two_mul_sub_mem_erase hm hk
    · intro k hk
      exact two_mul_sub_involutive (mem_erase.mp hk).2
  rw [← sum_erase_add _ _ hmem, hcancel, zero_add]
  have : 2 * m - m = m := by omega
  simp [pow_two, this]

lemma sq_eq_self_zmod2 (x : ZMod 2) : x ^ 2 = x :=
  (by decide : ∀ y : ZMod 2, y ^ 2 = y) x

lemma odd_seq_two_mul {b : ℕ → ℕ}
    (hrec : ∀ n, 1 < n →
      b n = (n + 1) * ∑ k ∈ Icc 1 (n - 1), b k * b (n - k))
    {m : ℕ} (hm : 0 < m) :
    Odd (b (2 * m)) ↔ Odd (b m) := by
  have hnm : 1 < 2 * m := by omega
  have hcast : (b (2 * m) : ZMod 2) = (b m : ZMod 2) := by
    have hodd : ((2 * m + 1 : ℕ) : ZMod 2) = 1 := by
      rw [ZMod.natCast_eq_one_iff_odd]
      exact odd_two_mul_add_one m
    rw [hrec (2 * m) hnm, Nat.cast_mul, hodd, one_mul, Nat.cast_sum]
    simp_rw [Nat.cast_mul]
    rw [convolution_pairing (fun k => (b k : ZMod 2)) hm, sq_eq_self_zmod2]
  rw [← ZMod.natCast_eq_one_iff_odd, hcast, ZMod.natCast_eq_one_iff_odd]

lemma even_seq_of_odd_index {b : ℕ → ℕ}
    (hrec : ∀ n, 1 < n →
      b n = (n + 1) * ∑ k ∈ Icc 1 (n - 1), b k * b (n - k))
    {n : ℕ} (hn : 1 < n) (hodd : Odd n) :
    Even (b n) := by
  have hfactor : Even (n + 1) :=
    even_add_one.mpr (not_even_iff_odd.mpr hodd)
  rw [hrec n hn]
  exact hfactor.mul_right _

/-- Any natural sequence satisfying Manyama's recurrence is odd exactly
at positive powers of two. -/
theorem odd_of_manyama_recurrence {b : ℕ → ℕ}
    (h1 : b 1 = 1)
    (hrec : ∀ n, 1 < n →
      b n = (n + 1) * ∑ k ∈ Icc 1 (n - 1), b k * b (n - k)) :
    ∀ n, 0 < n → (Odd (b n) ↔ ∃ t : ℕ, n = 2 ^ t) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rcases eq_or_lt_of_le (show 1 ≤ n from hn) with h1n | hn1
    · subst n
      refine ⟨fun _ => ⟨0, by simp⟩, fun _ => ?_⟩
      rw [h1]
      exact odd_one
    obtain ⟨m, hnm | hnm⟩ := Nat.even_or_odd' n
    · subst n
      have hm : 0 < m := by omega
      rw [odd_seq_two_mul hrec hm, ih m (by omega) hm]
      constructor
      · rintro ⟨t, ht⟩
        exact ⟨t + 1, by rw [ht, pow_succ, mul_comm]⟩
      · rintro ⟨t, ht⟩
        cases t with
        | zero =>
          simp at ht
        | succ t =>
          refine ⟨t, ?_⟩
          omega
    · subst n
      have ho : Odd (2 * m + 1) := odd_two_mul_add_one m
      constructor
      · intro hb
        have : Even (b (2 * m + 1)) := even_seq_of_odd_index hrec hn1 ho
        exact (not_odd_iff_even.2 this hb).elim
      · rintro ⟨t, ht⟩
        cases t with
        | zero =>
          simp at ht
          omega
        | succ t =>
          have : Even (2 ^ (t + 1)) := even_pow.2 ⟨even_two, succ_ne_zero t⟩
          exact (not_odd_iff_even.2 (ht ▸ this) ho).elim

theorem a_odd_iff_pow_two {n : ℕ} (hn : 0 < n) :
    Odd (a n) ↔ ∃ t : ℕ, n = 2 ^ t :=
  odd_of_manyama_recurrence a_one (fun _ hn => a_of_gt_one hn) n hn

/-! ## Weighted convolution identity -/

lemma Icc_image_sub {n : ℕ} (hn : 1 < n) :
    (Icc 1 (n - 1)).image (fun k => n - k) = Icc 1 (n - 1) := by
  ext k
  simp only [mem_image, mem_Icc]
  constructor
  · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
    omega
  · intro ⟨hk1, hk2⟩
    refine ⟨n - k, ⟨?_, ?_⟩, ?_⟩ <;> omega

lemma sum_reflect {n : ℕ} (hn : 1 < n) (g : ℕ → ℕ) :
    ∑ k ∈ Icc 1 (n - 1), g (n - k) = ∑ k ∈ Icc 1 (n - 1), g k := by
  have hinj : Set.InjOn (fun k : ℕ => n - k) (Icc 1 (n - 1)) := by
    intro x hx y hy hxy
    have hx' : x ∈ Icc 1 (n - 1) := by simpa using hx
    have hy' : y ∈ Icc 1 (n - 1) := by simpa using hy
    have hxle : x ≤ n := by
      have := mem_Icc.mp hx'
      omega
    have hyle : y ≤ n := by
      have := mem_Icc.mp hy'
      omega
    calc
      x = n - (n - x) := (Nat.sub_sub_self hxle).symm
      _ = n - (n - y) := by
        have : n - x = n - y := hxy
        rw [this]
      _ = y := Nat.sub_sub_self hyle
  rw [← sum_image hinj, Icc_image_sub hn]

/-- The two OEIS recurrences agree for an arbitrary sequence. -/
lemma weighted_eq_manyama (b : ℕ → ℕ) {n : ℕ} (hn : 1 < n) :
    ∑ k ∈ Icc 1 (n - 1), (2 * k + 1) * b k * b (n - k) =
      (n + 1) * ∑ k ∈ Icc 1 (n - 1), b k * b (n - k) := by
  have hsym :
      ∑ k ∈ Icc 1 (n - 1), (2 * (n - k) + 1) * b k * b (n - k) =
        ∑ k ∈ Icc 1 (n - 1), (2 * k + 1) * b k * b (n - k) := by
    trans ∑ k ∈ Icc 1 (n - 1),
        (2 * (n - k) + 1) * b (n - k) * b (n - (n - k))
    · refine sum_congr rfl fun k hk => ?_
      have : n - (n - k) = k := by
        have := mem_Icc.mp hk
        omega
      rw [this]
      ac_rfl
    · exact sum_reflect hn fun k => (2 * k + 1) * b k * b (n - k)
  have hadd :
      ∑ k ∈ Icc 1 (n - 1), (2 * k + 1) * b k * b (n - k) +
          ∑ k ∈ Icc 1 (n - 1), (2 * (n - k) + 1) * b k * b (n - k) =
        ∑ k ∈ Icc 1 (n - 1), (2 * n + 2) * (b k * b (n - k)) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun k hk => ?_
    have hk' := mem_Icc.mp hk
    rw [mul_assoc (2 * k + 1), mul_assoc (2 * (n - k) + 1), ← add_mul]
    congr 1
    omega
  have h2 :
      2 * ∑ k ∈ Icc 1 (n - 1), (2 * k + 1) * b k * b (n - k) =
        (2 * n + 2) * ∑ k ∈ Icc 1 (n - 1), b k * b (n - k) := by
    rw [two_mul]
    nth_rw 2 [← hsym]
    rw [hadd, mul_sum]
  have hfac :
      (2 * n + 2) * ∑ k ∈ Icc 1 (n - 1), b k * b (n - k) =
        2 * ((n + 1) * ∑ k ∈ Icc 1 (n - 1), b k * b (n - k)) := by
    ring
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) (h2.trans hfac)

lemma a_weighted {n : ℕ} (hn : 1 < n) :
    a n = ∑ k ∈ Icc 1 (n - 1), (2 * k + 1) * a k * a (n - k) := by
  rw [a_of_gt_one hn, ← weighted_eq_manyama a hn]

/-! ## Divisibility by 3 for n > 1 -/

lemma manyama_two {b : ℕ → ℕ} (h1 : b 1 = 1)
    (hrec : ∀ n, 1 < n →
      b n = (n + 1) * ∑ k ∈ Icc 1 (n - 1), b k * b (n - k)) :
    b 2 = 3 := by
  have hI : Icc (1 : ℕ) (2 - 1) = {1} := by decide
  rw [hrec 2 (by decide : 1 < 2), hI]
  simp [h1]

/-- Any natural sequence satisfying Manyama's recurrence is divisible by 3
for every index greater than one. -/
theorem three_dvd_of_manyama_recurrence {b : ℕ → ℕ}
    (h1 : b 1 = 1)
    (hrec : ∀ n, 1 < n →
      b n = (n + 1) * ∑ k ∈ Icc 1 (n - 1), b k * b (n - k)) :
    ∀ n, 1 < n → 3 ∣ b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have h2le : 2 ≤ n := by omega
    rcases eq_or_lt_of_le h2le with h2 | hlt
    · subst n
      rw [manyama_two h1 hrec]
    · rw [hrec n hn]
      refine dvd_mul_of_dvd_right ?_ (n + 1)
      refine dvd_sum fun k hk => ?_
      have hk' := mem_Icc.mp hk
      by_cases hk1 : k = 1
      · subst k
        have hn1 : 1 < n - 1 := by omega
        exact dvd_mul_of_dvd_right (ih (n - 1) (by omega) hn1) _
      · have hkgt : 1 < k := by omega
        exact dvd_mul_of_dvd_left (ih k (by omega) hkgt) _

theorem a_three_dvd {n : ℕ} (hn : 1 < n) : 3 ∣ a n :=
  three_dvd_of_manyama_recurrence a_one (fun _ hn => a_of_gt_one hn) n hn

/-! ## Generating-function equation -/

/-- Hanna's defining equation `A = X + (X A^2)'` over `ℕ`. -/
def SatisfiesHanna (F : ℕ⟦X⟧) : Prop :=
  F = X + derivative ℕ (X * F ^ 2)

/-- Product rule: `(X F^2)' = F^2 + 2 X F F'`. -/
lemma derivative_X_mul_sq (F : ℕ⟦X⟧) :
    derivative ℕ (X * F ^ 2) = F ^ 2 + 2 * X * F * derivative ℕ F := by
  rw [Derivation.leibniz (derivative ℕ) (X : ℕ⟦X⟧) (F ^ 2)]
  simp only [smul_eq_mul, derivative_X, mul_one]
  rw [derivative_pow, pow_one]
  ring

/-- OEIS formula (2): the product-rule expansion of Hanna's equation. -/
lemma hanna_iff_product_rule {F : ℕ⟦X⟧} :
    SatisfiesHanna F ↔ F = X + F ^ 2 + 2 * X * F * derivative ℕ F := by
  unfold SatisfiesHanna
  rw [derivative_X_mul_sq, add_assoc]

lemma coeff_hanna_rhs (F : ℕ⟦X⟧) (n : ℕ) :
    coeff n (X + derivative ℕ (X * F ^ 2)) =
      coeff n X + (n + 1) * coeff n (F ^ 2) := by
  rw [map_add (coeff n), coeff_derivative, coeff_succ_X_mul, mul_comm]
  simp

lemma coeff_sq (F : ℕ⟦X⟧) (n : ℕ) :
    coeff n (F ^ 2) = ∑ k ∈ range (n + 1), coeff k F * coeff (n - k) F := by
  rw [pow_two, coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i F * coeff j F) n

lemma range_succ_eq_insert_endpoints {n : ℕ} (hn : 0 < n) :
    range (n + 1) = insert n (insert 0 (Icc 1 (n - 1))) := by
  ext k
  simp only [mem_range, mem_insert, mem_Icc]
  omega

lemma n_not_mem_insert_zero_Icc {n : ℕ} (hn : 0 < n) :
    n ∉ insert 0 (Icc 1 (n - 1)) := by
  simp [mem_Icc]
  omega

lemma zero_not_mem_Icc_one {n : ℕ} : 0 ∉ Icc 1 (n - 1) := by
  simp [mem_Icc]

lemma coeff_sq_of_const_zero {F : ℕ⟦X⟧} (h0 : coeff 0 F = 0)
    {n : ℕ} (hn : 0 < n) :
    coeff n (F ^ 2) = ∑ k ∈ Icc 1 (n - 1), coeff k F * coeff (n - k) F := by
  rw [coeff_sq, range_succ_eq_insert_endpoints hn,
    sum_insert (n_not_mem_insert_zero_Icc hn),
    sum_insert zero_not_mem_Icc_one]
  simp [h0]

lemma eq_zero_or_one_of_mul_self {c : ℕ} (h : c = c * c) : c = 0 ∨ c = 1 := by
  by_cases hc : c = 0
  · exact Or.inl hc
  · exact Or.inr ((Nat.mul_eq_left hc).1 h.symm)

lemma hanna_coeff_zero {F : ℕ⟦X⟧} (hF : SatisfiesHanna F) :
    coeff 0 F = 0 := by
  have hc : coeff 0 F = coeff 0 F * coeff 0 F := by
    have h := congrArg (coeff 0) hF
    have hsq : coeff 0 (F ^ 2) = coeff 0 F * coeff 0 F := by
      rw [coeff_sq]
      simp
    rw [coeff_hanna_rhs, coeff_X, hsq] at h
    simpa using h
  rcases eq_zero_or_one_of_mul_self hc with h0 | h1
  · exact h0
  · have h1c := congrArg (coeff 1) hF
    have hsq : coeff 1 (F ^ 2) = 2 * coeff 1 F := by
      rw [coeff_sq]
      have : range (1 + 1) = ({0, 1} : Finset ℕ) := by decide
      rw [this]
      simp [h1]
      ring
    rw [coeff_hanna_rhs, coeff_X, hsq] at h1c
    simp at h1c
    omega

lemma hanna_coeff_one {F : ℕ⟦X⟧} (hF : SatisfiesHanna F) :
    coeff 1 F = 1 := by
  have h0 := hanna_coeff_zero hF
  have h := congrArg (coeff 1) hF
  have hsq : coeff 1 (F ^ 2) = 0 := by
    rw [coeff_sq_of_const_zero h0 (by decide : 0 < 1)]
    simp
  rw [coeff_hanna_rhs, coeff_X, hsq] at h
  simpa using h

lemma hanna_coeff_of_gt_one {F : ℕ⟦X⟧} (hF : SatisfiesHanna F)
    {n : ℕ} (hn : 1 < n) :
    coeff n F =
      (n + 1) * ∑ k ∈ Icc 1 (n - 1), coeff k F * coeff (n - k) F := by
  have h0 := hanna_coeff_zero hF
  have h := congrArg (coeff n) hF
  have hx : coeff n X = 0 := by
    rw [coeff_X, ite_eq_right]
    exact ne_of_gt hn
  rw [coeff_hanna_rhs, hx, zero_add,
    coeff_sq_of_const_zero h0 (by omega : 0 < n)] at h
  exact h

/-- Hanna's equation uniquely determines the coefficient sequence `a`. -/
theorem hanna_coeff_eq_a {F : ℕ⟦X⟧} (hF : SatisfiesHanna F) (n : ℕ) :
    coeff n F = a n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · simp [hanna_coeff_zero hF, a_zero]
    · rcases n with _ | n
      · simp [hanna_coeff_one hF, a_one]
      · have hn : 1 < n + 2 := by omega
        rw [hanna_coeff_of_gt_one hF hn, a_of_gt_one hn]
        congr 1
        refine sum_congr rfl fun k hk => ?_
        have hk' := mem_Icc.mp hk
        rw [ih k (by omega), ih (n + 2 - k) (by omega)]

lemma a_coeff_sq_pos {n : ℕ} (hn : 0 < n) :
    coeff n ((mk a) ^ 2) = ∑ k ∈ Icc 1 (n - 1), a k * a (n - k) := by
  simpa [coeff_mk] using
    coeff_sq_of_const_zero (F := mk a) (by simp [a_zero]) hn

/-- The recurrence generating function satisfies Hanna's equation. -/
theorem mk_a_satisfiesHanna : SatisfiesHanna (mk a) := by
  unfold SatisfiesHanna
  refine PowerSeries.ext fun n => ?_
  rw [coeff_hanna_rhs, coeff_mk]
  rcases n with _ | n
  · simp [a_zero, coeff_X, coeff_sq]
  · rcases n with _ | n
    · have hsq : coeff 1 ((mk a) ^ 2) = 0 :=
        a_coeff_sq_pos (by decide : (0 : ℕ) < 1)
      simp [a_one, coeff_X, hsq]
    · have hn : 1 < n + 2 := by omega
      have hx : coeff (n + 2) X = 0 := by
        rw [coeff_X, ite_eq_right]
        exact ne_of_gt hn
      rw [a_of_gt_one hn, a_coeff_sq_pos (by omega : 0 < n + 2), hx, zero_add]

/-- The OEIS generating-function definition has the stated parity. -/
theorem hanna_odd_iff_pow_two {F : ℕ⟦X⟧} (hF : SatisfiesHanna F)
    {n : ℕ} (hn : 0 < n) :
    Odd (coeff n F) ↔ ∃ t : ℕ, n = 2 ^ t := by
  simpa [hanna_coeff_eq_a hF] using a_odd_iff_pow_two hn

/-- The OEIS comment that `a(n)` is divisible by 3 for `n > 1`. -/
theorem hanna_three_dvd {F : ℕ⟦X⟧} (hF : SatisfiesHanna F)
    {n : ℕ} (hn : 1 < n) : 3 ∣ coeff n F := by
  simpa [hanna_coeff_eq_a hF] using a_three_dvd hn

#print axioms a_odd_iff_pow_two
#print axioms hanna_odd_iff_pow_two
#print axioms mk_a_satisfiesHanna
#print axioms hanna_coeff_eq_a
#print axioms a_three_dvd
#print axioms hanna_three_dvd
#print axioms weighted_eq_manyama
#print axioms hanna_iff_product_rule

end A397588
