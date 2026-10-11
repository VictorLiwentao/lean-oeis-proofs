/-
Copyright (c) 2026 Wentao Li.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Square/cube generating function for OEIS A368626

The sequence consists of the coefficients of the unique rational formal series
satisfying
$$A(x)=1+x(A(x)^2-A(-x)^2)/2+x(A(x)^3+A(-x)^3)/2.$$

*References:*
- [A368626](https://oeis.org/A368626), Paul D. Hanna, January 9, 2024.
-/

open Finset Nat

namespace A368626

/-- Convolution square. -/
def conv2 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), b k * b (n - k)

/-- Convolution cube. -/
def conv3 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), conv2 b k * b (n - k)

/-- Coefficient recurrence of OEIS A368626. -/
def a : ℕ → ℕ :=
  Nat.strongRec fun n ih =>
    if n = 0 then 1
    else
      let b : ℕ → ℕ := fun m => if h : m < n then ih m h else 0
      if Even n then conv2 b (n - 1) else conv3 b (n - 1)

lemma a_zero : a 0 = 1 := by
  rw [a, strongRec_eq]
  simp

lemma conv2_congr {b c : ℕ → ℕ} {n : ℕ} (h : ∀ k ≤ n, b k = c k) :
    conv2 b n = conv2 c n := by
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hnk : n - k ≤ n := Nat.sub_le _ _
  rw [h k hk', h (n - k) hnk]

lemma conv3_congr {b c : ℕ → ℕ} {n : ℕ} (h : ∀ k ≤ n, b k = c k) :
    conv3 b n = conv3 c n := by
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hnk : n - k ≤ n := Nat.sub_le _ _
  have hconv : conv2 b k = conv2 c k :=
    conv2_congr fun i hi => h i (le_trans hi hk')
  rw [hconv, h (n - k) hnk]

lemma a_of_pos {n : ℕ} (hn : 0 < n) :
    a n = if Even n then conv2 a (n - 1) else conv3 a (n - 1) := by
  have hne : n ≠ 0 := hn.ne'
  have hrec :
      a n =
        if Even n then
          conv2 (fun m => if h : m < n then a m else 0) (n - 1)
        else
          conv3 (fun m => if h : m < n then a m else 0) (n - 1) := by
    rw [a, strongRec_eq]
    simp [hne, a]
  rw [hrec]
  split_ifs with hE
  · refine conv2_congr fun k hk => ?_
    have hlt : k < n := Nat.lt_of_le_of_lt hk (Nat.sub_one_lt hne)
    simp [hlt]
  · refine conv3_congr fun k hk => ?_
    have hlt : k < n := Nat.lt_of_le_of_lt hk (Nat.sub_one_lt hne)
    simp [hlt]

lemma a_succ_even {n : ℕ} (h : Even (n + 1)) : a (n + 1) = conv2 a n := by
  simpa [h] using a_of_pos (n := n + 1) (Nat.succ_pos _)

lemma a_succ_odd {n : ℕ} (h : Odd (n + 1)) : a (n + 1) = conv3 a n := by
  have hne : ¬ Even (n + 1) := Nat.not_even_iff_odd.mpr h
  simpa [hne] using a_of_pos (n := n + 1) (Nat.succ_pos _)

lemma a_0 : a 0 = 1 := a_zero

lemma a_1 : a 1 = 1 := by
  rw [a_succ_odd (n := 0) odd_one]
  simp [conv3, conv2, a_zero]

lemma a_2 : a 2 = 2 := by
  rw [a_succ_even (n := 1) (by decide)]
  norm_num [conv3, conv2, sum_range_succ, a_zero, a_1]
lemma a_3 : a 3 = 9 := by
  rw [a_succ_odd (n := 2) (by decide)]
  norm_num [conv3, conv2, sum_range_succ, a_zero, a_1, a_2]
lemma a_4 : a 4 = 22 := by
  rw [a_succ_even (n := 3) (by decide)]
  norm_num [conv3, conv2, sum_range_succ, a_zero, a_1, a_2, a_3]
lemma a_5 : a 5 = 138 := by
  rw [a_succ_odd (n := 4) (by decide)]
  norm_num [conv3, conv2, sum_range_succ, a_zero, a_1, a_2, a_3, a_4]

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

lemma conv2_cast (b : ℕ → ℕ) (n : ℕ) :
    (conv2 b n : ZMod 2) =
      ∑ k ∈ range (n + 1), (b k : ZMod 2) * (b (n - k) : ZMod 2) := by
  simp [conv2, Nat.cast_sum, Nat.cast_mul]

lemma conv3_cast (b : ℕ → ℕ) (n : ℕ) :
    (conv3 b n : ZMod 2) =
      ∑ k ∈ range (n + 1), (conv2 b k : ZMod 2) * (b (n - k) : ZMod 2) := by
  simp [conv3, Nat.cast_sum, Nat.cast_mul]

lemma a_even_succ_even (m : ℕ) : Even (a (2 * m + 2)) := by
  have hE : Even (2 * m + 2) := by
    rw [show 2 * m + 2 = 2 * (m + 1) by omega]
    exact even_two_mul _
  have hcast : (a (2 * m + 2) : ZMod 2) = 0 := by
    rw [a_succ_even hE, conv2_cast]
    simpa using conv2_odd_eq_zero (fun k => (a k : ZMod 2)) m
  exact (ZMod.natCast_eq_zero_iff_even).1 hcast

lemma a_even_of_even {n : ℕ} (hE : Even n) (hpos : 0 < n) : Even (a n) := by
  obtain ⟨k, rfl⟩ := hE
  have hk : 0 < k := by omega
  have := a_even_succ_even (k - 1)
  convert this using 2
  omega

lemma sum_if_even (f : ℕ → ZMod 2) :
    ∀ m, ∑ k ∈ range (2 * m + 1), (if Even k then f k else 0) =
      ∑ t ∈ range (m + 1), f (2 * t) := by
  intro m
  induction m with
  | zero =>
    simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 by omega,
      sum_range_succ, sum_range_succ, ih]
    have hodd : ¬ Even (2 * m + 1) :=
      Nat.not_even_iff_odd.mpr (odd_two_mul_add_one m)
    have heven : Even (2 * m + 2) := by
      rw [show 2 * m + 2 = 2 * (m + 1) by omega]
      exact even_two_mul _
    simp [hodd, heven, sum_range_succ]
    rw [show 2 * m + 2 = 2 * (m + 1) by omega]

lemma conv2_even_eq_self (t : ℕ) :
    (conv2 a (2 * t) : ZMod 2) = (a t : ZMod 2) := by
  rw [conv2_cast, conv2_even_square (fun k => (a k : ZMod 2)) t, sq_eq_self_zmod2]

lemma conv3_even_eq (m : ℕ) :
    (conv3 a (2 * m) : ZMod 2) = (a m : ZMod 2) := by
  classical
  rw [conv3_cast]
  have hsplit :
      ∑ k ∈ range (2 * m + 1), (conv2 a k : ZMod 2) * (a (2 * m - k) : ZMod 2) =
        ∑ k ∈ range (2 * m + 1),
          if Even k then (conv2 a k : ZMod 2) * (a (2 * m - k) : ZMod 2) else 0 := by
    refine sum_congr rfl fun k hk => ?_
    split_ifs with hE
    · rfl
    · have hodd : Odd k := Nat.not_even_iff_odd.mp hE
      obtain ⟨t, rfl⟩ := hodd
      have : (conv2 a (2 * t + 1) : ZMod 2) = 0 := by
        rw [conv2_cast]
        simpa using conv2_odd_eq_zero (fun i => (a i : ZMod 2)) t
      simp [this]
  rw [hsplit, sum_if_even]
  have hterm (t : ℕ) (ht : t ∈ range (m + 1)) :
      (conv2 a (2 * t) : ZMod 2) * (a (2 * m - 2 * t) : ZMod 2) =
        if t = m then (a m : ZMod 2) else 0 := by
    have ht' : t ≤ m := Nat.lt_succ_iff.mp (mem_range.mp ht)
    rw [conv2_even_eq_self t]
    by_cases htm : t = m
    · subst htm
      simp [a_zero]
    · have hpos : 0 < 2 * m - 2 * t := by omega
      have hEv : Even (2 * m - 2 * t) := by
        rw [show 2 * m - 2 * t = 2 * (m - t) by omega]
        exact even_two_mul _
      have : (a (2 * m - 2 * t) : ZMod 2) = 0 :=
        (ZMod.natCast_eq_zero_iff_even).2 (a_even_of_even hEv hpos)
      simp [this, htm]
  have hm : m ∈ range (m + 1) := by simp
  have hsum :
      ∑ t ∈ range (m + 1),
          (conv2 a (2 * t) : ZMod 2) * (a (2 * m - 2 * t) : ZMod 2) =
        ∑ t ∈ range (m + 1), if t = m then (a m : ZMod 2) else 0 :=
    sum_congr rfl hterm
  rw [hsum, ← sum_erase_add _ _ hm]
  have hzero :
      ∑ t ∈ (range (m + 1)).erase m, (if t = m then (a m : ZMod 2) else 0) = 0 := by
    refine sum_eq_zero fun t ht => ?_
    have : t ≠ m := (mem_erase.mp ht).1
    simp [this]
  simp [hzero]

lemma a_odd_succ_iff {m : ℕ} : Odd (a (2 * m + 1)) ↔ Odd (a m) := by
  have hodd : Odd (2 * m + 1) := odd_two_mul_add_one m
  have hcast : (a (2 * m + 1) : ZMod 2) = (a m : ZMod 2) := by
    rw [a_succ_odd hodd, conv3_even_eq]
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

/-- OEIS A368626: `a(n)` is odd iff `n = 2^k - 1`. -/
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

open PowerSeries

/-- Substitution of $-x$ for $x$ in a formal power series. -/
noncomputable def atNeg (F : ℚ⟦X⟧) : ℚ⟦X⟧ := rescale (-1) F

/-- The right-hand side of Hanna's original equation, with division by $2$
interpreted in $\mathbb{Q}\llbracket x\rrbracket$. -/
noncomputable def hannaOperator (F : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  1 + X * (F ^ 2 - atNeg F ^ 2) * C (1 / 2) +
    X * (F ^ 3 + atNeg F ^ 3) * C (1 / 2)

/-- Hanna's original defining generating-function equation. -/
def IsHanna (F : ℚ⟦X⟧) : Prop := F = hannaOperator F

lemma coeff_atNeg_pow (F : ℚ⟦X⟧) (k n : ℕ) :
    coeff n (atNeg F ^ k) = (-1 : ℚ) ^ n * coeff n (F ^ k) := by
  rw [atNeg, ← map_pow, coeff_rescale]

lemma hanna_coeff_zero (F : ℚ⟦X⟧) : coeff 0 (hannaOperator F) = 1 := by
  simp [hannaOperator]

lemma hanna_coeff_succ (F : ℚ⟦X⟧) (n : ℕ) :
    coeff (n + 1) (hannaOperator F) =
      if Even (n + 1) then coeff n (F ^ 2) else coeff n (F ^ 3) := by
  simp only [hannaOperator, map_add, coeff_one, Nat.add_one_ne_zero, ite_false,
    zero_add, coeff_mul_C, coeff_succ_X_mul, map_sub, coeff_atNeg_pow]
  by_cases h : Even n
  · have hn : ¬ Even (n + 1) := fun h' => Nat.even_add_one.mp h' h
    rw [Even.neg_one_pow (α := ℚ) h, ite_eq_right hn]
    ring
  · have hn : Even (n + 1) := Nat.even_add_one.mpr h
    rw [Odd.neg_one_pow (α := ℚ) (Nat.not_even_iff_odd.mp h), ite_eq_left hn]
    ring

/-- Exact coefficient extraction of the original equation. -/
theorem isHanna_iff_coeff (F : ℚ⟦X⟧) :
    IsHanna F ↔ coeff 0 F = 1 ∧ ∀ n,
      coeff (n + 1) F =
        if Even (n + 1) then coeff n (F ^ 2) else coeff n (F ^ 3) := by
  constructor
  · intro h
    constructor
    · exact (congrArg (coeff 0) h).trans (hanna_coeff_zero F)
    · intro n
      exact (congrArg (coeff (n + 1)) h).trans (hanna_coeff_succ F n)
  · rintro ⟨h0, hs⟩
    apply PowerSeries.ext
    intro n
    cases n with
    | zero => rw [hanna_coeff_zero, h0]
    | succ n => rw [hanna_coeff_succ, hs]

lemma coeff_mul_range (F G : ℚ⟦X⟧) (n : ℕ) :
    coeff n (F * G) = ∑ k ∈ range (n + 1), coeff k F * coeff (n - k) G := by
  rw [coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i F * coeff j G) n

/-- The generating function of the historical natural-number recurrence. -/
noncomputable def recurrenceSeries : ℚ⟦X⟧ := mk fun n => (a n : ℚ)

lemma coeff_recurrenceSeries (n : ℕ) : coeff n recurrenceSeries = (a n : ℚ) :=
  coeff_mk _ _

lemma coeff_recurrenceSeries_sq (n : ℕ) :
    coeff n (recurrenceSeries ^ 2) = (conv2 a n : ℚ) := by
  rw [pow_two, coeff_mul_range]
  simp [coeff_recurrenceSeries, conv2, Nat.cast_sum, Nat.cast_mul]

lemma coeff_recurrenceSeries_cube (n : ℕ) :
    coeff n (recurrenceSeries ^ 3) = (conv3 a n : ℚ) := by
  rw [pow_succ, coeff_mul_range]
  simp [coeff_recurrenceSeries_sq, coeff_recurrenceSeries, conv3,
    Nat.cast_sum, Nat.cast_mul]

/-- The historical recurrence satisfies the original OEIS equation. -/
theorem recurrenceSeries_isHanna : IsHanna recurrenceSeries := by
  rw [isHanna_iff_coeff]
  constructor
  · simp [coeff_recurrenceSeries, a_zero]
  · intro n
    rw [coeff_recurrenceSeries, coeff_recurrenceSeries_sq, coeff_recurrenceSeries_cube]
    by_cases h : Even (n + 1)
    · rw [ite_eq_left h, a_succ_even h]
    · rw [ite_eq_right h, a_succ_odd (Nat.not_even_iff_odd.mp h)]

lemma coeff_pow_congr (F G : ℚ⟦X⟧) (k n : ℕ)
    (h : ∀ i ≤ n, coeff i F = coeff i G) : coeff n (F ^ k) = coeff n (G ^ k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, coeff_mul_range, coeff_mul_range]
    apply sum_congr rfl
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [ih i (fun j hj => h j (le_trans hj hin)), h (n - i) (Nat.sub_le _ _)]

/-- Every rational formal solution has the historical recurrence coefficients. -/
theorem coeff_eq_a_of_isHanna {F : ℚ⟦X⟧} (hF : IsHanna F) (n : ℕ) :
    coeff n F = (a n : ℚ) := by
  obtain ⟨h0, hs⟩ := (isHanna_iff_coeff F).mp hF
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa [a_zero] using h0
    | succ n =>
      have hagree : ∀ i ≤ n, coeff i F = coeff i recurrenceSeries := by
        intro i hi
        rw [coeff_recurrenceSeries]
        exact ih i (by omega)
      rw [hs, coeff_pow_congr F recurrenceSeries 2 n hagree,
        coeff_pow_congr F recurrenceSeries 3 n hagree,
        coeff_recurrenceSeries_sq, coeff_recurrenceSeries_cube]
      by_cases h : Even (n + 1)
      · rw [ite_eq_left h, a_succ_even h]
      · rw [ite_eq_right h, a_succ_odd (Nat.not_even_iff_odd.mp h)]

/-- The original equation has exactly one solution over the rational power series. -/
theorem isHanna_iff_eq_recurrenceSeries (F : ℚ⟦X⟧) :
    IsHanna F ↔ F = recurrenceSeries := by
  constructor
  · intro h
    apply PowerSeries.ext
    intro n
    rw [coeff_recurrenceSeries]
    exact coeff_eq_a_of_isHanna h n
  · rintro rfl
    exact recurrenceSeries_isHanna

/-- Existence and uniqueness for Hanna's original rational equation. -/
theorem exists_unique_isHanna : ∃! F : ℚ⟦X⟧, IsHanna F := by
  exact ⟨recurrenceSeries, recurrenceSeries_isHanna,
    fun F h => (isHanna_iff_eq_recurrenceSeries F).mp h⟩

/-- The original equation, with rational halves and substitution of $-x$. -/
theorem original_equation_unique : ∃! F : ℚ⟦X⟧,
    F = 1 + X * (F ^ 2 - rescale (-1) F ^ 2) * C (1 / 2) +
      X * (F ^ 3 + rescale (-1) F ^ 3) * C (1 / 2) := by
  exact exists_unique_isHanna

/-- The series is selected solely from the original OEIS equation. -/
noncomputable def oeisSeries : ℚ⟦X⟧ :=
  Classical.choose exists_unique_isHanna.exists

lemma oeisSeries_isHanna : IsHanna oeisSeries :=
  Classical.choose_spec exists_unique_isHanna.exists

lemma oeisSeries_eq_recurrenceSeries : oeisSeries = recurrenceSeries :=
  (isHanna_iff_eq_recurrenceSeries oeisSeries).mp oeisSeries_isHanna

/-- The natural coefficients of the equation-defined series. -/
noncomputable def oeisA (n : ℕ) : ℕ := (coeff n oeisSeries).num.toNat

lemma oeisA_eq_a (n : ℕ) : oeisA n = a n := by
  simp [oeisA, oeisSeries_eq_recurrenceSeries, coeff_recurrenceSeries]

lemma coeff_oeisSeries (n : ℕ) : coeff n oeisSeries = (oeisA n : ℚ) := by
  rw [oeisA_eq_a]
  exact coeff_eq_a_of_isHanna oeisSeries_isHanna n

lemma oeisA_0 : oeisA 0 = 1 := by rw [oeisA_eq_a, a_zero]
lemma oeisA_1 : oeisA 1 = 1 := by rw [oeisA_eq_a, a_1]
lemma oeisA_2 : oeisA 2 = 2 := by rw [oeisA_eq_a, a_2]
lemma oeisA_3 : oeisA 3 = 9 := by rw [oeisA_eq_a, a_3]
lemma oeisA_4 : oeisA 4 = 22 := by rw [oeisA_eq_a, a_4]
lemma oeisA_5 : oeisA 5 = 138 := by rw [oeisA_eq_a, a_5]

lemma isMersenne_iff (n : ℕ) : IsMersenne n ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩
    have hp : 0 < (2 : ℕ) ^ k := pow_pos (by decide) k
    exact ⟨k, by omega⟩

/-- OEIS: "a(n) is odd when n = 2^k - 1 for k >= 0 and even elsewhere."
This theorem concerns coefficients defined by the original equation. -/
theorem oeisA_odd_iff (n : ℕ) : Odd (oeisA n) ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  rw [oeisA_eq_a, a_odd_iff_mersenne, isMersenne_iff]

/-- The even-elsewhere clause of Hanna's conjecture. -/
theorem oeisA_even_iff (n : ℕ) : Even (oeisA n) ↔ ¬ ∃ k : ℕ, n = 2 ^ k - 1 := by
  rw [← Nat.not_odd_iff_even, oeisA_odd_iff]

/-- Every solution of the original equation has natural coefficients, and each
coefficient has the asserted parity, without integrality hypotheses. -/
theorem hanna_integrality_parity {F : ℚ⟦X⟧} (hF : IsHanna F) (n : ℕ) :
    ∃ m : ℕ, coeff n F = (m : ℚ) ∧
      (Odd m ↔ ∃ k : ℕ, n = 2 ^ k - 1) := by
  refine ⟨a n, coeff_eq_a_of_isHanna hF n, ?_⟩
  rw [a_odd_iff_mersenne, isMersenne_iff]


end A368626

namespace OeisA368626

/-- Coefficients of the square of a power series with coefficient sequence $b$. -/
def conv2 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), b k * b (n - k)

/-- Coefficients of the cube of a power series with coefficient sequence $b$. -/
def conv3 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), conv2 b k * b (n - k)

/-- Coefficients of $A(x)=1+x(A(x)^2-A(-x)^2)/2+x(A(x)^3+A(-x)^3)/2$. -/
def a : ℕ → ℕ :=
  Nat.strongRec fun n ih =>
    if n = 0 then 1
    else
      let b : ℕ → ℕ := fun m => if h : m < n then ih m h else 0
      if Even n then conv2 b (n - 1) else conv3 b (n - 1)

/-- The submitted recurrence is definitionally the proved recurrence. -/
theorem a_eq_proved (n : ℕ) : a n = A368626.a n := rfl

/-- Hanna's parity conjecture, including index zero. -/
theorem conjecture (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  rw [a_eq_proved]
  exact (A368626.a_odd_iff_mersenne n).trans (A368626.isMersenne_iff n)

end OeisA368626
