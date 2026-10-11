/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic

/-!
# OEIS A368634

OEIS name: expansion of the g.f. `A(x)` satisfying
`A(x) = 1 + x*(3*A(x)^2 - A(-x)^2)/2`.

Comment (Hanna): **Conjecture**: `a(n)` is odd when `n = 2^k - 1` for
`k ≥ 0` and even elsewhere.

Coefficient extraction of the functional equation yields the recurrence
`a 0 = 1` and, for `n ≥ 0`,

`a (n+1) = (if Even (n+1) then 2 else 1) * ∑_{k=0}^n a k * a (n-k)`.

The equation is interpreted in $\mathbb{Q}[[x]]$. Its unique solution has
natural-number coefficients given by the recurrence.

*References:*
- [A368634](https://oeis.org/A368634)
-/

open Finset Nat PowerSeries

namespace A368634

/-- Convolution square. -/
def conv2 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), b k * b (n - k)

/-- Coefficient recurrence of OEIS A368634. -/
def a : ℕ → ℕ :=
  Nat.strongRec fun n ih =>
    if n = 0 then 1
    else
      let b : ℕ → ℕ := fun m => if h : m < n then ih m h else 0
      (if Even n then 2 else 1) * conv2 b (n - 1)

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
    a n = (if Even n then 2 else 1) * conv2 a (n - 1) := by
  have hne : n ≠ 0 := hn.ne'
  have hrec :
      a n =
        (if Even n then 2 else 1) *
          conv2 (fun m => if h : m < n then a m else 0) (n - 1) := by
    rw [a, strongRec_eq]
    simp [hne, a]
  rw [hrec]
  refine congrArg (fun t => (if Even n then 2 else 1) * t) ?_
  refine conv2_congr fun k hk => ?_
  have hlt : k < n := Nat.lt_of_le_of_lt hk (Nat.sub_one_lt hne)
  simp [hlt]

lemma a_succ (n : ℕ) :
    a (n + 1) = (if Even (n + 1) then 2 else 1) * conv2 a n :=
  a_of_pos (Nat.succ_pos _)

theorem a_1 : a 1 = 1 := by
  rw [show 1 = 0 + 1 from rfl, a_succ]
  norm_num [conv2, a_zero]

theorem a_2 : a 2 = 4 := by
  rw [show 2 = 1 + 1 from rfl, a_succ]
  norm_num [conv2, Finset.sum_range_succ, a_zero, a_1]

theorem a_3 : a 3 = 9 := by
  rw [show 3 = 2 + 1 from rfl, a_succ]
  norm_num [conv2, Finset.sum_range_succ, a_zero, a_1, a_2]

theorem a_4 : a 4 = 52 := by
  rw [show 4 = 3 + 1 from rfl, a_succ]
  norm_num [conv2, Finset.sum_range_succ, a_zero, a_1, a_2, a_3]

theorem a_5 : a 5 = 138 := by
  rw [show 5 = 4 + 1 from rfl, a_succ]
  norm_num [conv2, Finset.sum_range_succ, a_zero, a_1, a_2, a_3, a_4]

lemma a_succ_mod2_odd (n : ℕ) (h : Odd (n + 1)) :
    (a (n + 1) : ZMod 2) =
      ∑ k ∈ range (n + 1), (a k : ZMod 2) * (a (n - k) : ZMod 2) := by
  have hne : ¬ Even (n + 1) := Nat.not_even_iff_odd.mpr h
  rw [a_succ, conv2, Nat.cast_mul, Nat.cast_sum]
  simp_rw [Nat.cast_mul]
  simp [hne]

lemma a_even_succ_even (m : ℕ) : Even (a (2 * m + 2)) := by
  have hE : Even (2 * m + 2) := by
    rw [show 2 * m + 2 = 2 * (m + 1) by omega]
    exact even_two_mul _
  rw [a_of_pos (by omega : 0 < 2 * m + 2)]
  simp [hE]

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

lemma a_odd_succ_iff {m : ℕ} : Odd (a (2 * m + 1)) ↔ Odd (a m) := by
  have hodd : Odd (2 * m + 1) := odd_two_mul_add_one m
  have hcast : (a (2 * m + 1) : ZMod 2) = (a m : ZMod 2) := by
    rw [a_succ_mod2_odd (2 * m) hodd,
      conv2_even_square (fun k => (a k : ZMod 2)) m, sq_eq_self_zmod2]
  rw [← ZMod.natCast_eq_one_iff_odd, hcast, ZMod.natCast_eq_one_iff_odd]

/-- `n` is of the form `2^k - 1`. -/
def IsMersenne (n : ℕ) : Prop := ∃ k : ℕ, n + 1 = 2 ^ k

lemma isMersenne_iff_eq_pow_sub_one (n : ℕ) :
    IsMersenne n ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩
    have hpos : 0 < (2 : ℕ) ^ k := pow_pos (by decide) k
    exact ⟨k, by omega⟩

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

/-- OEIS A368634: `a(n)` is odd iff `n = 2^k - 1`. -/
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


/-! ## The original generating-function definition -/

/-- Hanna's defining equation $F(x)=1+x(3F(x)^2-F(-x)^2)/2$ over
$\mathbb{Q}[[x]]$. `rescale (-1)` is the substitution $x\mapsto -x$. -/
def SatisfiesHanna (F : ℚ⟦X⟧) : Prop :=
  F = 1 + X * ((1 / 2 : ℚ) • ((3 : ℚ) • F ^ 2 - (rescale (-1) F) ^ 2))

lemma rescale_neg_one_eq_subst (F : ℚ⟦X⟧) :
    rescale (-1) F = subst (-X) F := by
  simpa using rescale_eq_subst (-1 : ℚ) F

/-- The rescaling formulation is exactly substitution of $-x$ in the original equation. -/
theorem satisfiesHanna_iff_subst (F : ℚ⟦X⟧) :
    SatisfiesHanna F ↔
      F = 1 + X * ((1 / 2 : ℚ) • ((3 : ℚ) • F ^ 2 - (subst (-X) F) ^ 2)) := by
  simp only [SatisfiesHanna, rescale_neg_one_eq_subst]

/-- The generating function constructed from the natural-number recurrence. -/
noncomputable def recurrenceSeries : ℚ⟦X⟧ := mk fun n => (a n : ℚ)

lemma coeff_recurrenceSeries (n : ℕ) : coeff n recurrenceSeries = (a n : ℚ) := by
  simp [recurrenceSeries, coeff_mk]

lemma coeff_sq (F : ℚ⟦X⟧) (n : ℕ) :
    coeff n (F ^ 2) = ∑ k ∈ range (n + 1), coeff k F * coeff (n - k) F := by
  rw [pow_two, coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i F * coeff j F) n

lemma coeff_neg_sq (F : ℚ⟦X⟧) (n : ℕ) :
    coeff n ((rescale (-1) F) ^ 2) = (-1 : ℚ) ^ n * coeff n (F ^ 2) := by
  rw [← map_pow, coeff_rescale]

lemma coeff_factor (n : ℕ) :
    (1 / 2 : ℚ) * (3 - (-1 : ℚ) ^ n) = if Even (n + 1) then 2 else 1 := by
  by_cases h : Even n
  · have hnp : ¬ Even (n + 1) := fun h' => Nat.even_add_one.mp h' h
    rw [h.neg_one_pow]
    norm_num [hnp]
  · have hnp : Even (n + 1) := Nat.even_add_one.mpr h
    rw [(Nat.not_even_iff_odd.mp h).neg_one_pow]
    norm_num [hnp]

lemma coeff_hanna_rhs_succ (F : ℚ⟦X⟧) (n : ℕ) :
    coeff (n + 1) (1 + X * ((1 / 2 : ℚ) •
      ((3 : ℚ) • F ^ 2 - (rescale (-1) F) ^ 2))) =
      (if Even (n + 1) then 2 else 1 : ℚ) *
        ∑ k ∈ range (n + 1), coeff k F * coeff (n - k) F := by
  simp only [map_add, coeff_one, Nat.add_one_ne_zero, ite_false, zero_add,
    coeff_succ_X_mul, coeff_smul, map_sub, smul_eq_mul, coeff_neg_sq]
  rw [← coeff_sq, ← coeff_factor]
  ring

/-- The functional equation is equivalent to its complete coefficient recurrence. -/
theorem satisfiesHanna_iff_coeff (F : ℚ⟦X⟧) :
    SatisfiesHanna F ↔ coeff 0 F = 1 ∧ ∀ n : ℕ,
      coeff (n + 1) F = (if Even (n + 1) then 2 else 1 : ℚ) *
        ∑ k ∈ range (n + 1), coeff k F * coeff (n - k) F := by
  constructor
  · intro h
    constructor
    · have h0 := congrArg (coeff 0) h
      simpa using h0
    · intro n
      exact (congrArg (coeff (n + 1)) h).trans (coeff_hanna_rhs_succ F n)
  · rintro ⟨h0, hs⟩
    refine PowerSeries.ext fun n => ?_
    cases n with
    | zero => simpa using h0
    | succ n => exact (hs n).trans (coeff_hanna_rhs_succ F n).symm

/-- The old recurrence constructs a solution of the original OEIS equation. -/
theorem recurrenceSeries_satisfiesHanna : SatisfiesHanna recurrenceSeries := by
  rw [satisfiesHanna_iff_coeff]
  constructor
  · simp [coeff_recurrenceSeries, a_zero]
  · intro n
    simp only [coeff_recurrenceSeries, a_succ, conv2, Nat.cast_mul, Nat.cast_sum]
    split_ifs <;> norm_num

/-- Every rational solution has exactly the coefficients of the old recurrence. -/
theorem coeff_eq_a_of_satisfiesHanna {F : ℚ⟦X⟧} (hF : SatisfiesHanna F) (n : ℕ) :
    coeff n F = (a n : ℚ) := by
  obtain ⟨h0, hs⟩ := (satisfiesHanna_iff_coeff F).mp hF
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa [a_zero] using h0
    | succ n =>
      rw [hs n]
      have hsum :
          ∑ k ∈ range (n + 1), coeff k F * coeff (n - k) F = (conv2 a n : ℚ) := by
        simp only [conv2, Nat.cast_sum, Nat.cast_mul]
        refine sum_congr rfl fun k hk => ?_
        have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
        rw [ih k (by omega), ih (n - k) (by omega)]
      rw [hsum, a_succ, Nat.cast_mul]
      split_ifs <;> norm_num

/-- The equation has a unique solution over the rationals; integrality is a conclusion. -/
theorem satisfiesHanna_iff_eq_recurrenceSeries (F : ℚ⟦X⟧) :
    SatisfiesHanna F ↔ F = recurrenceSeries := by
  constructor
  · intro hF
    exact PowerSeries.ext fun n =>
      (coeff_eq_a_of_satisfiesHanna hF n).trans (coeff_recurrenceSeries n).symm
  · rintro rfl
    exact recurrenceSeries_satisfiesHanna

theorem existsUnique_satisfiesHanna : ∃! F : ℚ⟦X⟧, SatisfiesHanna F := by
  exact ⟨recurrenceSeries, recurrenceSeries_satisfiesHanna,
    fun F hF => (satisfiesHanna_iff_eq_recurrenceSeries F).mp hF⟩

/-- The sequence defined by the unique solution of the OEIS generating-function equation. -/
noncomputable def oeisSeries : ℚ⟦X⟧ := existsUnique_satisfiesHanna.exists.choose

theorem oeisSeries_satisfiesHanna : SatisfiesHanna oeisSeries :=
  existsUnique_satisfiesHanna.exists.choose_spec

/-- Every coefficient of the OEIS-defined series is a natural number. -/
theorem oeisSeries_coeff_eq_a (n : ℕ) : coeff n oeisSeries = (a n : ℚ) :=
  coeff_eq_a_of_satisfiesHanna oeisSeries_satisfiesHanna n

/-- Natural-number coefficients of the OEIS-defined series. -/
noncomputable def oeisCoeff (n : ℕ) : ℕ :=
  (show ∃ m : ℕ, coeff n oeisSeries = (m : ℚ) from ⟨a n, oeisSeries_coeff_eq_a n⟩).choose

theorem cast_oeisCoeff (n : ℕ) : (oeisCoeff n : ℚ) = coeff n oeisSeries := by
  exact (Exists.choose_spec (show ∃ m : ℕ, coeff n oeisSeries = (m : ℚ) from
    ⟨a n, oeisSeries_coeff_eq_a n⟩)).symm

theorem oeisCoeff_eq_a (n : ℕ) : oeisCoeff n = a n := by
  exact_mod_cast (cast_oeisCoeff n).trans (oeisSeries_coeff_eq_a n)

theorem oeisCoeff_initial :
    oeisCoeff 0 = 1 ∧ oeisCoeff 1 = 1 ∧ oeisCoeff 2 = 4 ∧
      oeisCoeff 3 = 9 ∧ oeisCoeff 4 = 52 ∧ oeisCoeff 5 = 138 := by
  simp [oeisCoeff_eq_a, a_zero, a_1, a_2, a_3, a_4, a_5]

/-- The coefficients of the series defined by the original OEIS equation are odd
exactly at $n=2^k-1$, including $n=0$. -/
theorem oeisCoeff_odd_iff_mersenne (n : ℕ) :
    Odd (oeisCoeff n) ↔ ∃ k : ℕ, n + 1 = 2 ^ k := by
  rw [oeisCoeff_eq_a]
  exact a_odd_iff_mersenne n

/-- Hanna's conjecture for the sequence defined by the original generating-function equation:
$a(n)$ is odd when $n=2^k-1$ for $k\geq0$ and even elsewhere. -/
theorem oeis_parity (n : ℕ) :
    (Odd (oeisCoeff n) ↔ ∃ k : ℕ, n = 2 ^ k - 1) ∧
      (Even (oeisCoeff n) ↔ ¬ ∃ k : ℕ, n = 2 ^ k - 1) := by
  have ho : Odd (oeisCoeff n) ↔ ∃ k : ℕ, n = 2 ^ k - 1 :=
    (oeisCoeff_odd_iff_mersenne n).trans (isMersenne_iff_eq_pow_sub_one n)
  exact ⟨ho, by simpa only [not_odd_iff_even] using not_congr ho⟩

/-- Every solution of the original equation has natural-number coefficients with
Hanna's parity pattern. No integrality or recurrence hypothesis is assumed. -/
theorem hanna_parity {F : ℚ⟦X⟧} (hF : SatisfiesHanna F) (n : ℕ) :
    ∃ m : ℕ, coeff n F = (m : ℚ) ∧ (Odd m ↔ ∃ k : ℕ, n + 1 = 2 ^ k) := by
  exact ⟨a n, coeff_eq_a_of_satisfiesHanna hF n, a_odd_iff_mersenne n⟩

/-- Every rational series satisfying the source equation, written using literal
substitution of $-x$, has natural coefficients and exactly Hanna's parity pattern. -/
theorem original_equation_parity {F : ℚ⟦X⟧}
    (hF : F = 1 + X * ((1 / 2 : ℚ) • ((3 : ℚ) • F ^ 2 - (subst (-X) F) ^ 2)))
    (n : ℕ) :
    ∃ m : ℕ, coeff n F = (m : ℚ) ∧
      (Odd m ↔ ∃ k : ℕ, n = 2 ^ k - 1) ∧
      (Even m ↔ ¬ ∃ k : ℕ, n = 2 ^ k - 1) := by
  have h := (satisfiesHanna_iff_subst F).mpr hF
  refine ⟨oeisCoeff n, ?_, oeis_parity n⟩
  rw [oeisCoeff_eq_a]
  exact coeff_eq_a_of_satisfiesHanna h n


end A368634

namespace OeisA368634

/-- Coefficients of the square of a power series with coefficient sequence $b$. -/
def conv2 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), b k * b (n - k)

/-- Coefficients of $A(x)=1+x(3A(x)^2-A(-x)^2)/2$. -/
def a : ℕ → ℕ :=
  Nat.strongRec fun n ih =>
    if n = 0 then 1
    else
      let b : ℕ → ℕ := fun m => if h : m < n then ih m h else 0
      (if Even n then 2 else 1) * conv2 b (n - 1)

/-- The submitted recurrence is definitionally the proved recurrence. -/
theorem a_eq_proved (n : ℕ) : a n = A368634.a n := rfl

/-- Hanna's parity conjecture, including index zero. -/
theorem conjecture (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  rw [a_eq_proved]
  exact (A368634.a_odd_iff_mersenne n).trans (A368634.isMersenne_iff_eq_pow_sub_one n)

end OeisA368634
