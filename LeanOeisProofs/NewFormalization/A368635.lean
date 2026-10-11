/-
Copyright (c) 2026 Wentao Li.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Cast.CharZero

/-!
# The generating function $A(x)=1+3xA(x)^2-2xA(-x)^2$

*References:*
- [OEIS A368635](https://oeis.org/A368635), Paul D. Hanna, January 12, 2024.
-/

open Finset Nat PowerSeries

namespace A368635Proof
namespace Recurrence

/-- Convolution square. -/
def conv2 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), b k * b (n - k)

/-- Coefficient recurrence of OEIS A368635. -/
def a : ℕ → ℕ :=
  Nat.strongRec fun n ih =>
    if n = 0 then 1
    else
      let b : ℕ → ℕ := fun m => if h : m < n then ih m h else 0
      (if Even n then 5 else 1) * conv2 b (n - 1)

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
    a n = (if Even n then 5 else 1) * conv2 a (n - 1) := by
  have hne : n ≠ 0 := hn.ne'
  have hrec :
      a n =
        (if Even n then 5 else 1) *
          conv2 (fun m => if h : m < n then a m else 0) (n - 1) := by
    rw [a, strongRec_eq]
    simp [hne, a]
  rw [hrec]
  refine congrArg (fun t => (if Even n then 5 else 1) * t) ?_
  refine conv2_congr fun k hk => ?_
  have hlt : k < n := Nat.lt_of_le_of_lt hk (Nat.sub_one_lt hne)
  simp [hlt]

lemma a_succ (n : ℕ) :
    a (n + 1) = (if Even (n + 1) then 5 else 1) * conv2 a n :=
  a_of_pos (Nat.succ_pos _)

lemma a_succ_mod2 (n : ℕ) :
    (a (n + 1) : ZMod 2) =
      ∑ k ∈ range (n + 1), (a k : ZMod 2) * (a (n - k) : ZMod 2) := by
  have h3 : ((5 : ℕ) : ZMod 2) = 1 := by decide
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

/-- OEIS A368635: `a(n)` is odd iff `n = 2^k - 1`. -/
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


end Recurrence

section Bridge

variable {R : Type*} [CommRing R]

/-- The original defining equation, with `evalNegHom F` representing $F(-x)$. -/
def IsOEIS (F : PowerSeries R) : Prop :=
  F = 1 + 3 * X * F ^ 2 - 2 * X * (evalNegHom F) ^ 2

/-- The $n$th coefficient of the defining equation's right side. -/
lemma rhs_coeff_succ (F : PowerSeries R) (n : ℕ) :
    coeff (n + 1) (1 + 3 * X * F ^ 2 - 2 * X * (evalNegHom F) ^ 2) =
      (3 - 2 * (-1 : R) ^ n) *
        ∑ k ∈ range (n + 1), coeff k F * coeff (n - k) F := by
  have h3 : (3 : PowerSeries R) = C (3 : R) := (map_natCast C 3).symm
  have h2 : (2 : PowerSeries R) = C (2 : R) := (map_natCast C 2).symm
  rw [h3, h2]
  simp only [mul_assoc, map_sub, map_add, coeff_one, Nat.add_one_ne_zero,
    ite_false, zero_add, coeff_C_mul, coeff_succ_X_mul]
  rw [← map_pow, evalNegHom, coeff_rescale]
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  ring

lemma rhs_coeff_zero (F : PowerSeries R) :
    coeff 0 (1 + 3 * X * F ^ 2 - 2 * X * (evalNegHom F) ^ 2) = 1 := by
  have h3 : (3 : PowerSeries R) = C (3 : R) := (map_natCast C 3).symm
  have h2 : (2 : PowerSeries R) = C (2 : R) := (map_natCast C 2).symm
  rw [h3, h2]
  simp [mul_assoc]

/-- Coefficient extraction is equivalent to the formal-series equation. -/
theorem is_oeis_iff_coeff (F : PowerSeries R) :
    IsOEIS F ↔ coeff 0 F = 1 ∧ ∀ n : ℕ,
      coeff (n + 1) F = (3 - 2 * (-1 : R) ^ n) *
        ∑ k ∈ range (n + 1), coeff k F * coeff (n - k) F := by
  constructor
  · intro h
    constructor
    · rw [h, rhs_coeff_zero]
    · intro n
      simpa only [rhs_coeff_succ] using congrArg (coeff (n + 1)) h
  · rintro ⟨h0, hs⟩
    apply PowerSeries.ext
    intro n
    cases n with
    | zero => simpa only [rhs_coeff_zero] using h0
    | succ n => simpa only [rhs_coeff_succ] using hs n

lemma multiplier_eq (n : ℕ) :
    (3 - 2 * (-1 : R) ^ n) = ((if Even (n + 1) then 5 else 1 : ℕ) : R) := by
  simp only [Nat.even_add_one]
  by_cases hn : Even n
  · simp only [hn.neg_one_pow, hn, not_true_eq_false, ite_false, Nat.cast_one]
    ring
  · have ho : Odd n := not_even_iff_odd.mp hn
    simp only [ho.neg_one_pow, hn, not_false_eq_true, ite_true]
    ring

/-- The generating series of the historical natural-number recurrence. -/
noncomputable def recurrenceSeries (R : Type*) [CommRing R] : PowerSeries R :=
  PowerSeries.mk fun n => (Recurrence.a n : R)

theorem recurrence_series_is_oeis : IsOEIS (recurrenceSeries R) := by
  rw [is_oeis_iff_coeff]
  constructor
  · simp [recurrenceSeries, Recurrence.a_zero]
  · intro n
    simp only [recurrenceSeries, coeff_mk, multiplier_eq]
    rw [Recurrence.a_succ, Nat.cast_mul, Recurrence.conv2, Nat.cast_sum]
    simp only [Nat.cast_mul]

/-- Every solution of the original equation has the historical recurrence's coefficients. -/
theorem coeff_eq_recurrence {F : PowerSeries R} (hF : IsOEIS F) (n : ℕ) :
    coeff n F = (Recurrence.a n : R) := by
  obtain ⟨h0, hs⟩ := (is_oeis_iff_coeff F).mp hF
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa [Recurrence.a_zero] using h0
    | succ n =>
      rw [hs n, multiplier_eq, Recurrence.a_succ, Nat.cast_mul,
        Recurrence.conv2, Nat.cast_sum]
      congr 1
      apply sum_congr rfl
      intro k hk
      have hk' : k < n + 1 := mem_range.mp hk
      rw [ih k hk', ih (n - k) (by omega), Nat.cast_mul]

/-- The original equation has exactly one solution over every commutative ring. -/
theorem exists_unique_series (R : Type*) [CommRing R] : ∃! F : PowerSeries R, IsOEIS F := by
  refine ⟨recurrenceSeries R, recurrence_series_is_oeis, ?_⟩
  intro F hF
  apply PowerSeries.ext
  intro n
  simpa only [recurrenceSeries, coeff_mk] using coeff_eq_recurrence hF n

end Bridge

/-- Formula (1.b) is the original equation with rational half coefficients. -/
theorem is_oeis_iff_half_form (F : PowerSeries ℚ) :
    IsOEIS F ↔ F = 1 + C (1 / 2 : ℚ) * X * (F ^ 2 + (evalNegHom F) ^ 2) +
      C (5 / 2 : ℚ) * X * (F ^ 2 - (evalNegHom F) ^ 2) := by
  have hs : C (1 / 2 : ℚ) + C (5 / 2 : ℚ) = (3 : PowerSeries ℚ) := by
    rw [← map_add]
    norm_num
    exact map_natCast C 3
  have hd : C (1 / 2 : ℚ) - C (5 / 2 : ℚ) = (-2 : PowerSeries ℚ) := by
    rw [← map_sub]
    norm_num
    exact map_natCast C 2
  have hr : 1 + C (1 / 2 : ℚ) * X * (F ^ 2 + (evalNegHom F) ^ 2) +
      C (5 / 2 : ℚ) * X * (F ^ 2 - (evalNegHom F) ^ 2) =
      1 + 3 * X * F ^ 2 - 2 * X * (evalNegHom F) ^ 2 := by
    calc
      _ = 1 + (C (1 / 2 : ℚ) + C (5 / 2 : ℚ)) * X * F ^ 2 +
          (C (1 / 2 : ℚ) - C (5 / 2 : ℚ)) * X * (evalNegHom F) ^ 2 := by ring
      _ = _ := by rw [hs, hd]; ring
  rw [hr]
  rfl

/-- The rational generating series of a natural-number sequence. -/
noncomputable def seriesOf (b : ℕ → ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (b n : ℚ)

/-- A unique natural-number sequence satisfies the original OEIS equation. -/
theorem exists_unique_sequence : ∃! b : ℕ → ℕ, IsOEIS (seriesOf b) := by
  refine ⟨Recurrence.a, recurrence_series_is_oeis, ?_⟩
  intro b hb
  funext n
  have hn := coeff_eq_recurrence hb n
  exact Nat.cast_injective (by simpa only [seriesOf, coeff_mk] using hn)

/-- The sequence defined by the original generating-function equation. -/
noncomputable def a : ℕ → ℕ := Classical.choose exists_unique_sequence

theorem a_is_oeis : IsOEIS (seriesOf a) :=
  (Classical.choose_spec exists_unique_sequence).1

theorem a_eq_recurrence : a = Recurrence.a :=
  ((Classical.choose_spec exists_unique_sequence).2 Recurrence.a recurrence_series_is_oeis).symm

theorem a_0 : a 0 = 1 := by
  rw [a_eq_recurrence]
  exact Recurrence.a_zero

theorem a_1 : a 1 = 1 := by
  rw [a_eq_recurrence, Recurrence.a_succ 0, ← a_eq_recurrence]
  norm_num [Recurrence.conv2, sum_range_succ, a_0]

theorem a_2 : a 2 = 10 := by
  rw [a_eq_recurrence, Recurrence.a_succ 1, ← a_eq_recurrence]
  norm_num [Recurrence.conv2, sum_range_succ, a_0, a_1]

theorem a_3 : a 3 = 21 := by
  rw [a_eq_recurrence, Recurrence.a_succ 2, ← a_eq_recurrence]
  norm_num [Recurrence.conv2, sum_range_succ, a_0, a_1, a_2]
  decide

theorem a_4 : a 4 = 310 := by
  rw [a_eq_recurrence, Recurrence.a_succ 3, ← a_eq_recurrence]
  norm_num [Recurrence.conv2, sum_range_succ, a_0, a_1, a_2, a_3]
  decide

theorem a_5 : a 5 = 762 := by
  rw [a_eq_recurrence, Recurrence.a_succ 4, ← a_eq_recurrence]
  norm_num [Recurrence.conv2, sum_range_succ, a_0, a_1, a_2, a_3, a_4]
  decide

/-- Every rational formal-series solution has the natural coefficients of $a$. -/
theorem coeff_eq_a {F : PowerSeries ℚ} (hF : IsOEIS F) (n : ℕ) :
    coeff n F = (a n : ℚ) := by
  rw [a_eq_recurrence]
  exact coeff_eq_recurrence hF n

/-- The coefficient sequence of any solution is $a$. -/
theorem is_oeis_iff_eq_series_of_a (F : PowerSeries ℚ) :
    IsOEIS F ↔ F = seriesOf a := by
  constructor
  · intro h
    ext n
    simpa only [seriesOf, coeff_mk] using coeff_eq_a h n
  · rintro rfl
    exact a_is_oeis

/-- $a(n)$ is odd precisely at the indices $n=2^k-1$, including $n=0$. -/
theorem a_odd_iff_mersenne (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n + 1 = 2 ^ k := by
  rw [a_eq_recurrence]
  exact Recurrence.a_odd_iff_mersenne n

/-- At every other index, $a(n)$ is even. -/
theorem a_even_iff_not_mersenne (n : ℕ) :
    Even (a n) ↔ ¬ ∃ k : ℕ, n + 1 = 2 ^ k := by
  rw [← not_odd_iff_even, a_odd_iff_mersenne]

/-- "a(n) is odd when n = 2^k - 1 for k >= 0, and even elsewhere." -/
theorem a_odd_iff_power_sub_one (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  rw [a_odd_iff_mersenne]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩
    have hp : 0 < 2 ^ k := pow_pos (by decide) k
    exact ⟨k, by omega⟩

/-- Every rational solution has natural coefficients with exactly the asserted parity. -/
theorem oeis_parity {F : PowerSeries ℚ} (hF : IsOEIS F) (n : ℕ) :
    ∃ m : ℕ, coeff n F = (m : ℚ) ∧ (Odd m ↔ ∃ k : ℕ, n = 2 ^ k - 1) :=
  ⟨a n, coeff_eq_a hF n, a_odd_iff_power_sub_one n⟩

/-- The NAME equation has one rational solution, whose coefficients satisfy Hanna's parity clause. -/
theorem oeis_generating_function_and_parity :
    (∃! F : PowerSeries ℚ,
      F = 1 + 3 * X * F ^ 2 - 2 * X * (evalNegHom F) ^ 2) ∧
    ∀ F : PowerSeries ℚ,
      F = 1 + 3 * X * F ^ 2 - 2 * X * (evalNegHom F) ^ 2 →
      ∀ n : ℕ, ∃ m : ℕ, coeff n F = (m : ℚ) ∧
        (Odd m ↔ ∃ k : ℕ, n = 2 ^ k - 1) := by
  refine ⟨exists_unique_series ℚ, ?_⟩
  intro F hF n
  exact oeis_parity hF n


end A368635Proof

namespace OeisA368635

/-- Coefficients of the square of a power series with coefficient sequence $b$. -/
def conv2 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), b k * b (n - k)

/-- Coefficients of $A(x)=1+3xA(x)^2-2xA(-x)^2$. -/
def a : ℕ → ℕ :=
  Nat.strongRec fun n ih =>
    if n = 0 then 1
    else
      let b : ℕ → ℕ := fun m => if h : m < n then ih m h else 0
      (if Even n then 5 else 1) * conv2 b (n - 1)

/-- The submitted recurrence is definitionally the proved recurrence. -/
theorem a_eq_proved (n : ℕ) : a n = A368635Proof.Recurrence.a n := rfl

/-- Hanna's parity conjecture, including index zero. -/
theorem conjecture (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  rw [a_eq_proved]
  exact by
    rw [← A368635Proof.a_eq_recurrence]
    exact A368635Proof.a_odd_iff_power_sub_one n

end OeisA368635
