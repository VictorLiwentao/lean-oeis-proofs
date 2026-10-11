/-
Copyright (c) 2026 Wentao Li.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-!
# A generating function with powers two and four

OEIS A368628 is the coefficient sequence of the unique formal power series satisfying
$A(x)=1+x(A(x)^2-A(-x)^2)/2+x(A(x)^4+A(-x)^4)/2$.

*References:*
- [OEIS A368628](https://oeis.org/A368628), Paul D. Hanna, January 10, 2024.
-/

open Finset Nat PowerSeries

namespace A368628Proof

/-- Convolution square. -/
def conv2 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), b k * b (n - k)

def conv4 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  conv2 (conv2 b) n

/-- Coefficient recurrence of OEIS A368628. -/
def recurrence : ℕ → ℕ :=
  Nat.strongRec fun n ih =>
    if n = 0 then 1
    else
      let b : ℕ → ℕ := fun m => if h : m < n then ih m h else 0
      if Even n then conv2 b (n - 1) else conv4 b (n - 1)

lemma recurrence_zero : recurrence 0 = 1 := by
  rw [recurrence, strongRec_eq]
  simp

lemma conv2_congr {b c : ℕ → ℕ} {n : ℕ} (h : ∀ k ≤ n, b k = c k) :
    conv2 b n = conv2 c n := by
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hnk : n - k ≤ n := Nat.sub_le _ _
  rw [h k hk', h (n - k) hnk]

lemma recurrence_of_pos {n : ℕ} (hn : 0 < n) :
    recurrence n = if Even n then conv2 recurrence (n - 1) else conv4 recurrence (n - 1) := by
  have hne : n ≠ 0 := hn.ne'
  have ht : n - 1 < n := Nat.sub_one_lt hne
  have hrec :
      recurrence n =
        if Even n then
          conv2 (fun m => if h : m < n then recurrence m else 0) (n - 1)
        else
          conv4 (fun m => if h : m < n then recurrence m else 0) (n - 1) := by
    rw [recurrence, strongRec_eq]
    simp [hne, recurrence]
  rw [hrec]
  have hrestrict :
      conv2 (fun m => if h : m < n then recurrence m else 0) (n - 1) = conv2 recurrence (n - 1) := by
    refine conv2_congr fun k hk => ?_
    have : k < n := Nat.lt_of_le_of_lt hk ht
    simp [this]
  have hrestrict4 :
      conv4 (fun m => if h : m < n then recurrence m else 0) (n - 1) = conv4 recurrence (n - 1) := by
    unfold conv4
    refine conv2_congr fun k hk => ?_
    have hkn : k < n := Nat.lt_of_le_of_lt hk ht
    refine conv2_congr fun i hi => ?_
    have : i < n := Nat.lt_of_le_of_lt hi hkn
    simp [this]
  split_ifs with hE
  · exact hrestrict
  · exact hrestrict4

lemma recurrence_succ_even {n : ℕ} (h : Even (n + 1)) : recurrence (n + 1) = conv2 recurrence n := by
  simpa [h] using recurrence_of_pos (n := n + 1) (Nat.succ_pos _)

lemma recurrence_succ_odd {n : ℕ} (h : Odd (n + 1)) : recurrence (n + 1) = conv4 recurrence n := by
  have hne : ¬ Even (n + 1) := Nat.not_even_iff_odd.mpr h
  simpa [hne] using recurrence_of_pos (n := n + 1) (Nat.succ_pos _)

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

lemma conv4_cast (b : ℕ → ℕ) (n : ℕ) :
    (conv4 b n : ZMod 2) =
      ∑ k ∈ range (n + 1), (conv2 b k : ZMod 2) * (conv2 b (n - k) : ZMod 2) := by
  simp [conv4, conv2_cast]

lemma recurrence_even_succ_even (m : ℕ) : Even (recurrence (2 * m + 2)) := by
  have hE : Even (2 * m + 2) := by
    rw [show 2 * m + 2 = 2 * (m + 1) by omega]
    exact even_two_mul _
  have hcast : (recurrence (2 * m + 2) : ZMod 2) = 0 := by
    rw [recurrence_succ_even hE, conv2_cast]
    simpa using conv2_odd_eq_zero (fun k => (recurrence k : ZMod 2)) m
  exact (ZMod.natCast_eq_zero_iff_even).1 hcast

lemma conv4_even_eq_conv2 (m : ℕ) :
    (conv4 recurrence (2 * m) : ZMod 2) = (conv2 recurrence m : ZMod 2) := by
  rw [conv4_cast, conv2_even_square (fun k => (conv2 recurrence k : ZMod 2)) m, sq_eq_self_zmod2]

lemma recurrence_four_three_even (t : ℕ) : Even (recurrence (4 * t + 3)) := by
  have hodd : Odd (4 * t + 3) := by
    rw [show 4 * t + 3 = 2 * (2 * t + 1) + 1 by omega]
    exact odd_two_mul_add_one _
  have hcast : (recurrence (4 * t + 3) : ZMod 2) = 0 := by
    rw [recurrence_succ_odd hodd, show 4 * t + 2 = 2 * (2 * t + 1) by omega, conv4_even_eq_conv2,
      conv2_cast]
    simpa using conv2_odd_eq_zero (fun k => (recurrence k : ZMod 2)) t
  exact (ZMod.natCast_eq_zero_iff_even).1 hcast

lemma recurrence_four_one_iff {t : ℕ} : Odd (recurrence (4 * t + 1)) ↔ Odd (recurrence t) := by
  have hodd : Odd (4 * t + 1) := by
    rw [show 4 * t + 1 = 2 * (2 * t) + 1 by omega]
    exact odd_two_mul_add_one _
  have hcast : (recurrence (4 * t + 1) : ZMod 2) = (recurrence t : ZMod 2) := by
    rw [recurrence_succ_odd hodd, show 4 * t = 2 * (2 * t) by omega, conv4_even_eq_conv2, conv2_cast,
      conv2_even_square (fun k => (recurrence k : ZMod 2)) t, sq_eq_self_zmod2]
  rw [← ZMod.natCast_eq_one_iff_odd, hcast, ZMod.natCast_eq_one_iff_odd]

/-- `n` is of the form `(4^k - 1)/3`. -/
def IsRepunit4 (n : ℕ) : Prop := ∃ k : ℕ, 3 * n + 1 = 4 ^ k

lemma not_repunit4_even_succ (m : ℕ) : ¬ IsRepunit4 (2 * m + 2) := by
  rintro ⟨k, hk⟩
  have hval : 3 * (2 * m + 2) + 1 = 6 * m + 7 := by omega
  have hk' : 4 ^ k = 6 * m + 7 := by
    rw [← hk, hval]
  have hodd7 : Odd (6 * m + 7) := by
    rw [show 6 * m + 7 = 2 * (3 * m + 3) + 1 by omega]
    exact odd_two_mul_add_one _
  have hodd : Odd (4 ^ k) := by
    simpa [hk'] using hodd7
  cases k with
  | zero =>
    simp at hk'
  | succ k =>
    have he : Even (4 ^ (k + 1)) := ⟨2 * 4 ^ k, by rw [pow_succ]; omega⟩
    exact (not_odd_iff_even.2 he) hodd

lemma not_repunit4_four_three (t : ℕ) : ¬ IsRepunit4 (4 * t + 3) := by
  rintro ⟨k, hk⟩
  have hval : 3 * (4 * t + 3) + 1 = 12 * t + 10 := by omega
  have hk' : 4 ^ k = 12 * t + 10 := by
    rw [← hk, hval]
  cases k with
  | zero =>
    simp at hk'
  | succ k =>
    have : (4 ^ (k + 1)) % 4 = 0 := by
      rw [pow_succ]
      omega
    have : (12 * t + 10) % 4 = 0 := by
      rw [← hk', this]
    omega

lemma repunit4_four_one (t : ℕ) : IsRepunit4 (4 * t + 1) ↔ IsRepunit4 t := by
  constructor
  · rintro ⟨k, hk⟩
    have hval : 3 * (4 * t + 1) + 1 = 4 * (3 * t + 1) := by omega
    have hk' : 4 ^ k = 4 * (3 * t + 1) := by
      rw [← hk, hval]
    cases k with
    | zero =>
      omega
    | succ k =>
      refine ⟨k, ?_⟩
      have hps : 4 ^ (k + 1) = 4 ^ k * 4 := pow_succ _ _
      have : 4 ^ k * 4 = (3 * t + 1) * 4 := by
        rw [← hps, hk', mul_comm (3 * t + 1)]
      exact Nat.mul_right_cancel (by omega : 0 < 4) this.symm
  · rintro ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    have : 3 * (4 * t + 1) + 1 = 4 * (3 * t + 1) := by omega
    rw [this, hk, pow_succ, mul_comm]

/-- OEIS A368628: `recurrence(n)` is odd iff `n = (4^k - 1)/3`. -/
theorem recurrence_odd_iff_repunit4 (n : ℕ) : Odd (recurrence n) ↔ IsRepunit4 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · constructor
      · intro
        exact ⟨0, by simp⟩
      · intro
        simp [recurrence_zero]
    obtain ⟨m, rfl | rfl⟩ := even_or_odd' n
    · obtain ⟨t, rfl | rfl⟩ := even_or_odd' m
      · have : 2 * (2 * t) + 1 = 4 * t + 1 := by omega
        rw [this, recurrence_four_one_iff, ih t (by omega), ← repunit4_four_one]
      · have : 2 * (2 * t + 1) + 1 = 4 * t + 3 := by omega
        rw [this]
        constructor
        · intro hodd
          exact (not_odd_iff_even.2 (recurrence_four_three_even t) hodd).elim
        · intro hR
          exact (not_repunit4_four_three t hR).elim
    · constructor
      · intro hodd
        exact (not_odd_iff_even.2 (recurrence_even_succ_even m) hodd).elim
      · intro hR
        exact (not_repunit4_even_succ m hR).elim


/-- The right side of the original OEIS equation in $\mathbb{Q}[[X]]$.
`rescale (-1)` is substitution of $-X$ for $X$. -/
noncomputable def oeisRhs (F : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  1 + X * (C (1 / 2) * (F ^ 2 - (rescale (-1) F) ^ 2)) +
    X * (C (1 / 2) * (F ^ 4 + (rescale (-1) F) ^ 4))

/-- The original defining generating-function equation of OEIS A368628. -/
def SatisfiesOEIS (F : ℚ⟦X⟧) : Prop := F = oeisRhs F

lemma coeff_rescale_pow (F : ℚ⟦X⟧) (n p : ℕ) :
    coeff n ((rescale (-1) F) ^ p) = (-1 : ℚ) ^ n * coeff n (F ^ p) := by
  rw [← map_pow, coeff_rescale]

lemma coeff_oeis_rhs_zero (F : ℚ⟦X⟧) : coeff 0 (oeisRhs F) = 1 := by
  simp [oeisRhs]

lemma coeff_oeis_rhs_succ (F : ℚ⟦X⟧) (n : ℕ) :
    coeff (n + 1) (oeisRhs F) =
      if Even (n + 1) then coeff n (F ^ 2) else coeff n (F ^ 4) := by
  simp only [oeisRhs, map_add, coeff_one, Nat.add_eq_zero_iff, Nat.one_ne_zero,
    and_false, ite_false, zero_add, coeff_succ_X_mul, coeff_C_mul, map_sub,
    coeff_rescale_pow]
  by_cases hn : Even n
  · have hsucc : ¬ Even (n + 1) := by simpa only [Nat.even_add_one, not_not] using hn
    rw [ite_eq_right hsucc, hn.neg_one_pow]
    ring
  · have hsucc : Even (n + 1) := Nat.even_add_one.mpr hn
    rw [ite_eq_left hsucc, (Nat.not_even_iff_odd.mp hn).neg_one_pow]
    ring

/-- The defining equation is equivalent to its exact coefficient recurrence. -/
theorem satisfies_oeis_iff (F : ℚ⟦X⟧) :
    SatisfiesOEIS F ↔ coeff 0 F = 1 ∧ ∀ n : ℕ,
      coeff (n + 1) F = if Even (n + 1) then coeff n (F ^ 2) else coeff n (F ^ 4) := by
  constructor
  · intro h
    have heq : F = oeisRhs F := h
    constructor
    · simpa only [coeff_oeis_rhs_zero] using congrArg (coeff 0) heq
    · intro n
      simpa only [coeff_oeis_rhs_succ] using congrArg (coeff (n + 1)) heq
  · rintro ⟨hzero, hsucc⟩
    apply PowerSeries.ext
    intro n
    cases n with
    | zero => simpa only [coeff_oeis_rhs_zero] using hzero
    | succ n => simpa only [coeff_oeis_rhs_succ] using hsucc n

/-- The generating function of the old natural-number recurrence. -/
noncomputable def recurrenceSeries : ℚ⟦X⟧ := mk fun n => (recurrence n : ℚ)

lemma coeff_recurrence_series (n : ℕ) : coeff n recurrenceSeries = (recurrence n : ℚ) := by
  simp [recurrenceSeries, coeff_mk]

lemma coeff_sq (F : ℚ⟦X⟧) (n : ℕ) :
    coeff n (F ^ 2) = ∑ k ∈ range (n + 1), coeff k F * coeff (n - k) F := by
  rw [pow_two, coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i F * coeff j F) n

lemma coeff_recurrence_series_sq (n : ℕ) :
    coeff n (recurrenceSeries ^ 2) = (conv2 recurrence n : ℚ) := by
  simp [coeff_sq, coeff_recurrence_series, conv2, Nat.cast_sum, Nat.cast_mul]

lemma coeff_recurrence_series_fourth (n : ℕ) :
    coeff n (recurrenceSeries ^ 4) = (conv4 recurrence n : ℚ) := by
  rw [show recurrenceSeries ^ 4 = (recurrenceSeries ^ 2) ^ 2 by ring, coeff_sq]
  simp [coeff_recurrence_series_sq, conv4, conv2, Nat.cast_sum, Nat.cast_mul]

/-- The old recurrence satisfies the original OEIS equation, without a bridge hypothesis. -/
theorem recurrence_series_satisfies_oeis : SatisfiesOEIS recurrenceSeries := by
  rw [satisfies_oeis_iff]
  constructor
  · simp [coeff_recurrence_series, recurrence_zero]
  · intro n
    rw [coeff_recurrence_series, recurrence_of_pos (Nat.succ_pos n)]
    simp only [coeff_recurrence_series_sq, coeff_recurrence_series_fourth]
    split_ifs <;> rfl

lemma coeff_pow_congr {F G : ℚ⟦X⟧} (p n : ℕ)
    (h : ∀ i ≤ n, coeff i F = coeff i G) : coeff n (F ^ p) = coeff n (G ^ p) := by
  induction p generalizing n with
  | zero => simp
  | succ p ih =>
    rw [pow_succ, pow_succ, coeff_mul, coeff_mul]
    refine sum_congr rfl fun k hk => ?_
    have hsum := mem_antidiagonal.mp hk
    rw [ih k.1 (fun i hi => h i (by omega)), h k.2 (by omega)]

/-- Every rational solution has precisely the old recurrence coefficients. -/
theorem coeff_eq_recurrence {F : ℚ⟦X⟧} (hF : SatisfiesOEIS F) (n : ℕ) :
    coeff n F = (recurrence n : ℚ) := by
  obtain ⟨hzero, hsucc⟩ := (satisfies_oeis_iff F).mp hF
  have hrec := (satisfies_oeis_iff recurrenceSeries).mp recurrence_series_satisfies_oeis
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa [recurrence_zero] using hzero
    | succ n =>
      rw [hsucc n, ← coeff_recurrence_series, hrec.2 n]
      have hle : ∀ i ≤ n, coeff i F = coeff i recurrenceSeries := by
        intro i hi
        rw [coeff_recurrence_series]
        exact ih i (by omega)
      split_ifs
      · exact coeff_pow_congr 2 n hle
      · exact coeff_pow_congr 4 n hle

/-- The original OEIS equation has exactly one rational formal power series solution. -/
theorem exists_unique_oeis_series : ∃! F : ℚ⟦X⟧, SatisfiesOEIS F := by
  refine ⟨recurrenceSeries, recurrence_series_satisfies_oeis, ?_⟩
  intro F hF
  exact PowerSeries.ext fun n => (coeff_eq_recurrence hF n).trans
    (coeff_recurrence_series n).symm

/-- All coefficients of any rational solution are nonnegative integers. -/
theorem oeis_coeff_natural {F : ℚ⟦X⟧} (hF : SatisfiesOEIS F) (n : ℕ) :
    ∃ m : ℕ, coeff n F = (m : ℚ) := ⟨recurrence n, coeff_eq_recurrence hF n⟩

/-- The OEIS equation characterizes the old recurrence among natural sequences. -/
theorem oeis_sequence_iff (b : ℕ → ℕ) :
    SatisfiesOEIS (mk fun n => (b n : ℚ)) ↔ b = recurrence := by
  constructor
  · intro hb
    funext n
    have h := coeff_eq_recurrence hb n
    simpa only [coeff_mk, Nat.cast_inj] using h
  · rintro rfl
    exact recurrence_series_satisfies_oeis

/-- The original equation defines exactly one natural sequence. -/
theorem exists_unique_oeis_sequence :
    ∃! b : ℕ → ℕ, SatisfiesOEIS (mk fun n => (b n : ℚ)) := by
  refine ⟨recurrence, recurrence_series_satisfies_oeis, ?_⟩
  intro b hb
  exact (oeis_sequence_iff b).mp hb

/-- The natural coefficient sequence defined by the original OEIS equation. -/
noncomputable def a : ℕ → ℕ := Classical.choose exists_unique_oeis_sequence

lemma a_satisfies_oeis : SatisfiesOEIS (mk fun n => (a n : ℚ)) :=
  (Classical.choose_spec exists_unique_oeis_sequence).1

lemma a_eq_recurrence : a = recurrence := (oeis_sequence_iff a).mp a_satisfies_oeis

lemma a_of_pos {n : ℕ} (hn : 0 < n) :
    a n = if Even n then conv2 a (n - 1) else conv4 a (n - 1) := by
  rw [a_eq_recurrence]
  exact recurrence_of_pos hn

lemma a_0 : a 0 = 1 := by rw [a_eq_recurrence]; exact recurrence_zero
lemma a_1 : a 1 = 1 := by
  rw [a_eq_recurrence, recurrence_succ_odd (n := 0) odd_one]
  simp [conv4, conv2, recurrence_zero]
lemma a_2 : a 2 = 2 := by
  rw [a_of_pos (by decide : 0 < 2)]
  norm_num [conv2, sum_range_succ, a_0, a_1]
lemma a_3 : a 3 = 14 := by
  rw [a_of_pos (by decide : 0 < 3)]
  norm_num [conv4, conv2, sum_range_succ, a_0, a_1, a_2]
lemma a_4 : a 4 = 32 := by
  rw [a_of_pos (by decide : 0 < 4)]
  norm_num [conv2, sum_range_succ, a_0, a_1, a_2, a_3]
lemma a_5 : a 5 = 345 := by
  rw [a_of_pos (by decide : 0 < 5)]
  norm_num [conv4, conv2, sum_range_succ, a_0, a_1, a_2, a_3, a_4]

lemma is_repunit4_iff (n : ℕ) :
    IsRepunit4 n ↔ ∃ k : ℕ, n = (4 ^ k - 1) / 3 := by
  have hpow (k : ℕ) : ∃ m : ℕ, 4 ^ k = 3 * m + 1 := by
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨m, hm⟩ := ih
      refine ⟨4 * m + 1, ?_⟩
      rw [pow_succ, hm]
      omega
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    omega
  · rintro ⟨k, hk⟩
    obtain ⟨m, hm⟩ := hpow k
    refine ⟨k, ?_⟩
    omega

/--
"Conjecture: a(n) is odd when n = (4^k - 1)/3 for k >= 0, and even elsewhere."

This holds for the coefficients of the original OEIS generating-function equation.
-/
theorem oeis_parity {b : ℕ → ℕ}
    (hb : SatisfiesOEIS (mk fun n => (b n : ℚ))) (n : ℕ) :
    Odd (b n) ↔ IsRepunit4 n := by
  rw [(oeis_sequence_iff b).mp hb]
  exact recurrence_odd_iff_repunit4 n

/-- The odd coefficients of the OEIS-defined sequence have exactly the indices
$(4^k-1)/3$, including $k=0$. -/
theorem a_odd_iff (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n = (4 ^ k - 1) / 3 := by
  rw [← is_repunit4_iff]
  exact oeis_parity a_satisfies_oeis n

/-- All other coefficients of the OEIS-defined sequence are even. -/
theorem a_even_iff (n : ℕ) : Even (a n) ↔ ¬ ∃ k : ℕ, n = (4 ^ k - 1) / 3 := by
  rw [← a_odd_iff, not_odd_iff_even]

/-- Every rational solution has nonnegative integral coefficients with the stated parity. -/
theorem solution_coefficients {F : ℚ⟦X⟧} (hF : SatisfiesOEIS F) (n : ℕ) :
    coeff n F = (a n : ℚ) ∧
      (Odd (a n) ↔ ∃ k : ℕ, n = (4 ^ k - 1) / 3) ∧
      (Even (a n) ↔ ¬ ∃ k : ℕ, n = (4 ^ k - 1) / 3) := by
  refine ⟨?_, a_odd_iff n, a_even_iff n⟩
  rw [a_eq_recurrence]
  exact coeff_eq_recurrence hF n


end A368628Proof

/-! The executable sequence and parity statement submitted to Formal Conjectures. -/
namespace OeisA368628

/-- Coefficients of the square of a power series with coefficient sequence $b$. -/
def conv2 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), b k * b (n - k)

/-- Coefficients of the fourth power of a power series with coefficient sequence $b$. -/
def conv4 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  conv2 (conv2 b) n

/-- Coefficients of $A(x)=1+x(A(x)^2-A(-x)^2)/2+x(A(x)^4+A(-x)^4)/2$. -/
def a : ℕ → ℕ :=
  Nat.strongRec fun n ih =>
    if n = 0 then 1
    else
      let b : ℕ → ℕ := fun m => if h : m < n then ih m h else 0
      if Even n then conv2 b (n - 1) else conv4 b (n - 1)

/-- The submitted sequence is the recurrence in the generating-function proof. -/
theorem a_eq_recurrence : a = A368628Proof.recurrence := rfl

/-- The submitted sequence has the original OEIS generating function. -/
theorem generating_function :
    A368628Proof.SatisfiesOEIS (PowerSeries.mk fun n => (a n : ℚ)) := by
  exact A368628Proof.recurrence_series_satisfies_oeis

/-- The original equation uniquely characterizes the submitted sequence. -/
theorem generating_function_iff (b : ℕ → ℕ) :
    A368628Proof.SatisfiesOEIS (PowerSeries.mk fun n => (b n : ℚ)) ↔ b = a := by
  exact A368628Proof.oeis_sequence_iff b

/-- The parity conjecture, including index zero and the even complement. -/
theorem conjecture (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n = (4 ^ k - 1) / 3 := by
  exact (A368628Proof.recurrence_odd_iff_repunit4 n).trans
    (A368628Proof.is_repunit4_iff n)

end OeisA368628
