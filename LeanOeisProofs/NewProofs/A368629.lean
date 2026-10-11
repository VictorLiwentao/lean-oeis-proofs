/-
Copyright (c) 2026 Wentao Li.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
import Mathlib

/-!
# Parity of the coefficients of a functional equation

The generating function satisfies
$A(x)=1+x(A(x)^2+A(-x)^2)/2+x(A(x)^4-A(-x)^4)/2$.
Its coefficients begin $1,1,4,9,88,210$ at offset zero.

*References:*
- [OEIS A368629](https://oeis.org/A368629), Paul D. Hanna, January 10, 2024.
-/

open Finset Nat PowerSeries

namespace A368629

/-- Convolution square. -/
def conv2 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), b k * b (n - k)

def conv4 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  conv2 (conv2 b) n

/-- Coefficient recurrence of OEIS A368629. -/
def a : ℕ → ℕ :=
  Nat.strongRec fun n ih =>
    if n = 0 then 1
    else
      let b : ℕ → ℕ := fun m => if h : m < n then ih m h else 0
      if Even n then conv4 b (n - 1) else conv2 b (n - 1)

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
    a n = if Even n then conv4 a (n - 1) else conv2 a (n - 1) := by
  have hne : n ≠ 0 := hn.ne'
  have hrec :
      a n =
        if Even n then
          conv4 (fun m => if h : m < n then a m else 0) (n - 1)
        else
          conv2 (fun m => if h : m < n then a m else 0) (n - 1) := by
    rw [a, strongRec_eq]
    simp [hne, a]
  rw [hrec]
  have ht : n - 1 < n := Nat.sub_one_lt hne
  have hrestrict :
      conv2 (fun m => if h : m < n then a m else 0) (n - 1) = conv2 a (n - 1) := by
    refine conv2_congr fun k hk => ?_
    have : k < n := Nat.lt_of_le_of_lt hk ht
    simp [this]
  have hrestrict4 :
      conv4 (fun m => if h : m < n then a m else 0) (n - 1) = conv4 a (n - 1) := by
    unfold conv4
    refine conv2_congr fun k hk => ?_
    have hkn : k < n := Nat.lt_of_le_of_lt hk ht
    refine conv2_congr fun i hi => ?_
    have : i < n := Nat.lt_of_le_of_lt hi hkn
    simp [this]
  split_ifs with hE
  · exact hrestrict4
  · exact hrestrict

lemma a_succ_even {n : ℕ} (h : Even (n + 1)) : a (n + 1) = conv4 a n := by
  simpa [h] using a_of_pos (n := n + 1) (Nat.succ_pos _)

lemma a_succ_odd {n : ℕ} (h : Odd (n + 1)) : a (n + 1) = conv2 a n := by
  have hne : ¬ Even (n + 1) := Nat.not_even_iff_odd.mpr h
  simpa [hne] using a_of_pos (n := n + 1) (Nat.succ_pos _)

/-- The coefficient at index zero, including the $k=0$ parity boundary. -/
lemma a_0 : a 0 = 1 := a_zero

lemma a_1 : a 1 = 1 := by
  rw [a_of_pos (by decide : 0 < 1)]
  norm_num [conv2, sum_range_succ, a_0]

lemma a_2 : a 2 = 4 := by
  rw [a_of_pos (by decide : 0 < 2)]
  norm_num [conv4, conv2, sum_range_succ, a_0, a_1]

lemma a_3 : a 3 = 9 := by
  rw [a_of_pos (by decide : 0 < 3)]
  norm_num [conv2, sum_range_succ, a_0, a_1, a_2]

lemma a_4 : a 4 = 88 := by
  rw [a_of_pos (by decide : 0 < 4)]
  norm_num [conv4, conv2, sum_range_succ, a_0, a_1, a_2, a_3]

lemma a_5 : a 5 = 210 := by
  rw [a_of_pos (by decide : 0 < 5)]
  norm_num [conv2, sum_range_succ, a_0, a_1, a_2, a_3, a_4]

lemma conv2_cast (b : ℕ → ℕ) (n : ℕ) :
    (conv2 b n : ZMod 2) =
      ∑ k ∈ range (n + 1), (b k : ZMod 2) * (b (n - k) : ZMod 2) := by
  simp [conv2, Nat.cast_sum, Nat.cast_mul]

lemma conv4_cast (b : ℕ → ℕ) (n : ℕ) :
    (conv4 b n : ZMod 2) =
      ∑ k ∈ range (n + 1), (conv2 b k : ZMod 2) * (conv2 b (n - k) : ZMod 2) := by
  simp [conv4, conv2_cast]

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
  have hE : Even (2 * m + 2) := by
    rw [show 2 * m + 2 = 2 * (m + 1) by omega]
    exact even_two_mul _
  have hcast : (a (2 * m + 2) : ZMod 2) = 0 := by
    rw [a_succ_even hE, conv4_cast]
    simpa using conv2_odd_eq_zero (fun k => (conv2 a k : ZMod 2)) m
  exact (ZMod.natCast_eq_zero_iff_even).1 hcast

lemma a_odd_succ_iff {m : ℕ} : Odd (a (2 * m + 1)) ↔ Odd (a m) := by
  have hodd : Odd (2 * m + 1) := odd_two_mul_add_one m
  have hcast : (a (2 * m + 1) : ZMod 2) = (a m : ZMod 2) := by
    rw [a_succ_odd hodd, conv2_cast,
      conv2_even_square (fun k => (a k : ZMod 2)) m, sq_eq_self_zmod2]
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

/-- The historical recurrence is odd exactly at indices $2^k-1$. -/
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



/-- The series evaluated at $-x$. -/
noncomputable def negX (F : ℚ⟦X⟧) : ℚ⟦X⟧ := rescale (-1 : ℚ) F

/-- The right side of the original OEIS generating-function equation. -/
noncomputable def oeisRhs (F : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  1 + X * (C (1 / 2 : ℚ) * (F ^ 2 + (negX F) ^ 2)) +
    X * (C (1 / 2 : ℚ) * (F ^ 4 - (negX F) ^ 4))

/-- The original OEIS equation in rational formal power series. -/
def IsOEISSeries (F : ℚ⟦X⟧) : Prop := F = oeisRhs F

/-- The rational series formed from the historical natural-number recurrence. -/
noncomputable def generatingSeries : ℚ⟦X⟧ := mk fun n => (a n : ℚ)

@[simp] lemma coeff_generatingSeries (n : ℕ) :
    coeff n generatingSeries = (a n : ℚ) := coeff_mk _ _

lemma coeff_sq (F : ℚ⟦X⟧) (n : ℕ) :
    coeff n (F ^ 2) = ∑ k ∈ range (n + 1), coeff k F * coeff (n - k) F := by
  rw [pow_two, coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i F * coeff j F) n

lemma coeff_generatingSeries_sq (n : ℕ) :
    coeff n (generatingSeries ^ 2) = (conv2 a n : ℚ) := by
  simp [coeff_sq, conv2]

lemma fourth_as_sq_sq (F : ℚ⟦X⟧) : F ^ 4 = (F ^ 2) ^ 2 := by ring

lemma coeff_generatingSeries_fourth (n : ℕ) :
    coeff n (generatingSeries ^ 4) = (conv4 a n : ℚ) := by
  rw [fourth_as_sq_sq, coeff_sq]
  simp [coeff_generatingSeries_sq, conv4, conv2]

lemma coeff_oeisRhs_zero (F : ℚ⟦X⟧) : coeff 0 (oeisRhs F) = 1 := by
  simp [oeisRhs]

lemma coeff_oeisRhs_succ (F : ℚ⟦X⟧) (n : ℕ) :
    coeff (n + 1) (oeisRhs F) =
      (coeff n (F ^ 2) + (-1 : ℚ) ^ n * coeff n (F ^ 2)) / 2 +
      (coeff n (F ^ 4) - (-1 : ℚ) ^ n * coeff n (F ^ 4)) / 2 := by
  simp [oeisRhs, negX, ← map_pow, coeff_succ_X_mul, coeff_C_mul, div_eq_mul_inv]
  ring

lemma coeff_oeisRhs_succ_even (F : ℚ⟦X⟧) {n : ℕ} (hn : Even n) :
    coeff (n + 1) (oeisRhs F) = coeff n (F ^ 2) := by
  rw [coeff_oeisRhs_succ, Even.neg_one_pow hn]
  ring

lemma coeff_oeisRhs_succ_odd (F : ℚ⟦X⟧) {n : ℕ} (hn : Odd n) :
    coeff (n + 1) (oeisRhs F) = coeff n (F ^ 4) := by
  rw [coeff_oeisRhs_succ, Odd.neg_one_pow hn]
  ring

/-- The historical recurrence produces a solution of the original OEIS equation. -/
theorem generatingSeries_isOEISSeries : IsOEISSeries generatingSeries := by
  unfold IsOEISSeries
  ext n
  cases n with
  | zero => simp [coeff_oeisRhs_zero, a_zero]
  | succ n =>
    by_cases hn : Even n
    · rw [coeff_generatingSeries, coeff_oeisRhs_succ_even _ hn,
        coeff_generatingSeries_sq, a_succ_odd (Nat.odd_add_one.mpr (not_odd_iff_even.mpr hn))]
    · rw [coeff_generatingSeries,
        coeff_oeisRhs_succ_odd _ (Nat.not_even_iff_odd.mp hn),
        coeff_generatingSeries_fourth, a_succ_even (Nat.even_add_one.mpr hn)]

lemma coeff_sq_congr {F G : ℚ⟦X⟧} {n : ℕ}
    (h : ∀ k ≤ n, coeff k F = coeff k G) : coeff n (F ^ 2) = coeff n (G ^ 2) := by
  rw [coeff_sq, coeff_sq]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [h k hk', h (n - k) (Nat.sub_le _ _)]

lemma coeff_fourth_congr {F G : ℚ⟦X⟧} {n : ℕ}
    (h : ∀ k ≤ n, coeff k F = coeff k G) : coeff n (F ^ 4) = coeff n (G ^ 4) := by
  rw [fourth_as_sq_sq, fourth_as_sq_sq]
  apply coeff_sq_congr
  intro k hk
  exact coeff_sq_congr fun i hi => h i (hi.trans hk)

/-- Every rational solution of the OEIS equation has the historical recurrence's coefficients. -/
theorem coeff_eq_a_of_isOEISSeries {F : ℚ⟦X⟧} (hF : IsOEISSeries F) (n : ℕ) :
    coeff n F = (a n : ℚ) := by
  have hA := generatingSeries_isOEISSeries
  change F = oeisRhs F at hF
  change generatingSeries = oeisRhs generatingSeries at hA
  have heq : coeff n F = coeff n generatingSeries := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => rw [hF, hA, coeff_oeisRhs_zero, coeff_oeisRhs_zero]
      | succ n =>
        have hp : ∀ k ≤ n, coeff k F = coeff k generatingSeries :=
          fun k hk => ih k (by omega)
        calc
          coeff (n + 1) F = coeff (n + 1) (oeisRhs F) := congrArg (coeff (n + 1)) hF
          _ = coeff (n + 1) (oeisRhs generatingSeries) := by
            rw [coeff_oeisRhs_succ, coeff_oeisRhs_succ,
              coeff_sq_congr hp, coeff_fourth_congr hp]
          _ = coeff (n + 1) generatingSeries := (congrArg (coeff (n + 1)) hA).symm
  simpa using heq

/-- The OEIS equation has exactly one rational formal-power-series solution. -/
theorem isOEISSeries_iff_eq (F : ℚ⟦X⟧) :
    IsOEISSeries F ↔ F = generatingSeries := by
  constructor
  · intro hF
    ext n
    simpa using coeff_eq_a_of_isOEISSeries hF n
  · rintro rfl
    exact generatingSeries_isOEISSeries

/-- The literal OEIS equation holds exactly for the recurrence-generated series. -/
theorem original_equation_iff_eq (F : ℚ⟦X⟧) :
    (F = 1 + X * (C (1 / 2 : ℚ) * (F ^ 2 + (rescale (-1 : ℚ) F) ^ 2)) +
      X * (C (1 / 2 : ℚ) * (F ^ 4 - (rescale (-1 : ℚ) F) ^ 4))) ↔
    F = generatingSeries := isOEISSeries_iff_eq F

/-- There exists exactly one solution of the original OEIS equation. -/
theorem existsUnique_oeisSeries : ∃! F : ℚ⟦X⟧, IsOEISSeries F := by
  refine ⟨generatingSeries, generatingSeries_isOEISSeries, ?_⟩
  intro F hF
  exact (isOEISSeries_iff_eq F).mp hF

/-- Every coefficient of the OEIS-defined series is a natural number, with the claimed parity. -/
theorem oeis_coeff_parity {F : ℚ⟦X⟧} (hF : IsOEISSeries F) (n : ℕ) :
    ∃ m : ℕ, coeff n F = (m : ℚ) ∧ (Odd m ↔ ∃ k : ℕ, n + 1 = 2 ^ k) := by
  exact ⟨a n, coeff_eq_a_of_isOEISSeries hF n, a_odd_iff_mersenne n⟩

/-- The original OEIS equation, natural coefficients, and oddness conjecture hold together. -/
theorem oeis_equation_and_parity :
    ∃ F : ℚ⟦X⟧, IsOEISSeries F ∧
      (∀ G : ℚ⟦X⟧, IsOEISSeries G → G = F) ∧
      ∀ n : ℕ, ∃ m : ℕ, coeff n F = (m : ℚ) ∧
        (Odd m ↔ ∃ k : ℕ, n + 1 = 2 ^ k) := by
  refine ⟨generatingSeries, generatingSeries_isOEISSeries, ?_, ?_⟩
  · intro G hG
    exact (isOEISSeries_iff_eq G).mp hG
  · exact oeis_coeff_parity generatingSeries_isOEISSeries

/-- The unique solution chosen from the original generating-function equation. -/
noncomputable def oeisSeries : ℚ⟦X⟧ := Classical.choose existsUnique_oeisSeries

lemma oeisSeries_spec : IsOEISSeries oeisSeries :=
  (Classical.choose_spec existsUnique_oeisSeries).1

/-- Every solution has a uniquely determined natural coefficient at each index. -/
theorem existsUnique_nat_coeff {F : ℚ⟦X⟧} (hF : IsOEISSeries F) (n : ℕ) :
    ∃! m : ℕ, coeff n F = (m : ℚ) := by
  refine ⟨a n, coeff_eq_a_of_isOEISSeries hF n, ?_⟩
  intro m hm
  exact Nat.cast_injective (hm.symm.trans (coeff_eq_a_of_isOEISSeries hF n))

/-- The natural coefficient sequence of the equation-defined series. -/
noncomputable def oeisA (n : ℕ) : ℕ :=
  Classical.choose (existsUnique_nat_coeff oeisSeries_spec n)

lemma coeff_oeisSeries (n : ℕ) : coeff n oeisSeries = (oeisA n : ℚ) :=
  (Classical.choose_spec (existsUnique_nat_coeff oeisSeries_spec n)).1

/-- The equation-defined sequence agrees with the historical recurrence at every index. -/
theorem oeisA_eq_a (n : ℕ) : oeisA n = a n := by
  exact Nat.cast_injective
    ((coeff_oeisSeries n).symm.trans (coeff_eq_a_of_isOEISSeries oeisSeries_spec n))

lemma oeisA_0 : oeisA 0 = 1 := by rw [oeisA_eq_a, a_0]
lemma oeisA_1 : oeisA 1 = 1 := by rw [oeisA_eq_a, a_1]
lemma oeisA_2 : oeisA 2 = 4 := by rw [oeisA_eq_a, a_2]
lemma oeisA_3 : oeisA 3 = 9 := by rw [oeisA_eq_a, a_3]
lemma oeisA_4 : oeisA 4 = 88 := by rw [oeisA_eq_a, a_4]
lemma oeisA_5 : oeisA 5 = 210 := by rw [oeisA_eq_a, a_5]

lemma isMersenne_iff_sub (n : ℕ) : IsMersenne n ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩
    have hp : 0 < (2 : ℕ) ^ k := pow_pos (by decide) k
    exact ⟨k, by omega⟩

/--
"Conjecture: a(n) is odd when n = 2^k - 1 for k >= 0, and even elsewhere."
- Paul D. Hanna, OEIS A368629.
-/
theorem oeisA_odd_iff (n : ℕ) : Odd (oeisA n) ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  rw [oeisA_eq_a, a_odd_iff_mersenne, isMersenne_iff_sub]

/-- All other coefficients of the equation-defined sequence are even. -/
theorem oeisA_even_iff (n : ℕ) : Even (oeisA n) ↔ ¬ ∃ k : ℕ, n = 2 ^ k - 1 := by
  rw [← not_odd_iff_even, oeisA_odd_iff]

/-- The chosen series satisfies the original equation with rational halves. -/
theorem oeisSeries_original_equation :
    oeisSeries = 1 + X * (C (1 / 2 : ℚ) *
      (oeisSeries ^ 2 + (rescale (-1 : ℚ) oeisSeries) ^ 2)) +
      X * (C (1 / 2 : ℚ) *
      (oeisSeries ^ 4 - (rescale (-1 : ℚ) oeisSeries) ^ 4)) := oeisSeries_spec


end A368629

namespace OeisA368629

/-- Coefficients of the square of a power series with coefficient sequence $b$. -/
def conv2 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), b k * b (n - k)

/-- Coefficients of the fourth power of a power series with coefficient sequence $b$. -/
def conv4 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  conv2 (conv2 b) n

/-- Coefficients of $A(x)=1+x(A(x)^2+A(-x)^2)/2+x(A(x)^4-A(-x)^4)/2$. -/
def a : ℕ → ℕ :=
  Nat.strongRec fun n ih =>
    if n = 0 then 1
    else
      let b : ℕ → ℕ := fun m => if h : m < n then ih m h else 0
      if Even n then conv4 b (n - 1) else conv2 b (n - 1)

/-- The submitted recurrence is definitionally the proved recurrence. -/
theorem a_eq_proved (n : ℕ) : a n = A368629.a n := rfl

/-- Hanna's parity conjecture, including index zero. -/
theorem conjecture (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  rw [a_eq_proved]
  exact (A368629.a_odd_iff_mersenne n).trans (A368629.isMersenne_iff_sub n)

end OeisA368629
