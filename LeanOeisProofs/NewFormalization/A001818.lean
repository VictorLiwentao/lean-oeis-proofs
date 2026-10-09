/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Wentao Li.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Original Lean formalization: The Formal Conjectures Authors.
New Lean proof development and write-up: Wentao Li.
Mathematics: Yue-Feng She, Zhi-Wei Sun and Wei Xia,
A novel permanent identity with applications, arXiv:2208.12167v2,
Theorem 1.3(ii) (even-size case). Dependency: Guo–Li–Tao–Wei,
arXiv:2206.02592; Calogero–Perelomov, Linear Algebra Appl. 25 (1979).
This file treats only OeisA1818.conjecture1. It does not treat conjecture2,
A002454, or A356041 as assigned targets. It does not claim new informal
mathematics or first-formalization priority.
AI assistance: Cursor Grok 4.6 Extra High, 2026-09-13.
-/

import Mathlib


namespace OeisA1818

def a (n : ℕ) : ℕ :=
  (∏ k ∈ Finset.range n, (2 * k + 1)) ^ 2

end OeisA1818


/-!
Exact target: `OeisA1818.conjecture1` from frozen
`FormalConjectures/OEIS/1818.lean`.
-/

open Complex Equiv Finset Matrix

namespace A001818C1

open OeisA1818

/-- The source matrix. The wrapper never uses the admitted source theorem. -/
noncomputable def sunMatrix (n : ℕ) (ζ : ℂ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ :=
  fun i j =>
    if i = j then
      (1 : ℂ)
    else
      (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))

/-- Integer ascription on `i.val - j.val` is `ℤ` subtraction, not truncated `ℕ`. -/
theorem int_sub_val {n : ℕ} (i j : Fin n) :
    (i.val - j.val : ℤ) = (i.val : ℤ) - (j.val : ℤ) := rfl

theorem sunMatrix_eq_frozen (n : ℕ) (ζ : ℂ) :
    sunMatrix n ζ = fun (i j : Fin (2 * n)) =>
      if i = j then
        (1 : ℂ)
      else
        (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ)) :=
  rfl

lemma zeta_ne_zero {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) : ζ ≠ 0 := by
  intro h
  have := hζ.pow_eq_one
  rw [h, zero_pow (NeZero.ne N)] at this
  exact zero_ne_one this

lemma zpow_int_val_sub {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (i j : Fin N) : ζ ^ (i.val - j.val : ℤ) = ζ ^ (i - j).val := by
  have hz := zeta_ne_zero hζ
  have hN : ζ ^ (N : ℤ) = 1 := by rw [zpow_natCast, hζ.pow_eq_one]
  have hite := Fin.intCast_val_sub_eq_sub_add_ite (n := N) i j
  rw [← zpow_natCast, hite, zpow_add₀ hz]
  split_ifs with hle
  · simp
  · rw [hN, mul_one]

lemma abs_val_sub_lt {N : ℕ} (i j : Fin N) : |(i.val : ℤ) - j.val| < N := by
  have hi := i.isLt
  have hj := j.isLt
  rw [abs_sub_lt_iff]
  constructor <;> omega

lemma zpow_sub_ne_one {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {i j : Fin N} (hij : i ≠ j) : ζ ^ (i.val - j.val : ℤ) ≠ 1 := by
  intro h
  have hdvd : (N : ℤ) ∣ (i.val - j.val : ℤ) := (hζ.zpow_eq_one_iff_dvd _).1 h
  have hne : (i.val : ℤ) - j.val ≠ 0 := by
    intro h0
    exact hij (Fin.ext (Int.natCast_inj.mp (sub_eq_zero.mp h0)))
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : k = 0 := by
    have hNpos : (0 : ℤ) < N := Nat.cast_pos.mpr (Nat.pos_of_neZero N)
    by_contra hkne
    have hmul : |k| * (N : ℤ) < N := by
      have h' : |(N : ℤ) * k| < N := by
        simpa [hk] using abs_val_sub_lt i j
      simpa [abs_mul, Nat.abs_cast, mul_comm] using h'
    have hge : (N : ℤ) ≤ |k| * N :=
      le_mul_of_one_le_left (le_of_lt hNpos) (Int.one_le_abs hkne)
    exact (not_le.mpr hmul) hge
  exact hne (by simp [hk, hk0])

lemma denom_ne_zero {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {i j : Fin N} (hij : i ≠ j) : 1 - ζ ^ (i.val - j.val : ℤ) ≠ 0 := by
  exact sub_ne_zero.2 (zpow_sub_ne_one hζ hij).symm

lemma sunMatrix_apply_ne {n : ℕ} [NeZero n] {ζ : ℂ} (_hζ : IsPrimitiveRoot ζ (2 * n))
    {i j : Fin (2 * n)} (hij : i ≠ j) :
    sunMatrix n ζ i j =
      (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ)) := by
  simp [sunMatrix, hij]

lemma sunMatrix_apply_eq {n : ℕ} (ζ : ℂ) (i : Fin (2 * n)) :
    sunMatrix n ζ i i = 1 := by
  simp [sunMatrix]

/- Permanent of size 2, and the `n = 1` case. -/

lemma univ_perm_fin_two :
    (univ : Finset (Perm (Fin 2))) = {1, Equiv.swap (0 : Fin 2) 1} := by
  ext σ
  simp only [mem_univ, mem_insert, mem_singleton, true_iff]
  have fin2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := fun x => by
    fin_cases x <;> simp
  rcases fin2 (σ 0) with h0 | h0 <;> rcases fin2 (σ 1) with h1 | h1
  · have := σ.injective (h0.trans h1.symm)
    exact absurd this (by decide : (0 : Fin 2) ≠ 1)
  · left
    ext x
    fin_cases x <;> simp [h0, h1]
  · right
    ext x
    fin_cases x <;> simp [h0, h1]
  · have := σ.injective (h0.trans h1.symm)
    exact absurd this (by decide : (0 : Fin 2) ≠ 1)

lemma permanent_fin_two {R : Type*} [CommSemiring R] (M : Matrix (Fin 2) (Fin 2) R) :
    M.permanent = M 0 0 * M 1 1 + M 1 0 * M 0 1 := by
  have hne : (1 : Perm (Fin 2)) ≠ Equiv.swap 0 1 := by
    intro h
    have := congr_fun (congr_arg (fun f : Perm (Fin 2) => (f : Fin 2 → Fin 2)) h) 0
    simp at this
  simp [permanent, univ_perm_fin_two, Fin.prod_univ_two, hne]

lemma a_one : a 1 = 1 := by
  simp [a]

/-- Direct evaluation of C1 at `n = 1`. Primitive 2nd roots are `-1`. -/
theorem conjecture1_of_one {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 2) :
    (sunMatrix 1 ζ).permanent = (a 1 : ℂ) := by
  have hζ' : ζ = -1 := IsPrimitiveRoot.eq_neg_one_of_two_right hζ
  rw [hζ', a_one]
  have hM : sunMatrix 1 (-1) = (1 : Matrix (Fin (2 * 1)) (Fin (2 * 1)) ℂ) := by
    ext i j
    by_cases hij : i = j
    · simp [sunMatrix, hij, Matrix.one_apply]
    · have hpow' : (-1 : ℂ) ^ (i.val - j.val : ℤ) = -1 := by
        have : (i.val - j.val : ℤ) = 1 ∨ (i.val - j.val : ℤ) = -1 := by
          fin_cases i <;> fin_cases j <;> simp_all
        rcases this with h | h <;> simp [h]
      simp [sunMatrix, hij, hpow', Matrix.one_apply_ne hij]
  rw [hM, permanent_one, Nat.cast_one]

/- Arithmetic-geometric sums for roots of unity. -/

lemma geom_sum_eq_zero_of_pow_eq_one {x : ℂ} {m : ℕ} (_hm : 1 < m) (hx1 : x ≠ 1)
    (hxm : x ^ m = 1) : ∑ k ∈ range m, x ^ k = 0 := by
  rw [geom_sum_eq hx1, hxm, sub_self, zero_div]

lemma sum_nat_mul_geom {x : ℂ} {m : ℕ} (hm : 1 < m) (hx1 : x ≠ 1) (hxm : x ^ m = 1) :
    ∑ k ∈ range m, (k : ℂ) * x ^ k = m / (x - 1) := by
  have S := geom_sum_eq_zero_of_pow_eq_one hm hx1 hxm
  set T := ∑ k ∈ range m, (k : ℂ) * x ^ k
  have hxT : x * T = ∑ k ∈ range m, (k : ℂ) * x ^ (k + 1) := by
    simp only [T, mul_sum, pow_succ]
    refine sum_congr rfl fun k _ => ?_
    ring
  have hshift :
      ∑ k ∈ range m, (k : ℂ) * x ^ (k + 1) =
        ∑ j ∈ Icc 1 m, ((j : ℂ) - 1) * x ^ j := by
    refine sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [mem_range, mem_Icc] at hk ⊢
      omega
    · intro a _ha b _hb h
      exact Nat.succ_injective h
    · intro j hj
      simp only [mem_Icc] at hj
      exact ⟨j - 1, by
        simp only [mem_range]
        omega, by omega⟩
    · intro k _hk
      simp
  have hsplit :
      ∑ j ∈ Icc 1 m, ((j : ℂ) - 1) * x ^ j =
        ∑ j ∈ Icc 1 (m - 1), ((j : ℂ) - 1) * x ^ j + ((m : ℂ) - 1) * x ^ m := by
    have hdis : m ∉ Icc 1 (m - 1) := by
      simp only [mem_Icc, not_and, not_le]
      omega
    have hunion : Icc 1 m = insert m (Icc 1 (m - 1)) := by
      ext t
      simp only [mem_insert, mem_Icc]
      omega
    rw [hunion, sum_insert hdis, add_comm]
  have hmid :
      ∑ j ∈ Icc 1 (m - 1), ((j : ℂ) - 1) * x ^ j =
        ∑ j ∈ range m, ((j : ℂ) - 1) * x ^ j + 1 := by
    have h0 : (0 : ℕ) ∉ Icc 1 (m - 1) := by simp
    have : range m = insert 0 (Icc 1 (m - 1)) := by
      ext t
      simp only [mem_range, mem_insert, mem_Icc]
      omega
    rw [this, sum_insert h0]
    simp [sub_mul]
  have hdiff : T - ∑ k ∈ range m, (k : ℂ) * x ^ (k + 1) = -m := by
    rw [hshift, hsplit, hxm, mul_one, hmid]
    have : ∑ j ∈ range m, ((j : ℂ) - 1) * x ^ j =
        T - ∑ j ∈ range m, x ^ j := by
      simp [T, sub_mul, sum_sub_distrib]
    rw [this, S]
    ring
  have hfac : T * (1 - x) = -m := by
    convert hdiff using 1
    rw [← hxT]
    ring
  have hxsub : x - 1 ≠ 0 := sub_ne_zero.2 hx1
  have hmul : T * (x - 1) = m := by
    have hx : x - 1 = -(1 - x) := by ring
    rw [hx, mul_neg, hfac, neg_neg]
  exact eq_div_of_mul_eq hxsub hmul

lemma inv_one_sub_eq_sum {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {k : ℕ} (hk0 : k ≠ 0) (hk : k < N) :
    (1 - ζ ^ k)⁻¹ = -(N : ℂ)⁻¹ * ∑ j ∈ Icc 1 (N - 1), (j : ℂ) * (ζ ^ k) ^ j := by
  have hN : 1 < N := by
    have : 0 < N := Nat.pos_of_neZero N
    omega
  have hx1 : ζ ^ k ≠ 1 := by
    intro h
    have := (hζ.pow_eq_one_iff_dvd k).1 h
    exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk0) hk this
  have hpow : (ζ ^ k) ^ N = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hsum := sum_nat_mul_geom (x := ζ ^ k) hN hx1 hpow
  have heq : (range N).erase 0 = Icc 1 (N - 1) := by
    ext t
    simp only [mem_erase, mem_range, mem_Icc]
    omega
  have hr : ∑ j ∈ range N, (j : ℂ) * (ζ ^ k) ^ j =
      ∑ j ∈ Icc 1 (N - 1), (j : ℂ) * (ζ ^ k) ^ j := by
    have h0 : (0 : ℕ) ∈ range N := mem_range.2 (Nat.pos_of_neZero N)
    let f : ℕ → ℂ := fun j => (j : ℂ) * (ζ ^ k) ^ j
    have hsplit := sum_erase_add (s := range N) (f := f) h0
    have hf0 : f 0 = 0 := by simp [f]
    have : ∑ j ∈ (range N).erase 0, f j = ∑ j ∈ range N, f j := by
      rw [← hsplit, hf0, add_zero]
    rw [heq] at this
    exact this.symm
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hxsub : ζ ^ k - 1 ≠ 0 := sub_ne_zero.2 hx1
  have hsum' : ∑ j ∈ Icc 1 (N - 1), (j : ℂ) * (ζ ^ k) ^ j =
      (N : ℂ) / (ζ ^ k - 1) := by
    rw [← hr, hsum]
  have hneg : (1 - ζ ^ k)⁻¹ = - (ζ ^ k - 1)⁻¹ := by
    have : 1 - ζ ^ k = - (ζ ^ k - 1) := by ring
    rw [this, inv_neg]
  have hinv : (ζ ^ k - 1)⁻¹ =
      (N : ℂ)⁻¹ * ∑ j ∈ Icc 1 (N - 1), (j : ℂ) * (ζ ^ k) ^ j := by
    rw [hsum']
    field_simp [hN0, hxsub]
  rw [hneg, hinv]
  ring

lemma zeta_pow_ne_one_of_lt {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {k : ℕ} (hk0 : k ≠ 0) (hk : k < N) : ζ ^ k ≠ 1 := by
  intro h
  exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk0) hk ((hζ.pow_eq_one_iff_dvd k).1 h)

lemma inv_one_sub_add_inv_one_sub_inv {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {k : ℕ} (hk0 : k ≠ 0) (hk : k < N) :
    (1 - ζ ^ k)⁻¹ + (1 - ζ ^ (N - k))⁻¹ = 1 := by
  have h1 := zeta_pow_ne_one_of_lt hζ hk0 hk
  have hz : ζ ≠ 0 := by
    intro h
    have := hζ.pow_eq_one
    have hN : N ≠ 0 := ne_of_gt (lt_of_le_of_lt (Nat.zero_le k) hk)
    rw [h, zero_pow hN] at this
    exact zero_ne_one this
  have hsum : ζ ^ k * ζ ^ (N - k) = 1 := by
    rw [← pow_add, Nat.add_sub_of_le (le_of_lt hk), hζ.pow_eq_one]
  have hNk : (ζ ^ k)⁻¹ = ζ ^ (N - k) := inv_eq_of_mul_eq_one_right hsum
  have hz0 : ζ ^ k ≠ 0 := pow_ne_zero k hz
  have hz1 : 1 - ζ ^ k ≠ 0 := sub_ne_zero.2 h1.symm
  have hform : 1 - (ζ ^ k)⁻¹ = (ζ ^ k - 1) / ζ ^ k := by
    field_simp [hz0]
  calc
    (1 - ζ ^ k)⁻¹ + (1 - ζ ^ (N - k))⁻¹
        = (1 - ζ ^ k)⁻¹ + (1 - (ζ ^ k)⁻¹)⁻¹ := by rw [hNk]
    _ = (1 - ζ ^ k)⁻¹ + ((ζ ^ k - 1) / ζ ^ k)⁻¹ := by rw [hform]
    _ = (1 - ζ ^ k)⁻¹ + ζ ^ k / (ζ ^ k - 1) := by rw [inv_div]
    _ = (1 - ζ ^ k)⁻¹ + ζ ^ k / -(1 - ζ ^ k) := by ring
    _ = (1 - ζ ^ k)⁻¹ - ζ ^ k / (1 - ζ ^ k) := by
          rw [div_neg]
          ring
    _ = 1 := by field_simp [hz1]

lemma mem_Icc_one_pred_sub {N k : ℕ} (hk : k ∈ Icc 1 (N - 1)) :
    N - k ∈ Icc 1 (N - 1) := by
  simp only [mem_Icc] at hk ⊢
  have hkN : k ≤ N := le_trans hk.2 (Nat.sub_le N 1)
  constructor
  · exact (Nat.le_sub_iff_add_le hkN).mpr (by omega)
  · exact tsub_le_tsub_left hk.1 N

lemma card_Icc_one_pred {N : ℕ} (hN : 1 < N) :
    ((Icc 1 (N - 1)).card : ℂ) = (N - 1 : ℂ) := by
  rw [Nat.card_Icc]
  have : N - 1 + 1 - 1 = N - 1 := by omega
  rw [this, Nat.cast_sub (le_of_lt hN), Nat.cast_one]

lemma sum_inv_one_sub_eq_half {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (hN : 1 < N) :
    ∑ k ∈ Icc 1 (N - 1), (1 - ζ ^ k)⁻¹ = (N - 1 : ℂ) / 2 := by
  have hconst : ∀ k ∈ Icc 1 (N - 1),
      (1 - ζ ^ k)⁻¹ + (1 - ζ ^ (N - k))⁻¹ = 1 := by
    intro k hk
    simp only [mem_Icc] at hk
    exact inv_one_sub_add_inv_one_sub_inv hζ (by omega) (by omega)
  have hpair : ∑ k ∈ Icc 1 (N - 1),
      ((1 - ζ ^ k)⁻¹ + (1 - ζ ^ (N - k))⁻¹) = (N - 1 : ℂ) := by
    rw [sum_congr rfl hconst, sum_const, nsmul_one, card_Icc_one_pred hN]
  have hreindex : ∑ k ∈ Icc 1 (N - 1), (1 - ζ ^ (N - k))⁻¹ =
      ∑ k ∈ Icc 1 (N - 1), (1 - ζ ^ k)⁻¹ := by
    refine sum_bij (fun k _ => N - k) (fun k hk => mem_Icc_one_pred_sub hk) ?_ ?_ ?_
    · intro a ha b hb h
      simp only [mem_Icc] at ha hb
      have haN : a ≤ N := le_trans ha.2 (Nat.sub_le N 1)
      have hbN : b ≤ N := le_trans hb.2 (Nat.sub_le N 1)
      exact (tsub_right_inj haN hbN).1 h
    · intro k hk
      refine ⟨N - k, mem_Icc_one_pred_sub hk, ?_⟩
      simp only [mem_Icc] at hk
      exact Nat.sub_sub_self (le_trans hk.2 (Nat.sub_le N 1))
    · intro _ _
      rfl
  have htwo : 2 * ∑ k ∈ Icc 1 (N - 1), (1 - ζ ^ k)⁻¹ = (N - 1 : ℂ) := by
    calc
      2 * ∑ k ∈ Icc 1 (N - 1), (1 - ζ ^ k)⁻¹
          = ∑ k ∈ Icc 1 (N - 1), (1 - ζ ^ k)⁻¹ +
              ∑ k ∈ Icc 1 (N - 1), (1 - ζ ^ k)⁻¹ := by rw [two_mul]
      _ = ∑ k ∈ Icc 1 (N - 1), (1 - ζ ^ k)⁻¹ +
              ∑ k ∈ Icc 1 (N - 1), (1 - ζ ^ (N - k))⁻¹ := by rw [hreindex]
      _ = ∑ k ∈ Icc 1 (N - 1),
            ((1 - ζ ^ k)⁻¹ + (1 - ζ ^ (N - k))⁻¹) := sum_add_distrib.symm
      _ = (N - 1 : ℂ) := hpair
  exact eq_div_of_mul_eq two_ne_zero (by rw [mul_comm]; exact htwo)

lemma range_eq_insert_zero_Icc {N : ℕ} (hN : 1 < N) :
    range N = insert 0 (Icc 1 (N - 1)) := by
  ext t
  simp only [mem_range, mem_insert, mem_Icc]
  omega

lemma sum_Icc_pow {x : ℂ} {N : ℕ} (hN : 1 < N) (hxN : x ^ N = 1) :
    ∑ k ∈ Icc 1 (N - 1), x ^ k = if x = 1 then (N - 1 : ℂ) else -1 := by
  have h0 : (0 : ℕ) ∉ Icc 1 (N - 1) := by simp
  have hsum : ∑ k ∈ range N, x ^ k = 1 + ∑ k ∈ Icc 1 (N - 1), x ^ k := by
    rw [range_eq_insert_zero_Icc hN, sum_insert h0, pow_zero]
  split_ifs with hx
  · subst hx
    simp [sum_const]
    rw [Nat.cast_sub (le_of_lt hN), Nat.cast_one]
  · have h0sum : ∑ k ∈ range N, x ^ k = 0 :=
      geom_sum_eq_zero_of_pow_eq_one hN hx hxN
    have hadd : 1 + ∑ k ∈ Icc 1 (N - 1), x ^ k = 0 := by rw [← hsum, h0sum]
    rw [add_comm] at hadd
    exact eq_neg_of_add_eq_zero_left hadd

lemma sum_Icc_zeta_pow {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (hN : 1 < N) (m : ℕ) :
    ∑ t ∈ Icc 1 (N - 1), (ζ ^ m) ^ t = if N ∣ m then (N - 1 : ℂ) else -1 := by
  have hxN : (ζ ^ m) ^ N = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  rw [sum_Icc_pow hN hxN]
  simp [hζ.pow_eq_one_iff_dvd]

lemma sum_Icc_cast {N : ℕ} (hN : 1 < N) :
    ∑ k ∈ Icc 1 (N - 1), (k : ℂ) = (N : ℂ) * (N - 1) / 2 := by
  have h0 : (0 : ℕ) ∉ Icc 1 (N - 1) := by simp
  have hsum : ∑ k ∈ range N, (k : ℂ) = ∑ k ∈ Icc 1 (N - 1), (k : ℂ) := by
    rw [range_eq_insert_zero_Icc hN, sum_insert h0]
    simp
  have hnat := congrArg (fun n : ℕ => (n : ℂ)) (sum_range_id_mul_two N)
  simp only [Nat.cast_mul, Nat.cast_two, Nat.cast_sub (le_of_lt hN)] at hnat
  rw [Nat.cast_sum, Nat.cast_one] at hnat
  exact eq_div_of_mul_eq two_ne_zero (by rw [← hsum]; convert hnat using 1)

lemma zpow_neg_mul_eq_pow_sub {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (r : Fin N) (k : ℕ) :
    ζ ^ ((-(r.val : ℤ)) * k) = (ζ ^ (N - r.val)) ^ k := by
  have hz := zeta_ne_zero hζ
  have hr : r.val ≤ N := le_of_lt r.isLt
  have hexp : ((-(r.val : ℤ)) * k) = (N - (r.val : ℤ)) * k - (N : ℤ) * k := by ring
  have hcast : (N : ℤ) - r.val = ((N - r.val : ℕ) : ℤ) := (Nat.cast_sub hr).symm
  have hNk : ζ ^ (N * k) = 1 := by
    rw [pow_mul, hζ.pow_eq_one, one_pow]
  have hL : ζ ^ (((N - r.val : ℕ) : ℤ) * k) = (ζ ^ (N - r.val)) ^ k := by
    rw [← Nat.cast_mul, zpow_natCast, pow_mul]
  have hR : ζ ^ ((N : ℤ) * k) = ζ ^ (N * k) := by
    rw [← Nat.cast_mul, zpow_natCast]
  calc
    ζ ^ ((-(r.val : ℤ)) * k)
        = ζ ^ ((N - (r.val : ℤ)) * k - (N : ℤ) * k) := by rw [hexp]
    _ = ζ ^ (((N - r.val : ℕ) : ℤ) * k - (N : ℤ) * k) := by rw [hcast]
    _ = ζ ^ (((N - r.val : ℕ) : ℤ) * k) / ζ ^ ((N : ℤ) * k) := zpow_sub₀ hz _ _
    _ = (ζ ^ (N - r.val)) ^ k / ζ ^ (N * k) := by rw [hL, hR]
    _ = (ζ ^ (N - r.val)) ^ k := by rw [hNk, div_one]

/-- Zero-diagonal Calogero circulant: off-diagonal `2 / (1 - ζ^{i-j})`. -/
noncomputable def calogero (N : ℕ) (ζ : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => if i = j then 0 else 2 / (1 - ζ ^ (i.val - j.val : ℤ))

lemma calogero_apply_eq {N : ℕ} (ζ : ℂ) (i : Fin N) : calogero N ζ i i = 0 := by
  simp [calogero]

lemma calogero_apply_ne {N : ℕ} {ζ : ℂ} {i j : Fin N} (hij : i ≠ j) :
    calogero N ζ i j = 2 / (1 - ζ ^ (i.val - j.val : ℤ)) := by
  simp [calogero, hij]

lemma eq_of_dvd_of_bounds {N m : ℕ} (hN : 1 < N) (h2 : 2 ≤ m) (hmax : m ≤ 2 * N - 2)
    (hdvd : N ∣ m) : m = N := by
  obtain ⟨t, rfl⟩ := hdvd
  have : t = 1 := by
    have hpos : t ≠ 0 := by
      rintro rfl
      simp at h2
    have hle1 : t ≤ 1 := by
      by_contra ht
      have : 2 ≤ t := by omega
      have hmul : N * 2 ≤ N * t := Nat.mul_le_mul_left N this
      have : 2 * N ≤ 2 * N - 2 := by
        rw [mul_comm N 2] at hmul
        exact le_trans hmul hmax
      omega
    omega
  simp [this]

lemma dvd_add_sub_iff {N j r : ℕ} (hN : 1 < N) (hj1 : 1 ≤ j) (hj : j < N)
    (hr0 : 0 < r) (hr : r < N) :
    N ∣ j + (N - r) ↔ j = r := by
  have hle : r ≤ N := le_of_lt hr
  constructor
  · intro h
    have h2 : 2 ≤ j + (N - r) := by omega
    have hmax : j + (N - r) ≤ 2 * N - 2 := by omega
    have hm : j + (N - r) = N := eq_of_dvd_of_bounds hN h2 hmax h
    omega
  · intro h
    subst h
    simp [Nat.add_sub_of_le hle]

lemma sum_cast_mul_ite {N r : ℕ} (hr : r ∈ Icc 1 (N - 1)) :
    ∑ j ∈ Icc 1 (N - 1), (j : ℂ) * (if j = r then (N - 1 : ℂ) else -1) =
      -∑ j ∈ Icc 1 (N - 1), (j : ℂ) + (r : ℂ) * N := by
  have hsplit :=
    (sum_erase_add (s := Icc 1 (N - 1))
      (f := fun j => (j : ℂ) * (if j = r then (N - 1 : ℂ) else (-1 : ℂ))) hr).symm
  have herase :
      ∑ j ∈ (Icc 1 (N - 1)).erase r,
          (j : ℂ) * (if j = r then (N - 1 : ℂ) else -1) =
        ∑ j ∈ (Icc 1 (N - 1)).erase r, -(j : ℂ) := by
    refine sum_congr rfl fun j hj => ?_
    have : j ≠ r := (mem_erase.mp hj).1
    simp [this]
  have hsum :
      ∑ j ∈ Icc 1 (N - 1), (j : ℂ) =
        ∑ j ∈ (Icc 1 (N - 1)).erase r, (j : ℂ) + r := by
    simpa using
      (sum_erase_add (s := Icc 1 (N - 1)) (f := fun j => (j : ℂ)) hr).symm
  calc
    ∑ j ∈ Icc 1 (N - 1), (j : ℂ) * (if j = r then (N - 1 : ℂ) else -1)
        = ∑ j ∈ (Icc 1 (N - 1)).erase r,
              (j : ℂ) * (if j = r then (N - 1 : ℂ) else -1) +
            (r : ℂ) * (if r = r then (N - 1 : ℂ) else -1) := hsplit
    _ = ∑ j ∈ (Icc 1 (N - 1)).erase r, -(j : ℂ) + (r : ℂ) * (N - 1) := by
          rw [herase, if_pos rfl]
    _ = -∑ j ∈ (Icc 1 (N - 1)).erase r, (j : ℂ) + (r : ℂ) * (N - 1) := by
          rw [sum_neg_distrib]
    _ = -(∑ j ∈ Icc 1 (N - 1), (j : ℂ) - r) + (r : ℂ) * (N - 1) := by
          rw [hsum]; ring
    _ = -∑ j ∈ Icc 1 (N - 1), (j : ℂ) + (r : ℂ) * N := by ring

/-- Eigenvalue `N - 1 - 2 r` of the Calogero circulant, as a kernel sum. -/
lemma calogero_kernel_sum {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (hN : 1 < N) (r : Fin N) :
    ∑ k ∈ Icc 1 (N - 1), 2 * ζ ^ ((-(r.val : ℤ)) * k) * (1 - ζ ^ k)⁻¹ =
      (N : ℂ) - 1 - 2 * r.val := by
  by_cases hr : r = 0
  · subst hr
    simp [neg_zero, zero_mul, ← mul_sum]
    rw [sum_inv_one_sub_eq_half hζ hN]
    ring
  · have hr0 : r.val ≠ 0 := fun h => hr (Fin.ext h)
    have hrpos : 0 < r.val := Nat.pos_of_ne_zero hr0
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
    have hterm :
        ∑ k ∈ Icc 1 (N - 1), 2 * ζ ^ ((-(r.val : ℤ)) * k) * (1 - ζ ^ k)⁻¹ =
          2 * ∑ k ∈ Icc 1 (N - 1),
            (ζ ^ (N - r.val)) ^ k * (1 - ζ ^ k)⁻¹ := by
      have hpt : ∀ k ∈ Icc 1 (N - 1),
          2 * ζ ^ ((-(r.val : ℤ)) * k) * (1 - ζ ^ k)⁻¹ =
            2 * ((ζ ^ (N - r.val)) ^ k * (1 - ζ ^ k)⁻¹) := by
        intro k _
        rw [zpow_neg_mul_eq_pow_sub hζ r k]
        ring
      rw [sum_congr rfl hpt, mul_sum]
    rw [hterm]
    have hinv : ∀ k ∈ Icc 1 (N - 1),
        (1 - ζ ^ k)⁻¹ =
          -(N : ℂ)⁻¹ * ∑ j ∈ Icc 1 (N - 1), (j : ℂ) * (ζ ^ k) ^ j := by
      intro k hk
      simp only [mem_Icc] at hk
      exact inv_one_sub_eq_sum hζ (by omega) (by omega)
    have hswap :
        ∑ k ∈ Icc 1 (N - 1), (ζ ^ (N - r.val)) ^ k * (1 - ζ ^ k)⁻¹ =
          -(N : ℂ)⁻¹ * ∑ j ∈ Icc 1 (N - 1), (j : ℂ) *
            ∑ t ∈ Icc 1 (N - 1), (ζ ^ (j + (N - r.val))) ^ t := by
      have h1 :
          ∑ k ∈ Icc 1 (N - 1), (ζ ^ (N - r.val)) ^ k * (1 - ζ ^ k)⁻¹ =
            ∑ k ∈ Icc 1 (N - 1), (ζ ^ (N - r.val)) ^ k *
              (-(N : ℂ)⁻¹ * ∑ j ∈ Icc 1 (N - 1), (j : ℂ) * (ζ ^ k) ^ j) :=
        sum_congr rfl fun k hk => by rw [hinv k hk]
      rw [h1]
      have hpt : ∀ k ∈ Icc 1 (N - 1),
          (ζ ^ (N - r.val)) ^ k *
              (-(N : ℂ)⁻¹ * ∑ j ∈ Icc 1 (N - 1), (j : ℂ) * (ζ ^ k) ^ j) =
            -(N : ℂ)⁻¹ * ∑ j ∈ Icc 1 (N - 1),
              (j : ℂ) * ((ζ ^ (N - r.val)) ^ k * (ζ ^ k) ^ j) := by
        intro k _
        simp [mul_sum, mul_left_comm]
      rw [sum_congr rfl hpt, ← mul_sum, sum_comm]
      refine congrArg _ (sum_congr rfl fun j _ => ?_)
      rw [mul_sum]
      refine sum_congr rfl fun t _ => ?_
      have : (ζ ^ (N - r.val)) ^ t * (ζ ^ t) ^ j =
          (ζ ^ (j + (N - r.val))) ^ t := by
        rw [pow_right_comm, ← pow_add, add_comm, pow_right_comm]
      rw [this]
    rw [hswap]
    have hgeom : ∀ j ∈ Icc 1 (N - 1),
        ∑ t ∈ Icc 1 (N - 1), (ζ ^ (j + (N - r.val))) ^ t =
          if j = r.val then (N - 1 : ℂ) else -1 := by
      intro j hj
      simp only [mem_Icc] at hj
      have hjlt : j < N := lt_of_le_of_lt hj.2 (Nat.sub_lt (Nat.pos_of_neZero N) (by omega))
      have hiff := dvd_add_sub_iff hN hj.1 hjlt hrpos r.isLt
      rw [sum_Icc_zeta_pow hζ hN]
      simp [hiff]
    have hr_mem : r.val ∈ Icc 1 (N - 1) := by
      simp only [mem_Icc]
      omega
    have hsumj :
        ∑ j ∈ Icc 1 (N - 1), (j : ℂ) *
            ∑ t ∈ Icc 1 (N - 1), (ζ ^ (j + (N - r.val))) ^ t =
          -∑ j ∈ Icc 1 (N - 1), (j : ℂ) + (r.val : ℂ) * N := by
      rw [sum_congr rfl fun j hj => congrArg _ (hgeom j hj)]
      exact sum_cast_mul_ite hr_mem
    rw [hsumj, sum_Icc_cast hN]
    field_simp [hN0]
    ring

lemma zeta_pow_fin_injective {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) :
    Function.Injective (fun i : Fin N => ζ ^ i.val) := by
  intro i j h
  exact Fin.ext (hζ.pow_inj i.isLt j.isLt h)

noncomputable def fourierMatrix (N : ℕ) (ζ : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  vandermonde (fun i : Fin N => ζ ^ i.val)

lemma det_fourierMatrix_ne_zero {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) :
    (fourierMatrix N ζ).det ≠ 0 := by
  rw [fourierMatrix, det_vandermonde_ne_zero_iff]
  exact zeta_pow_fin_injective hζ

lemma zeta_pow_div {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (i j : Fin N) : ζ ^ (i - j).val = ζ ^ i.val / ζ ^ j.val := by
  rw [← zpow_int_val_sub hζ, zpow_sub₀ (zeta_ne_zero hζ), zpow_natCast, zpow_natCast]

lemma pow_mul_val_sub {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (r i k : Fin N) :
    ζ ^ (r.val * (i - k).val) =
      ζ ^ (r.val * i.val) * ζ ^ ((-(r.val : ℤ)) * k.val) := by
  have hz := zeta_ne_zero hζ
  have hrk : ζ ^ ((-(r.val : ℤ)) * k.val) = ((ζ ^ k.val) ^ r.val)⁻¹ := by
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [← pow_mul, ← zpow_natCast, ← zpow_add₀ hz]
    have hsum : ((k.val * r.val : ℕ) : ℤ) + ((-(r.val : ℤ)) * k.val) = 0 := by
      push_cast
      ring
    rw [hsum, zpow_zero]
  have hri : (ζ ^ i.val) ^ r.val = ζ ^ (r.val * i.val) := by
    rw [← pow_mul, mul_comm]
  calc
    ζ ^ (r.val * (i - k).val)
        = (ζ ^ (i - k).val) ^ r.val := by rw [mul_comm r.val, pow_mul]
    _ = (ζ ^ i.val / ζ ^ k.val) ^ r.val := by rw [zeta_pow_div hζ]
    _ = (ζ ^ i.val) ^ r.val / (ζ ^ k.val) ^ r.val := div_pow _ _ _
    _ = ζ ^ (r.val * i.val) * ζ ^ ((-(r.val : ℤ)) * k.val) := by
          rw [hri, hrk, div_eq_mul_inv]

lemma fin_ne_sub {N : ℕ} [NeZero N] {i k : Fin N} (hk : k ≠ 0) : i ≠ i - k := by
  intro h
  apply hk
  have h' : i - i = i - (i - k) := congrArg (fun x : Fin N => i - x) h
  rw [sub_self, sub_sub_cancel] at h'
  exact h'.symm

lemma sum_fin_offzero {N : ℕ} [NeZero N] (f : ℕ → ℂ) :
    ∑ k : Fin N, (if k = 0 then (0 : ℂ) else f k.val) = ∑ k ∈ Icc 1 (N - 1), f k := by
  have h0 : (0 : Fin N) ∈ (univ : Finset (Fin N)) := mem_univ _
  rw [← sum_erase_add (s := (univ : Finset (Fin N)))
        (f := fun k : Fin N => if k = 0 then (0 : ℂ) else f k.val) h0]
  have hzero :
      (if (0 : Fin N) = 0 then (0 : ℂ) else f (0 : Fin N).val) = 0 := if_pos rfl
  rw [hzero, add_zero]
  refine sum_bij (fun (k : Fin N) (_ : k ∈ univ.erase 0) => k.val) ?_ ?_ ?_ ?_
  · intro k hk
    have hk0 : k ≠ 0 := (mem_erase.mp hk).1
    have hkval : k.val ≠ 0 := fun h => hk0 (Fin.ext h)
    simp only [mem_Icc]
    exact ⟨Nat.pos_of_ne_zero hkval, Nat.le_pred_of_lt k.isLt⟩
  · intro a _ b _ h
    exact Fin.ext h
  · intro t ht
    simp only [mem_Icc] at ht
    have htN : t < N :=
      lt_of_le_of_lt ht.2 (Nat.sub_lt (Nat.pos_of_neZero N) Nat.zero_lt_one)
    have ht0 : t ≠ 0 := Nat.ne_zero_of_lt ht.1
    refine ⟨⟨t, htN⟩, ?_, rfl⟩
    refine mem_erase.2 ⟨?_, mem_univ _⟩
    intro h
    exact ht0 (congrArg Fin.val h)
  · intro k hk
    have hk0 : k ≠ 0 := (mem_erase.mp hk).1
    simp [hk0]

lemma calogero_mulVec {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (hN : 1 < N) (r i : Fin N) :
    (calogero N ζ).mulVec (fun j => ζ ^ (r.val * j.val)) i =
      ((N : ℂ) - 1 - 2 * r.val) * ζ ^ (r.val * i.val) := by
  have hre :
      (calogero N ζ).mulVec (fun j => ζ ^ (r.val * j.val)) i =
        ∑ k : Fin N, calogero N ζ i (i - k) * ζ ^ (r.val * (i - k).val) := by
    rw [mulVec, dotProduct]
    exact (Fintype.sum_equiv (Equiv.subLeft i)
      (fun k => calogero N ζ i (i - k) * ζ ^ (r.val * (i - k).val))
      (fun j => calogero N ζ i j * ζ ^ (r.val * j.val))
      (fun k => by simp [Equiv.subLeft_apply])).symm
  rw [hre]
  have hpt : ∀ k : Fin N,
      calogero N ζ i (i - k) * ζ ^ (r.val * (i - k).val) =
        (if k = 0 then (0 : ℂ)
          else 2 * ζ ^ ((-(r.val : ℤ)) * k.val) * (1 - ζ ^ k.val)⁻¹) *
          ζ ^ (r.val * i.val) := by
    intro k
    by_cases hk0 : k = 0
    · subst hk0
      simp [calogero_apply_eq, sub_zero]
    · have hik := fin_ne_sub (i := i) hk0
      rw [calogero_apply_ne hik, pow_mul_val_sub hζ r i k]
      have hzpow : ζ ^ (i.val - (i - k).val : ℤ) = ζ ^ k.val := by
        rw [zpow_int_val_sub hζ, sub_sub_cancel]
      rw [hzpow, div_eq_mul_inv, if_neg hk0]
      ring
  rw [sum_congr rfl fun k _ => hpt k, ← sum_mul,
    sum_fin_offzero (fun k =>
      2 * ζ ^ ((-(r.val : ℤ)) * k) * (1 - ζ ^ k)⁻¹),
    calogero_kernel_sum hζ hN r]

lemma fourier_pow (N : ℕ) (ζ : ℂ) (j r : Fin N) :
    (ζ ^ j.val) ^ r.val = ζ ^ (r.val * j.val) := by
  rw [← pow_mul, mul_comm]

lemma calogero_mul_fourier {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (hN : 1 < N) :
    calogero N ζ * fourierMatrix N ζ =
      fourierMatrix N ζ * diagonal fun r : Fin N => (N : ℂ) - 1 - 2 * r.val := by
  ext i r
  have hvec := calogero_mulVec hζ hN r i
  calc
    (calogero N ζ * fourierMatrix N ζ) i r
        = ∑ j, calogero N ζ i j * fourierMatrix N ζ j r := mul_apply
    _ = ∑ j, calogero N ζ i j * ζ ^ (r.val * j.val) := by
          simp [fourierMatrix, vandermonde_apply, fourier_pow]
    _ = (calogero N ζ).mulVec (fun j => ζ ^ (r.val * j.val)) i := rfl
    _ = ((N : ℂ) - 1 - 2 * r.val) * ζ ^ (r.val * i.val) := hvec
    _ = fourierMatrix N ζ i r * ((N : ℂ) - 1 - 2 * r.val) := by
          simp [fourierMatrix, vandermonde_apply, fourier_pow, mul_comm]
    _ = (fourierMatrix N ζ *
          diagonal fun t : Fin N => (N : ℂ) - 1 - 2 * t.val) i r :=
          (mul_diagonal (fun t : Fin N => (N : ℂ) - 1 - 2 * t.val)
            (fourierMatrix N ζ) i r).symm

lemma prod_odd_cast {n : ℕ} :
    ∏ k ∈ range n, (2 * k + 1 : ℂ) =
      ∏ k ∈ range n, ((2 * k + 1 : ℕ) : ℂ) := by
  refine prod_congr rfl fun k _ => ?_
  simp [Nat.cast_add, Nat.cast_mul, Nat.cast_one]

lemma prod_calogero_eigenvalues (n : ℕ) :
    ∏ r : Fin (2 * n), (((2 * n : ℕ) : ℂ) - 1 - 2 * r.val) =
      (-1 : ℂ) ^ n * a n := by
  rw [Fin.prod_univ_eq_prod_range (fun k => ((2 * n : ℕ) : ℂ) - 1 - 2 * k) (2 * n)]
  rw [show range (2 * n) = range (n + n) from by rw [two_mul]]
  rw [prod_range_add]
  have hpos :
      ∏ k ∈ range n, (((2 * n : ℕ) : ℂ) - 1 - 2 * k) =
        ∏ k ∈ range n, (2 * k + 1 : ℂ) := by
    have hcast : ∀ k ∈ range n,
        (((2 * n : ℕ) : ℂ) - 1 - 2 * k) =
          (2 : ℂ) * ((n - 1 - k : ℕ) : ℂ) + 1 := by
      intro k hk
      simp only [mem_range] at hk
      have hle : k + 1 ≤ n := Nat.succ_le_of_lt hk
      have hnk : ((n - 1 - k : ℕ) : ℂ) = (n : ℂ) - 1 - k := by
        have : n - 1 - k = n - (k + 1) := by omega
        rw [this, Nat.cast_sub hle, Nat.cast_add, Nat.cast_one]
        ring
      rw [hnk, Nat.cast_mul, Nat.cast_two]
      ring
    rw [prod_congr rfl hcast]
    exact prod_range_reflect (fun k => (2 * k + 1 : ℂ)) n
  have hneg :
      ∏ k ∈ range n, (((2 * n : ℕ) : ℂ) - 1 - 2 * ((n + k : ℕ) : ℂ)) =
        (-1 : ℂ) ^ n * ∏ k ∈ range n, (2 * k + 1 : ℂ) := by
    have hpt : ∀ k ∈ range n,
        (((2 * n : ℕ) : ℂ) - 1 - 2 * ((n + k : ℕ) : ℂ)) =
          -((2 * k + 1 : ℂ)) := by
      intro k _
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_two]
      ring
    rw [prod_congr rfl hpt, prod_neg, card_range]
  rw [hpos, hneg, prod_odd_cast, a, Nat.cast_pow, Nat.cast_prod]
  ring

lemma det_calogero {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 * n)) :
    (calogero (2 * n) ζ).det = (-1 : ℂ) ^ n * a n := by
  have : NeZero (2 * n) := ⟨by omega⟩
  have hN : 1 < 2 * n := by omega
  have hF := det_fourierMatrix_ne_zero (N := 2 * n) hζ
  have hdet := congrArg det (calogero_mul_fourier (N := 2 * n) hζ hN)
  rw [det_mul, det_mul, det_diagonal, mul_comm (fourierMatrix (2 * n) ζ).det] at hdet
  rw [← prod_calogero_eigenvalues n]
  exact mul_right_cancel₀ hF hdet

lemma prod_zpow_eq_zpow_sum {ι : Type*} [DecidableEq ι] {ζ : ℂ} (hz : ζ ≠ 0)
    (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, ζ ^ f i = ζ ^ ∑ i ∈ s, f i := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, zpow_add₀ hz, ih]

lemma sum_val_perm {N : ℕ} (σ : Perm (Fin N)) :
    ∑ i : Fin N, ((σ i).val : ℤ) = ∑ i : Fin N, (i.val : ℤ) :=
  Fintype.sum_equiv σ (fun i : Fin N => ((σ i).val : ℤ))
    (fun i : Fin N => (i.val : ℤ)) fun _ => rfl

lemma prod_zeta_perm {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (σ : Perm (Fin N)) :
    ∏ i, ζ ^ ((σ i).val - i.val : ℤ) = 1 := by
  have hz := zeta_ne_zero hζ
  have hsum : ∑ i : Fin N, ((σ i).val - i.val : ℤ) = 0 := by
    simp [sum_sub_distrib, sum_val_perm σ]
  rw [prod_zpow_eq_zpow_sum hz (univ : Finset (Fin N))
      (fun i => ((σ i).val - i.val : ℤ)), hsum, zpow_zero]

lemma one_add_div_eq_neg_one_add_two_div {z : ℂ} (hz : 1 - z ≠ 0) :
    (1 + z) / (1 - z) = -1 + 2 / (1 - z) := by
  field_simp [hz]
  ring

lemma one_add_div_sub_one {z : ℂ} (hz : 1 - z ≠ 0) :
    (1 + z) / (1 - z) - 1 = 2 * z / (1 - z) := by
  field_simp [hz]
  ring

noncomputable def allOnes (N : ℕ) : Matrix (Fin N) (Fin N) ℂ := fun _ _ => 1

lemma sunMatrix_sub_ones_diag {n : ℕ} (ζ : ℂ) (i : Fin (2 * n)) :
    (sunMatrix n ζ - allOnes (2 * n)) i i = 0 := by
  simp [sunMatrix, allOnes, Matrix.sub_apply]

lemma sunMatrix_sub_ones_off {n : ℕ} [NeZero n] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 * n))
    {i j : Fin (2 * n)} (hij : i ≠ j) :
    (sunMatrix n ζ - allOnes (2 * n)) i j =
      2 * ζ ^ (i.val - j.val : ℤ) / (1 - ζ ^ (i.val - j.val : ℤ)) := by
  have hden := denom_ne_zero (N := 2 * n) hζ hij
  have hM := sunMatrix_apply_ne (n := n) hζ hij
  simp [allOnes, Matrix.sub_apply, hM]
  exact one_add_div_sub_one hden

lemma prod_eq_zero_of_fixed {N : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin N) (Fin N) R) (hdiag : ∀ i, M i i = 0) {σ : Perm (Fin N)}
    (hfix : ∃ i, σ i = i) : ∏ i, M (σ i) i = 0 := by
  obtain ⟨i, hi⟩ := hfix
  exact prod_eq_zero (mem_univ i) (by simp [hi, hdiag i])

lemma permanent_of_zero_diag {N : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin N) (Fin N) R) (hdiag : ∀ i, M i i = 0) :
    M.permanent =
      ∑ σ : Perm (Fin N),
        if (∀ i, σ i ≠ i) then ∏ i, M (σ i) i else 0 := by
  refine sum_congr rfl fun σ _ => ?_
  by_cases h : ∀ i, σ i ≠ i
  · simp [h]
  · simp [h]
    exact prod_eq_zero_of_fixed M hdiag (by simpa using h)

lemma det_of_zero_diag {N : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin N) (Fin N) R) (hdiag : ∀ i, M i i = 0) :
    M.det =
      ∑ σ : Perm (Fin N),
        if (∀ i, σ i ≠ i) then (Perm.sign σ : R) * ∏ i, M (σ i) i else 0 := by
  rw [det_apply']
  refine sum_congr rfl fun σ _ => ?_
  by_cases h : ∀ i, σ i ≠ i
  · simp [h]
  · have hz : ∏ i, M (σ i) i = 0 :=
      prod_eq_zero_of_fixed M hdiag (by simpa using h)
    simp [h, hz]

lemma calogero_prod_of_derangement {N : ℕ} [NeZero N] {ζ : ℂ}
    {σ : Perm (Fin N)} (hder : ∀ i, σ i ≠ i) :
    ∏ i, calogero N ζ (σ i) i =
      (2 : ℂ) ^ N * ∏ i, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹ := by
  have hpt : ∀ i, calogero N ζ (σ i) i =
      2 * (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹ := by
    intro i
    rw [calogero_apply_ne (hder i), div_eq_mul_inv]
  simp_rw [hpt]
  rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]

lemma det_calogero_eq_signed_sum {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ}
    (_hζ : IsPrimitiveRoot ζ (2 * n)) :
    (calogero (2 * n) ζ).det =
      (2 : ℂ) ^ (2 * n) *
        ∑ σ : Perm (Fin (2 * n)),
          if (∀ i, σ i ≠ i) then
            (Perm.sign σ : ℂ) * ∏ i, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
          else 0 := by
  have : NeZero (2 * n) := ⟨by omega⟩
  have hdiag : ∀ i : Fin (2 * n), calogero (2 * n) ζ i i = 0 := fun i =>
    calogero_apply_eq _ _
  rw [det_of_zero_diag _ hdiag]
  have hterm : ∀ σ : Perm (Fin (2 * n)),
      (if (∀ i, σ i ≠ i) then
          (Perm.sign σ : ℂ) * ∏ i, calogero (2 * n) ζ (σ i) i
        else 0) =
        (2 : ℂ) ^ (2 * n) *
          (if (∀ i, σ i ≠ i) then
            (Perm.sign σ : ℂ) * ∏ i, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
          else 0) := by
    intro σ
    split_ifs with h
    · rw [calogero_prod_of_derangement (N := 2 * n) h]
      ring
    · simp
  simp_rw [hterm, ← mul_sum]

lemma sunMatrix_sub_ones_prod_of_derangement {n : ℕ} [NeZero n] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n)) {σ : Perm (Fin (2 * n))}
    (hder : ∀ i, σ i ≠ i) :
    ∏ i, (sunMatrix n ζ - allOnes (2 * n)) (σ i) i =
      (2 : ℂ) ^ (2 * n) * ∏ i, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹ := by
  have hpt : ∀ i, (sunMatrix n ζ - allOnes (2 * n)) (σ i) i =
      2 * ζ ^ ((σ i).val - i.val : ℤ) *
        (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹ := by
    intro i
    rw [sunMatrix_sub_ones_off hζ (hder i), div_eq_mul_inv]
  simp_rw [hpt]
  rw [prod_mul_distrib, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin,
    prod_zeta_perm (N := 2 * n) hζ]
  ring

lemma permanent_sunMatrix_sub_ones {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n)) :
    (sunMatrix n ζ - allOnes (2 * n)).permanent =
      (2 : ℂ) ^ (2 * n) *
        ∑ σ : Perm (Fin (2 * n)),
          if (∀ i, σ i ≠ i) then
            ∏ i, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
          else 0 := by
  have : NeZero n := ⟨by omega⟩
  have hdiag : ∀ i : Fin (2 * n), (sunMatrix n ζ - allOnes (2 * n)) i i = 0 :=
    fun i => sunMatrix_sub_ones_diag ζ i
  rw [permanent_of_zero_diag _ hdiag]
  have hterm : ∀ σ : Perm (Fin (2 * n)),
      (if (∀ i, σ i ≠ i) then
          ∏ i, (sunMatrix n ζ - allOnes (2 * n)) (σ i) i
        else 0) =
        (2 : ℂ) ^ (2 * n) *
          (if (∀ i, σ i ≠ i) then
            ∏ i, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
          else 0) := by
    intro σ
    split_ifs with h
    · exact sunMatrix_sub_ones_prod_of_derangement hζ h
    · simp
  simp_rw [hterm, ← mul_sum]

lemma signed_derangement_inv_sum {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n)) :
    (∑ σ : Perm (Fin (2 * n)),
        if (∀ i, σ i ≠ i) then
          (Perm.sign σ : ℂ) * ∏ i, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
        else 0) =
      (-1 : ℂ) ^ n * a n / (2 : ℂ) ^ (2 * n) := by
  have hdet := det_calogero hn hζ
  have hsum := det_calogero_eq_signed_sum hn hζ
  have h2 : (2 : ℂ) ^ (2 * n) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [hdet] at hsum
  exact eq_div_of_mul_eq h2 (by rw [mul_comm]; exact hsum.symm)

/-- Guo–Li–Tao–Wei Lemma 3.1 weight along the support of `σ`. -/
noncomputable def cycleEdgeWeight {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) (σ : Perm α) : ℂ :=
  ∏ i ∈ σ.support, (x (σ i) - x i)⁻¹

/-- Two opposite 3-cycles cancel. This is the length-3 case of Guo Lemma 3.1. -/
lemma two_three_cycles_cancel {x y z : ℂ} (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x) :
    (y - x)⁻¹ * (z - y)⁻¹ * (x - z)⁻¹ +
      (z - x)⁻¹ * (y - z)⁻¹ * (x - y)⁻¹ = 0 := by
  have hyx : y - x ≠ 0 := sub_ne_zero.2 hxy.symm
  have hzy : z - y ≠ 0 := sub_ne_zero.2 hyz.symm
  have hxz : x - z ≠ 0 := sub_ne_zero.2 hzx.symm
  have hzx' : z - x ≠ 0 := sub_ne_zero.2 hzx
  have hyz' : y - z ≠ 0 := sub_ne_zero.2 hyz
  have hxy' : x - y ≠ 0 := sub_ne_zero.2 hxy
  field_simp [hyx, hzy, hxz, hzx', hyz', hxy']
  ring

lemma inv_sub_sub_eq {R : Type*} [Field R] (w y z : R) (hy : w ≠ y) (hz : w ≠ z) :
    (z - y) / ((w - y) * (z - w)) = (w - y)⁻¹ - (w - z)⁻¹ := by
  have h1 : w - y ≠ 0 := sub_ne_zero.2 hy
  have h2 : w - z ≠ 0 := sub_ne_zero.2 hz
  have h3 : z - w ≠ 0 := sub_ne_zero.2 hz.symm
  field_simp [h1, h2, h3]
  ring

/-- Insertion kernel along a cycle of the remaining points. The sum telescopes. -/
lemma sum_insert_kernel {m : ℕ} [NeZero m] (w : ℂ) (z : Fin m → ℂ)
    (hw : ∀ k, w ≠ z k) :
    ∑ k : Fin m, (z (k + 1) - z k) / ((w - z k) * (z (k + 1) - w)) = 0 := by
  have hterm : ∀ k, (z (k + 1) - z k) / ((w - z k) * (z (k + 1) - w)) =
      (w - z k)⁻¹ - (w - z (k + 1))⁻¹ := fun k =>
    inv_sub_sub_eq w (z k) (z (k + 1)) (hw k) (hw (k + 1))
  simp_rw [hterm]
  rw [sum_sub_distrib]
  have hperm :
      ∑ k : Fin m, (w - z (k + 1))⁻¹ = ∑ k : Fin m, (w - z k)⁻¹ :=
    Fintype.sum_equiv (Equiv.addRight (1 : Fin m))
      (fun k => (w - z (k + 1))⁻¹) (fun k => (w - z k)⁻¹) (fun _ => rfl)
  rw [hperm, sub_self]

lemma prod_toFinset_getElem {α : Type*} [DecidableEq α] {R : Type*} [CommMonoid R]
    {l : List α} (hl : l.Nodup) (g : α → R) :
    ∏ a ∈ l.toFinset, g a = ∏ i : Fin l.length, g (l[i.val]) := by
  refine (prod_bij (fun (i : Fin l.length) (_ : i ∈ univ) => l[i.val]) ?_ ?_ ?_ ?_).symm
  · intro i _
    simp
  · intro i _ j _ h
    exact Fin.ext (List.Nodup.getElem_inj_iff hl |>.mp h)
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp ha)
    exact ⟨⟨i, hi⟩, mem_univ _, rfl⟩
  · intro i _
    rfl

lemma prod_fin_eq_prod_range {n : ℕ} (f : Fin n → ℂ) :
    ∏ i, f i = ∏ i ∈ (range n).attach, f ⟨i.1, mem_range.mp i.2⟩ := by
  refine prod_bij (fun (i : Fin n) _ => ⟨i.val, mem_range.mpr i.isLt⟩) ?_ ?_ ?_ ?_
  · intro i _
    simp
  · intro i _ j _ h
    exact Fin.ext (congrArg Subtype.val h)
  · intro a _
    exact ⟨⟨a.1, mem_range.mp a.2⟩, mem_univ _, rfl⟩
  · intro i _
    rfl

lemma cycleEdgeWeight_formPerm {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {l : List α} (hl : l.Nodup) (h2 : 2 ≤ l.length) :
    cycleEdgeWeight x l.formPerm =
      ∏ i : Fin l.length,
        (x (l[(i.val + 1) % l.length]'(Nat.mod_lt _ (by omega))) - x (l[i.val]))⁻¹ := by
  have hne : ∀ a : α, l ≠ [a] := by
    intro a h
    simp [h] at h2
  rw [cycleEdgeWeight, List.support_formPerm_of_nodup l hl hne,
    prod_toFinset_getElem hl]
  refine prod_congr rfl fun i _ => ?_
  rw [List.formPerm_apply_getElem l hl i.val i.isLt]

lemma cycleEdgeWeight_mul_disjoint {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {σ τ : Perm α} (h : Equiv.Perm.Disjoint σ τ) :
    cycleEdgeWeight x (σ * τ) = cycleEdgeWeight x σ * cycleEdgeWeight x τ := by
  simp only [cycleEdgeWeight]
  rw [h.support_mul, prod_union h.disjoint_support]
  refine congr_arg₂ (· * ·) ?_ ?_
  · refine prod_congr rfl fun a ha => ?_
    have hτ : τ a = a := Equiv.Perm.notMem_support.mp (h.mem_imp ha)
    simp [hτ]
  · refine prod_congr rfl fun a ha => ?_
    have hσa : σ (τ a) = τ a := by
      have : τ a ∈ τ.support := (Equiv.Perm.apply_mem_support (f := τ)).2 ha
      exact Equiv.Perm.notMem_support.mp (h.symm.mem_imp this)
    simp [hσa]

lemma getElem_rotate_zero {α : Type*} (L : List α) {k : ℕ} (_hk : k < L.length) :
    (L.rotate k)[0]'(by simp [List.length_rotate]; omega) = L[k] := by
  simp [List.getElem_rotate, Nat.mod_eq_of_lt _hk]

lemma getElem_rotate_last {α : Type*} (L : List α) {k : ℕ}
    (h2 : 2 ≤ L.length) (_hk : k < L.length) :
    (L.rotate k)[L.length - 1]'(by simp [List.length_rotate]; omega) =
      L[(k + (L.length - 1)) % L.length]'(Nat.mod_lt _ (by omega)) := by
  have hlt : L.length - 1 < (L.rotate k).length := by
    simp [List.length_rotate]; omega
  rw [List.getElem_rotate (h := hlt), Nat.add_comm]

lemma formPerm_cons_apply_head {α : Type*} [DecidableEq α] {p : α} {L : List α}
    (hl : (p :: L).Nodup) (hLpos : 1 ≤ L.length) :
    (p :: L).formPerm p = L[0]'(by omega) := by
  have hlen : 1 < (p :: L).length := by simp; omega
  simpa using List.formPerm_apply_getElem_zero (p :: L) hl hlen

lemma getLast_cons_eq {α : Type*} {p : α} {L : List α} (hLne : L ≠ []) :
    (p :: L).getLast (List.cons_ne_nil p L) = L.getLast hLne := by
  cases L with
  | nil => contradiction
  | cons _ _ => rfl

lemma formPerm_cons_apply_getLast {α : Type*} [DecidableEq α] {p : α} {L : List α}
    (hLne : L ≠ []) :
    (p :: L).formPerm (L.getLast hLne) = p := by
  simpa [getLast_cons_eq hLne] using List.formPerm_apply_getLast p L

lemma formPerm_apply_getLast_eq_head {α : Type*} [DecidableEq α] {L : List α}
    (hL : L.Nodup) (hLne : L ≠ []) (h2 : 2 ≤ L.length) :
    L.formPerm (L.getLast hLne) = L[0]'(by omega) := by
  rw [List.getLast_eq_getElem, List.formPerm_apply_getElem L hL]
  have hmod : (L.length - 1 + 1) % L.length = 0 := by
    rw [Nat.sub_add_cancel (show 1 ≤ L.length by omega), Nat.mod_self]
  simp [hmod]

lemma formPerm_cons_apply_of_ne_getLast {α : Type*} [DecidableEq α] {p : α} {L : List α}
    (hl : (p :: L).Nodup) (hL : L.Nodup) (hLne : L ≠ []) {a : α}
    (ha : a ∈ L) (ha_ne : a ≠ L.getLast hLne) :
    (p :: L).formPerm a = L.formPerm a := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
  have hk1 : k + 1 < L.length := by
    have hk_ne : k ≠ L.length - 1 := by
      intro hke
      apply ha_ne
      rw [List.getLast_eq_getElem]
      subst hke
      rfl
    omega
  have hidx : L[k] = (p :: L)[k + 1]'(by simp; omega) :=
    (List.getElem_cons_succ p L k (by simp; omega)).symm
  rw [List.formPerm_apply_lt_getElem L hL k hk1, hidx,
    List.formPerm_apply_lt_getElem (p :: L) hl (k + 1) (by simp; omega)]
  exact (List.getElem_cons_succ p L (k + 1) (by simp; omega)).symm

/-- Inserting `p` on one edge of the `L`-cycle multiplies the remaining-cycle weight
by the insertion kernel. -/
lemma cycleEdgeWeight_formPerm_cons {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {p : α} {L : List α}
    (hL : L.Nodup) (hp : p ∉ L) (h2 : 2 ≤ L.length)
    (hx : Function.Injective x) :
    cycleEdgeWeight x (List.formPerm (p :: L)) =
      cycleEdgeWeight x L.formPerm *
        (x (L[0]'(by omega)) - x (L[L.length - 1]'(by omega))) *
        (x (L[0]'(by omega)) - x p)⁻¹ *
        (x p - x (L[L.length - 1]'(by omega)))⁻¹ := by
  have hl : (p :: L).Nodup := List.nodup_cons.2 ⟨hp, hL⟩
  have hLne : L ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hneG : ∀ a : α, p :: L ≠ [a] := by
    cases L with
    | nil => intro a _; simp at h2
    | cons _ _ => intro a h; simp at h
  have hneL : ∀ a : α, L ≠ [a] := by
    intro a h
    have hlenL : L.length = 1 := by simp [h]
    omega
  unfold cycleEdgeWeight
  rw [List.support_formPerm_of_nodup _ hl hneG,
    List.support_formPerm_of_nodup _ hL hneL, List.toFinset_cons]
  have hp' : p ∉ L.toFinset := by simpa using hp
  rw [prod_insert hp', formPerm_cons_apply_head hl (by omega)]
  have hlast_mem : L.getLast hLne ∈ L.toFinset :=
    List.mem_toFinset.2 (List.getLast_mem hLne)
  rw [← prod_erase_mul L.toFinset _ hlast_mem]
  have hagree :
      ∏ a ∈ L.toFinset.erase (L.getLast hLne),
          (x ((p :: L).formPerm a) - x a)⁻¹ =
        ∏ a ∈ L.toFinset.erase (L.getLast hLne),
          (x (L.formPerm a) - x a)⁻¹ :=
    prod_congr rfl fun a ha => by
      rw [formPerm_cons_apply_of_ne_getLast hl hL hLne
        (List.mem_toFinset.mp (mem_of_mem_erase ha)) (ne_of_mem_erase ha)]
  rw [hagree, formPerm_cons_apply_getLast hLne]
  have hLsplit :
      (∏ i ∈ L.toFinset, (x (L.formPerm i) - x i)⁻¹) =
        (∏ a ∈ L.toFinset.erase (L.getLast hLne), (x (L.formPerm a) - x a)⁻¹) *
          (x (L.formPerm (L.getLast hLne)) - x (L.getLast hLne))⁻¹ :=
    (prod_erase_mul L.toFinset (fun i => (x (L.formPerm i) - x i)⁻¹) hlast_mem).symm
  rw [hLsplit, formPerm_apply_getLast_eq_head hL hLne h2]
  have hlast_get : L.getLast hLne = L[L.length - 1]'(by omega) := List.getLast_eq_getElem _
  rw [hlast_get]
  have hx0p : x (L[0]'(by omega)) ≠ x p :=
    hx.ne (ne_of_mem_of_not_mem (List.getElem_mem _) hp)
  have hxpLast : x p ≠ x (L[L.length - 1]'(by omega)) :=
    hx.ne (ne_of_mem_of_not_mem (List.getElem_mem _) hp).symm
  have hxends : x (L[0]'(by omega)) ≠ x (L[L.length - 1]'(by omega)) := by
    refine hx.ne ?_
    exact (List.Nodup.getElem_inj_iff hL).not.mpr (by omega)
  have hne1 : x (L[0]'(by omega)) - x (L[L.length - 1]'(by omega)) ≠ 0 :=
    sub_ne_zero.2 hxends
  have hne2 : x (L[0]'(by omega)) - x p ≠ 0 := sub_ne_zero.2 hx0p
  have hne3 : x p - x (L[L.length - 1]'(by omega)) ≠ 0 := sub_ne_zero.2 hxpLast
  field_simp [hne1, hne2, hne3]

/-- Guo Lemma 3.1 class sum: rotating the tail after a fixed point sums to zero. -/
lemma sum_cycleEdgeWeight_cons_rotate {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {p : α} {L : List α}
    (hL : L.Nodup) (hp : p ∉ L) (h2 : 2 ≤ L.length)
    (hx : Function.Injective x) :
    ∑ k : Fin L.length, cycleEdgeWeight x (List.formPerm (p :: L.rotate k.val)) = 0 := by
  have : NeZero L.length := ⟨by omega⟩
  have hμ :
      ∀ k : Fin L.length,
        cycleEdgeWeight x (List.formPerm (p :: L.rotate k.val)) =
          cycleEdgeWeight x L.formPerm *
            (x ((L.rotate k.val)[0]'(by simp [List.length_rotate]; omega)) -
              x ((L.rotate k.val)[L.length - 1]'(by simp [List.length_rotate]; omega))) *
            (x ((L.rotate k.val)[0]'(by simp [List.length_rotate]; omega)) - x p)⁻¹ *
            (x p - x ((L.rotate k.val)[L.length - 1]'(by simp [List.length_rotate]; omega)))⁻¹ := by
    intro k
    have hrot : (L.rotate k.val).Nodup := (List.nodup_rotate).2 hL
    have hp' : p ∉ L.rotate k.val := by
      simpa [List.mem_rotate] using hp
    have h2' : 2 ≤ (L.rotate k.val).length := by simpa [List.length_rotate] using h2
    have hcons := cycleEdgeWeight_formPerm_cons (x := x) hrot hp' h2' hx
    rw [List.formPerm_rotate L hL k.val] at hcons
    simpa [List.length_rotate] using hcons
  simp_rw [hμ, mul_assoc]
  rw [← mul_sum]
  convert mul_zero (cycleEdgeWeight x L.formPerm)
  let z : Fin L.length → ℂ := fun i => x (L[i.val])
  have hw : ∀ k : Fin L.length, x p ≠ z k := fun k =>
    hx.ne (ne_of_mem_of_not_mem (List.getElem_mem _) hp).symm
  let extra : Fin L.length → ℂ := fun k =>
    (x ((L.rotate k.val)[0]'(by simp [List.length_rotate]; omega)) -
      x ((L.rotate k.val)[L.length - 1]'(by simp [List.length_rotate]; omega))) *
      ((x ((L.rotate k.val)[0]'(by simp [List.length_rotate]; omega)) - x p)⁻¹ *
        (x p - x ((L.rotate k.val)[L.length - 1]'(by simp [List.length_rotate]; omega)))⁻¹)
  show ∑ k, extra k = 0
  have hidx : ∀ k : Fin L.length,
      ((k + 1).val + (L.length - 1)) % L.length = k.val := by
    intro k
    have npos : 0 < L.length := by omega
    have hk1 : (k + 1).val = (k.val + 1) % L.length := by simp [Fin.val_add]
    rw [hk1]
    calc ((k.val + 1) % L.length + (L.length - 1)) % L.length
        = (k.val + 1 + (L.length - 1)) % L.length := Nat.mod_add_mod _ _ _
      _ = (k.val + L.length) % L.length := by
          have : 1 + (L.length - 1) = L.length := by omega
          rw [Nat.add_assoc, this]
      _ = k.val := by
          rw [Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod, Nat.mod_eq_of_lt k.isLt]
  have hshift : ∀ k : Fin L.length,
      extra (k + 1) =
        (z (k + 1) - z k) / ((x p - z k) * (z (k + 1) - x p)) := by
    intro k
    have h0 := getElem_rotate_zero L (k + 1).isLt
    have hlast := getElem_rotate_last L h2 (k + 1).isLt
    have hidxk : ((k + 1).val + (L.length - 1)) % L.length = k.val := hidx k
    have hne1 : z (k + 1) - x p ≠ 0 := sub_ne_zero.2 (hw (k + 1)).symm
    have hne2 : x p - z k ≠ 0 := sub_ne_zero.2 (hw k)
    simp only [extra, h0, hlast, hidxk, z] at hne1 hne2 ⊢
    field_simp [hne1, hne2]
  have hreindex : ∑ k, extra (k + 1) = ∑ k, extra k :=
    Fintype.sum_equiv (Equiv.addRight (1 : Fin L.length))
      (fun k => extra (k + 1)) extra (fun _ => rfl)
  have hker :
      ∑ k, extra (k + 1) =
        ∑ k, (z (k + 1) - z k) / ((x p - z k) * (z (k + 1) - x p)) :=
    sum_congr rfl fun k _ => hshift k
  rw [← hreindex, hker]
  exact sum_insert_kernel (x p) z hw

lemma ofFn_rotate {α : Type*} {m : ℕ} [NeZero m] (f : Fin m → α) (k : Fin m) :
    (List.ofFn f).rotate k.val = List.ofFn fun i => f (i + k) := by
  refine List.ext_getElem (by simp [List.length_rotate, List.length_ofFn]) ?_
  intro i hi _hi'
  have him : i < m := by simp [List.length_ofFn] at hi; exact hi
  rw [List.getElem_rotate]
  simp only [List.getElem_ofFn, List.length_ofFn]
  refine congr_arg f ?_
  ext
  simp [Fin.val_add]

/-- Guo Lemma 3.1: the sum of insertion weights over all listings of the remaining
points is zero when at least two remaining points are present. -/
lemma sum_cycleEdgeWeight_ncycles {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) (hx : Function.Injective x) (p : α)
    (hcard : 2 ≤ Fintype.card {q : α // q ≠ p}) :
    ∑ e : Fin (Fintype.card {q : α // q ≠ p}) ≃ {q : α // q ≠ p},
      cycleEdgeWeight x (List.formPerm (p :: List.ofFn fun i => (e i).1)) = 0 := by
  set m := Fintype.card {q : α // q ≠ p}
  have : NeZero m := ⟨by omega⟩
  have hclass :
      ∀ e : Fin m ≃ {q : α // q ≠ p},
        ∑ k : Fin m,
            cycleEdgeWeight x
              (List.formPerm
                (p :: (List.ofFn fun i => (e i).1).rotate k.val)) = 0 := by
    intro e
    let L := List.ofFn fun i => (e i).1
    have hL : L.Nodup :=
      List.nodup_ofFn_ofInjective fun i j hij => e.injective (Subtype.ext hij)
    have hpL : p ∉ L := by
      intro hmem
      rw [List.mem_ofFn'] at hmem
      obtain ⟨i, hi⟩ := hmem
      exact (e i).2 hi
    have h2 : 2 ≤ L.length := by
      simpa [L, List.length_ofFn] using hcard
    have hsum := sum_cycleEdgeWeight_cons_rotate (x := x) hL hpL h2 hx
    have hlen : L.length = m := List.length_ofFn
    refine Eq.trans ?_ hsum
    refine Fintype.sum_equiv (finCongr hlen.symm)
      (fun k : Fin m =>
        cycleEdgeWeight x (List.formPerm (p :: L.rotate k.val)))
      (fun k : Fin L.length =>
        cycleEdgeWeight x (List.formPerm (p :: L.rotate k.val)))
      (fun _ => rfl)
  let W : (Fin m ≃ {q : α // q ≠ p}) → ℂ :=
    fun σ => cycleEdgeWeight x (List.formPerm (p :: List.ofFn fun i : Fin m => (σ i).1))
  have hrot :
      ∀ (e : Fin m ≃ {q : α // q ≠ p}) (k : Fin m),
        (List.ofFn fun i => (e i).1).rotate k.val =
          List.ofFn fun i : Fin m => (e (i + k)).1 := fun e k => ofFn_rotate _ k
  have hWrot :
      ∀ (e : Fin m ≃ {q : α // q ≠ p}) (k : Fin m),
        cycleEdgeWeight x
            (List.formPerm (p :: (List.ofFn fun i => (e i).1).rotate k.val)) =
          W ((Equiv.addRight k).trans e) := by
    intro e k
    rw [hrot]
    rfl
  have hdouble :
      ∑ e : Fin m ≃ {q : α // q ≠ p}, ∑ k : Fin m, W ((Equiv.addRight k).trans e) = 0 := by
    simp_rw [← hWrot]
    rw [sum_congr rfl fun e _ => hclass e]
    simp
  have hreindex :
      ∀ k : Fin m,
        ∑ e : Fin m ≃ {q : α // q ≠ p}, W ((Equiv.addRight k).trans e) =
          ∑ e, W e := by
    intro k
    let φ :=
      (Equiv.addRight k).symm.equivCongr (Equiv.refl {q : α // q ≠ p})
    have hφ : ∀ e, φ e = (Equiv.addRight k).trans e := by
      intro e
      ext i
      dsimp [φ]
    simp_rw [← hφ]
    exact Equiv.sum_comp φ W
  rw [sum_comm] at hdouble
  simp_rw [hreindex] at hdouble
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hdouble
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  exact (mul_eq_zero.mp hdouble).resolve_left hm0

lemma zeta_pow_sub {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (i j : Fin N) :
    ζ ^ j.val - ζ ^ i.val =
      - (ζ ^ i.val) * (1 - ζ ^ (j.val - i.val : ℤ)) := by
  have hz := zeta_ne_zero hζ
  have hi : ζ ^ i.val ≠ 0 := pow_ne_zero _ hz
  have hdiv : ζ ^ j.val / ζ ^ i.val = ζ ^ (j.val - i.val : ℤ) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hz]
  have hsplit : ζ ^ j.val - ζ ^ i.val = ζ ^ i.val * (ζ ^ j.val / ζ ^ i.val - 1) := by
    field_simp [hi]
  rw [hsplit, hdiv]
  ring

lemma cycleEdgeWeight_zeta {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (σ : Perm (Fin N)) :
    cycleEdgeWeight (fun i => ζ ^ i.val) σ =
      (∏ i ∈ σ.support, (-ζ ^ i.val)⁻¹) *
        ∏ i ∈ σ.support, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹ := by
  unfold cycleEdgeWeight
  have hterm : ∀ i ∈ σ.support,
      (ζ ^ (σ i).val - ζ ^ i.val)⁻¹ =
        (-ζ ^ i.val)⁻¹ * (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹ := by
    intro i hi
    have hij : σ i ≠ i := Equiv.Perm.mem_support.mp hi
    have hζi : ζ ^ i.val ≠ 0 := pow_ne_zero _ (zeta_ne_zero hζ)
    have hne : 1 - ζ ^ ((σ i).val - i.val : ℤ) ≠ 0 := denom_ne_zero hζ hij
    rw [zeta_pow_sub hζ]
    field_simp [hζi, hne]
  simp_rw [← prod_mul_distrib]
  refine prod_congr rfl hterm

lemma card_subtype_ne {α : Type*} [Fintype α] [DecidableEq α] (p : α) :
    Fintype.card {q : α // q ≠ p} = Fintype.card α - 1 := by
  rw [Fintype.card_subtype, Finset.filter_ne', card_erase_of_mem (mem_univ p), card_univ]

lemma listing_nodup {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    (e : Fin (Fintype.card {q : α // q ≠ p}) ≃ {q : α // q ≠ p}) :
    (p :: List.ofFn fun i => (e i).1).Nodup := by
  refine List.nodup_cons.2 ⟨?_, List.nodup_ofFn_ofInjective fun i j hij =>
    e.injective (Subtype.ext hij)⟩
  intro hmem
  rw [List.mem_ofFn'] at hmem
  obtain ⟨i, hi⟩ := hmem
  exact (e i).2 hi

lemma listing_isCycle {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    (e : Fin (Fintype.card {q : α // q ≠ p}) ≃ {q : α // q ≠ p})
    (hcard : 2 ≤ Fintype.card {q : α // q ≠ p}) :
    (List.formPerm (p :: List.ofFn fun i => (e i).1)).IsCycle := by
  refine List.isCycle_formPerm (listing_nodup e) ?_
  simpa [List.length_cons, List.length_ofFn] using
    (Nat.le_add_right_of_le hcard : 2 ≤ Fintype.card {q : α // q ≠ p} + 1)

lemma listing_support_univ {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    (e : Fin (Fintype.card {q : α // q ≠ p}) ≃ {q : α // q ≠ p})
    (hcard : 2 ≤ Fintype.card {q : α // q ≠ p}) :
    (List.formPerm (p :: List.ofFn fun i => (e i).1)).support = (univ : Finset α) := by
  have hne : ∀ a : α, p :: List.ofFn (fun i => (e i).1) ≠ [a] := by
    intro a h
    have hlen := congr_arg List.length h
    simp only [List.length_cons, List.length_ofFn, List.length_nil] at hlen
    omega
  rw [List.support_formPerm_of_nodup _ (listing_nodup e) hne, List.toFinset_cons]
  ext q
  simp only [mem_insert, List.mem_toFinset, mem_univ, iff_true]
  by_cases hqp : q = p
  · exact Or.inl hqp
  · refine Or.inr ?_
    rw [List.mem_ofFn']
    refine ⟨e.symm ⟨q, hqp⟩, ?_⟩
    simp

/-- Cycle determined by a listing of the remaining points after a fixed `p`. -/
noncomputable def listingPerm {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    (e : Fin (Fintype.card {q : α // q ≠ p}) ≃ {q : α // q ≠ p}) : Perm α :=
  List.formPerm (p :: List.ofFn fun i => (e i).1)

lemma listingPerm_eq_formPerm {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    (e : Fin (Fintype.card {q : α // q ≠ p}) ≃ {q : α // q ≠ p}) :
    listingPerm e = List.formPerm (p :: List.ofFn fun i => (e i).1) :=
  rfl

lemma listingPerm_isCycle {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    (e : Fin (Fintype.card {q : α // q ≠ p}) ≃ {q : α // q ≠ p})
    (hcard : 2 ≤ Fintype.card {q : α // q ≠ p}) :
    (listingPerm e).IsCycle := by
  delta listingPerm
  exact listing_isCycle e hcard

lemma listingPerm_support_univ {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    (e : Fin (Fintype.card {q : α // q ≠ p}) ≃ {q : α // q ≠ p})
    (hcard : 2 ≤ Fintype.card {q : α // q ≠ p}) :
    (listingPerm e).support = (univ : Finset α) := by
  delta listingPerm
  exact listing_support_univ e hcard

lemma derangement_support_univ {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α}
    (h : ∀ i, σ i ≠ i) : σ.support = univ := by
  ext i
  simp [Equiv.Perm.mem_support, h]

lemma cycleEdgeWeight_zeta_univ {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {σ : Perm (Fin N)} (hsup : σ.support = univ) :
    cycleEdgeWeight (fun i => ζ ^ i.val) σ =
      (∏ i : Fin N, (-ζ ^ i.val)⁻¹) *
        ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹ := by
  rw [cycleEdgeWeight_zeta hζ, hsup]

lemma zeta_inv_prod_ne_zero {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) :
    (∏ i : Fin N, (-ζ ^ i.val)⁻¹) ≠ 0 :=
  prod_ne_zero_iff.2 fun i _ =>
    inv_ne_zero (neg_ne_zero.2 (pow_ne_zero i.val (zeta_ne_zero hζ)))

lemma listing_inv_one_sub_sum {N : ℕ} [NeZero N] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (p : Fin N)
    (hcard : 2 ≤ Fintype.card {q : Fin N // q ≠ p}) :
    ∑ e : Fin (Fintype.card {q : Fin N // q ≠ p}) ≃ {q : Fin N // q ≠ p},
      ∏ i : Fin N, (1 - ζ ^ (((listingPerm e) i).val - i.val : ℤ))⁻¹ = 0 := by
  have hsum := sum_cycleEdgeWeight_ncycles (fun i => ζ ^ i.val)
    (zeta_pow_fin_injective hζ) p hcard
  have hterm : ∀ e,
      cycleEdgeWeight (fun i => ζ ^ i.val)
          (List.formPerm (p :: List.ofFn fun i => (e i).1)) =
        (∏ i : Fin N, (-ζ ^ i.val)⁻¹) *
          ∏ i : Fin N, (1 - ζ ^ (((listingPerm e) i).val - i.val : ℤ))⁻¹ := fun e => by
    have hsup := listingPerm_support_univ e hcard
    have := cycleEdgeWeight_zeta_univ hζ hsup
    exact this
  simp_rw [hterm] at hsum
  rw [← mul_sum] at hsum
  exact (mul_eq_zero.mp hsum).resolve_left (zeta_inv_prod_ne_zero hζ)

lemma isCycle_univ_ne {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} (hsup : σ.support = univ) (p : α) : σ p ≠ p :=
  Equiv.Perm.mem_support.mp (by rw [hsup]; exact mem_univ p)

lemma orderOf_isCycle_univ {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} (hσ : σ.IsCycle) (hsup : σ.support = univ) :
    orderOf σ = Fintype.card α := by
  rw [hσ.orderOf, hsup, card_univ]

lemma card_subtype_ne_lt_card {α : Type*} [Fintype α] [DecidableEq α]
    (p : α) (i : Fin (Fintype.card {q : α // q ≠ p})) :
    i.val + 1 < Fintype.card α := by
  have hle : i.val + 1 ≤ Fintype.card {q : α // q ≠ p} := Nat.succ_le_of_lt i.isLt
  have hcard := card_subtype_ne p
  have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.2 ⟨p⟩
  omega

lemma isCycle_pow_succ_ne {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} (hσ : σ.IsCycle) (hsup : σ.support = univ) (p : α)
    (i : Fin (Fintype.card {q : α // q ≠ p})) :
    (σ ^ (i.val + 1)) p ≠ p := by
  have hp := isCycle_univ_ne hsup p
  intro h
  have h1 : σ ^ (i.val + 1) = 1 := (hσ.pow_eq_one_iff' hp).2 h
  have hdvd : orderOf σ ∣ i.val + 1 := orderOf_dvd_iff_pow_eq_one.2 h1
  have hlt : i.val + 1 < orderOf σ := by
    rw [orderOf_isCycle_univ hσ hsup]
    exact card_subtype_ne_lt_card p i
  exact Nat.not_dvd_of_pos_of_lt (Nat.succ_pos _) hlt hdvd

noncomputable def ncycleToListingFun {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    {σ : Perm α} (hσ : σ.IsCycle) (hsup : σ.support = univ)
    (i : Fin (Fintype.card {q : α // q ≠ p})) : {q : α // q ≠ p} :=
  ⟨(σ ^ (i.val + 1)) p, isCycle_pow_succ_ne hσ hsup p i⟩

lemma ncycleToListingFun_injective {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    {σ : Perm α} (hσ : σ.IsCycle) (hsup : σ.support = univ) :
    Function.Injective (ncycleToListingFun (p := p) hσ hsup) := by
  intro i j hij
  have hij' : (σ ^ (i.val + 1)) p = (σ ^ (j.val + 1)) p :=
    congrArg Subtype.val hij
  have hp := isCycle_univ_ne hsup p
  have heq : σ ^ (i.val + 1) = σ ^ (j.val + 1) :=
    (hσ.pow_eq_pow_iff).2 ⟨p, hp, hij'⟩
  have hmod := pow_inj_mod.mp heq
  have hlt : ∀ k : Fin (Fintype.card {q : α // q ≠ p}),
      k.val + 1 < orderOf σ := fun k => by
    rw [orderOf_isCycle_univ hσ hsup]
    exact card_subtype_ne_lt_card p k
  rw [Nat.mod_eq_of_lt (hlt i), Nat.mod_eq_of_lt (hlt j)] at hmod
  exact Fin.ext (Nat.succ_injective hmod)

lemma ncycleToListingFun_surjective {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    {σ : Perm α} (hσ : σ.IsCycle) (hsup : σ.support = univ) :
    Function.Surjective (ncycleToListingFun (p := p) hσ hsup) := by
  intro q
  have hp := isCycle_univ_ne hsup p
  have hq := isCycle_univ_ne hsup q.1
  have hsc : Equiv.Perm.SameCycle σ p q.1 :=
    ((Equiv.Perm.isCycle_iff_sameCycle hp).1 hσ).mpr hq
  obtain ⟨k, hklt, hk⟩ := Equiv.Perm.SameCycle.exists_pow_eq' hsc
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero, Perm.one_apply] at hk
    exact q.2 hk.symm
  have hkpos : 1 ≤ k := Nat.pos_of_ne_zero hk0
  have hord := orderOf_isCycle_univ hσ hsup
  have hi : k - 1 < Fintype.card {q : α // q ≠ p} := by
    rw [card_subtype_ne, ← hord]
    omega
  refine ⟨⟨k - 1, hi⟩, ?_⟩
  apply Subtype.ext
  change (σ ^ (k - 1 + 1)) p = q.1
  rw [Nat.sub_add_cancel hkpos, hk]

noncomputable def ncycleToListing {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    {σ : Perm α} (hσ : σ.IsCycle) (hsup : σ.support = univ) :
    Fin (Fintype.card {q : α // q ≠ p}) ≃ {q : α // q ≠ p} :=
  Equiv.ofBijective (ncycleToListingFun (p := p) hσ hsup)
    ⟨ncycleToListingFun_injective hσ hsup, ncycleToListingFun_surjective hσ hsup⟩

lemma ncycleToListing_apply {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    {σ : Perm α} (hσ : σ.IsCycle) (hsup : σ.support = univ)
    (i : Fin (Fintype.card {q : α // q ≠ p})) :
    (ncycleToListing (p := p) hσ hsup i).1 = (σ ^ (i.val + 1)) p :=
  rfl

lemma toList_eq_cons_ofFn {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} (hσ : σ.IsCycle) (hsup : σ.support = univ) (p : α) :
    Equiv.Perm.toList σ p =
      p :: List.ofFn fun i : Fin (Fintype.card {q : α // q ≠ p}) =>
        (σ ^ (i.val + 1)) p := by
  have hp := isCycle_univ_ne hsup p
  have hlen : (Equiv.Perm.toList σ p).length = Fintype.card α := by
    rw [Equiv.Perm.length_toList, hσ.cycleOf_eq hp, hsup, card_univ]
  refine List.ext_getElem ?_ ?_
  · have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.2 ⟨p⟩
    rw [hlen, List.length_cons, List.length_ofFn, card_subtype_ne]
    omega
  · intro n hn _hn'
    rw [Equiv.Perm.getElem_toList]
    cases n with
    | zero =>
      simp [pow_zero]
    | succ k =>
      simp [List.getElem_ofFn]

lemma ncycleToListing_listingPerm {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    (e : Fin (Fintype.card {q : α // q ≠ p}) ≃ {q : α // q ≠ p})
    (hcard : 2 ≤ Fintype.card {q : α // q ≠ p}) :
    ncycleToListing (listingPerm_isCycle e hcard) (listingPerm_support_univ e hcard) = e := by
  ext i
  rw [ncycleToListing_apply]
  have hnodup := listing_nodup (p := p) e
  have hlt' : i.val + 1 < Fintype.card {q : α // q ≠ p} + 1 := Nat.succ_lt_succ i.isLt
  have hpow := List.formPerm_pow_apply_head p (List.ofFn fun j => (e j).1) hnodup (i.val + 1)
  delta listingPerm
  rw [hpow]
  simp only [List.length_cons, List.length_ofFn, Nat.mod_eq_of_lt hlt',
    List.getElem_cons_succ, List.getElem_ofFn]

lemma listingPerm_ncycleToListing {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    {σ : Perm α} (hσ : σ.IsCycle) (hsup : σ.support = univ) :
    listingPerm (ncycleToListing (p := p) hσ hsup) = σ := by
  have hp := isCycle_univ_ne hsup p
  have hlist :
      (p :: List.ofFn fun i : Fin (Fintype.card {q : α // q ≠ p}) =>
          (ncycleToListing (p := p) hσ hsup i).1) =
        Equiv.Perm.toList σ p := by
    simp_rw [ncycleToListing_apply]
    exact (toList_eq_cons_ofFn hσ hsup p).symm
  delta listingPerm
  rw [hlist, Equiv.Perm.formPerm_toList, hσ.cycleOf_eq hp]

noncomputable def listingEquiv {α : Type*} [Fintype α] [DecidableEq α] (p : α)
    (hcard : 2 ≤ Fintype.card {q : α // q ≠ p}) :
    (Fin (Fintype.card {q : α // q ≠ p}) ≃ {q : α // q ≠ p}) ≃
      {σ : Perm α // σ.IsCycle ∧ σ.support = univ} where
  toFun e := ⟨listingPerm e, listingPerm_isCycle e hcard, listingPerm_support_univ e hcard⟩
  invFun σ := ncycleToListing σ.2.1 σ.2.2
  left_inv e := ncycleToListing_listingPerm e hcard
  right_inv σ := Subtype.ext (listingPerm_ncycleToListing σ.2.1 σ.2.2)

open scoped Classical in
lemma ncycle_inv_one_sub_sum {N : ℕ} [NeZero N] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (p : Fin N)
    (hcard : 2 ≤ Fintype.card {q : Fin N // q ≠ p}) :
    ∑ σ : {σ : Perm (Fin N) // σ.IsCycle ∧ σ.support = univ},
      ∏ i : Fin N, (1 - ζ ^ ((σ.1 i).val - i.val : ℤ))⁻¹ = 0 := by
  rw [← Equiv.sum_comp (listingEquiv p hcard)
    (fun σ => ∏ i : Fin N, (1 - ζ ^ ((σ.1 i).val - i.val : ℤ))⁻¹)]
  dsimp only [listingEquiv]
  exact listing_inv_one_sub_sum hζ p hcard

lemma cycleEdgeWeight_ofSubtype {α : Type*} [Fintype α] [DecidableEq α]
    {p : α → Prop} [DecidablePred p] (x : α → ℂ) (u : Perm (Subtype p)) :
    cycleEdgeWeight x (Equiv.Perm.ofSubtype u) =
      cycleEdgeWeight (fun q : Subtype p => x q.1) u := by
  simp only [cycleEdgeWeight, Equiv.Perm.support_ofSubtype]
  rw [prod_map]
  refine prod_congr rfl fun q _ => ?_
  simp [Equiv.Perm.ofSubtype_apply_coe]

lemma ofSubtype_isCycle {α : Type*} [DecidableEq α] {p : α → Prop} [DecidablePred p]
    {u : Perm (Subtype p)} (hu : u.IsCycle) :
    (Equiv.Perm.ofSubtype u).IsCycle :=
  hu.extendDomain (Equiv.refl _)

lemma support_ofSubtype_subset {α : Type*} [Fintype α] [DecidableEq α] {s : Finset α}
    (u : Perm {a // a ∈ s}) :
    (Equiv.Perm.ofSubtype u).support ⊆ s := by
  intro x hx
  obtain ⟨hx', _⟩ := (Equiv.Perm.mem_support_ofSubtype x u).mp hx
  exact hx'

lemma ofSubtype_disjoint_of_support_subset_compl {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} (u : Perm {a // a ∈ s}) {τ : Perm α} (hτ : τ.support ⊆ sᶜ) :
    Equiv.Perm.Disjoint (Equiv.Perm.ofSubtype u) τ := by
  rw [Equiv.Perm.disjoint_iff_disjoint_support]
  exact Finset.disjoint_of_subset_left (support_ofSubtype_subset u)
    (Finset.disjoint_of_subset_right hτ disjoint_compl_right)

lemma two_le_card_subtype_ne_of_three {α : Type*} [Fintype α] [DecidableEq α] (p : α)
    (h : 3 ≤ Fintype.card α) :
    2 ≤ Fintype.card {q : α // q ≠ p} := by
  rw [card_subtype_ne]
  omega

lemma sum_cycleEdgeWeight_replace_cycle {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) (hx : Function.Injective x) {s : Finset α}
    (p : {a // a ∈ s})
    (hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p})
    {τ : Perm α} (hτ : τ.support ⊆ sᶜ) :
    ∑ e : Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃ {q : {a // a ∈ s} // q ≠ p},
      cycleEdgeWeight x (Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ) = 0 := by
  have hterm : ∀ e,
      cycleEdgeWeight x (Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ) =
        cycleEdgeWeight (fun q : {a // a ∈ s} => x q.1) (listingPerm (p := p) e) *
          cycleEdgeWeight x τ := fun e => by
    rw [cycleEdgeWeight_mul_disjoint x
        (ofSubtype_disjoint_of_support_subset_compl (listingPerm (p := p) e) hτ)]
    refine congr_arg (· * cycleEdgeWeight x τ) ?_
    convert cycleEdgeWeight_ofSubtype x (listingPerm (p := p) e)
  simp_rw [hterm]
  rw [← sum_mul]
  have h0 :
      ∑ e : Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃ {q : {a // a ∈ s} // q ≠ p},
        cycleEdgeWeight (fun q : {a // a ∈ s} => x q.1) (listingPerm (p := p) e) = 0 := by
    refine (sum_congr rfl fun e _ =>
      congrArg _ (listingPerm_eq_formPerm (p := p) e)).trans ?_
    exact sum_cycleEdgeWeight_ncycles (fun q : {a // a ∈ s} => x q.1)
      (hx.comp Subtype.val_injective) p hcard
  rw [h0, zero_mul]

lemma coe_units_neg_one_pow (k : ℕ) :
    ((↑((-1 : ℤˣ) ^ k) : ℤ) : ℂ) = (-1 : ℂ) ^ k := by
  rw [Units.val_pow_eq_pow_val]
  simp

lemma sign_of_cycleType_replicate_two {n : ℕ} {σ : Perm (Fin (2 * n))}
    (h : σ.cycleType = Multiset.replicate n 2) :
    (Perm.sign σ : ℂ) = (-1 : ℂ) ^ n := by
  rw [Equiv.Perm.sign_of_cycleType, h, Multiset.sum_replicate, Multiset.card_replicate,
    nsmul_eq_mul]
  exact (coe_units_neg_one_pow (n * 2 + n)).trans (by
    rw [pow_add, mul_comm n 2, pow_mul, neg_one_sq, one_pow, one_mul])

lemma cycleType_eq_replicate_two {n : ℕ} {σ : Perm (Fin (2 * n))}
    (hsup : σ.support = univ) (h2 : ∀ m ∈ σ.cycleType, m = 2) :
    σ.cycleType = Multiset.replicate n 2 := by
  have hr : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate_card.2 h2
  have hsum : σ.cycleType.sum = 2 * n := by
    rw [Equiv.Perm.sum_cycleType, hsup, card_univ, Fintype.card_fin]
  have hcard : Multiset.card σ.cycleType * 2 = 2 * n := by
    rw [← Nat.nsmul_eq_mul, ← Multiset.sum_replicate, ← hr, hsum]
  have hn : Multiset.card σ.cycleType = n := by omega
  rw [hr, hn]

lemma derangement_long_cycle_or_replicate_two {n : ℕ} {σ : Perm (Fin (2 * n))}
    (hsup : σ.support = univ) :
    (∃ c ∈ σ.cycleFactorsFinset, 3 ≤ c.support.card) ∨
      σ.cycleType = Multiset.replicate n 2 := by
  by_cases hlong : ∃ c ∈ σ.cycleFactorsFinset, 3 ≤ c.support.card
  · exact Or.inl hlong
  · refine Or.inr (cycleType_eq_replicate_two hsup ?_)
    intro m hm
    have hm2 : 2 ≤ m := Equiv.Perm.two_le_of_mem_cycleType hm
    have hm3 : ¬ 3 ≤ m := by
      intro h3
      rw [Equiv.Perm.cycleType_def] at hm
      obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hm
      exact hlong ⟨c, Finset.mem_def.mpr hc, h3⟩
    omega

lemma inv_one_sub_prod_of_univ {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {σ : Perm (Fin N)} (hsup : σ.support = univ) :
    ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹ =
      (∏ i : Fin N, (-ζ ^ i.val)⁻¹)⁻¹ *
        cycleEdgeWeight (fun i => ζ ^ i.val) σ := by
  have hC := zeta_inv_prod_ne_zero hζ
  rw [eq_inv_mul_iff_mul_eq₀ hC]
  exact (cycleEdgeWeight_zeta_univ hζ hsup).symm

lemma involution_unsigned_eq_neg_signed {n : ℕ} {ζ : ℂ} :
    (∑ σ : Perm (Fin (2 * n)),
      if (∀ i, σ i ≠ i) ∧ σ.cycleType = Multiset.replicate n 2 then
        ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
      else 0) =
      (-1 : ℂ) ^ n *
        ∑ σ : Perm (Fin (2 * n)),
          if (∀ i, σ i ≠ i) ∧ σ.cycleType = Multiset.replicate n 2 then
            (Perm.sign σ : ℂ) *
              ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
          else 0 := by
  have hterm : ∀ σ : Perm (Fin (2 * n)),
      (if (∀ i, σ i ≠ i) ∧ σ.cycleType = Multiset.replicate n 2 then
        ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
      else 0) =
        (-1 : ℂ) ^ n *
          (if (∀ i, σ i ≠ i) ∧ σ.cycleType = Multiset.replicate n 2 then
            (Perm.sign σ : ℂ) *
              ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
          else 0) := by
    intro σ
    split_ifs with h
    · have hsign := sign_of_cycleType_replicate_two h.2
      rw [hsign, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
    · rw [mul_zero]
  simp_rw [hterm, ← mul_sum]

lemma mem_of_support_subset {α : Type*} [Fintype α] [DecidableEq α] {s : Finset α}
    {f : Perm α} (h : f.support ⊆ s) (x : α) : x ∈ s ↔ f x ∈ s := by
  constructor
  · intro hx
    by_cases hsup : x ∈ f.support
    · exact h (Equiv.Perm.apply_mem_support.mpr hsup)
    · rwa [Equiv.Perm.notMem_support.mp hsup]
  · intro hx
    by_cases hsup : x ∈ f.support
    · exact h hsup
    · rwa [← Equiv.Perm.notMem_support.mp hsup]

lemma ofSubtype_subtypePerm_of_support_subset {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} {f : Perm α} (hsub : f.support ⊆ s) :
    Equiv.Perm.ofSubtype
      (f.subtypePerm fun x => (mem_of_support_subset (s := s) hsub x).symm) = f := by
  ext x
  by_cases hx : x ∈ s
  · rw [Equiv.Perm.ofSubtype_apply_of_mem _ hx, Equiv.Perm.subtypePerm_apply]
  · rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hx]
    exact (Equiv.Perm.notMem_support.mp fun h => hx (hsub h)).symm

lemma two_le_card_subtype_ne_of_card_three {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} (p : {a // a ∈ s}) (hs : 3 ≤ s.card) :
    2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p} := by
  rw [card_subtype_ne, Fintype.card_coe]
  omega

lemma listingPerm_apply_ne {α : Type*} [Fintype α] [DecidableEq α] {s : Finset α}
    (p : {a // a ∈ s})
    (e : Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃ {q : {a // a ∈ s} // q ≠ p})
    (hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p})
    (q : {a // a ∈ s}) : listingPerm (p := p) e q ≠ q := by
  have hsup := listingPerm_support_univ (p := p) e hcard
  have hmem : q ∈ (listingPerm (p := p) e).support := by
    rw [hsup]
    exact mem_univ q
  exact Equiv.Perm.mem_support.mp hmem

lemma support_ofSubtype_listing {α : Type*} [Fintype α] [DecidableEq α] {s : Finset α}
    (p : {a // a ∈ s})
    (e : Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃ {q : {a // a ∈ s} // q ≠ p})
    (hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p}) :
    (Equiv.Perm.ofSubtype (listingPerm (p := p) e)).support = s := by
  ext x
  constructor
  · intro hx
    by_cases hx' : x ∈ s
    · exact hx'
    · have hne := Equiv.Perm.mem_support.mp hx
      rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hx'] at hne
      exact (hne rfl).elim
  · intro hx
    refine Equiv.Perm.mem_support.mpr ?_
    rw [Equiv.Perm.ofSubtype_apply_of_mem _ hx]
    intro h
    exact listingPerm_apply_ne p e hcard ⟨x, hx⟩ (Subtype.ext h)

lemma support_mul_listing_τ {α : Type*} [Fintype α] [DecidableEq α] {s : Finset α}
    (p : {a // a ∈ s})
    (e : Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃ {q : {a // a ∈ s} // q ≠ p})
    (hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p})
    {τ : Perm α} (hτ : τ.support = sᶜ) :
    (Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ).support = univ := by
  have hd := ofSubtype_disjoint_of_support_subset_compl (listingPerm (p := p) e)
    (show τ.support ⊆ sᶜ from hτ.symm ▸ Subset.rfl)
  rw [Equiv.Perm.Disjoint.support_mul hd, support_ofSubtype_listing p e hcard, hτ, union_compl]

lemma inv_one_sub_replace_cycle {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {s : Finset (Fin N)} (p : {a // a ∈ s})
    (hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p})
    {τ : Perm (Fin N)} (hτ : τ.support = sᶜ) :
    ∑ e : Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃ {q : {a // a ∈ s} // q ≠ p},
      ∏ i : Fin N,
        (1 - ζ ^ (((Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ) i).val
          - i.val : ℤ))⁻¹ = 0 := by
  have hterm : ∀ e,
      (∏ i : Fin N,
          (1 - ζ ^ (((Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ) i).val
            - i.val : ℤ))⁻¹) =
        (∏ i : Fin N, (-ζ ^ i.val)⁻¹)⁻¹ *
          cycleEdgeWeight (fun i => ζ ^ i.val)
            (Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ) := fun e =>
    inv_one_sub_prod_of_univ hζ (support_mul_listing_τ p e hcard hτ)
  simp_rw [hterm]
  rw [← mul_sum, sum_cycleEdgeWeight_replace_cycle (fun i => ζ ^ i.val)
      (zeta_pow_fin_injective hζ) p hcard (show τ.support ⊆ sᶜ from hτ.symm ▸ Subset.rfl),
    mul_zero]

/-- Points that lie on a cycle of length at least 3. -/
noncomputable def longPoints {α : Type*} [Fintype α] [DecidableEq α] (σ : Perm α) :
    Finset α :=
  univ.filter fun a => 3 ≤ (σ.cycleOf a).support.card

lemma mem_longPoints {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α} {a : α} :
    a ∈ longPoints σ ↔ 3 ≤ (σ.cycleOf a).support.card := by
  simp [longPoints]

lemma longPoints_nonempty_iff {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α} :
    (longPoints σ).Nonempty ↔ ∃ c ∈ σ.cycleFactorsFinset, 3 ≤ c.support.card := by
  constructor
  · intro ⟨a, ha⟩
    rw [mem_longPoints] at ha
    have hne : σ a ≠ a := by
      intro h
      have h1 : σ.cycleOf a = 1 := (Equiv.Perm.cycleOf_eq_one_iff σ).mpr h
      have h0 : (σ.cycleOf a).support.card = 0 := by
        rw [h1, Equiv.Perm.support_one, card_empty]
      omega
    exact ⟨σ.cycleOf a, (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff).2
      (Equiv.Perm.mem_support.mpr hne), ha⟩
  · intro ⟨c, hc, h3⟩
    obtain ⟨a, ha⟩ := Equiv.Perm.IsCycle.nonempty_support
      (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1
    refine ⟨a, mem_longPoints.mpr ?_⟩
    rwa [← Equiv.Perm.cycle_is_cycleOf ha hc]

lemma inv_apply_eq_self_of_apply_eq_self {α : Type*} {c : Perm α} {x : α}
    (h : c x = x) : c⁻¹ x = x := by
  refine c.injective ?_
  have hleft : c (c⁻¹ x) = x := by simp
  rw [hleft, h]

lemma remainder_apply_eq_self_of_mem {α : Type*} [Fintype α] [DecidableEq α]
    {σ c : Perm α} (hc : c ∈ σ.cycleFactorsFinset) {x : α} (hx : x ∈ c.support) :
    (σ * c⁻¹) x = x := by
  have hagree := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).2
  have hxinv : c⁻¹ x ∈ c.support := by
    have hx' : x ∈ c⁻¹.support := by rwa [Equiv.Perm.support_inv]
    have hx'' : c⁻¹ x ∈ c⁻¹.support := Equiv.Perm.apply_mem_support.mpr hx'
    rwa [Equiv.Perm.support_inv] at hx''
  change σ (c⁻¹ x) = x
  rw [← hagree _ hxinv]
  simp

lemma remainder_support_eq_compl {α : Type*} [Fintype α] [DecidableEq α]
    {σ c : Perm α} (hc : c ∈ σ.cycleFactorsFinset) (hsup : σ.support = univ) :
    (σ * c⁻¹).support = c.supportᶜ := by
  ext x
  constructor
  · intro hxrem
    by_cases hx : x ∈ c.support
    · have : x ∉ (σ * c⁻¹).support :=
        Equiv.Perm.notMem_support.mpr (remainder_apply_eq_self_of_mem hc hx)
      exact (this hxrem).elim
    · exact mem_compl.mpr hx
  · intro hxcompl
    have hx : x ∉ c.support := mem_compl.mp hxcompl
    have hcx : c x = x := Equiv.Perm.notMem_support.mp hx
    have hinv : c⁻¹ x = x := inv_apply_eq_self_of_apply_eq_self hcx
    refine Equiv.Perm.mem_support.mpr ?_
    change σ (c⁻¹ x) ≠ x
    rw [hinv]
    exact Equiv.Perm.mem_support.mp (hsup.symm ▸ mem_univ x)

lemma ofSubtype_mul_remainder {α : Type*} [Fintype α] [DecidableEq α]
    {σ c : Perm α} (hc : c ∈ σ.cycleFactorsFinset) :
    Equiv.Perm.ofSubtype
        (c.subtypePerm fun x =>
          (mem_of_support_subset (s := c.support) (Subset.rfl) x).symm) *
      (σ * c⁻¹) = σ := by
  rw [ofSubtype_subtypePerm_of_support_subset (s := c.support) Subset.rfl]
  have hd := Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc
  rw [← hd.commute.eq]
  simp

lemma not_mem_support_of_mem_of_subset_compl {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} {τ : Perm α} (hτ : τ.support ⊆ sᶜ) {x : α} (hx : x ∈ s) :
    τ x = x :=
  Equiv.Perm.notMem_support.mp fun h => (mem_compl.mp (hτ h)) hx

lemma cycleOf_mul_listing {α : Type*} [Fintype α] [DecidableEq α] {s : Finset α}
    (p : {a // a ∈ s})
    (e : Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃ {q : {a // a ∈ s} // q ≠ p})
    (hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p})
    {τ : Perm α} (hτ : τ.support ⊆ sᶜ) {x : α} (hx : x ∈ s) :
    (Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ).cycleOf x =
      Equiv.Perm.ofSubtype (listingPerm (p := p) e) := by
  have hd := ofSubtype_disjoint_of_support_subset_compl (listingPerm (p := p) e) hτ
  have hτx : τ x = x := not_mem_support_of_mem_of_subset_compl hτ hx
  have hcycle := ofSubtype_isCycle (listingPerm_isCycle (p := p) e hcard)
  have hne : Equiv.Perm.ofSubtype (listingPerm (p := p) e) x ≠ x :=
    Equiv.Perm.mem_support.mp (by
      rw [support_ofSubtype_listing p e hcard]
      exact hx)
  rw [Equiv.Perm.cycleOf_mul_of_apply_right_eq_self hd.commute x hτx]
  exact Equiv.Perm.IsCycle.cycleOf_eq hcycle hne

lemma longPoints_mul_listing {α : Type*} [Fintype α] [DecidableEq α] {s : Finset α}
    (p : {a // a ∈ s})
    (e : Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃ {q : {a // a ∈ s} // q ≠ p})
    (hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p})
    (hs : 3 ≤ s.card) {τ : Perm α} (hτ : τ.support ⊆ sᶜ) :
    longPoints (Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ) =
      s ∪ longPoints τ := by
  ext x
  by_cases hx : x ∈ s
  · have hcy := cycleOf_mul_listing p e hcard hτ hx
    have hsup : (Equiv.Perm.ofSubtype (listingPerm (p := p) e)).support = s :=
      support_ofSubtype_listing p e hcard
    simp only [mem_longPoints, mem_union, hx, true_or, iff_true]
    rw [hcy, hsup]
    exact hs
  · have hd := ofSubtype_disjoint_of_support_subset_compl (listingPerm (p := p) e) hτ
    have hfx : Equiv.Perm.ofSubtype (listingPerm (p := p) e) x = x :=
      Equiv.Perm.notMem_support.mp (by
        rw [support_ofSubtype_listing p e hcard]
        exact hx)
    have hcy : (Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ).cycleOf x =
        τ.cycleOf x := by
      rw [Equiv.Perm.Disjoint.cycleOf_mul_distrib hd,
        (Equiv.Perm.cycleOf_eq_one_iff _).mpr hfx, one_mul]
    simp only [mem_longPoints, mem_union, hx, false_or]
    rw [hcy]

noncomputable def longKey {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (σ : Perm α) : Finset α × Perm α :=
  if h : (longPoints σ).Nonempty then
    ((σ.cycleOf ((longPoints σ).min' h)).support,
      σ * (σ.cycleOf ((longPoints σ).min' h))⁻¹)
  else
    (∅, 1)

lemma sum_eq_sum_longKey {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (g : Perm α → ℂ) :
    ∑ σ : Perm α, g σ =
      ∑ s : Finset α, ∑ τ : Perm α,
        ∑ σ : Perm α, if longKey σ = (s, τ) then g σ else 0 := by
  have hσ : ∀ σ : Perm α,
      g σ = ∑ s : Finset α, ∑ τ : Perm α,
        if longKey σ = (s, τ) then g σ else 0 := by
    intro σ
    have hpair :
        (∑ p : Finset α × Perm α, if longKey σ = p then g σ else 0) = g σ := by
      rw [sum_ite_eq, if_pos (mem_univ _)]
    have hprod :
        (∑ p : Finset α × Perm α, if longKey σ = p then g σ else 0) =
          ∑ s : Finset α, ∑ τ : Perm α,
            if longKey σ = (s, τ) then g σ else 0 := by
      exact Fintype.sum_prod_type
        (fun p : Finset α × Perm α => if longKey σ = p then g σ else 0)
    exact hpair.symm.trans hprod
  refine (Fintype.sum_congr _ _ hσ).trans ?_
  rw [sum_comm]
  refine Fintype.sum_congr _ _ fun s => ?_
  rw [sum_comm]

lemma min'_union_eq_of_le {α : Type*} [DecidableEq α] [LinearOrder α] {s t : Finset α}
    (hs : s.Nonempty) (h : ∀ a ∈ t, s.min' hs ≤ a) :
    (s ∪ t).min' (hs.mono subset_union_left) = s.min' hs := by
  apply le_antisymm
  · exact (isLeast_min' (s ∪ t) (hs.mono subset_union_left)).2
      (mem_union.mpr (Or.inl (min'_mem s hs)))
  · have hmem := min'_mem (s ∪ t) (hs.mono subset_union_left)
    rcases mem_union.mp hmem with hys | hyt
    · exact (isLeast_min' s hs).2 hys
    · exact h _ hyt

lemma mul_right_inv_eq_of_disjoint {α : Type*} {f τ : Perm α}
    (h : Equiv.Perm.Disjoint f τ) : (f * τ) * f⁻¹ = τ := by
  rw [h.commute.eq]
  simp

lemma longKey_of_listing {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {s : Finset α} (hsn : s.Nonempty) (hs : 3 ≤ s.card)
    (p : {a // a ∈ s}) (hp : p.1 = s.min' hsn)
    (e : Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃ {q : {a // a ∈ s} // q ≠ p})
    (hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p})
    {τ : Perm α} (hτ : τ.support ⊆ sᶜ)
    (hdist : ∀ a ∈ longPoints τ, p.1 ≤ a) :
    longKey (Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ) = (s, τ) := by
  set f := Equiv.Perm.ofSubtype (listingPerm (p := p) e)
  set σ := f * τ
  have hlp : longPoints σ = s ∪ longPoints τ :=
    longPoints_mul_listing p e hcard hs hτ
  have hne : (longPoints σ).Nonempty := by
    rw [hlp]
    exact ⟨p.1, mem_union.mpr (Or.inl p.2)⟩
  have hmin : (longPoints σ).min' hne = p.1 := by
    have hmin' :
        (s ∪ longPoints τ).min' (hsn.mono subset_union_left) = s.min' hsn :=
      min'_union_eq_of_le hsn (fun a ha => hp ▸ hdist a ha)
    refine Eq.trans ?_ (hp ▸ hmin')
    congr 1
  have hcy : σ.cycleOf ((longPoints σ).min' hne) = f := by
    rw [hmin]
    have hx : p.1 ∈ s := p.2
    exact cycleOf_mul_listing p e hcard hτ hx
  unfold longKey
  rw [dif_pos hne]
  apply Prod.ext
  · change (σ.cycleOf ((longPoints σ).min' hne)).support = s
    rw [hcy]
    exact support_ofSubtype_listing p e hcard
  · change σ * (σ.cycleOf ((longPoints σ).min' hne))⁻¹ = τ
    rw [hcy]
    exact mul_right_inv_eq_of_disjoint
      (ofSubtype_disjoint_of_support_subset_compl (listingPerm (p := p) e) hτ)

lemma isCycle_subtypePerm_of_support {α : Type*} [Fintype α] [DecidableEq α]
    {c : Perm α} (hc : c.IsCycle) (h2 : 2 ≤ c.support.card) :
    (c.subtypePerm fun x =>
      (mem_of_support_subset (s := c.support) Subset.rfl x).symm).IsCycle := by
  have hon : c.IsCycleOn (c.support : Set α) := by
    convert hc.isCycleOn
    ext x
    simp [Equiv.Perm.mem_support]
  have hnt : (c.support : Set α).Nontrivial := by
    obtain ⟨a, b, ha, hb, hne⟩ := (one_lt_card_iff (s := c.support)).1 (by omega)
    exact ⟨a, ha, b, hb, hne⟩
  convert hon.isCycle_subtypePerm hnt

lemma support_subtypePerm_univ {α : Type*} [Fintype α] [DecidableEq α]
    {c : Perm α} :
    (c.subtypePerm fun x =>
      (mem_of_support_subset (s := c.support) Subset.rfl x).symm).support = univ := by
  ext q
  constructor
  · intro _hq
    exact mem_univ q
  · intro _hq
    rw [Equiv.Perm.support_subtypePerm]
    exact mem_filter.mpr ⟨mem_univ q, Equiv.Perm.mem_support.mp q.2⟩

lemma support_cycleOf_subset_longPoints {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} {a : α} (h : 3 ≤ (σ.cycleOf a).support.card) :
    (σ.cycleOf a).support ⊆ longPoints σ := by
  intro x hx
  have hsc : σ.SameCycle a x := (Equiv.Perm.mem_support_cycleOf_iff.mp hx).1
  rw [mem_longPoints, ← hsc.cycleOf_eq]
  exact h

lemma eq_listing_of_longKey {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {σ : Perm α} {s : Finset α} {τ : Perm α}
    (hkey : longKey σ = (s, τ)) (hne : (longPoints σ).Nonempty)
    (_hsupσ : σ.support = univ) :
    ∃ (hsn : s.Nonempty) (_hs : 3 ≤ s.card)
      (p : {a // a ∈ s}) (_hp : p.1 = s.min' hsn)
      (_hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p})
      (e : Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃ {q : {a // a ∈ s} // q ≠ p}),
        Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ = σ := by
  let pα := (longPoints σ).min' hne
  let c := σ.cycleOf pα
  have hlong : longKey σ = (c.support, σ * c⁻¹) := by
    dsimp [longKey]
    rw [dif_pos hne]
  rw [hlong] at hkey
  rw [show s = c.support from (congrArg Prod.fst hkey).symm]
  rw [show τ = σ * c⁻¹ from (congrArg Prod.snd hkey).symm]
  have hpα : pα ∈ longPoints σ := min'_mem _ hne
  have h3 : 3 ≤ c.support.card := mem_longPoints.mp hpα
  have hpαs : pα ∈ c.support := by
    have hneσ : σ pα ≠ pα := by
      intro h
      have h1 : c = 1 := (Equiv.Perm.cycleOf_eq_one_iff σ).mpr h
      have h0 : c.support.card = 0 := by
        rw [h1, Equiv.Perm.support_one, card_empty]
      omega
    have : c pα ≠ pα := by
      rwa [Equiv.Perm.cycleOf_apply_self]
    exact Equiv.Perm.mem_support.mpr this
  have hpσ' : pα ∈ σ.support := by
    have : c pα ≠ pα := Equiv.Perm.mem_support.mp hpαs
    rwa [Equiv.Perm.mem_support, ← Equiv.Perm.cycleOf_apply_self]
  have hcmem : c ∈ σ.cycleFactorsFinset :=
    (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff).2 hpσ'
  have hsn : c.support.Nonempty := ⟨pα, hpαs⟩
  refine ⟨hsn, h3, ⟨pα, hpαs⟩, ?_, two_le_card_subtype_ne_of_card_three ⟨pα, hpαs⟩ h3, ?_, ?_⟩
  · apply le_antisymm
    · exact (isLeast_min' (longPoints σ) hne).2
        (support_cycleOf_subset_longPoints h3 (min'_mem c.support hsn))
    · exact (isLeast_min' c.support hsn).2 hpαs
  · have hcyc : c.IsCycle :=
      Equiv.Perm.isCycle_cycleOf _ (Equiv.Perm.mem_support.mp hpσ')
    exact ncycleToListing (isCycle_subtypePerm_of_support hcyc (by omega))
      (support_subtypePerm_univ (c := c))
  · have hcyc : c.IsCycle :=
      Equiv.Perm.isCycle_cycleOf _ (Equiv.Perm.mem_support.mp hpσ')
    have hu := isCycle_subtypePerm_of_support hcyc (by omega)
    have hsupu := support_subtypePerm_univ (c := c)
    have heq :
        listingPerm (p := ⟨pα, hpαs⟩) (ncycleToListing hu hsupu) =
          c.subtypePerm fun x =>
            (mem_of_support_subset (s := c.support) Subset.rfl x).symm :=
      listingPerm_ncycleToListing hu hsupu
    rw [heq]
    exact ofSubtype_mul_remainder hcmem

lemma cycleOf_min_ne_self {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {σ : Perm α} (hne : (longPoints σ).Nonempty) :
    σ ((longPoints σ).min' hne) ≠ (longPoints σ).min' hne := by
  intro h
  have h1 : σ.cycleOf ((longPoints σ).min' hne) = 1 :=
    (Equiv.Perm.cycleOf_eq_one_iff σ).mpr h
  have h3 : 3 ≤ (σ.cycleOf ((longPoints σ).min' hne)).support.card :=
    mem_longPoints.mp (min'_mem _ hne)
  have h0 : (σ.cycleOf ((longPoints σ).min' hne)).support.card = 0 := by
    rw [h1, Equiv.Perm.support_one, card_empty]
  omega

lemma cycleOf_min_mem_cycleFactorsFinset {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] {σ : Perm α} (hne : (longPoints σ).Nonempty) :
    σ.cycleOf ((longPoints σ).min' hne) ∈ σ.cycleFactorsFinset :=
  (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff).2
    (Equiv.Perm.mem_support.mpr (cycleOf_min_ne_self hne))

lemma longKey_eq {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {σ : Perm α} (hne : (longPoints σ).Nonempty) :
    longKey σ =
      ((σ.cycleOf ((longPoints σ).min' hne)).support,
        σ * (σ.cycleOf ((longPoints σ).min' hne))⁻¹) := by
  dsimp [longKey]
  rw [dif_pos hne]

lemma three_le_card_fst_longKey {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {σ : Perm α} {s : Finset α} {τ : Perm α}
    (hkey : longKey σ = (s, τ)) (hne : (longPoints σ).Nonempty) :
    3 ≤ s.card := by
  rw [show s = (σ.cycleOf ((longPoints σ).min' hne)).support from
    congrArg Prod.fst (hkey.symm.trans (longKey_eq hne))]
  exact mem_longPoints.mp (min'_mem _ hne)

lemma remainder_support_of_longKey {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] {σ : Perm α} {s : Finset α} {τ : Perm α}
    (hkey : longKey σ = (s, τ)) (hne : (longPoints σ).Nonempty)
    (hsup : σ.support = univ) : τ.support = sᶜ := by
  rw [show τ = σ * (σ.cycleOf ((longPoints σ).min' hne))⁻¹ from
      congrArg Prod.snd (hkey.symm.trans (longKey_eq hne)),
    show s = (σ.cycleOf ((longPoints σ).min' hne)).support from
      congrArg Prod.fst (hkey.symm.trans (longKey_eq hne))]
  exact remainder_support_eq_compl (cycleOf_min_mem_cycleFactorsFinset hne) hsup

lemma eq_mul_remainder_of_mem_cycleFactorsFinset {α : Type*} [Fintype α]
    [DecidableEq α] {σ c : Perm α} (hc : c ∈ σ.cycleFactorsFinset) :
    σ = c * (σ * c⁻¹) := by
  have h := ofSubtype_mul_remainder hc
  rw [ofSubtype_subtypePerm_of_support_subset (s := c.support) Subset.rfl] at h
  exact h.symm

lemma longPoints_mul_inv_cycle_subset {α : Type*} [Fintype α] [DecidableEq α]
    {σ c : Perm α} (hc : c ∈ σ.cycleFactorsFinset) :
    longPoints (σ * c⁻¹) ⊆ longPoints σ := by
  intro a ha
  rw [mem_longPoints] at ha ⊢
  have hd := Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc
  have hσeq := eq_mul_remainder_of_mem_cycleFactorsFinset hc
  by_cases hx : a ∈ c.support
  · have hfix : (σ * c⁻¹) a = a := remainder_apply_eq_self_of_mem hc hx
    have h1 : (σ * c⁻¹).cycleOf a = 1 :=
      (Equiv.Perm.cycleOf_eq_one_iff (σ * c⁻¹)).mpr hfix
    have h0 : ((σ * c⁻¹).cycleOf a).support.card = 0 := by
      rw [h1, Equiv.Perm.support_one, card_empty]
    omega
  · have hcx : c a = a := Equiv.Perm.notMem_support.mp hx
    have hc1 : c.cycleOf a = 1 := (Equiv.Perm.cycleOf_eq_one_iff c).mpr hcx
    have hcy : σ.cycleOf a = (σ * c⁻¹).cycleOf a := by
      have hleft : σ.cycleOf a = (c * (σ * c⁻¹)).cycleOf a :=
        congrArg (fun f => f.cycleOf a) hσeq
      rw [hleft, Equiv.Perm.Disjoint.cycleOf_mul_distrib hd.symm a, hc1, one_mul]
    rwa [hcy]

lemma min'_fst_eq_min'_longPoints {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] {σ : Perm α} {s : Finset α} {τ : Perm α}
    (hsn : s.Nonempty) (hkey : longKey σ = (s, τ))
    (hne : (longPoints σ).Nonempty) :
    s.min' hsn = (longPoints σ).min' hne := by
  have hs : s = (σ.cycleOf ((longPoints σ).min' hne)).support :=
    congrArg Prod.fst (hkey.symm.trans (longKey_eq hne))
  apply le_antisymm
  · have hpαs : (longPoints σ).min' hne ∈ s := by
      rw [hs]
      exact Equiv.Perm.mem_support.mpr (by
        rw [Equiv.Perm.cycleOf_apply_self]
        exact cycleOf_min_ne_self hne)
    exact (isLeast_min' s hsn).2 hpαs
  · have hsub : s ⊆ longPoints σ := by
      rw [hs]
      exact support_cycleOf_subset_longPoints (mem_longPoints.mp (min'_mem _ hne))
    exact (isLeast_min' (longPoints σ) hne).2 (hsub (min'_mem s hsn))

lemma dist_of_longKey {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {σ : Perm α} {s : Finset α} {τ : Perm α} (hsn : s.Nonempty)
    (hkey : longKey σ = (s, τ)) (hne : (longPoints σ).Nonempty) :
    ∀ a ∈ longPoints τ, s.min' hsn ≤ a := by
  have hτ : τ = σ * (σ.cycleOf ((longPoints σ).min' hne))⁻¹ :=
    congrArg Prod.snd (hkey.symm.trans (longKey_eq hne))
  intro a ha
  have hsub : longPoints τ ⊆ longPoints σ := by
    rw [hτ]
    exact longPoints_mul_inv_cycle_subset (cycleOf_min_mem_cycleFactorsFinset hne)
  have hle : (longPoints σ).min' hne ≤ a :=
    (isLeast_min' (longPoints σ) hne).2 (hsub ha)
  rw [min'_fst_eq_min'_longPoints hsn hkey hne]
  exact hle

lemma listingPerm_injective {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    (hcard : 2 ≤ Fintype.card {q : α // q ≠ p}) :
    Function.Injective (listingPerm (p := p)) := by
  intro e₁ e₂ h
  exact (listingEquiv p hcard).injective (Subtype.ext h)

lemma ofSubtype_listing_mul_injective {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} (p : {a // a ∈ s})
    (hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p})
    (τ : Perm α) :
    Function.Injective fun e =>
      Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ := by
  intro e₁ e₂ h
  have h' : Equiv.Perm.ofSubtype (listingPerm (p := p) e₁) * τ =
      Equiv.Perm.ofSubtype (listingPerm (p := p) e₂) * τ := h
  have hf :
      Equiv.Perm.ofSubtype (listingPerm (p := p) e₁) =
        Equiv.Perm.ofSubtype (listingPerm (p := p) e₂) := by
    calc
      Equiv.Perm.ofSubtype (listingPerm (p := p) e₁) =
          Equiv.Perm.ofSubtype (listingPerm (p := p) e₁) * τ * τ⁻¹ := by simp
      _ = Equiv.Perm.ofSubtype (listingPerm (p := p) e₂) * τ * τ⁻¹ := by rw [h']
      _ = Equiv.Perm.ofSubtype (listingPerm (p := p) e₂) := by simp
  exact listingPerm_injective hcard (Equiv.Perm.ofSubtype_injective hf)

lemma listing_mem_long_fiber {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] {s : Finset α} (hsn : s.Nonempty) (hs : 3 ≤ s.card)
    (p : {a // a ∈ s}) (hp : p.1 = s.min' hsn)
    (hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p})
    {τ : Perm α} (hτ : τ.support = sᶜ)
    (hdist : ∀ a ∈ longPoints τ, p.1 ≤ a)
    (e : Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃ {q : {a // a ∈ s} // q ≠ p}) :
    longKey (Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ) = (s, τ) ∧
      (∀ i, (Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ) i ≠ i) ∧
        (longPoints (Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ)).Nonempty := by
  have hsub : τ.support ⊆ sᶜ := hτ ▸ Subset.rfl
  refine ⟨longKey_of_listing hsn hs p hp e hcard hsub hdist, ?_, ?_⟩
  · intro i
    have hsup := support_mul_listing_τ p e hcard hτ
    exact Equiv.Perm.mem_support.mp (by
      rw [hsup]
      exact mem_univ i)
  · rw [longPoints_mul_listing p e hcard hs hsub]
    exact hsn.mono subset_union_left

lemma mem_range_listing_of_longKey {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] {s : Finset α} (hsn : s.Nonempty)
    (p : {a // a ∈ s}) (hp : p.1 = s.min' hsn)
    {τ σ : Perm α} (hkey : longKey σ = (s, τ))
    (hne : (longPoints σ).Nonempty) (hsup : σ.support = univ) :
    ∃ e : Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃
        {q : {a // a ∈ s} // q ≠ p},
      Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ = σ := by
  obtain ⟨hsn', _hs, p', hp', _hcard, e, heq⟩ := eq_listing_of_longKey hkey hne hsup
  have hp_eq : p' = p := Subtype.ext <|
    hp'.trans <|
      (le_antisymm
          ((isLeast_min' s hsn').2 (min'_mem s hsn))
          ((isLeast_min' s hsn).2 (min'_mem s hsn'))).trans
        hp.symm
  subst hp_eq
  exact ⟨e, heq⟩

lemma long_fiber_inv_one_sub {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (s : Finset (Fin N)) (τ : Perm (Fin N)) :
    (∑ σ : Perm (Fin N),
      if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
        ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
      else 0) = 0 := by
  by_cases hs3 : 3 ≤ s.card
  · have hsn : s.Nonempty := Finset.card_pos.mp (by omega)
    by_cases hτ : τ.support = sᶜ
    · by_cases hdist : ∀ a ∈ longPoints τ, s.min' hsn ≤ a
      · let p : {a // a ∈ s} := ⟨s.min' hsn, min'_mem s hsn⟩
        have hp : p.1 = s.min' hsn := rfl
        have hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p} :=
          two_le_card_subtype_ne_of_card_three (p := p) hs3
        let φ : (Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃
            {q : {a // a ∈ s} // q ≠ p}) → Perm (Fin N) := fun e =>
          Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ
        have hinj : Function.Injective φ :=
          ofSubtype_listing_mul_injective (p := p) hcard τ
        have hsum := inv_one_sub_replace_cycle (p := p) hζ hcard hτ
        refine Eq.trans ?_ hsum
        refine (Fintype.sum_of_injective φ hinj
            (fun e => ∏ i : Fin N,
              (1 - ζ ^ ((φ e i).val - i.val : ℤ))⁻¹)
            (fun σ =>
              if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
                ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
              else 0)
            ?_ ?_).symm
        · intro σ hσ
          split_ifs with hfiber
          · exact (hσ (Set.mem_range.mpr (mem_range_listing_of_longKey hsn p hp
              hfiber.1 hfiber.2.2 (derangement_support_univ hfiber.2.1)))).elim
          · rfl
        · intro e
          have hdist' : ∀ a ∈ longPoints τ, p.1 ≤ a := by
            intro a ha
            rw [hp]
            exact hdist a ha
          have hmem := listing_mem_long_fiber hsn hs3 p hp hcard hτ hdist' e
          have hφ : φ e = Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ := rfl
          rw [hφ, if_pos hmem]
      · have h0 : ∀ σ : Perm (Fin N),
            (if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
              ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
            else 0) = 0 := by
          intro σ
          split_ifs with hfiber
          · exact (hdist (dist_of_longKey hsn hfiber.1 hfiber.2.2)).elim
          · rfl
        exact (Fintype.sum_congr _ _ h0).trans (by simp)
    · have h0 : ∀ σ : Perm (Fin N),
          (if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
            ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
          else 0) = 0 := by
        intro σ
        split_ifs with hfiber
        · exact (hτ (remainder_support_of_longKey hfiber.1 hfiber.2.2
            (derangement_support_univ hfiber.2.1))).elim
        · rfl
      exact (Fintype.sum_congr _ _ h0).trans (by simp)
  · have h0 : ∀ σ : Perm (Fin N),
        (if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
          ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
        else 0) = 0 := by
      intro σ
      split_ifs with hfiber
      · exact (hs3 (three_le_card_fst_longKey hfiber.1 hfiber.2.2)).elim
      · rfl
    exact (Fintype.sum_congr _ _ h0).trans (by simp)

lemma ite_longKey_and {N : ℕ} {s : Finset (Fin N)} {τ : Perm (Fin N)}
    (g : Perm (Fin N) → ℂ) (σ : Perm (Fin N)) :
    (if longKey σ = (s, τ) then
        if (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then g σ else 0
      else 0) =
      if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
        g σ
      else 0 := by
  by_cases hkey : longKey σ = (s, τ)
  · by_cases hdl : (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty
    · simp [hkey, hdl]
    · simp [hkey, hdl]
  · simp [hkey]

lemma long_cycle_inv_one_sub_sum {N : ℕ} [NeZero N] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) :
    (∑ σ : Perm (Fin N),
      if (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
        ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
      else 0) = 0 := by
  rw [sum_eq_sum_longKey (fun σ =>
    if (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
      ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
    else 0)]
  refine Eq.trans (Fintype.sum_congr _ _ fun s =>
      Fintype.sum_congr _ _ fun τ =>
        Fintype.sum_congr _ _ fun σ =>
          ite_longKey_and (fun σ =>
            ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹) σ) ?_
  refine Eq.trans (Fintype.sum_congr _ _ fun s =>
      Fintype.sum_congr _ _ fun τ => long_fiber_inv_one_sub hζ s τ) (by simp)

lemma coe_sign_mul {α : Type*} [Fintype α] [DecidableEq α] (f g : Perm α) :
    (Perm.sign (f * g) : ℂ) = (Perm.sign f : ℂ) * (Perm.sign g : ℂ) := by
  rw [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]

lemma coe_sign_isCycle {α : Type*} [Fintype α] [DecidableEq α] {f : Perm α}
    (hf : f.IsCycle) :
    (Perm.sign f : ℂ) = -(-1 : ℂ) ^ f.support.card := by
  rw [Equiv.Perm.IsCycle.sign hf]
  rw [Units.val_neg, Int.cast_neg, coe_units_neg_one_pow]

lemma sign_eq_of_mem_longKey {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] {σ : Perm α} {s : Finset α} {τ : Perm α}
    (hkey : longKey σ = (s, τ)) (hne : (longPoints σ).Nonempty)
    (hsup : σ.support = univ) :
    (Perm.sign σ : ℂ) = -(-1 : ℂ) ^ s.card * (Perm.sign τ : ℂ) := by
  have hs3 := three_le_card_fst_longKey hkey hne
  have hsn : s.Nonempty := Finset.card_pos.mp (by omega)
  let p : {a // a ∈ s} := ⟨s.min' hsn, min'_mem s hsn⟩
  have hp : p.1 = s.min' hsn := rfl
  have hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p} :=
    two_le_card_subtype_ne_of_card_three (p := p) hs3
  obtain ⟨e, heq⟩ := mem_range_listing_of_longKey hsn p hp hkey hne hsup
  have hcyc := ofSubtype_isCycle (listingPerm_isCycle (p := p) e hcard)
  rw [← heq, coe_sign_mul, coe_sign_isCycle hcyc, support_ofSubtype_listing p e hcard]

lemma long_fiber_signed_inv_one_sub {N : ℕ} [NeZero N] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (s : Finset (Fin N)) (τ : Perm (Fin N)) :
    (∑ σ : Perm (Fin N),
      if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
        (Perm.sign σ : ℂ) * ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
      else 0) = 0 := by
  have hterm : ∀ σ : Perm (Fin N),
      (if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
        (Perm.sign σ : ℂ) * ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
      else 0) =
        (-(-1 : ℂ) ^ s.card * (Perm.sign τ : ℂ)) *
          (if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
            ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
          else 0) := by
    intro σ
    split_ifs with h
    · rw [sign_eq_of_mem_longKey h.1 h.2.2 (derangement_support_univ h.2.1)]
    · rw [mul_zero]
  simp_rw [hterm, ← mul_sum, long_fiber_inv_one_sub hζ s τ, mul_zero]

lemma long_cycle_signed_inv_one_sub_sum {N : ℕ} [NeZero N] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) :
    (∑ σ : Perm (Fin N),
      if (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
        (Perm.sign σ : ℂ) * ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
      else 0) = 0 := by
  rw [sum_eq_sum_longKey (fun σ =>
    if (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
      (Perm.sign σ : ℂ) * ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
    else 0)]
  refine Eq.trans (Fintype.sum_congr _ _ fun s =>
      Fintype.sum_congr _ _ fun τ =>
        Fintype.sum_congr _ _ fun σ =>
          ite_longKey_and (fun σ =>
            (Perm.sign σ : ℂ) *
              ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹) σ) ?_
  refine Eq.trans (Fintype.sum_congr _ _ fun s =>
      Fintype.sum_congr _ _ fun τ => long_fiber_signed_inv_one_sub hζ s τ) (by simp)

lemma not_mem_longPoints_of_cycleType_eq_two {n : ℕ} {σ : Perm (Fin (2 * n))}
    (h : σ.cycleType = Multiset.replicate n 2) {a : Fin (2 * n)} :
    a ∉ longPoints σ := by
  intro ha
  rw [mem_longPoints] at ha
  have hne : σ a ≠ a := by
    intro hfix
    have h1 : σ.cycleOf a = 1 := (Equiv.Perm.cycleOf_eq_one_iff σ).mpr hfix
    have h0 : (σ.cycleOf a).support.card = 0 := by
      rw [h1, Equiv.Perm.support_one, card_empty]
    omega
  have hcmem : σ.cycleOf a ∈ σ.cycleFactorsFinset :=
    (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff).2 (Equiv.Perm.mem_support.mpr hne)
  have hmem : (σ.cycleOf a).support.card ∈ σ.cycleType := by
    rw [Equiv.Perm.cycleType_def]
    exact Multiset.mem_map.mpr ⟨σ.cycleOf a, Finset.mem_def.mp hcmem, rfl⟩
  have heq2 : (σ.cycleOf a).support.card = 2 :=
    (Multiset.mem_replicate.mp (h ▸ hmem)).2
  omega

lemma derangement_inv_one_sub_eq_involution {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ}
    (_hζ : IsPrimitiveRoot ζ (2 * n)) :
    (∑ σ : Perm (Fin (2 * n)),
      if (∀ i, σ i ≠ i) then
        ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
      else 0) =
      ∑ σ : Perm (Fin (2 * n)),
        if (∀ i, σ i ≠ i) ∧ σ.cycleType = Multiset.replicate n 2 then
          ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
        else 0 := by
  have : NeZero (2 * n) := ⟨by omega⟩
  have hterm : ∀ σ : Perm (Fin (2 * n)),
      (if (∀ i, σ i ≠ i) then
        ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
      else 0) =
        (if (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
          ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
        else 0) +
          (if (∀ i, σ i ≠ i) ∧ σ.cycleType = Multiset.replicate n 2 then
            ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
          else 0) := by
    intro σ
    by_cases hder : ∀ i, σ i ≠ i
    · have hcases :=
        derangement_long_cycle_or_replicate_two (derangement_support_univ hder)
      rcases hcases with hL | hinv
      · have hne : (longPoints σ).Nonempty := longPoints_nonempty_iff.2 hL
        have hninv : ¬ σ.cycleType = Multiset.replicate n 2 := by
          intro hct
          obtain ⟨a, ha⟩ := hne
          exact not_mem_longPoints_of_cycleType_eq_two hct ha
        rw [if_pos hder, if_pos ⟨hder, hne⟩,
          if_neg (mt And.right hninv), add_zero]
      · have hnlong : ¬ (longPoints σ).Nonempty := by
          intro hne
          obtain ⟨a, ha⟩ := hne
          exact not_mem_longPoints_of_cycleType_eq_two hinv ha
        rw [if_pos hder, if_neg (mt And.right hnlong), if_pos ⟨hder, hinv⟩,
          zero_add]
    · rw [if_neg hder, if_neg (mt And.left hder), if_neg (mt And.left hder),
        add_zero]
  refine Eq.trans (Fintype.sum_congr _ _ hterm) ?_
  rw [sum_add_distrib, long_cycle_inv_one_sub_sum (N := 2 * n) ‹_›, zero_add]

lemma signed_derangement_eq_involution {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ}
    (_hζ : IsPrimitiveRoot ζ (2 * n)) :
    (∑ σ : Perm (Fin (2 * n)),
      if (∀ i, σ i ≠ i) then
        (Perm.sign σ : ℂ) * ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
      else 0) =
      ∑ σ : Perm (Fin (2 * n)),
        if (∀ i, σ i ≠ i) ∧ σ.cycleType = Multiset.replicate n 2 then
          (Perm.sign σ : ℂ) *
            ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
        else 0 := by
  have : NeZero (2 * n) := ⟨by omega⟩
  have hterm : ∀ σ : Perm (Fin (2 * n)),
      (if (∀ i, σ i ≠ i) then
        (Perm.sign σ : ℂ) * ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
      else 0) =
        (if (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
          (Perm.sign σ : ℂ) * ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
        else 0) +
          (if (∀ i, σ i ≠ i) ∧ σ.cycleType = Multiset.replicate n 2 then
            (Perm.sign σ : ℂ) *
              ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
          else 0) := by
    intro σ
    by_cases hder : ∀ i, σ i ≠ i
    · have hcases :=
        derangement_long_cycle_or_replicate_two (derangement_support_univ hder)
      rcases hcases with hL | hinv
      · have hne : (longPoints σ).Nonempty := longPoints_nonempty_iff.2 hL
        have hninv : ¬ σ.cycleType = Multiset.replicate n 2 := by
          intro hct
          obtain ⟨a, ha⟩ := hne
          exact not_mem_longPoints_of_cycleType_eq_two hct ha
        rw [if_pos hder, if_pos ⟨hder, hne⟩,
          if_neg (mt And.right hninv), add_zero]
      · have hnlong : ¬ (longPoints σ).Nonempty := by
          intro hne
          obtain ⟨a, ha⟩ := hne
          exact not_mem_longPoints_of_cycleType_eq_two hinv ha
        rw [if_pos hder, if_neg (mt And.right hnlong), if_pos ⟨hder, hinv⟩,
          zero_add]
    · rw [if_neg hder, if_neg (mt And.left hder), if_neg (mt And.left hder),
        add_zero]
  refine Eq.trans (Fintype.sum_congr _ _ hterm) ?_
  rw [sum_add_distrib, long_cycle_signed_inv_one_sub_sum (N := 2 * n) ‹_›, zero_add]

lemma unsigned_derangement_inv_sum {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n)) :
    (∑ σ : Perm (Fin (2 * n)),
      if (∀ i, σ i ≠ i) then
        ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
      else 0) =
      (a n : ℂ) / (2 : ℂ) ^ (2 * n) := by
  rw [derangement_inv_one_sub_eq_involution hn hζ, involution_unsigned_eq_neg_signed,
    ← signed_derangement_eq_involution hn hζ, signed_derangement_inv_sum hn hζ,
    ← mul_div_assoc, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
    one_mul]

lemma permanent_sunMatrix_sub_ones_eq_a {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n)) :
    (sunMatrix n ζ - allOnes (2 * n)).permanent = (a n : ℂ) := by
  have h2 : (2 : ℂ) ^ (2 * n) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [permanent_sunMatrix_sub_ones hn hζ, unsigned_derangement_inv_sum hn hζ]
  exact mul_div_cancel₀ _ h2

/-- Cayley-kernel weight of a permutation. The empty product is 1. -/
noncomputable def cayleyWeight {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) (σ : Perm α) : ℂ :=
  ∏ i ∈ σ.support, (x i + x (σ i)) / (x i - x (σ i))

lemma cayleyFactor_swap {R : Type*} [Field R] (a b : R) :
    (b + a) / (b - a) = -((a + b) / (a - b)) := by
  by_cases h : a = b
  · simp [h]
  · have hab : a - b ≠ 0 := sub_ne_zero.2 h
    have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm h)
    field_simp [hab, hba]
    ring

lemma cayleyWeight_one {α : Type*} [Fintype α] [DecidableEq α] (x : α → ℂ) :
    cayleyWeight x (1 : Perm α) = 1 := by
  simp [cayleyWeight]

lemma cayleyWeight_mul_disjoint {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {σ τ : Perm α} (h : Equiv.Perm.Disjoint σ τ) :
    cayleyWeight x (σ * τ) = cayleyWeight x σ * cayleyWeight x τ := by
  simp only [cayleyWeight]
  rw [h.support_mul, prod_union h.disjoint_support]
  refine congr_arg₂ (· * ·) ?_ ?_
  · refine prod_congr rfl fun a ha => ?_
    have hτ : τ a = a := Equiv.Perm.notMem_support.mp (h.mem_imp ha)
    simp [hτ]
  · refine prod_congr rfl fun a ha => ?_
    have hσa : σ (τ a) = τ a := by
      have : τ a ∈ τ.support := (Equiv.Perm.apply_mem_support (f := τ)).2 ha
      exact Equiv.Perm.notMem_support.mp (h.symm.mem_imp this)
    simp [hσa]

lemma cayleyWeight_inv {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) (σ : Perm α) :
    cayleyWeight x σ⁻¹ = (-1 : ℂ) ^ σ.support.card * cayleyWeight x σ := by
  have hsup : σ⁻¹.support = σ.support := Equiv.Perm.support_inv σ
  unfold cayleyWeight
  rw [hsup]
  have hterm : ∀ i ∈ σ.support,
      (x i + x (σ⁻¹ i)) / (x i - x (σ⁻¹ i)) =
        -((x (σ⁻¹ i) + x i) / (x (σ⁻¹ i) - x i)) := fun i _ =>
    cayleyFactor_swap (x (σ⁻¹ i)) (x i)
  rw [prod_congr rfl hterm, prod_neg]
  refine congr_arg ((-1 : ℂ) ^ σ.support.card * ·) ?_
  refine prod_bij (fun i _ => σ⁻¹ i) ?_ ?_ ?_ ?_
  · intro i hi
    have hi' : i ∈ σ⁻¹.support := by rwa [hsup]
    have : σ⁻¹ i ∈ σ⁻¹.support := Equiv.Perm.apply_mem_support.mpr hi'
    rwa [hsup] at this
  · intro i _ i' _ h
    exact σ⁻¹.injective h
  · intro j hj
    refine ⟨σ j, Equiv.Perm.apply_mem_support.mpr hj, ?_⟩
    simp
  · intro i _hi
    simp

lemma cayley_add_eq {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (i j : Fin N) :
    ζ ^ i.val + ζ ^ j.val =
      ζ ^ i.val * (1 + ζ ^ (j.val - i.val : ℤ)) := by
  have hz := zeta_ne_zero hζ
  have hi : ζ ^ i.val ≠ 0 := pow_ne_zero _ hz
  have hdiv : ζ ^ j.val / ζ ^ i.val = ζ ^ (j.val - i.val : ℤ) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hz]
  have hsplit : ζ ^ i.val + ζ ^ j.val =
      ζ ^ i.val * (1 + ζ ^ j.val / ζ ^ i.val) := by
    field_simp [hi]
  rw [hsplit, hdiv]

lemma cayley_sub_eq {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (i j : Fin N) :
    ζ ^ i.val - ζ ^ j.val =
      ζ ^ i.val * (1 - ζ ^ (j.val - i.val : ℤ)) := by
  rw [← neg_sub, zeta_pow_sub hζ i j, neg_mul, neg_neg]

lemma cayley_eq_sunFactor {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {i j : Fin N} (hij : i ≠ j) :
    (ζ ^ i.val + ζ ^ j.val) / (ζ ^ i.val - ζ ^ j.val) =
      (1 + ζ ^ (j.val - i.val : ℤ)) / (1 - ζ ^ (j.val - i.val : ℤ)) := by
  have hi : ζ ^ i.val ≠ 0 := pow_ne_zero _ (zeta_ne_zero hζ)
  have hden := denom_ne_zero hζ hij.symm
  rw [cayley_add_eq hζ i j, cayley_sub_eq hζ i j]
  field_simp [hi, hden]

lemma prod_sunMatrix_eq_cayleyWeight {n : ℕ} [NeZero n] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n)) (σ : Perm (Fin (2 * n))) :
    (∏ i : Fin (2 * n), sunMatrix n ζ (σ i) i) =
      cayleyWeight (fun i => ζ ^ i.val) σ := by
  unfold cayleyWeight
  rw [← union_compl σ.support, prod_union disjoint_compl_right]
  have hfix : ∏ i ∈ σ.supportᶜ, sunMatrix n ζ (σ i) i = 1 := by
    refine prod_eq_one fun i hi => ?_
    have : σ i = i := Equiv.Perm.notMem_support.mp (mem_compl.mp hi)
    rw [this, sunMatrix_apply_eq]
  rw [hfix, mul_one]
  refine prod_congr rfl fun i hi => ?_
  have hne : σ i ≠ i := Equiv.Perm.mem_support.mp hi
  rw [sunMatrix_apply_ne hζ hne]
  exact (cayley_eq_sunFactor (N := 2 * n) hζ hne.symm).symm

lemma permanent_sunMatrix_eq_sum_cayleyWeight {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n)) :
    (sunMatrix n ζ).permanent =
      ∑ σ : Perm (Fin (2 * n)), cayleyWeight (fun i => ζ ^ i.val) σ := by
  have : NeZero n := ⟨by omega⟩
  unfold Matrix.permanent
  refine Fintype.sum_congr _ _ fun σ =>
    prod_sunMatrix_eq_cayleyWeight hζ σ

/-- Points that lie on an odd-length cycle. Cycle factors have length at least 2,
so these cycles have length at least 3. -/
noncomputable def oddLongPoints {α : Type*} [Fintype α] [DecidableEq α] (σ : Perm α) :
    Finset α :=
  univ.filter fun a => Odd ((σ.cycleOf a).support.card)

lemma mem_oddLongPoints {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α} {a : α} :
    a ∈ oddLongPoints σ ↔ Odd ((σ.cycleOf a).support.card) := by
  simp [oddLongPoints]

lemma odd_card_cycleOf_ne_self {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} {a : α} (h : Odd ((σ.cycleOf a).support.card)) : σ a ≠ a := by
  intro hfix
  have h1 : σ.cycleOf a = 1 := (Equiv.Perm.cycleOf_eq_one_iff σ).mpr hfix
  have h0 : (σ.cycleOf a).support.card = 0 := by
    rw [h1, Equiv.Perm.support_one, card_empty]
  exact Nat.not_odd_zero (h0 ▸ h)

lemma oddLongPoints_nonempty_iff {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α} :
    (oddLongPoints σ).Nonempty ↔ ∃ c ∈ σ.cycleFactorsFinset, Odd c.support.card := by
  constructor
  · intro ⟨a, ha⟩
    rw [mem_oddLongPoints] at ha
    exact ⟨σ.cycleOf a, (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff).2
      (Equiv.Perm.mem_support.mpr (odd_card_cycleOf_ne_self ha)), ha⟩
  · intro ⟨c, hc, hodd⟩
    obtain ⟨a, ha⟩ := Equiv.Perm.IsCycle.nonempty_support
      (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1
    refine ⟨a, mem_oddLongPoints.mpr ?_⟩
    rwa [← Equiv.Perm.cycle_is_cycleOf ha hc]

lemma odd_cycleOf_min_ne_self {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {σ : Perm α} (hne : (oddLongPoints σ).Nonempty) :
    σ ((oddLongPoints σ).min' hne) ≠ (oddLongPoints σ).min' hne :=
  odd_card_cycleOf_ne_self (mem_oddLongPoints.mp (min'_mem _ hne))

lemma odd_cycleOf_min_mem_cycleFactorsFinset {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] {σ : Perm α} (hne : (oddLongPoints σ).Nonempty) :
    σ.cycleOf ((oddLongPoints σ).min' hne) ∈ σ.cycleFactorsFinset :=
  (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff).2
    (Equiv.Perm.mem_support.mpr (odd_cycleOf_min_ne_self hne))

lemma odd_cycleOf_min_odd {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {σ : Perm α} (hne : (oddLongPoints σ).Nonempty) :
    Odd ((σ.cycleOf ((oddLongPoints σ).min' hne)).support.card) :=
  mem_oddLongPoints.mp (min'_mem _ hne)

lemma cayleyWeight_reverse_odd_cycle {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {σ c : Perm α} (hc : c ∈ σ.cycleFactorsFinset)
    (hodd : Odd c.support.card) :
    cayleyWeight x (c⁻¹ * (σ * c⁻¹)) = - cayleyWeight x σ := by
  have hd := Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc
  have hσeq := eq_mul_remainder_of_mem_cycleFactorsFinset hc
  have hdis : Equiv.Perm.Disjoint c⁻¹ (σ * c⁻¹) := hd.symm.inv_left
  calc
    cayleyWeight x (c⁻¹ * (σ * c⁻¹))
        = cayleyWeight x c⁻¹ * cayleyWeight x (σ * c⁻¹) :=
      cayleyWeight_mul_disjoint x hdis
    _ = (-1 : ℂ) ^ c.support.card * cayleyWeight x c * cayleyWeight x (σ * c⁻¹) := by
      rw [cayleyWeight_inv]
    _ = - (cayleyWeight x c * cayleyWeight x (σ * c⁻¹)) := by
      rw [Odd.neg_one_pow hodd]
      ring
    _ = - cayleyWeight x (c * (σ * c⁻¹)) := by
      rw [cayleyWeight_mul_disjoint x hd.symm]
    _ = - cayleyWeight x σ := by
      rw [← hσeq]

lemma cycleOf_reverse_odd_of_mem {α : Type*} [Fintype α] [DecidableEq α]
    {σ c : Perm α} (hc : c ∈ σ.cycleFactorsFinset) {a : α} (ha : a ∈ c.support) :
    (c⁻¹ * (σ * c⁻¹)).cycleOf a = c⁻¹ := by
  have hd := Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc
  have hdis : Equiv.Perm.Disjoint c⁻¹ (σ * c⁻¹) := hd.symm.inv_left
  have hcyc : c⁻¹.IsCycle := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1.inv
  have hmem : c⁻¹ ∈ (c⁻¹ * (σ * c⁻¹)).cycleFactorsFinset := by
    rw [hdis.cycleFactorsFinset_mul_eq_union, hcyc.cycleFactorsFinset_eq_singleton]
    simp
  have ha' : a ∈ c⁻¹.support := by rwa [Equiv.Perm.support_inv]
  exact (Equiv.Perm.cycle_is_cycleOf ha' hmem).symm

lemma cycleOf_reverse_odd_of_not_mem {α : Type*} [Fintype α] [DecidableEq α]
    {σ c : Perm α} (hc : c ∈ σ.cycleFactorsFinset) {a : α} (ha : a ∉ c.support) :
    (c⁻¹ * (σ * c⁻¹)).cycleOf a = σ.cycleOf a := by
  have hd := Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc
  have hσeq := eq_mul_remainder_of_mem_cycleFactorsFinset hc
  have hcx : c a = a := Equiv.Perm.notMem_support.mp ha
  have hc1 : c.cycleOf a = 1 := (Equiv.Perm.cycleOf_eq_one_iff c).mpr hcx
  have hinv1 : c⁻¹.cycleOf a = 1 :=
    (Equiv.Perm.cycleOf_eq_one_iff c⁻¹).mpr (inv_apply_eq_self_of_apply_eq_self hcx)
  have hdis : Equiv.Perm.Disjoint c⁻¹ (σ * c⁻¹) := hd.symm.inv_left
  have hcyσ : σ.cycleOf a = (σ * c⁻¹).cycleOf a := by
    have hleft : σ.cycleOf a = (c * (σ * c⁻¹)).cycleOf a :=
      congrArg (fun f => f.cycleOf a) hσeq
    rw [hleft, Equiv.Perm.Disjoint.cycleOf_mul_distrib hd.symm a, hc1, one_mul]
  have hcyσ' : (c⁻¹ * (σ * c⁻¹)).cycleOf a = (σ * c⁻¹).cycleOf a := by
    rw [Equiv.Perm.Disjoint.cycleOf_mul_distrib hdis a, hinv1, one_mul]
  rw [hcyσ', hcyσ]

lemma oddLongPoints_reverse_odd_cycle {α : Type*} [Fintype α] [DecidableEq α]
    {σ c : Perm α} (hc : c ∈ σ.cycleFactorsFinset) :
    oddLongPoints (c⁻¹ * (σ * c⁻¹)) = oddLongPoints σ := by
  ext a
  simp only [mem_oddLongPoints]
  by_cases ha : a ∈ c.support
  · rw [cycleOf_reverse_odd_of_mem hc ha, Equiv.Perm.support_inv,
      Equiv.Perm.cycle_is_cycleOf ha hc]
  · rw [cycleOf_reverse_odd_of_not_mem hc ha]

/-- Reverse the distinguished odd cycle of `σ`, the cycle of the least odd-cycle point. -/
noncomputable def reverseOddCycle {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (σ : Perm α) : Perm α :=
  if h : (oddLongPoints σ).Nonempty then
    (σ.cycleOf ((oddLongPoints σ).min' h))⁻¹ *
      (σ * (σ.cycleOf ((oddLongPoints σ).min' h))⁻¹)
  else
    σ

lemma reverseOddCycle_of_nonempty {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {σ : Perm α} (h : (oddLongPoints σ).Nonempty) :
    reverseOddCycle σ =
      (σ.cycleOf ((oddLongPoints σ).min' h))⁻¹ *
        (σ * (σ.cycleOf ((oddLongPoints σ).min' h))⁻¹) :=
  dif_pos h

lemma reverseOddCycle_of_empty {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {σ : Perm α} (h : ¬ (oddLongPoints σ).Nonempty) :
    reverseOddCycle σ = σ :=
  dif_neg h

lemma cayleyWeight_reverseOddCycle {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (x : α → ℂ) (σ : Perm α) :
    cayleyWeight x (reverseOddCycle σ) =
      if (oddLongPoints σ).Nonempty then - cayleyWeight x σ
      else cayleyWeight x σ := by
  by_cases h : (oddLongPoints σ).Nonempty
  · rw [if_pos h, reverseOddCycle_of_nonempty h]
    exact cayleyWeight_reverse_odd_cycle x
      (odd_cycleOf_min_mem_cycleFactorsFinset h) (odd_cycleOf_min_odd h)
  · rw [if_neg h, reverseOddCycle_of_empty h]

lemma oddLongPoints_reverseOddCycle {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (σ : Perm α) :
    oddLongPoints (reverseOddCycle σ) = oddLongPoints σ := by
  by_cases h : (oddLongPoints σ).Nonempty
  · rw [reverseOddCycle_of_nonempty h]
    exact oddLongPoints_reverse_odd_cycle (odd_cycleOf_min_mem_cycleFactorsFinset h)
  · rw [reverseOddCycle_of_empty h]

lemma reverseOddCycle_cycleOf_min {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {σ : Perm α} (h : (oddLongPoints σ).Nonempty) :
    (reverseOddCycle σ).cycleOf ((oddLongPoints σ).min' h) =
      (σ.cycleOf ((oddLongPoints σ).min' h))⁻¹ := by
  rw [reverseOddCycle_of_nonempty h]
  exact cycleOf_reverse_odd_of_mem (odd_cycleOf_min_mem_cycleFactorsFinset h)
    (Equiv.Perm.mem_support.mpr (by
      rw [Equiv.Perm.cycleOf_apply_self]
      exact odd_cycleOf_min_ne_self h))

lemma reverse_odd_cycle_mul_inv {α : Type*} [Fintype α] [DecidableEq α]
    {σ c : Perm α} (hc : c ∈ σ.cycleFactorsFinset) :
    c * ((c⁻¹ * (σ * c⁻¹)) * c) = σ := by
  have hd := Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc
  have hdis : Equiv.Perm.Disjoint c⁻¹ (σ * c⁻¹) := hd.symm.inv_left
  have hσeq := eq_mul_remainder_of_mem_cycleFactorsFinset hc
  have hmul : (c⁻¹ * (σ * c⁻¹)) * c = σ * c⁻¹ := by
    rw [hdis.commute.eq]
    simp
  rw [hmul, ← hσeq]

lemma reverseOddCycle_involutive {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] :
    Function.Involutive (reverseOddCycle : Perm α → Perm α) := by
  intro σ
  by_cases h : (oddLongPoints σ).Nonempty
  · have hne' : (oddLongPoints (reverseOddCycle σ)).Nonempty := by
      rwa [oddLongPoints_reverseOddCycle]
    have hmin : (oddLongPoints (reverseOddCycle σ)).min' hne' =
        (oddLongPoints σ).min' h := by
      apply le_antisymm
      · exact (isLeast_min' _ hne').2 (by
          rw [oddLongPoints_reverseOddCycle]
          exact min'_mem _ h)
      · exact (isLeast_min' _ h).2 (by
          rw [← oddLongPoints_reverseOddCycle]
          exact min'_mem _ hne')
    rw [reverseOddCycle_of_nonempty hne', hmin, reverseOddCycle_cycleOf_min h, inv_inv,
      reverseOddCycle_of_nonempty h]
    exact reverse_odd_cycle_mul_inv (odd_cycleOf_min_mem_cycleFactorsFinset h)
  · rw [reverseOddCycle_of_empty h, reverseOddCycle_of_empty h]

lemma sum_cayleyWeight_eq_sum_no_odd {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] (x : α → ℂ) :
    (∑ σ : Perm α, cayleyWeight x σ) =
      ∑ σ : Perm α, if (oddLongPoints σ).Nonempty then 0 else cayleyWeight x σ := by
  have hrev :
      (∑ σ : Perm α, cayleyWeight x (reverseOddCycle σ)) =
        ∑ σ : Perm α, cayleyWeight x σ :=
    Equiv.sum_comp (reverseOddCycle_involutive.toPerm reverseOddCycle) (cayleyWeight x)
  have hsum :
      (∑ σ : Perm α, (cayleyWeight x σ + cayleyWeight x (reverseOddCycle σ))) =
        2 * ∑ σ : Perm α, cayleyWeight x σ := by
    rw [sum_add_distrib, hrev, two_mul]
  have hterm : ∀ σ : Perm α,
      cayleyWeight x σ + cayleyWeight x (reverseOddCycle σ) =
        if (oddLongPoints σ).Nonempty then 0 else 2 * cayleyWeight x σ := by
    intro σ
    by_cases h : (oddLongPoints σ).Nonempty
    · rw [if_pos h, cayleyWeight_reverseOddCycle, if_pos h]
      ring
    · rw [if_neg h, cayleyWeight_reverseOddCycle, if_neg h]
      ring
  have hite : ∀ σ : Perm α,
      (if (oddLongPoints σ).Nonempty then (0 : ℂ) else 2 * cayleyWeight x σ) =
        2 * (if (oddLongPoints σ).Nonempty then 0 else cayleyWeight x σ) := by
    intro σ
    split_ifs <;> ring
  have hsum' :
      (∑ σ : Perm α, (cayleyWeight x σ + cayleyWeight x (reverseOddCycle σ))) =
        2 * ∑ σ : Perm α, if (oddLongPoints σ).Nonempty then 0 else cayleyWeight x σ := by
    rw [Fintype.sum_congr _ _ hterm, Fintype.sum_congr _ _ hite, mul_sum]
  exact mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0) (hsum.symm.trans hsum')

lemma permanent_sunMatrix_eq_sum_no_odd {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n)) :
    (sunMatrix n ζ).permanent =
      ∑ σ : Perm (Fin (2 * n)),
        if (oddLongPoints σ).Nonempty then 0
        else cayleyWeight (fun i => ζ ^ i.val) σ := by
  rw [permanent_sunMatrix_eq_sum_cayleyWeight hn hζ]
  exact sum_cayleyWeight_eq_sum_no_odd _

lemma oddLongPoints_eq_empty_iff {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α} :
    oddLongPoints σ = ∅ ↔ ∀ c ∈ σ.cycleFactorsFinset, Even c.support.card := by
  rw [← not_nonempty_iff_eq_empty, oddLongPoints_nonempty_iff]
  simp only [not_exists, not_and, Nat.not_odd_iff_even]

lemma oddLongPoints_one {α : Type*} [Fintype α] [DecidableEq α] :
    oddLongPoints (1 : Perm α) = ∅ := by
  ext a
  simp [mem_oddLongPoints, Equiv.Perm.cycleOf_one, Equiv.Perm.support_one]

lemma oddLongPoints_swap {α : Type*} [Fintype α] [DecidableEq α]
    {a b : α} (h : a ≠ b) : oddLongPoints (Equiv.swap a b) = ∅ := by
  ext x
  simp only [mem_oddLongPoints]
  have hodd : ¬ Odd ((Equiv.swap a b).cycleOf x).support.card := by
    by_cases hx : x = a ∨ x = b
    · have hxsup : x ∈ (Equiv.swap a b).support := by
        rw [Equiv.Perm.support_swap h]
        simpa using hx
      have : (Equiv.swap a b).cycleOf x = Equiv.swap a b :=
        Equiv.Perm.IsCycle.cycleOf_eq (Equiv.Perm.isCycle_swap h)
          (Equiv.Perm.mem_support.mp hxsup)
      rw [this, Equiv.Perm.support_swap h]
      have hcard : ({a, b} : Finset α).card = 2 := by
        rw [card_insert_of_notMem (by simp [h]), card_singleton]
      simp [hcard]
    · have hxab : x ≠ a ∧ x ≠ b := by
        simp only [not_or] at hx
        exact hx
      have hfix : Equiv.swap a b x = x := swap_apply_of_ne_of_ne hxab.1 hxab.2
      have h1 : (Equiv.swap a b).cycleOf x = 1 :=
        (Equiv.Perm.cycleOf_eq_one_iff _).mpr hfix
      simp [h1, Equiv.Perm.support_one]
  simp [hodd]

lemma cayleyWeight_swap {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {a b : α} (h : a ≠ b) :
    cayleyWeight x (Equiv.swap a b) =
      (x a + x b) / (x a - x b) * ((x b + x a) / (x b - x a)) := by
  unfold cayleyWeight
  rw [Equiv.Perm.support_swap h, prod_insert (by simp [h]), prod_singleton]
  simp [swap_apply_left, swap_apply_right]

lemma cayleyWeight_swap_sq {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {a b : α} (h : a ≠ b) :
    cayleyWeight x (Equiv.swap a b) = - ((x a + x b) / (x a - x b)) ^ 2 := by
  rw [cayleyWeight_swap x h, cayleyFactor_swap (x a) (x b)]
  ring

lemma one_add_cayleyWeight_swap {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {a b : α} (hab : a ≠ b) (hx : x a ≠ x b) :
    1 + cayleyWeight x (Equiv.swap a b) =
      -4 * x a * x b / (x a - x b) ^ 2 := by
  have hden : x a - x b ≠ 0 := sub_ne_zero.2 hx
  rw [cayleyWeight_swap_sq x hab]
  field_simp [hden]
  ring

lemma cayleyWeight_ofSubtype {α : Type*} [Fintype α] [DecidableEq α]
    {p : α → Prop} [DecidablePred p] (x : α → ℂ) (u : Perm (Subtype p)) :
    cayleyWeight x (Equiv.Perm.ofSubtype u) =
      cayleyWeight (fun q : Subtype p => x q.1) u := by
  simp only [cayleyWeight, Equiv.Perm.support_ofSubtype]
  rw [prod_map]
  refine prod_congr rfl fun q _ => ?_
  simp [Equiv.Perm.ofSubtype_apply_coe]

/-- Cayley-kernel sum after odd cycles of length at least 3 have cancelled. -/
noncomputable def cayleySum {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (x : α → ℂ) : ℂ :=
  ∑ σ : Perm α, if (oddLongPoints σ).Nonempty then 0 else cayleyWeight x σ

lemma permanent_sunMatrix_eq_cayleySum {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n)) :
    (sunMatrix n ζ).permanent = cayleySum (fun i : Fin (2 * n) => ζ ^ i.val) :=
  permanent_sunMatrix_eq_sum_no_odd hn hζ

lemma one_ne_swap_fin_two :
    (1 : Perm (Fin 2)) ≠ Equiv.swap 0 1 := by
  intro h
  have := congr_fun (congr_arg (fun f : Perm (Fin 2) => (f : Fin 2 → Fin 2)) h) 0
  simp at this

lemma cayleySum_fin_two (x : Fin 2 → ℂ) :
    cayleySum x = 1 + cayleyWeight x (Equiv.swap (0 : Fin 2) 1) := by
  unfold cayleySum
  rw [show (univ : Finset (Perm (Fin 2))) = {1, Equiv.swap 0 1} from
    univ_perm_fin_two]
  rw [sum_insert (by simp [one_ne_swap_fin_two]), sum_singleton]
  have h1 : ¬ (oddLongPoints (1 : Perm (Fin 2))).Nonempty := by
    simp [oddLongPoints_one]
  have hs : ¬ (oddLongPoints (Equiv.swap (0 : Fin 2) 1)).Nonempty := by
    simp [oddLongPoints_swap Fin.zero_ne_one]
  rw [if_neg h1, if_neg hs, cayleyWeight_one]

lemma cayleySum_fin_two_eq {x : Fin 2 → ℂ} (hx : x 0 ≠ x 1) :
    cayleySum x = -4 * x 0 * x 1 / (x 0 - x 1) ^ 2 := by
  rw [cayleySum_fin_two, one_add_cayleyWeight_swap x Fin.zero_ne_one hx]

lemma disjoint_swap_of_fixed {α : Type*} [DecidableEq α] {p q : α} (_hpq : p ≠ q)
    {τ : Perm α} (hp : τ p = p) (hq : τ q = q) :
    Equiv.Perm.Disjoint (Equiv.swap p q) τ := by
  intro x
  by_cases hxp : x = p
  · right
    rw [hxp, hp]
  · by_cases hxq : x = q
    · right
      rw [hxq, hq]
    · left
      exact swap_apply_of_ne_of_ne hxp hxq

lemma cycleOf_mul_swap_of_mem {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (hpq : p ≠ q) {τ : Perm α}
    (hdis : Equiv.Perm.Disjoint (Equiv.swap p q) τ) {x : α}
    (hx : x = p ∨ x = q) :
    (Equiv.swap p q * τ).cycleOf x = Equiv.swap p q := by
  have hsw : (Equiv.swap p q).IsCycle := Equiv.Perm.isCycle_swap hpq
  have hxsup : x ∈ (Equiv.swap p q).support := by
    rw [Equiv.Perm.support_swap hpq]
    simpa using hx
  have hτx : τ x = x := by
    have := hdis x
    have hne : Equiv.swap p q x ≠ x := Equiv.Perm.mem_support.mp hxsup
    exact this.resolve_left hne
  have hmem : Equiv.swap p q ∈ (Equiv.swap p q * τ).cycleFactorsFinset := by
    rw [hdis.cycleFactorsFinset_mul_eq_union, hsw.cycleFactorsFinset_eq_singleton]
    simp
  exact (Equiv.Perm.cycle_is_cycleOf hxsup hmem).symm

lemma cycleOf_mul_swap_of_not_mem {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (_hpq : p ≠ q) {τ : Perm α}
    (hdis : Equiv.Perm.Disjoint (Equiv.swap p q) τ) {x : α}
    (hx : x ≠ p ∧ x ≠ q) :
    (Equiv.swap p q * τ).cycleOf x = τ.cycleOf x := by
  have hswx : Equiv.swap p q x = x := swap_apply_of_ne_of_ne hx.1 hx.2
  have h1 : (Equiv.swap p q).cycleOf x = 1 :=
    (Equiv.Perm.cycleOf_eq_one_iff _).mpr hswx
  rw [Equiv.Perm.Disjoint.cycleOf_mul_distrib hdis x, h1, one_mul]

lemma oddLongPoints_mul_swap {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (hpq : p ≠ q) {τ : Perm α}
    (hdis : Equiv.Perm.Disjoint (Equiv.swap p q) τ) :
    oddLongPoints (Equiv.swap p q * τ) = oddLongPoints τ := by
  ext x
  simp only [mem_oddLongPoints]
  by_cases hx : x = p ∨ x = q
  · rw [cycleOf_mul_swap_of_mem hpq hdis hx, Equiv.Perm.support_swap hpq]
    have hcard : ({p, q} : Finset α).card = 2 := by
      rw [card_insert_of_notMem (by simp [hpq]), card_singleton]
    have hτx : τ x = x := by
      have hxsup : x ∈ (Equiv.swap p q).support := by
        rw [Equiv.Perm.support_swap hpq]
        simpa using hx
      have hne : Equiv.swap p q x ≠ x := Equiv.Perm.mem_support.mp hxsup
      exact (hdis x).resolve_left hne
    have h1 : τ.cycleOf x = 1 := (Equiv.Perm.cycleOf_eq_one_iff τ).mpr hτx
    simp [hcard, h1, Equiv.Perm.support_one]
  · have hxab : x ≠ p ∧ x ≠ q := by
      simp only [not_or] at hx
      exact hx
    rw [cycleOf_mul_swap_of_not_mem hpq hdis hxab]

lemma ofSubtype_zpow {α : Type*} [DecidableEq α] {p : α → Prop} [DecidablePred p]
    (u : Perm (Subtype p)) (n : ℤ) :
    Equiv.Perm.ofSubtype u ^ n = Equiv.Perm.ofSubtype (u ^ n) :=
  (MonoidHom.map_zpow Equiv.Perm.ofSubtype u n).symm

lemma sameCycle_ofSubtype_coe {α : Type*} [DecidableEq α] {s : Finset α}
    (u : Perm {a // a ∈ s}) {x y : {a // a ∈ s}} :
    Equiv.Perm.SameCycle (Equiv.Perm.ofSubtype u) x.1 y.1 ↔
      Equiv.Perm.SameCycle u x y := by
  constructor
  · intro ⟨n, h⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    rw [← h, ofSubtype_zpow, Equiv.Perm.ofSubtype_apply_coe]
  · intro ⟨n, h⟩
    refine ⟨n, ?_⟩
    rw [ofSubtype_zpow, Equiv.Perm.ofSubtype_apply_coe]
    exact congrArg Subtype.val h

lemma sameCycle_ofSubtype_mem {α : Type*} [DecidableEq α] {s : Finset α}
    (u : Perm {a // a ∈ s}) {x y : α} (hx : x ∈ s)
    (h : Equiv.Perm.SameCycle (Equiv.Perm.ofSubtype u) x y) : y ∈ s := by
  obtain ⟨n, hxy⟩ := h
  rw [ofSubtype_zpow, Equiv.Perm.ofSubtype_apply_of_mem _ hx] at hxy
  exact hxy ▸ ((u ^ n) ⟨x, hx⟩).2

lemma support_cycleOf_ofSubtype {α : Type*} [Fintype α] [DecidableEq α] {s : Finset α}
    (u : Perm {a // a ∈ s}) {x : α} (hx : x ∈ s) :
    ((Equiv.Perm.ofSubtype u).cycleOf x).support =
      (u.cycleOf ⟨x, hx⟩).support.map (Function.Embedding.subtype (fun a => a ∈ s)) := by
  ext y
  simp only [Equiv.Perm.mem_support_cycleOf_iff, mem_map, Function.Embedding.coe_subtype]
  constructor
  · intro ⟨hsame, hsup⟩
    have hy : y ∈ s := sameCycle_ofSubtype_mem u hx hsame
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    constructor
    · exact (sameCycle_ofSubtype_coe u).1 hsame
    · have hne : Equiv.Perm.ofSubtype u x ≠ x := Equiv.Perm.mem_support.mp hsup
      exact Equiv.Perm.mem_support.mpr fun h =>
        hne (by
          rw [Equiv.Perm.ofSubtype_apply_of_mem u hx]
          exact congrArg Subtype.val h)
  · intro ⟨z, hmem, hz⟩
    subst hz
    constructor
    · exact (sameCycle_ofSubtype_coe u).2 hmem.1
    · have hne : u ⟨x, hx⟩ ≠ ⟨x, hx⟩ := Equiv.Perm.mem_support.mp hmem.2
      exact Equiv.Perm.mem_support.mpr fun h =>
        hne (Subtype.ext (by
          rw [← Equiv.Perm.ofSubtype_apply_of_mem u hx]
          exact h))

lemma oddLongPoints_ofSubtype_nonempty_iff {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} (u : Perm {a // a ∈ s}) :
    (oddLongPoints (Equiv.Perm.ofSubtype u)).Nonempty ↔
      (oddLongPoints u).Nonempty := by
  constructor
  · intro ⟨x, hx⟩
    rw [mem_oddLongPoints] at hx
    have hmove : Equiv.Perm.ofSubtype u x ≠ x := odd_card_cycleOf_ne_self hx
    have hxs : x ∈ s := by
      by_contra hns
      exact hmove (Equiv.Perm.ofSubtype_apply_of_not_mem u hns)
    refine ⟨⟨x, hxs⟩, mem_oddLongPoints.mpr ?_⟩
    rw [support_cycleOf_ofSubtype u hxs, card_map] at hx
    exact hx
  · intro ⟨⟨x, hxs⟩, hx⟩
    rw [mem_oddLongPoints] at hx
    refine ⟨x, mem_oddLongPoints.mpr ?_⟩
    rwa [support_cycleOf_ofSubtype u hxs, card_map]

lemma cayleySum_ofSubtype {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {s : Finset α} (x : α → ℂ) (u : Perm {a // a ∈ s}) :
    (if (oddLongPoints (Equiv.Perm.ofSubtype u)).Nonempty then (0 : ℂ)
      else cayleyWeight x (Equiv.Perm.ofSubtype u)) =
      if (oddLongPoints u).Nonempty then 0
      else cayleyWeight (fun a : {a // a ∈ s} => x a.1) u := by
  by_cases h : (oddLongPoints (Equiv.Perm.ofSubtype u)).Nonempty
  · have h' : (oddLongPoints u).Nonempty :=
      (oddLongPoints_ofSubtype_nonempty_iff u).1 h
    simp [h, h']
  · have h' : ¬ (oddLongPoints u).Nonempty := fun hne =>
      h ((oddLongPoints_ofSubtype_nonempty_iff u).2 hne)
    rw [if_neg h, if_neg h']
    convert cayleyWeight_ofSubtype (p := fun a => a ∈ s) x u

/-- Cayley-kernel even-cycle sum on a subset. -/
noncomputable def cayleySumOn {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (s : Finset α) (x : α → ℂ) : ℂ :=
  cayleySum (fun a : {a // a ∈ s} => x a.1)

lemma ofSubtype_fixes_pair {α : Type*} [Fintype α] [DecidableEq α] {p q : α}
    (u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ}) :
    Equiv.Perm.ofSubtype u p = p ∧ Equiv.Perm.ofSubtype u q = q := by
  constructor
  · exact Equiv.Perm.ofSubtype_apply_of_not_mem u (by simp)
  · exact Equiv.Perm.ofSubtype_apply_of_not_mem u (by simp)

lemma disjoint_swap_ofSubtype_pair {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (hpq : p ≠ q) (u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ}) :
    Equiv.Perm.Disjoint (Equiv.swap p q) (Equiv.Perm.ofSubtype u) :=
  disjoint_swap_of_fixed hpq (ofSubtype_fixes_pair u).1 (ofSubtype_fixes_pair u).2

lemma swap_mul_ofSubtype_apply {α : Type*} [Fintype α] [DecidableEq α] {p q : α}
    (u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ}) :
    (Equiv.swap p q * Equiv.Perm.ofSubtype u) p = q := by
  change Equiv.swap p q (Equiv.Perm.ofSubtype u p) = q
  rw [(ofSubtype_fixes_pair u).1, swap_apply_left]

lemma cycleOf_swap_mul_ofSubtype {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (hpq : p ≠ q) (u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ}) :
    (Equiv.swap p q * Equiv.Perm.ofSubtype u).cycleOf p = Equiv.swap p q :=
  cycleOf_mul_swap_of_mem hpq (disjoint_swap_ofSubtype_pair hpq u) (Or.inl rfl)

lemma cayleySum_term_swap_ofSubtype {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] {p q : α} (hpq : p ≠ q) (x : α → ℂ)
    (u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ}) :
    (if (oddLongPoints (Equiv.swap p q * Equiv.Perm.ofSubtype u)).Nonempty then (0 : ℂ)
      else cayleyWeight x (Equiv.swap p q * Equiv.Perm.ofSubtype u)) =
      cayleyWeight x (Equiv.swap p q) *
        (if (oddLongPoints u).Nonempty then 0
          else cayleyWeight (fun a : {a // a ∈ ({p, q} : Finset α)ᶜ} => x a.1) u) := by
  have hdis := disjoint_swap_ofSubtype_pair hpq u
  rw [oddLongPoints_mul_swap hpq hdis, cayleyWeight_mul_disjoint x hdis]
  have hfac :
      (if (oddLongPoints (Equiv.Perm.ofSubtype u)).Nonempty then (0 : ℂ)
        else cayleyWeight x (Equiv.swap p q) *
          cayleyWeight x (Equiv.Perm.ofSubtype u)) =
        cayleyWeight x (Equiv.swap p q) *
          (if (oddLongPoints (Equiv.Perm.ofSubtype u)).Nonempty then 0
            else cayleyWeight x (Equiv.Perm.ofSubtype u)) := by
    split_ifs <;> ring
  rw [hfac]
  exact congrArg (fun t => cayleyWeight x (Equiv.swap p q) * t) (cayleySum_ofSubtype x u)

lemma sum_cayleySum_term_swap_ofSubtype {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] {p q : α} (hpq : p ≠ q) (x : α → ℂ) :
    (∑ u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ},
      if (oddLongPoints (Equiv.swap p q * Equiv.Perm.ofSubtype u)).Nonempty then (0 : ℂ)
      else cayleyWeight x (Equiv.swap p q * Equiv.Perm.ofSubtype u)) =
      cayleyWeight x (Equiv.swap p q) * cayleySumOn ({p, q} : Finset α)ᶜ x := by
  simp_rw [cayleySum_term_swap_ofSubtype hpq x]
  rw [← mul_sum]
  rfl

lemma ne_of_cycleOf_support_card_two {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} {p : α} (h : (σ.cycleOf p).support.card = 2) : σ p ≠ p := by
  intro hfix
  have h1 : σ.cycleOf p = 1 := (Equiv.Perm.cycleOf_eq_one_iff σ).mpr hfix
  have h0 : (σ.cycleOf p).support.card = 0 := by
    rw [h1, Equiv.Perm.support_one, card_empty]
  omega

lemma cycleOf_eq_swap_of_card_two {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} {p : α} (h : (σ.cycleOf p).support.card = 2) :
    σ.cycleOf p = Equiv.swap p (σ p) := by
  have hp := ne_of_cycleOf_support_card_two h
  have hf : Equiv.Perm.IsSwap (σ.cycleOf p) :=
    (Equiv.Perm.card_support_eq_two).mp h
  obtain ⟨a, b, hab, heq⟩ := hf
  have hp_mem : p ∈ (σ.cycleOf p).support :=
    Equiv.Perm.mem_support.mpr (by
      rw [Equiv.Perm.cycleOf_apply_self σ p]
      exact hp)
  have hpab : p = a ∨ p = b := by
    rw [heq, Equiv.Perm.support_swap hab, mem_insert, mem_singleton] at hp_mem
    exact hp_mem
  have happ : (σ.cycleOf p) p = σ p := Equiv.Perm.cycleOf_apply_self σ p
  rcases hpab with hpa | hpb
  · subst hpa
    have hb : b = σ p := by
      rw [heq, swap_apply_left] at happ
      exact happ
    rw [heq, hb]
  · subst hpb
    have ha : a = σ p := by
      rw [heq, swap_apply_right] at happ
      exact happ
    rw [heq, ha, Equiv.swap_comm]

lemma swap_mem_cycleFactors_of_cycleOf {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (hpq : p ≠ q) {σ : Perm α} (h : σ.cycleOf p = Equiv.swap p q) :
    Equiv.swap p q ∈ σ.cycleFactorsFinset := by
  have hp : p ∈ σ.support := by
    rw [Equiv.Perm.mem_support]
    have happ := Equiv.Perm.cycleOf_apply_self σ p
    rw [h, swap_apply_left] at happ
    exact happ ▸ hpq.symm
  have hmem : σ.cycleOf p ∈ σ.cycleFactorsFinset :=
    (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff).2 hp
  rwa [h] at hmem

lemma remainder_support_subset_cycle_compl {α : Type*} [Fintype α] [DecidableEq α]
    {σ c : Perm α} (hc : c ∈ σ.cycleFactorsFinset) :
    (σ * c⁻¹).support ⊆ c.supportᶜ := by
  intro x hx
  rw [mem_compl]
  intro hxmem
  exact (Equiv.Perm.notMem_support.mpr (remainder_apply_eq_self_of_mem hc hxmem)) hx

lemma eq_swap_mul_remainder {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (hpq : p ≠ q) {σ : Perm α} (h : σ.cycleOf p = Equiv.swap p q) :
    σ = Equiv.swap p q * (σ * Equiv.swap p q) := by
  have hσeq := eq_mul_remainder_of_mem_cycleFactorsFinset
    (swap_mem_cycleFactors_of_cycleOf hpq h)
  rwa [Equiv.swap_inv] at hσeq

lemma exists_eq_swap_mul_ofSubtype {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (hpq : p ≠ q) {σ : Perm α} (h : σ.cycleOf p = Equiv.swap p q) :
    ∃ u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ},
      σ = Equiv.swap p q * Equiv.Perm.ofSubtype u := by
  have hc := swap_mem_cycleFactors_of_cycleOf hpq h
  have hsub : (σ * Equiv.swap p q).support ⊆ ({p, q} : Finset α)ᶜ := by
    have hrem : (σ * (Equiv.swap p q)⁻¹).support ⊆ (Equiv.swap p q).supportᶜ :=
      remainder_support_subset_cycle_compl hc
    rwa [Equiv.swap_inv, Equiv.Perm.support_swap hpq] at hrem
  refine ⟨(σ * Equiv.swap p q).subtypePerm fun x =>
      (mem_of_support_subset hsub x).symm, ?_⟩
  have hrec := ofSubtype_subtypePerm_of_support_subset hsub
  rw [hrec]
  exact eq_swap_mul_remainder hpq h

lemma swap_eq_swap_iff_right {α : Type*} [DecidableEq α] {p q q' : α}
    (_hpq : p ≠ q) (h : Equiv.swap p q = Equiv.swap p q') : q = q' := by
  have := congr_fun (congr_arg (fun f : Perm α => (f : α → α)) h) p
  simpa [swap_apply_left] using this

noncomputable def equiv_remainder_of_swap_cycle {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (hpq : p ≠ q) :
    Perm {a // a ∈ ({p, q} : Finset α)ᶜ} ≃
      {σ : Perm α // σ.cycleOf p = Equiv.swap p q} :=
  Equiv.ofBijective
    (fun u => ⟨Equiv.swap p q * Equiv.Perm.ofSubtype u, cycleOf_swap_mul_ofSubtype hpq u⟩)
    ⟨fun u v h =>
        Equiv.Perm.ofSubtype_injective (mul_left_cancel (congrArg Subtype.val h)),
      fun σ => by
        obtain ⟨u, hu⟩ := exists_eq_swap_mul_ofSubtype hpq σ.2
        exact ⟨u, Subtype.ext hu.symm⟩⟩

lemma sum_fiber_swap_ofSubtype {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (hpq : p ≠ q) (f : Perm α → ℂ) :
    (∑ σ : Perm α, if σ.cycleOf p = Equiv.swap p q then f σ else 0) =
      ∑ u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ},
        f (Equiv.swap p q * Equiv.Perm.ofSubtype u) := by
  have hsub :
      (∑ σ ∈ univ.filter (fun σ : Perm α => σ.cycleOf p = Equiv.swap p q), f σ) =
        ∑ σ : {σ : Perm α // σ.cycleOf p = Equiv.swap p q}, f σ.1 :=
    sum_subtype (univ.filter (fun σ : Perm α => σ.cycleOf p = Equiv.swap p q))
      (fun σ => by simp) f
  calc (∑ σ : Perm α, if σ.cycleOf p = Equiv.swap p q then f σ else 0)
      = ∑ σ ∈ univ.filter (fun σ : Perm α => σ.cycleOf p = Equiv.swap p q), f σ :=
        (sum_filter (fun σ : Perm α => σ.cycleOf p = Equiv.swap p q) f).symm
    _ = ∑ σ : {σ : Perm α // σ.cycleOf p = Equiv.swap p q}, f σ.1 := hsub
    _ = ∑ u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ},
          f (equiv_remainder_of_swap_cycle hpq u).1 :=
        (Equiv.sum_comp (equiv_remainder_of_swap_cycle hpq) (fun σ => f σ.1)).symm
    _ = ∑ u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ},
          f (Equiv.swap p q * Equiv.Perm.ofSubtype u) :=
        rfl

lemma cayleySum_sigma2 {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (p : α) (x : α → ℂ) :
    (∑ σ : Perm α,
        if (σ.cycleOf p).support.card = 2 then
          (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
        else 0) =
      ∑ q : α, if q = p then 0 else
        cayleyWeight x (Equiv.swap p q) * cayleySumOn ({p, q} : Finset α)ᶜ x := by
  have hsplit : ∀ σ : Perm α,
      (if (σ.cycleOf p).support.card = 2 then
        (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
      else 0) =
        ∑ q : α, if q = p then 0 else
          if σ.cycleOf p = Equiv.swap p q then
            (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
          else 0 := by
    intro σ
    by_cases hcard : (σ.cycleOf p).support.card = 2
    · have hp := ne_of_cycleOf_support_card_two hcard
      have hcy := cycleOf_eq_swap_of_card_two hcard
      rw [if_pos hcard]
      have hsum :
          (∑ q : α, if q = p then (0 : ℂ) else
            if σ.cycleOf p = Equiv.swap p q then
              (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
            else 0) =
            if σ p = p then (0 : ℂ) else
              if σ.cycleOf p = Equiv.swap p (σ p) then
                (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
              else 0 :=
        Fintype.sum_eq_single (σ p) fun q hq => by
          by_cases hqp : q = p
          · simp [hqp]
          · have hne : σ.cycleOf p ≠ Equiv.swap p q := fun hsw =>
              hq (swap_eq_swap_iff_right (p := p) hp.symm (hcy.symm.trans hsw)).symm
            simp [hqp, hne]
      rw [hsum]
      simp [hp, hcy]
    · rw [if_neg hcard]
      refine (sum_eq_zero fun q _ => ?_).symm
      by_cases hpq : q = p
      · simp [hpq]
      · have hpq' : p ≠ q := fun h => hpq h.symm
        simp only [hpq, ↓reduceIte]
        by_cases hcy : σ.cycleOf p = Equiv.swap p q
        · exact (hcard (by simp [hcy, Equiv.Perm.card_support_swap hpq'])).elim
        · simp [hcy]
  refine (Fintype.sum_congr _ _ hsplit).trans ?_
  rw [sum_comm]
  refine Fintype.sum_congr _ _ fun q => ?_
  by_cases hpq : q = p
  · simp [hpq]
  · have hpq' : p ≠ q := fun h => hpq h.symm
    simp only [hpq, ↓reduceIte]
    rw [sum_fiber_swap_ofSubtype hpq'
      (fun σ => if (oddLongPoints σ).Nonempty then 0 else cayleyWeight x σ)]
    exact sum_cayleySum_term_swap_ofSubtype hpq' x

/-- She–Sun–Xia (2.4). -/
lemma cayley_triple_identity (x y z : ℂ)
    (hyz : y + z ≠ 0) (hxz : x ≠ z) (hyx : y ≠ x) :
    (y - z) / (y + z) * (x + z) / (x - z) * (y + x) / (y - x) =
      (z - y) / (z + y) + 2 * x * ((x - z)⁻¹ - (x - y)⁻¹) := by
  have hyx0 : y - x ≠ 0 := sub_ne_zero.2 hyx
  have hxz0 : x - z ≠ 0 := sub_ne_zero.2 hxz
  have hzy : z + y ≠ 0 := by rw [add_comm]; exact hyz
  field_simp [hyz, hyx0, hxz0, hzy]
  ring

lemma cayleyWeight_formPerm {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {l : List α} (hl : l.Nodup) (h2 : 2 ≤ l.length) :
    cayleyWeight x l.formPerm =
      ∏ i : Fin l.length,
        (x (l[i.val]) +
            x (l[(i.val + 1) % l.length]'(Nat.mod_lt _ (by omega)))) /
        (x (l[i.val]) -
            x (l[(i.val + 1) % l.length]'(Nat.mod_lt _ (by omega)))) := by
  have hne : ∀ a : α, l ≠ [a] := by
    intro a h
    simp [h] at h2
  rw [cayleyWeight, List.support_formPerm_of_nodup l hl hne, prod_toFinset_getElem hl]
  refine prod_congr rfl fun i _ => ?_
  rw [List.formPerm_apply_getElem l hl i.val i.isLt]

/-- Inserting `p` on the closing edge of `L` multiplies the remaining Cayley weight
by the three-point kernel, after clearing the skipped `L`-edge. -/
lemma cayleyWeight_formPerm_cons {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {p : α} {L : List α}
    (hL : L.Nodup) (hp : p ∉ L) (h2 : 2 ≤ L.length)
    (hx : Function.Injective x) :
    cayleyWeight x (List.formPerm (p :: L)) *
        ((x (L[L.length - 1]'(by omega)) + x (L[0]'(by omega))) /
          (x (L[L.length - 1]'(by omega)) - x (L[0]'(by omega)))) =
      cayleyWeight x L.formPerm *
        ((x p + x (L[0]'(by omega))) / (x p - x (L[0]'(by omega)))) *
        ((x (L[L.length - 1]'(by omega)) + x p) /
          (x (L[L.length - 1]'(by omega)) - x p)) := by
  have hl : (p :: L).Nodup := List.nodup_cons.2 ⟨hp, hL⟩
  have hLne : L ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hneG : ∀ a : α, p :: L ≠ [a] := by
    cases L with
    | nil => intro a _; simp at h2
    | cons _ _ => intro a h; simp at h
  have hneL : ∀ a : α, L ≠ [a] := by
    intro a h
    have hlenL : L.length = 1 := by simp [h]
    omega
  unfold cayleyWeight
  rw [List.support_formPerm_of_nodup _ hl hneG,
    List.support_formPerm_of_nodup _ hL hneL, List.toFinset_cons]
  have hp' : p ∉ L.toFinset := by simpa using hp
  rw [prod_insert hp', formPerm_cons_apply_head hl (by omega)]
  have hlast_mem : L.getLast hLne ∈ L.toFinset :=
    List.mem_toFinset.2 (List.getLast_mem hLne)
  rw [← prod_erase_mul L.toFinset _ hlast_mem]
  have hagree :
      ∏ a ∈ L.toFinset.erase (L.getLast hLne),
          (x a + x ((p :: L).formPerm a)) / (x a - x ((p :: L).formPerm a)) =
        ∏ a ∈ L.toFinset.erase (L.getLast hLne),
          (x a + x (L.formPerm a)) / (x a - x (L.formPerm a)) :=
    prod_congr rfl fun a ha => by
      rw [formPerm_cons_apply_of_ne_getLast hl hL hLne
        (List.mem_toFinset.mp (mem_of_mem_erase ha)) (ne_of_mem_erase ha)]
  rw [hagree, formPerm_cons_apply_getLast hLne]
  have hLsplit :
      (∏ i ∈ L.toFinset, (x i + x (L.formPerm i)) / (x i - x (L.formPerm i))) =
        (∏ a ∈ L.toFinset.erase (L.getLast hLne),
            (x a + x (L.formPerm a)) / (x a - x (L.formPerm a))) *
          ((x (L.getLast hLne) + x (L.formPerm (L.getLast hLne))) /
            (x (L.getLast hLne) - x (L.formPerm (L.getLast hLne)))) :=
    (prod_erase_mul L.toFinset
      (fun i => (x i + x (L.formPerm i)) / (x i - x (L.formPerm i))) hlast_mem).symm
  rw [hLsplit, formPerm_apply_getLast_eq_head hL hLne h2]
  have hlast_get : L.getLast hLne = L[L.length - 1]'(by omega) := List.getLast_eq_getElem _
  rw [hlast_get]
  have hx0p : x (L[0]'(by omega)) ≠ x p :=
    hx.ne (ne_of_mem_of_not_mem (List.getElem_mem _) hp)
  have hxpLast : x p ≠ x (L[L.length - 1]'(by omega)) :=
    hx.ne (ne_of_mem_of_not_mem (List.getElem_mem _) hp).symm
  have hxends : x (L[0]'(by omega)) ≠ x (L[L.length - 1]'(by omega)) := by
    refine hx.ne ?_
    exact (List.Nodup.getElem_inj_iff hL).not.mpr (by omega)
  have hne1 : x (L[L.length - 1]'(by omega)) - x (L[0]'(by omega)) ≠ 0 :=
    sub_ne_zero.2 hxends.symm
  have hne2 : x p - x (L[0]'(by omega)) ≠ 0 := sub_ne_zero.2 hx0p.symm
  have hne3 : x (L[L.length - 1]'(by omega)) - x p ≠ 0 := sub_ne_zero.2 hxpLast.symm
  field_simp [hne1, hne2, hne3]

lemma support_subset_compl_of_fixed {α : Type*} [Fintype α] [DecidableEq α]
    {p : α} {σ : Perm α} (h : σ p = p) : σ.support ⊆ ({p} : Finset α)ᶜ := by
  intro x hx
  rw [mem_compl, mem_singleton]
  intro hxp
  subst hxp
  exact Equiv.Perm.mem_support.mp hx h

noncomputable def equiv_remainder_of_fixed {α : Type*} [Fintype α] [DecidableEq α]
    (p : α) : Perm {a // a ∈ ({p} : Finset α)ᶜ} ≃ {σ : Perm α // σ p = p} :=
  Equiv.ofBijective
    (fun u => ⟨Equiv.Perm.ofSubtype u, Equiv.Perm.ofSubtype_apply_of_not_mem u (by simp)⟩)
    ⟨fun u v h => Equiv.Perm.ofSubtype_injective (congrArg Subtype.val h),
      fun σ => by
        have hsub : σ.1.support ⊆ ({p} : Finset α)ᶜ :=
          support_subset_compl_of_fixed σ.2
        refine ⟨σ.1.subtypePerm fun x => (mem_of_support_subset hsub x).symm, ?_⟩
        exact Subtype.ext (ofSubtype_subtypePerm_of_support_subset hsub)⟩

lemma sum_fiber_fixed {α : Type*} [Fintype α] [DecidableEq α]
    (p : α) (f : Perm α → ℂ) :
    (∑ σ : Perm α, if σ p = p then f σ else 0) =
      ∑ u : Perm {a // a ∈ ({p} : Finset α)ᶜ}, f (Equiv.Perm.ofSubtype u) := by
  have hsub :
      (∑ σ ∈ univ.filter (fun σ : Perm α => σ p = p), f σ) =
        ∑ σ : {σ : Perm α // σ p = p}, f σ.1 :=
    sum_subtype (univ.filter (fun σ : Perm α => σ p = p)) (fun σ => by simp) f
  calc (∑ σ : Perm α, if σ p = p then f σ else 0)
      = ∑ σ ∈ univ.filter (fun σ : Perm α => σ p = p), f σ :=
        (sum_filter (fun σ : Perm α => σ p = p) f).symm
    _ = ∑ σ : {σ : Perm α // σ p = p}, f σ.1 := hsub
    _ = ∑ u : Perm {a // a ∈ ({p} : Finset α)ᶜ},
          f (equiv_remainder_of_fixed p u).1 :=
        (Equiv.sum_comp (equiv_remainder_of_fixed p) (fun σ => f σ.1)).symm
    _ = ∑ u : Perm {a // a ∈ ({p} : Finset α)ᶜ}, f (Equiv.Perm.ofSubtype u) :=
        rfl

lemma cayleySum_sigma1 {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (p : α) (x : α → ℂ) :
    (∑ σ : Perm α,
        if σ p = p then
          (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
        else 0) =
      cayleySumOn ({p} : Finset α)ᶜ x := by
  rw [sum_fiber_fixed p
    (fun σ => if (oddLongPoints σ).Nonempty then 0 else cayleyWeight x σ)]
  exact Fintype.sum_congr _ _ fun u => cayleySum_ofSubtype x u

lemma cayleySum_split {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (p : α) (x : α → ℂ) :
    cayleySum x =
      (∑ σ : Perm α,
          if σ p = p then
            (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
          else 0) +
      (∑ σ : Perm α,
          if (σ.cycleOf p).support.card = 2 then
            (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
          else 0) +
      (∑ σ : Perm α,
          if 4 ≤ (σ.cycleOf p).support.card then
            (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
          else 0) := by
  unfold cayleySum
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine Fintype.sum_congr _ _ fun σ => ?_
  by_cases hp : σ p = p
  · have h0 : (σ.cycleOf p).support.card = 0 := by
      have h1 : σ.cycleOf p = 1 := (Equiv.Perm.cycleOf_eq_one_iff σ).mpr hp
      rw [h1, Equiv.Perm.support_one, card_empty]
    have h2 : ¬ (σ.cycleOf p).support.card = 2 := by omega
    have h4 : ¬ 4 ≤ (σ.cycleOf p).support.card := by omega
    simp [hp, h2, h4]
  · have hcard : 2 ≤ (σ.cycleOf p).support.card :=
      Equiv.Perm.IsCycle.two_le_card_support (Equiv.Perm.isCycle_cycleOf σ hp)
    by_cases h2 : (σ.cycleOf p).support.card = 2
    · simp [hp, h2]
    · by_cases h4 : 4 ≤ (σ.cycleOf p).support.card
      · simp [hp, h2, h4]
      · have h3 : (σ.cycleOf p).support.card = 3 := by omega
        have hodd : (oddLongPoints σ).Nonempty := by
          refine ⟨p, mem_oddLongPoints.mpr ?_⟩
          rw [h3]
          exact ⟨1, rfl⟩
        simp [hp, h2, h4, hodd]

lemma cayleySum_eq_sigma1_add_sigma2_add {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] (p : α) (x : α → ℂ) :
    cayleySum x =
      cayleySumOn ({p} : Finset α)ᶜ x +
      (∑ q : α, if q = p then 0 else
        cayleyWeight x (Equiv.swap p q) * cayleySumOn ({p, q} : Finset α)ᶜ x) +
      (∑ σ : Perm α,
          if 4 ≤ (σ.cycleOf p).support.card then
            (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
          else 0) := by
  rw [cayleySum_split p x, cayleySum_sigma1 p x, cayleySum_sigma2 p x]

lemma add_mul_add_eq (t y z : ℂ) :
    (t + y) * (t + z) = (t - y) * (t - z) + 2 * t * (y + z) := by
  ring

lemma cayley_insert_div (t y z : ℂ) (hty : t ≠ y) (htz : t ≠ z) :
    ((t + z) / (t - z)) * ((y + t) / (y - t)) =
      -((t + y) * (t + z) / ((t - y) * (t - z))) := by
  have h1 : t - y ≠ 0 := sub_ne_zero.2 hty
  have h2 : t - z ≠ 0 := sub_ne_zero.2 htz
  have h3 : y - t ≠ 0 := sub_ne_zero.2 (Ne.symm hty)
  field_simp [h1, h2, h3]
  ring

lemma cayley_insert_one_add (t y z : ℂ) (hty : t ≠ y) (htz : t ≠ z) :
    (t + y) * (t + z) / ((t - y) * (t - z)) =
      1 + 2 * t * (y + z) / ((t - y) * (t - z)) := by
  have h1 : t - y ≠ 0 := sub_ne_zero.2 hty
  have h2 : t - z ≠ 0 := sub_ne_zero.2 htz
  field_simp [h1, h2]
  ring

lemma cayley_insert_eq_neg_one_sub (t y z : ℂ) (hty : t ≠ y) (htz : t ≠ z) :
    ((t + z) / (t - z)) * ((y + t) / (y - t)) =
      -1 - 2 * t * (y + z) / ((t - y) * (t - z)) := by
  rw [cayley_insert_div t y z hty htz, cayley_insert_one_add t y z hty htz]
  ring

lemma sub_div_inv_sub (t y z : ℂ) (hty : t ≠ y) (htz : t ≠ z) :
    (y - z) / ((t - y) * (t - z)) = (t - y)⁻¹ - (t - z)⁻¹ := by
  have h1 : t - y ≠ 0 := sub_ne_zero.2 hty
  have h2 : t - z ≠ 0 := sub_ne_zero.2 htz
  field_simp [h1, h2]
  ring

/-- Consecutive Cayley factors along a path, without the closing edge. -/
noncomputable def cayleyPathWeight {α : Type*} (x : α → ℂ) (L : List α) : ℂ :=
  (List.zipWith (fun a b => (x a + x b) / (x a - x b)) L L.tail).prod

lemma cayleyPathWeight_eq_prod_range {α : Type*} (x : α → ℂ) (L : List α) :
    cayleyPathWeight x L =
      ∏ i ∈ range (L.length - 1),
        if h : i + 1 < L.length then
          (x (L[i]'(Nat.lt_of_succ_lt h)) + x (L[i + 1])) /
            (x (L[i]'(Nat.lt_of_succ_lt h)) - x (L[i + 1]))
        else 1 := by
  induction L with
  | nil => simp [cayleyPathWeight]
  | cons a L ih =>
    cases L with
    | nil => simp [cayleyPathWeight]
    | cons b t =>
      have hsplit :
          cayleyPathWeight x (a :: b :: t) =
            (x a + x b) / (x a - x b) * cayleyPathWeight x (b :: t) := by
        unfold cayleyPathWeight
        simp [List.tail_cons, List.zipWith_cons_cons, List.prod_cons]
      have hlen : (a :: b :: t).length - 1 = t.length + 1 := by simp
      rw [hsplit, hlen, prod_range_succ', ih]
      have h0 :
          (if h : (0 : ℕ) + 1 < (a :: b :: t).length then
              (x ((a :: b :: t)[0]'(Nat.lt_of_succ_lt h)) + x ((a :: b :: t)[0 + 1])) /
                (x ((a :: b :: t)[0]'(Nat.lt_of_succ_lt h)) - x ((a :: b :: t)[0 + 1]))
            else 1) =
            (x a + x b) / (x a - x b) := by
        simp
      have htail :
          (∏ k ∈ range ((b :: t).length - 1),
              if h : k + 1 < (b :: t).length then
                (x ((b :: t)[k]'(Nat.lt_of_succ_lt h)) + x ((b :: t)[k + 1])) /
                  (x ((b :: t)[k]'(Nat.lt_of_succ_lt h)) - x ((b :: t)[k + 1]))
              else 1) =
            ∏ k ∈ range t.length,
              if h : k + 1 + 1 < (a :: b :: t).length then
                (x ((a :: b :: t)[k + 1]'(Nat.lt_of_succ_lt h)) +
                    x ((a :: b :: t)[k + 1 + 1])) /
                  (x ((a :: b :: t)[k + 1]'(Nat.lt_of_succ_lt h)) -
                    x ((a :: b :: t)[k + 1 + 1]))
              else 1 := by
        have hbt : (b :: t).length - 1 = t.length := by simp
        simp_rw [hbt]
        refine prod_congr rfl fun k hk => ?_
        have hk' : k < t.length := mem_range.mp hk
        have hpos : k + 1 + 1 < (a :: b :: t).length := by simp; omega
        have hpos' : k + 1 < (b :: t).length := by simp; omega
        simp only [hpos, hpos', ↓reduceDIte, List.getElem_cons_succ]
      rw [htail, h0]
      ring

lemma cayleyWeight_formPerm_eq_path_mul_wrap {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {L : List α} (hl : L.Nodup) (h2 : 2 ≤ L.length) :
    cayleyWeight x L.formPerm =
      cayleyPathWeight x L *
        ((x (L[L.length - 1]'(by omega)) + x (L[0]'(by omega))) /
          (x (L[L.length - 1]'(by omega)) - x (L[0]'(by omega)))) := by
  have hnpos : 0 < L.length := by omega
  rw [cayleyWeight_formPerm x hl h2]
  let f : ℕ → ℂ := fun i =>
    if hi : i < L.length then
      (x (L[i]) + x (L[(i + 1) % L.length]'(Nat.mod_lt _ hnpos))) /
        (x (L[i]) - x (L[(i + 1) % L.length]'(Nat.mod_lt _ hnpos)))
    else 1
  have hfeq :
      (∏ i : Fin L.length,
          (x (L[i.val]) + x (L[(i.val + 1) % L.length]'(Nat.mod_lt _ hnpos))) /
            (x (L[i.val]) - x (L[(i.val + 1) % L.length]'(Nat.mod_lt _ hnpos)))) =
        ∏ i : Fin L.length, f i := by
    refine Fintype.prod_congr _ _ fun i => ?_
    simp only [f]
    have hi := i.isLt
    simp [hi]
  rw [hfeq, Fin.prod_univ_eq_prod_range]
  have hprod :
      (∏ i ∈ range ((L.length - 1) + 1), f i) =
        (∏ i ∈ range (L.length - 1), f i) * f (L.length - 1) :=
    prod_range_succ f (L.length - 1)
  have hlen : (L.length - 1) + 1 = L.length := Nat.succ_pred_eq_of_pos hnpos
  rw [hlen] at hprod
  rw [hprod]
  have hpath : cayleyPathWeight x L = ∏ i ∈ range (L.length - 1), f i := by
    rw [cayleyPathWeight_eq_prod_range]
    refine prod_congr rfl fun i hi => ?_
    have hi' : i < L.length - 1 := mem_range.mp hi
    have hilt : i + 1 < L.length := by omega
    have hiL : i < L.length := by omega
    simp only [f, hiL, ↓reduceDIte]
    simp [Nat.mod_eq_of_lt hilt, hilt]
  have hlast : f (L.length - 1) =
      (x (L[L.length - 1]'(by omega)) + x (L[0]'(by omega))) /
        (x (L[L.length - 1]'(by omega)) - x (L[0]'(by omega))) := by
    have hlt : L.length - 1 < L.length := Nat.sub_lt hnpos (by omega)
    simp only [f, hlt, ↓reduceDIte]
    have hmod : ((L.length - 1) + 1) % L.length = 0 := by
      rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hnpos), Nat.mod_self]
    simp [hmod]
  rw [hpath, hlast]

lemma cayleyWeight_formPerm_cons_eq_path {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {p : α} {L : List α}
    (hL : L.Nodup) (hp : p ∉ L) (h1 : 1 ≤ L.length) :
    cayleyWeight x (List.formPerm (p :: L)) =
      cayleyPathWeight x L *
        ((x p + x (L[0]'(by omega))) / (x p - x (L[0]'(by omega)))) *
        ((x (L[L.length - 1]'(by omega)) + x p) /
          (x (L[L.length - 1]'(by omega)) - x p)) := by
  have hl : (p :: L).Nodup := List.nodup_cons.2 ⟨hp, hL⟩
  have h2 : 2 ≤ (p :: L).length := by simp; omega
  have hnpos : 0 < L.length + 1 := by omega
  rw [cayleyWeight_formPerm x hl h2]
  simp only [List.length_cons]
  let f : ℕ → ℂ := fun i =>
    if hi : i < L.length + 1 then
      (x ((p :: L)[i]) +
          x ((p :: L)[(i + 1) % (L.length + 1)]'(Nat.mod_lt _ hnpos))) /
        (x ((p :: L)[i]) -
          x ((p :: L)[(i + 1) % (L.length + 1)]'(Nat.mod_lt _ hnpos)))
    else 1
  have hfeq :
      (∏ i : Fin (L.length + 1),
          (x ((p :: L)[i.val]) +
              x ((p :: L)[(i.val + 1) % (L.length + 1)]'(Nat.mod_lt _ hnpos))) /
            (x ((p :: L)[i.val]) -
              x ((p :: L)[(i.val + 1) % (L.length + 1)]'(Nat.mod_lt _ hnpos)))) =
        ∏ i : Fin (L.length + 1), f i := by
    refine Fintype.prod_congr _ _ fun i => ?_
    simp only [f]
    have hi := i.isLt
    simp [hi]
  rw [hfeq, Fin.prod_univ_eq_prod_range, prod_range_succ']
  have hmid :
      (∏ k ∈ range L.length, f (k + 1)) =
        cayleyPathWeight x L *
          ((x (L[L.length - 1]'(by omega)) + x p) /
            (x (L[L.length - 1]'(by omega)) - x p)) := by
    have hprod :
        (∏ k ∈ range ((L.length - 1) + 1), f (k + 1)) =
          (∏ k ∈ range (L.length - 1), f (k + 1)) * f ((L.length - 1) + 1) :=
      prod_range_succ (fun k => f (k + 1)) (L.length - 1)
    have hlen : (L.length - 1) + 1 = L.length := by omega
    rw [hlen] at hprod
    rw [hprod]
    have hpath : (∏ k ∈ range (L.length - 1), f (k + 1)) = cayleyPathWeight x L := by
      rw [cayleyPathWeight_eq_prod_range]
      refine prod_congr rfl fun k hk => ?_
      have hk' : k < L.length - 1 := mem_range.mp hk
      have hk1 : k + 1 < L.length + 1 := by omega
      have hpos : k + 1 + 1 < L.length + 1 := by omega
      have hpos' : k + 1 < L.length := by omega
      simp only [f, hk1, ↓reduceDIte, List.getElem_cons_succ]
      simp [Nat.mod_eq_of_lt hpos, List.getElem_cons_succ, hpos']
    have hlast : f L.length =
        (x (L[L.length - 1]'(by omega)) + x p) /
          (x (L[L.length - 1]'(by omega)) - x p) := by
      have hlt : L.length < L.length + 1 := Nat.lt_succ_self _
      simp only [f, hlt, ↓reduceDIte]
      have hmod : (L.length + 1) % (L.length + 1) = 0 := Nat.mod_self _
      simp [hmod, List.getElem_cons_zero]
      cases L with
      | nil => simp at h1
      | cons _ _ => simp
    rw [hpath, hlast]
  have h0 : f 0 =
      (x p + x (L[0]'(by omega))) / (x p - x (L[0]'(by omega))) := by
    have hlt : (0 : ℕ) < L.length + 1 := by omega
    simp only [f, hlt, ↓reduceDIte, List.getElem_cons_zero]
    have hmod : (0 + 1) % (L.length + 1) = 1 := Nat.mod_eq_of_lt (by omega)
    simp [hmod, List.getElem_cons_succ]
  rw [hmid, h0]
  ring

lemma path_mul_add_eq_weight_mul_sub {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {L : List α} (hl : L.Nodup) (h2 : 2 ≤ L.length)
    (hx : x (L[L.length - 1]'(by omega)) ≠ x (L[0]'(by omega))) :
    cayleyPathWeight x L *
        (x (L[L.length - 1]'(by omega)) + x (L[0]'(by omega))) =
      cayleyWeight x L.formPerm *
        (x (L[L.length - 1]'(by omega)) - x (L[0]'(by omega))) := by
  have hden :
      x (L[L.length - 1]'(by omega)) - x (L[0]'(by omega)) ≠ 0 :=
    sub_ne_zero.2 hx
  rw [cayleyWeight_formPerm_eq_path_mul_wrap x hl h2]
  field_simp [hden]

lemma cayleyWeight_cons_rotate_eq {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {p : α} {L : List α} {k : ℕ}
    (hL : L.Nodup) (hp : p ∉ L) (h2 : 2 ≤ L.length) (hk : k < L.length) :
    cayleyWeight x (List.formPerm (p :: L.rotate k)) =
      cayleyPathWeight x (L.rotate k) *
        ((x p + x (L[k]'(hk))) / (x p - x (L[k]'(hk)))) *
        ((x ((L.rotate k)[L.length - 1]'(by simp [List.length_rotate]; omega)) + x p) /
          (x ((L.rotate k)[L.length - 1]'(by simp [List.length_rotate]; omega)) - x p)) := by
  have hrot : (L.rotate k).Nodup := (List.nodup_rotate).2 hL
  have hp' : p ∉ L.rotate k := by simpa [List.mem_rotate] using hp
  have h1' : 1 ≤ (L.rotate k).length := by simp [List.length_rotate]; omega
  rw [cayleyWeight_formPerm_cons_eq_path (x := x) hrot hp' h1']
  simp [List.length_rotate, getElem_rotate_zero L hk]

lemma rotate_last_ne_head {α : Type*} {L : List α} {k : ℕ}
    (hL : L.Nodup) (h2 : 2 ≤ L.length) (_hk : k < L.length) :
    (L.rotate k)[L.length - 1]'(by simp [List.length_rotate]; omega) ≠
      (L.rotate k)[0]'(by simp [List.length_rotate]; omega) := by
  have hrot : (L.rotate k).Nodup := (List.nodup_rotate).2 hL
  exact (List.Nodup.getElem_inj_iff hrot).not.mpr (by omega)

/-- `path_mul_add_eq_weight_mul_sub` with the last index written as an equal length `n`. -/
lemma path_mul_add_eq_weight_mul_sub_of_length {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {M : List α} {n : ℕ} (hl : M.Nodup) (h2 : 2 ≤ M.length)
    (hn : M.length = n)
    (hx : x (M[n - 1]'(by omega)) ≠ x (M[0]'(by omega))) :
    cayleyPathWeight x M * (x (M[n - 1]'(by omega)) + x (M[0]'(by omega))) =
      cayleyWeight x M.formPerm *
        (x (M[n - 1]'(by omega)) - x (M[0]'(by omega))) := by
  subst n
  exact path_mul_add_eq_weight_mul_sub x hl h2 hx

lemma cayleyWeight_cons_rotate_eq_neg_path {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {p : α} {L : List α} {k : ℕ}
    (hL : L.Nodup) (hp : p ∉ L) (h2 : 2 ≤ L.length) (hk : k < L.length)
    (hx : Function.Injective x) :
    cayleyWeight x (List.formPerm (p :: L.rotate k)) =
      - cayleyPathWeight x (L.rotate k) -
        2 * x p * cayleyWeight x L.formPerm *
          ((x p - x ((L.rotate k)[L.length - 1]'(by simp [List.length_rotate]; omega)))⁻¹ -
            (x p - x ((L.rotate k)[0]'(by simp [List.length_rotate]; omega)))⁻¹) := by
  have hrot : (L.rotate k).Nodup := (List.nodup_rotate).2 hL
  have hp' : p ∉ L.rotate k := by simpa [List.mem_rotate] using hp
  have h2' : 2 ≤ (L.rotate k).length := by simpa [List.length_rotate] using h2
  have hyz := rotate_last_ne_head hL h2 hk
  have hyx : x ((L.rotate k)[L.length - 1]'(by simp [List.length_rotate]; omega)) ≠ x p :=
    hx.ne (ne_of_mem_of_not_mem (List.getElem_mem _) hp')
  have hzx : x ((L.rotate k)[0]'(by simp [List.length_rotate]; omega)) ≠ x p :=
    hx.ne (ne_of_mem_of_not_mem (List.getElem_mem _) hp')
  have hA :=
    path_mul_add_eq_weight_mul_sub_of_length (x := x) hrot h2'
      (List.length_rotate L k) (hx.ne hyz)
  have hX : cayleyWeight x (L.rotate k).formPerm = cayleyWeight x L.formPerm := by
    rw [List.formPerm_rotate L hL k]
  rw [cayleyWeight_cons_rotate_eq (x := x) hL hp h2 hk, ← getElem_rotate_zero L hk]
  have hfac := cayley_insert_eq_neg_one_sub (x p)
    (x ((L.rotate k)[L.length - 1]'(by simp [List.length_rotate]; omega)))
    (x ((L.rotate k)[0]'(by simp [List.length_rotate]; omega)))
    hyx.symm hzx.symm
  rw [mul_assoc, hfac, mul_sub, mul_neg, mul_one]
  set A := cayleyPathWeight x (L.rotate k)
  set t := x p
  set y := x ((L.rotate k)[L.length - 1]'(by simp [List.length_rotate]; omega))
  set z := x ((L.rotate k)[0]'(by simp [List.length_rotate]; omega))
  set X := cayleyWeight x L.formPerm
  refine congrArg (fun w => -A - w) ?_
  have hAyz : A * (y + z) = X * (y - z) := by
    rw [← hX]
    exact hA
  have hsub := sub_div_inv_sub t y z hyx.symm hzx.symm
  simp only [div_eq_mul_inv]
  calc
    A * (2 * t * (y + z) * ((t - y) * (t - z))⁻¹)
        = 2 * t * (A * (y + z)) * ((t - y) * (t - z))⁻¹ := by ring
    _ = 2 * t * (X * (y - z)) * ((t - y) * (t - z))⁻¹ := by rw [hAyz]
    _ = 2 * t * X * ((y - z) * ((t - y) * (t - z))⁻¹) := by ring
    _ = 2 * t * X * ((y - z) / ((t - y) * (t - z))) := by simp [div_eq_mul_inv]
    _ = 2 * t * X * ((t - y)⁻¹ - (t - z)⁻¹) := by rw [hsub]

lemma sum_cayleyWeight_cons_rotate {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {p : α} {L : List α}
    (hL : L.Nodup) (hp : p ∉ L) (h2 : 2 ≤ L.length)
    (hx : Function.Injective x) :
    ∑ k : Fin L.length, cayleyWeight x (List.formPerm (p :: L.rotate k.val)) =
      - ∑ k : Fin L.length, cayleyPathWeight x (L.rotate k.val) := by
  have : NeZero L.length := ⟨by omega⟩
  let a : Fin L.length := ⟨L.length - 1, by omega⟩
  let f : Fin L.length → ℂ := fun k => (x p - x (L[k.val]))⁻¹
  let d : Fin L.length → ℂ := fun k => f (k + a) - f k
  have hterm : ∀ k : Fin L.length,
      cayleyWeight x (List.formPerm (p :: L.rotate k.val)) =
        - cayleyPathWeight x (L.rotate k.val) -
          2 * x p * cayleyWeight x L.formPerm * d k := by
    intro k
    have h := cayleyWeight_cons_rotate_eq_neg_path (x := x) hL hp h2 k.isLt hx
    have h0 := getElem_rotate_zero L k.isLt
    have hlast := getElem_rotate_last L h2 k.isLt
    have hidx : (k + a).val = (k.val + (L.length - 1)) % L.length := by
      simp [a, Fin.val_add]
    rw [h0, hlast] at h
    simpa [d, f, hidx] using h
  simp_rw [hterm]
  rw [sum_sub_distrib, sum_neg_distrib]
  have hconst :
      (∑ k, (2 : ℂ) * x p * cayleyWeight x L.formPerm * d k) =
        (2 : ℂ) * x p * cayleyWeight x L.formPerm * ∑ k, d k := by
    simp [mul_sum, mul_assoc]
  rw [hconst]
  have htel : ∑ k, d k = 0 := by
    simp_rw [d]
    rw [sum_sub_distrib]
    have hre :
        (∑ k : Fin L.length, f (k + a)) = ∑ k : Fin L.length, f k :=
      Fintype.sum_equiv (Equiv.addRight a) (fun k => f (k + a)) f fun _ => rfl
    rw [hre, sub_self]
  rw [htel, mul_zero, sub_zero]

lemma cayleyPathWeight_eq_of_eqOn {α : Type*} (x x' : α → ℂ) {L : List α}
    (h : ∀ a ∈ L, x a = x' a) :
    cayleyPathWeight x L = cayleyPathWeight x' L := by
  rw [cayleyPathWeight_eq_prod_range, cayleyPathWeight_eq_prod_range]
  refine prod_congr rfl fun i _ => ?_
  split_ifs with hlt
  · have hmem0 : L[i]'(Nat.lt_of_succ_lt hlt) ∈ L := List.getElem_mem _
    have hmem1 : L[i + 1] ∈ L := List.getElem_mem _
    simp [h _ hmem0, h _ hmem1]
  · rfl

lemma cayleyPathWeight_rotate_eq_of_eqOn_compl {α : Type*} [DecidableEq α]
    (x x' : α → ℂ) {p : α} {L : List α} {k : ℕ}
    (hp : p ∉ L) (h : ∀ q, q ≠ p → x q = x' q) :
    cayleyPathWeight x (L.rotate k) = cayleyPathWeight x' (L.rotate k) :=
  cayleyPathWeight_eq_of_eqOn x x' fun a ha =>
    h a (ne_of_mem_of_not_mem (List.mem_rotate.mp ha) hp)

/-- She–Sun–Xia Lemma 2.3, rotate-class form: the Hamiltonian listing sum
through `p` does not change if `x` is altered only at `p`. -/
lemma sum_cayleyWeight_listings_eq_of_eqOn_compl {α : Type*} [Fintype α] [DecidableEq α]
    (x x' : α → ℂ) (p : α)
    (hx : Function.Injective x) (hx' : Function.Injective x')
    (h : ∀ q, q ≠ p → x q = x' q)
    (hcard : 2 ≤ Fintype.card {q : α // q ≠ p}) :
    ∑ e : Fin (Fintype.card {q : α // q ≠ p}) ≃ {q : α // q ≠ p},
        cayleyWeight x (List.formPerm (p :: List.ofFn fun i => (e i).1)) =
      ∑ e : Fin (Fintype.card {q : α // q ≠ p}) ≃ {q : α // q ≠ p},
        cayleyWeight x' (List.formPerm (p :: List.ofFn fun i => (e i).1)) := by
  set m := Fintype.card {q : α // q ≠ p}
  have : NeZero m := ⟨by omega⟩
  let Wx : (Fin m ≃ {q : α // q ≠ p}) → ℂ :=
    fun σ => cayleyWeight x (List.formPerm (p :: List.ofFn fun i : Fin m => (σ i).1))
  let Wx' : (Fin m ≃ {q : α // q ≠ p}) → ℂ :=
    fun σ => cayleyWeight x' (List.formPerm (p :: List.ofFn fun i : Fin m => (σ i).1))
  have hrot :
      ∀ (e : Fin m ≃ {q : α // q ≠ p}) (k : Fin m),
        (List.ofFn fun i => (e i).1).rotate k.val =
          List.ofFn fun i : Fin m => (e (i + k)).1 := fun e k => ofFn_rotate _ k
  have hWrot :
      ∀ (e : Fin m ≃ {q : α // q ≠ p}) (k : Fin m),
        cayleyWeight x
            (List.formPerm (p :: (List.ofFn fun i => (e i).1).rotate k.val)) =
          Wx ((Equiv.addRight k).trans e) := by
    intro e k
    rw [hrot]
    rfl
  have hWrot' :
      ∀ (e : Fin m ≃ {q : α // q ≠ p}) (k : Fin m),
        cayleyWeight x'
            (List.formPerm (p :: (List.ofFn fun i => (e i).1).rotate k.val)) =
          Wx' ((Equiv.addRight k).trans e) := by
    intro e k
    rw [hrot]
    rfl
  have hclass :
      ∀ e : Fin m ≃ {q : α // q ≠ p},
        ∑ k : Fin m,
            cayleyWeight x
              (List.formPerm
                (p :: (List.ofFn fun i => (e i).1).rotate k.val)) =
          ∑ k : Fin m,
            cayleyWeight x'
              (List.formPerm
                (p :: (List.ofFn fun i => (e i).1).rotate k.val)) := by
    intro e
    let L := List.ofFn fun i => (e i).1
    have hL : L.Nodup :=
      List.nodup_ofFn_ofInjective fun i j hij => e.injective (Subtype.ext hij)
    have hpL : p ∉ L := by
      intro hmem
      rw [List.mem_ofFn'] at hmem
      obtain ⟨i, hi⟩ := hmem
      exact (e i).2 hi
    have h2 : 2 ≤ L.length := by
      simpa [L, List.length_ofFn] using hcard
    have hxsum := sum_cayleyWeight_cons_rotate (x := x) hL hpL h2 hx
    have hx'sum := sum_cayleyWeight_cons_rotate (x := x') hL hpL h2 hx'
    have hlen : L.length = m := List.length_ofFn
    have hre_x :
        (∑ k : Fin m,
            cayleyWeight x (List.formPerm (p :: L.rotate k.val))) =
          ∑ k : Fin L.length,
            cayleyWeight x (List.formPerm (p :: L.rotate k.val)) :=
      Fintype.sum_equiv (finCongr hlen.symm)
        (fun k : Fin m => cayleyWeight x (List.formPerm (p :: L.rotate k.val)))
        (fun k : Fin L.length => cayleyWeight x (List.formPerm (p :: L.rotate k.val)))
        (fun _ => rfl)
    have hre_x' :
        (∑ k : Fin m,
            cayleyWeight x' (List.formPerm (p :: L.rotate k.val))) =
          ∑ k : Fin L.length,
            cayleyWeight x' (List.formPerm (p :: L.rotate k.val)) :=
      Fintype.sum_equiv (finCongr hlen.symm)
        (fun k : Fin m => cayleyWeight x' (List.formPerm (p :: L.rotate k.val)))
        (fun k : Fin L.length => cayleyWeight x' (List.formPerm (p :: L.rotate k.val)))
        (fun _ => rfl)
    have hpath :
        (∑ k : Fin L.length, cayleyPathWeight x (L.rotate k.val)) =
          ∑ k : Fin L.length, cayleyPathWeight x' (L.rotate k.val) :=
      sum_congr rfl fun k _ =>
        cayleyPathWeight_rotate_eq_of_eqOn_compl x x' hpL h
    rw [hre_x, hre_x', hxsum, hx'sum, hpath]
  have hreindex :
      ∀ (W : (Fin m ≃ {q : α // q ≠ p}) → ℂ) (k : Fin m),
        ∑ e, W ((Equiv.addRight k).trans e) = ∑ e, W e := by
    intro W k
    let φ :=
      (Equiv.addRight k).symm.equivCongr (Equiv.refl {q : α // q ≠ p})
    have hφ : ∀ e, φ e = (Equiv.addRight k).trans e := by
      intro e
      ext i
      dsimp [φ]
    simp_rw [← hφ]
    exact Equiv.sum_comp φ W
  have hdouble :
      ∑ e, ∑ k : Fin m, Wx ((Equiv.addRight k).trans e) =
        ∑ e, ∑ k : Fin m, Wx' ((Equiv.addRight k).trans e) := by
    simp_rw [← hWrot, ← hWrot']
    exact sum_congr rfl fun e _ => hclass e
  have hL :
      (∑ k : Fin m, ∑ e, Wx ((Equiv.addRight k).trans e)) =
        ∑ k : Fin m, ∑ e, Wx e :=
    sum_congr rfl fun k _ => hreindex Wx k
  have hR :
      (∑ k : Fin m, ∑ e, Wx' ((Equiv.addRight k).trans e)) =
        ∑ k : Fin m, ∑ e, Wx' e :=
    sum_congr rfl fun k _ => hreindex Wx' k
  have hswap (W : (Fin m ≃ {q : α // q ≠ p}) → ℂ) :
      (∑ e, ∑ k : Fin m, W ((Equiv.addRight k).trans e)) =
        ∑ k : Fin m, ∑ e, W ((Equiv.addRight k).trans e) :=
    sum_comm
  rw [hswap Wx, hswap Wx', hL, hR] at hdouble
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hdouble
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  exact mul_left_cancel₀ hm0 hdouble

open scoped Classical in
lemma sum_cayleyWeight_hamiltonian_eq_listings {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) (p : α) (hcard : 2 ≤ Fintype.card {q : α // q ≠ p}) :
    ∑ σ : {σ : Perm α // σ.IsCycle ∧ σ.support = univ}, cayleyWeight x σ.1 =
      ∑ e : Fin (Fintype.card {q : α // q ≠ p}) ≃ {q : α // q ≠ p},
        cayleyWeight x (listingPerm e) := by
  rw [← Equiv.sum_comp (listingEquiv p hcard) (fun σ => cayleyWeight x σ.1)]
  dsimp only [listingEquiv]
  rfl

open scoped Classical in
lemma sum_cayleyWeight_hamiltonian_eq_of_eqOn_compl {α : Type*} [Fintype α] [DecidableEq α]
    (x x' : α → ℂ) (p : α)
    (hx : Function.Injective x) (hx' : Function.Injective x')
    (h : ∀ q, q ≠ p → x q = x' q)
    (hcard : 2 ≤ Fintype.card {q : α // q ≠ p}) :
    ∑ σ : {σ : Perm α // σ.IsCycle ∧ σ.support = univ}, cayleyWeight x σ.1 =
      ∑ σ : {σ : Perm α // σ.IsCycle ∧ σ.support = univ}, cayleyWeight x' σ.1 := by
  rw [sum_cayleyWeight_hamiltonian_eq_listings x p hcard,
    sum_cayleyWeight_hamiltonian_eq_listings x' p hcard]
  simpa [listingPerm] using
    sum_cayleyWeight_listings_eq_of_eqOn_compl x x' p hx hx' h hcard

lemma exists_natCast_notMem (s : Finset ℂ) : ∃ n : ℕ, (n : ℂ) ∉ s := by
  let t : Finset ℕ :=
    s.preimage (fun n : ℕ => (n : ℂ)) (Nat.cast_injective.injOn)
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset t
  exact ⟨n, fun hmem => hn (Finset.mem_preimage.mpr hmem)⟩

lemma exists_fin_off (s : Finset ℂ) :
    ∀ n : ℕ, ∃ f : Fin n → ℂ, Function.Injective f ∧ ∀ i, f i ∉ s
  | 0 => ⟨fun i => i.elim0, fun i j _ => i.elim0, fun i => i.elim0⟩
  | n + 1 => by
    obtain ⟨f, hf, hfs⟩ := exists_fin_off s n
    obtain ⟨m, hm⟩ := exists_natCast_notMem (s ∪ (Finset.univ.image f : Finset ℂ))
    refine ⟨Fin.cons (m : ℂ) f, ?_, ?_⟩
    · refine (Fin.cons_injective_iff).2 ⟨?_, hf⟩
      intro ⟨i, hi⟩
      have hmi : (m : ℂ) = f i := hi.symm
      have hmem : (m : ℂ) ∈ s ∪ Finset.univ.image f :=
        mem_union.2 (Or.inr (mem_image.2 ⟨i, mem_univ _, hmi.symm⟩))
      exact hm hmem
    · intro i
      refine Fin.cases ?_ (fun j => hfs j) i
      intro hmem
      exact hm (mem_union.2 (Or.inl hmem))

lemma exists_injective_off {α : Type*} [Fintype α] (s : Finset ℂ) :
    ∃ u : α → ℂ, Function.Injective u ∧ ∀ a, u a ∉ s := by
  obtain ⟨f, hf, hfs⟩ := exists_fin_off s (Fintype.card α)
  let e := Fintype.equivFin α
  exact ⟨fun a => f (e a), hf.comp e.injective, fun a => hfs (e a)⟩

lemma injective_update {α : Type*} [DecidableEq α] (x : α → ℂ) (p : α) (z : ℂ)
    (hx : Function.Injective x) (hz : ∀ q, q ≠ p → z ≠ x q) :
    Function.Injective (Function.update x p z) := by
  intro a b hab
  by_cases hap : a = p
  · by_cases hbp : b = p
    · exact hap.trans hbp.symm
    · have : z = x b := by
        rw [hap, Function.update_self, Function.update_of_ne hbp] at hab
        exact hab
      exact (hz b hbp this).elim
  · by_cases hbp : b = p
    · have : x a = z := by
        rw [hbp, Function.update_of_ne hap, Function.update_self] at hab
        exact hab
      exact (hz a hap this.symm).elim
    · have : x a = x b := by
        rw [Function.update_of_ne hap, Function.update_of_ne hbp] at hab
        exact hab
      exact hx this

open scoped Classical in
lemma sum_cayleyWeight_hamiltonian_eq_update {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) (p : α) (z : ℂ)
    (hx : Function.Injective x) (hz : ∀ q, q ≠ p → z ≠ x q)
    (hα : 3 ≤ Fintype.card α) :
    ∑ σ : {σ : Perm α // σ.IsCycle ∧ σ.support = univ}, cayleyWeight x σ.1 =
      ∑ σ : {σ : Perm α // σ.IsCycle ∧ σ.support = univ},
        cayleyWeight (Function.update x p z) σ.1 := by
  have hcard : 2 ≤ Fintype.card {q : α // q ≠ p} := by
    rw [card_subtype_ne]
    omega
  exact sum_cayleyWeight_hamiltonian_eq_of_eqOn_compl x (Function.update x p z) p hx
    (injective_update x p z hx hz)
    (fun q hq => (Function.update_of_ne hq z x).symm) hcard

noncomputable def updateOn {α : Type*} [DecidableEq α] (x u : α → ℂ) : List α → α → ℂ
  | [] => x
  | a :: L => Function.update (updateOn x u L) a (u a)

lemma updateOn_apply {α : Type*} [DecidableEq α] (x u : α → ℂ) :
    ∀ {L : List α}, L.Nodup → ∀ a,
      updateOn x u L a = if a ∈ L then u a else x a
  | [], _, a => by simp [updateOn]
  | b :: L, hnd, a => by
    have hL : L.Nodup := (List.nodup_cons.mp hnd).2
    simp only [updateOn, List.mem_cons]
    by_cases ha : a = b
    · subst ha
      simp [Function.update_self]
    · rw [Function.update_of_ne ha, updateOn_apply (L := L) x u hL a]
      simp [ha]

lemma injective_updateOn {α : Type*} [DecidableEq α] (x u : α → ℂ) {L : List α}
    (hx : Function.Injective x) (hu : Function.Injective u)
    (hdis : ∀ a q, u a ≠ x q) (hnd : L.Nodup) :
    Function.Injective (updateOn x u L) := by
  intro a b hab
  have hab' :
      (if a ∈ L then u a else x a) = if b ∈ L then u b else x b := by
    simpa [updateOn_apply x u hnd] using hab
  by_cases ha : a ∈ L
  · by_cases hb : b ∈ L
    · simp [ha, hb] at hab'
      exact hu hab'
    · simp [ha, hb] at hab'
      exact (hdis a b hab').elim
  · by_cases hb : b ∈ L
    · simp [ha, hb] at hab'
      exact (hdis b a hab'.symm).elim
    · simp [ha, hb] at hab'
      exact hx hab'

open scoped Classical in
lemma sum_cayleyWeight_hamiltonian_eq_updateOn {α : Type*} [Fintype α] [DecidableEq α]
    (x u : α → ℂ) {L : List α}
    (hx : Function.Injective x) (hu : Function.Injective u)
    (hdis : ∀ a q, u a ≠ x q) (hα : 3 ≤ Fintype.card α) (hnd : L.Nodup) :
    ∑ σ : {σ : Perm α // σ.IsCycle ∧ σ.support = univ}, cayleyWeight x σ.1 =
      ∑ σ : {σ : Perm α // σ.IsCycle ∧ σ.support = univ},
        cayleyWeight (updateOn x u L) σ.1 := by
  induction L with
  | nil => simp [updateOn]
  | cons a L ih =>
    have hL : L.Nodup := (List.nodup_cons.mp hnd).2
    have ha : a ∉ L := (List.nodup_cons.mp hnd).1
    rw [ih hL, updateOn]
    refine sum_cayleyWeight_hamiltonian_eq_update (updateOn x u L) a (u a)
      (injective_updateOn x u hx hu hdis hL) ?_ hα
    intro q hq
    have hcur : updateOn x u L q = if q ∈ L then u q else x q :=
      updateOn_apply x u hL q
    rw [hcur]
    split_ifs with hqL
    · exact hu.ne (ne_of_mem_of_not_mem hqL ha).symm
    · exact hdis a q

lemma updateOn_eq_of_forall_mem {α : Type*} [DecidableEq α] (x u : α → ℂ)
    {L : List α} (hnd : L.Nodup) (hL : ∀ a, a ∈ L) : updateOn x u L = u := by
  ext a
  simp [updateOn_apply x u hnd, hL a]

open scoped Classical in
lemma sum_cayleyWeight_hamiltonian_eq_of_injective {α : Type*} [Fintype α] [DecidableEq α]
    (x x' : α → ℂ) (hx : Function.Injective x) (hx' : Function.Injective x')
    (hα : 3 ≤ Fintype.card α) :
    ∑ σ : {σ : Perm α // σ.IsCycle ∧ σ.support = univ}, cayleyWeight x σ.1 =
      ∑ σ : {σ : Perm α // σ.IsCycle ∧ σ.support = univ}, cayleyWeight x' σ.1 := by
  obtain ⟨u, hu, hus⟩ :=
    exists_injective_off (α := α)
      ((univ : Finset α).image x ∪ (univ : Finset α).image x')
  have hdisx : ∀ a q, u a ≠ x q := fun a q h =>
    hus a (mem_union.2 (Or.inl (mem_image.2 ⟨q, mem_univ _, h.symm⟩)))
  have hdisx' : ∀ a q, u a ≠ x' q := fun a q h =>
    hus a (mem_union.2 (Or.inr (mem_image.2 ⟨q, mem_univ _, h.symm⟩)))
  let L := (univ : Finset α).toList
  have hnd : L.Nodup := Finset.nodup_toList _
  have hmem : ∀ a, a ∈ L := fun a => Finset.mem_toList.2 (mem_univ a)
  have hxu := sum_cayleyWeight_hamiltonian_eq_updateOn x u hx hu hdisx hα hnd
  have hx'u := sum_cayleyWeight_hamiltonian_eq_updateOn x' u hx' hu hdisx' hα hnd
  rw [hxu, hx'u, updateOn_eq_of_forall_mem (L := L) x u hnd hmem,
    updateOn_eq_of_forall_mem (L := L) x' u hnd hmem]

lemma permCongr_mul {α β : Type*} (e : α ≃ β) (σ τ : Perm α) :
    e.permCongr (σ * τ) = e.permCongr σ * e.permCongr τ := by
  ext x
  simp [Equiv.permCongr_apply]

lemma permCongr_one {α β : Type*} (e : α ≃ β) : e.permCongr (1 : Perm α) = 1 :=
  Equiv.permCongr_refl e

lemma permCongr_inv {α β : Type*} (e : α ≃ β) (σ : Perm α) :
    e.permCongr σ⁻¹ = (e.permCongr σ)⁻¹ := by
  have h : e.permCongr σ * e.permCongr σ⁻¹ = (1 : Perm β) := by
    rw [← permCongr_mul, mul_inv_cancel, permCongr_one]
  exact (mul_eq_one_iff_inv_eq.mp h).symm

lemma permCongr_pow {α β : Type*} (e : α ≃ β) (σ : Perm α) (n : ℕ) :
    e.permCongr σ ^ n = e.permCongr (σ ^ n) := by
  induction n with
  | zero => simp [permCongr_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, ih, permCongr_mul]

lemma permCongr_zpow {α β : Type*} (e : α ≃ β) (σ : Perm α) (n : ℤ) :
    e.permCongr σ ^ n = e.permCongr (σ ^ n) := by
  cases n with
  | ofNat n =>
    simp [permCongr_pow]
  | negSucc n =>
    rw [zpow_negSucc, zpow_negSucc, permCongr_pow, permCongr_inv]

lemma support_permCongr {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (σ : Perm α) :
    (e.permCongr σ).support = σ.support.map e.toEmbedding := by
  ext b
  simp only [Equiv.Perm.mem_support, Equiv.permCongr_apply, mem_map, Equiv.toEmbedding_apply]
  constructor
  · intro h
    refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
    intro hf
    exact h (by rw [hf, e.apply_symm_apply])
  · rintro ⟨a, ha, rfl⟩
    intro hf
    have : σ a = a := e.injective (by simpa using hf)
    exact ha this

lemma cayleyWeight_permCongr {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (y : β → ℂ) (σ : Perm α) :
    cayleyWeight (y ∘ e) σ = cayleyWeight y (e.permCongr σ) := by
  simp only [cayleyWeight]
  rw [support_permCongr, prod_map]
  refine prod_congr rfl fun a _ => ?_
  simp [Function.comp, Equiv.permCongr_apply]

lemma isCycle_permCongr {α β : Type*} (e : α ≃ β) {σ : Perm α} (hσ : σ.IsCycle) :
    (e.permCongr σ).IsCycle := by
  obtain ⟨x, hx, hsame⟩ := hσ
  refine ⟨e x, ?_, ?_⟩
  · intro hfix
    simp [Equiv.permCongr_apply] at hfix
    exact hx hfix
  · intro y hy
    have hy' : σ (e.symm y) ≠ e.symm y := by
      intro hf
      apply hy
      simp [Equiv.permCongr_apply, hf]
    obtain ⟨n, hn⟩ := hsame hy'
    refine ⟨n, ?_⟩
    rw [permCongr_zpow, Equiv.permCongr_apply, e.symm_apply_apply, hn, e.apply_symm_apply]

lemma support_univ_permCongr {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) {σ : Perm α} (h : σ.support = univ) :
    (e.permCongr σ).support = univ := by
  ext b
  simp only [support_permCongr, h, mem_map, mem_univ, true_and, Equiv.toEmbedding_apply,
    iff_true]
  exact ⟨e.symm b, e.apply_symm_apply b⟩

open scoped Classical in
lemma sum_cayleyWeight_hamiltonian_permCongr {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (y : β → ℂ) :
    ∑ σ : {σ : Perm α // σ.IsCycle ∧ σ.support = univ}, cayleyWeight (y ∘ e) σ.1 =
      ∑ τ : {τ : Perm β // τ.IsCycle ∧ τ.support = univ}, cayleyWeight y τ.1 := by
  let φ : {σ : Perm α // σ.IsCycle ∧ σ.support = univ} ≃
      {τ : Perm β // τ.IsCycle ∧ τ.support = univ} :=
    { toFun := fun σ =>
        ⟨e.permCongr σ.1, isCycle_permCongr e σ.2.1, support_univ_permCongr e σ.2.2⟩
      invFun := fun τ =>
        ⟨e.symm.permCongr τ.1, isCycle_permCongr e.symm τ.2.1,
          support_univ_permCongr e.symm τ.2.2⟩
      left_inv := fun σ => by
        ext1
        change e.symm.permCongr (e.permCongr σ.1) = σ.1
        ext x
        simp [Equiv.permCongr_apply]
      right_inv := fun τ => by
        ext1
        change e.permCongr (e.symm.permCongr τ.1) = τ.1
        ext x
        simp [Equiv.permCongr_apply] }
  rw [← Equiv.sum_comp φ (fun τ => cayleyWeight y τ.1)]
  refine Fintype.sum_congr _ _ fun σ => ?_
  exact cayleyWeight_permCongr e y σ.1

open scoped Classical in
lemma sum_cayleyWeight_hamiltonian_eq_of_card_eq {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (x : α → ℂ) (y : β → ℂ) (hx : Function.Injective x) (hy : Function.Injective y)
    (hα : 3 ≤ Fintype.card α) (hcard : Fintype.card α = Fintype.card β) :
    ∑ σ : {σ : Perm α // σ.IsCycle ∧ σ.support = univ}, cayleyWeight x σ.1 =
      ∑ τ : {τ : Perm β // τ.IsCycle ∧ τ.support = univ}, cayleyWeight y τ.1 := by
  let e : α ≃ β :=
    (Fintype.equivFin α).trans ((finCongr hcard).trans (Fintype.equivFin β).symm)
  have hy' : Function.Injective (y ∘ e) := hy.comp e.injective
  have hxeq := sum_cayleyWeight_hamiltonian_eq_of_injective x (y ∘ e) hx hy' hα
  rw [hxeq, sum_cayleyWeight_hamiltonian_permCongr e y]

open scoped Classical in
lemma sum_cayleyWeight_hamiltonian_subtype_eq_fin {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (x : α → ℂ) (y : Fin s.card → ℂ)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hs : 3 ≤ s.card) :
    ∑ u : {u : Perm {a // a ∈ s} // u.IsCycle ∧ u.support = univ},
        cayleyWeight (fun a : {a // a ∈ s} => x a.1) u.1 =
      ∑ τ : {τ : Perm (Fin s.card) // τ.IsCycle ∧ τ.support = univ},
        cayleyWeight y τ.1 := by
  have hx' : Function.Injective (fun a : {a // a ∈ s} => x a.1) :=
    hx.comp Subtype.val_injective
  have hα : 3 ≤ Fintype.card {a // a ∈ s} := by
    simpa [Fintype.card_coe] using hs
  have hcard : Fintype.card {a // a ∈ s} = Fintype.card (Fin s.card) := by
    simp [Fintype.card_coe]
  exact sum_cayleyWeight_hamiltonian_eq_of_card_eq
    (fun a : {a // a ∈ s} => x a.1) y hx' hy hα hcard

/-- Sum of Cayley weights of Hamiltonian cycles. Independent of the injective
assignment when the type has cardinality at least 3. -/
noncomputable def hamiltonianCayleySum {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) : ℂ :=
  open scoped Classical in
  ∑ σ : {σ : Perm α // σ.IsCycle ∧ σ.support = univ}, cayleyWeight x σ.1

/-- Paper `s_k`: Hamiltonian Cayley sum on `2k` letters. For `k = 1` this is
`-1`. For `k ≥ 2` Lemma 2.3 makes it independent of the injective assignment. -/
noncomputable def cayleyHamConst (k : ℕ) : ℂ :=
  hamiltonianCayleySum (fun i : Fin (2 * k) => (i.val : ℂ))

lemma injective_natCast_fin (m : ℕ) :
    Function.Injective (fun i : Fin m => (i.val : ℂ)) :=
  Nat.cast_injective.comp Fin.val_injective

lemma support_ofSubtype_eq {α : Type*} [Fintype α] [DecidableEq α] {s : Finset α}
    {u : Perm {a // a ∈ s}} (h : u.support = univ) :
    (Equiv.Perm.ofSubtype u).support = s := by
  ext x
  simp only [Equiv.Perm.mem_support]
  constructor
  · intro hne
    by_contra hxs
    exact hne (Equiv.Perm.ofSubtype_apply_of_not_mem u hxs)
  · intro hx
    rw [Equiv.Perm.ofSubtype_apply_of_mem u hx]
    intro hf
    have hmem : (⟨x, hx⟩ : {a // a ∈ s}) ∈ u.support := by
      rw [h]
      exact mem_univ _
    exact Equiv.Perm.mem_support.mp hmem (Subtype.ext hf)

lemma cayleyWeight_ofSubtype_finset {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} (x : α → ℂ) (u : Perm {a // a ∈ s}) :
    cayleyWeight x (Equiv.Perm.ofSubtype u) =
      cayleyWeight (fun a : {a // a ∈ s} => x a.1) u := by
  unfold cayleyWeight
  refine prod_bij (fun y hy => ⟨y, support_ofSubtype_subset u hy⟩) ?_ ?_ ?_ ?_
  · intro y hy
    have hne : Equiv.Perm.ofSubtype u y ≠ y := Equiv.Perm.mem_support.mp hy
    have hy' : y ∈ s := support_ofSubtype_subset u hy
    rw [Equiv.Perm.ofSubtype_apply_of_mem u hy'] at hne
    exact Equiv.Perm.mem_support.mpr fun hf => hne (congrArg Subtype.val hf)
  · intro y1 _ y2 _ h
    exact Subtype.ext_iff.mp h
  · intro q hq
    have hne : u q ≠ q := Equiv.Perm.mem_support.mp hq
    refine ⟨q.1, ?_, Subtype.ext rfl⟩
    refine Equiv.Perm.mem_support.mpr ?_
    rw [Equiv.Perm.ofSubtype_apply_coe]
    exact fun hx => hne (Subtype.ext hx)
  · intro y hy
    have hy' : y ∈ s := support_ofSubtype_subset u hy
    simp [Equiv.Perm.ofSubtype_apply_of_mem u hy']

lemma subtypePerm_ofSubtype {α : Type*} [Fintype α] [DecidableEq α] {s : Finset α}
    (u : Perm {a // a ∈ s}) :
    (Equiv.Perm.ofSubtype u).subtypePerm
      (fun x => (mem_of_support_subset (support_ofSubtype_subset u) x).symm) = u := by
  ext q
  rw [Equiv.Perm.subtypePerm_apply]
  exact Equiv.Perm.ofSubtype_apply_coe u q

lemma isCycle_subtypePerm_of_support_eq {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} {σ : Perm α} (hσ : σ.IsCycle) (hs : σ.support = s)
    (h2 : 2 ≤ s.card) :
    (σ.subtypePerm fun x =>
      (mem_of_support_subset (s := s)
        (show σ.support ⊆ s from hs.symm ▸ Subset.rfl) x).symm).IsCycle := by
  subst hs
  exact isCycle_subtypePerm_of_support hσ h2

lemma support_subtypePerm_eq_univ {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} {σ : Perm α} (hs : σ.support = s) :
    (σ.subtypePerm fun x =>
      (mem_of_support_subset (s := s)
        (show σ.support ⊆ s from hs.symm ▸ Subset.rfl) x).symm).support = univ := by
  rw [Equiv.Perm.support_subtypePerm]
  ext q
  simp only [mem_filter, mem_univ, true_and, iff_true]
  exact Equiv.Perm.mem_support.mp (hs ▸ q.2)

noncomputable def cycleSupportEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (hs : 2 ≤ s.card) :
    {u : Perm {a // a ∈ s} // u.IsCycle ∧ u.support = univ} ≃
      {σ : Perm α // σ.IsCycle ∧ σ.support = s} where
  toFun u :=
    ⟨Equiv.Perm.ofSubtype u.1, ofSubtype_isCycle u.2.1, support_ofSubtype_eq u.2.2⟩
  invFun σ :=
    ⟨σ.1.subtypePerm fun x =>
      (mem_of_support_subset (s := s)
        (show σ.1.support ⊆ s from σ.2.2.symm ▸ Subset.rfl) x).symm,
      isCycle_subtypePerm_of_support_eq σ.2.1 σ.2.2 hs,
      support_subtypePerm_eq_univ σ.2.2⟩
  left_inv u := by
    apply Subtype.ext
    ext q
    rw [Equiv.Perm.subtypePerm_apply]
    exact Equiv.Perm.ofSubtype_apply_coe u.1 q
  right_inv σ :=
    Subtype.ext (ofSubtype_subtypePerm_of_support_subset
      (show σ.1.support ⊆ s from σ.2.2.symm ▸ Subset.rfl))

open scoped Classical in
lemma sum_hamiltonian_eq_sum_ite {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) :
    hamiltonianCayleySum x =
      ∑ σ : Perm α, if σ.IsCycle ∧ σ.support = univ then cayleyWeight x σ else 0 := by
  unfold hamiltonianCayleySum
  rw [← sum_subtype (p := fun σ : Perm α => σ.IsCycle ∧ σ.support = univ)
      (univ.filter (fun σ : Perm α => σ.IsCycle ∧ σ.support = univ))
      (fun σ => by simp) (fun σ => cayleyWeight x σ),
    sum_filter]

open scoped Classical in
lemma sum_cayleyWeight_cycles_support {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) (s : Finset α) (hs : 2 ≤ s.card) :
    (∑ σ : Perm α, if σ.IsCycle ∧ σ.support = s then cayleyWeight x σ else 0) =
      hamiltonianCayleySum (fun a : {a // a ∈ s} => x a.1) := by
  rw [← sum_filter,
    sum_subtype (p := fun σ : Perm α => σ.IsCycle ∧ σ.support = s)
      (univ.filter (fun σ : Perm α => σ.IsCycle ∧ σ.support = s))
      (fun σ => by simp) (fun σ => cayleyWeight x σ),
    hamiltonianCayleySum,
    ← Equiv.sum_comp (cycleSupportEquiv s hs) (fun σ => cayleyWeight x σ.1)]
  refine Fintype.sum_congr _ _ fun u => ?_
  exact cayleyWeight_ofSubtype_finset x u.1

open scoped Classical in
lemma hamiltonianCayleySum_eq_cayleyHamConst {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) (hx : Function.Injective x) {k : ℕ}
    (hα : 3 ≤ Fintype.card α) (hcard : Fintype.card α = 2 * k) :
    hamiltonianCayleySum x = cayleyHamConst k := by
  have hy : Function.Injective (fun i : Fin (2 * k) => (i.val : ℂ)) :=
    injective_natCast_fin (2 * k)
  have h3 : 3 ≤ Fintype.card (Fin (2 * k)) := by
    simpa [Fintype.card_fin, hcard] using hα
  simpa [hamiltonianCayleySum, cayleyHamConst] using
    sum_cayleyWeight_hamiltonian_eq_of_card_eq x
      (fun i : Fin (2 * k) => (i.val : ℂ)) hx hy hα (by simp [hcard])

open scoped Classical in
lemma hamiltonianCayleySum_subtype_eq_cayleyHamConst {α : Type*}
    [Fintype α] [DecidableEq α] (s : Finset α) (x : α → ℂ)
    (hx : Function.Injective x) {k : ℕ}
    (hs : 3 ≤ s.card) (hcard : s.card = 2 * k) :
    hamiltonianCayleySum (fun a : {a // a ∈ s} => x a.1) = cayleyHamConst k := by
  have hx' : Function.Injective (fun a : {a // a ∈ s} => x a.1) :=
    hx.comp Subtype.val_injective
  have hα : 3 ≤ Fintype.card {a // a ∈ s} := by
    simpa [Fintype.card_coe] using hs
  have hcard' : Fintype.card {a // a ∈ s} = 2 * k := by
    simpa [Fintype.card_coe] using hcard
  exact hamiltonianCayleySum_eq_cayleyHamConst _ hx' hα hcard'

lemma card_powersetCard_mem {α : Type*} [Fintype α] [DecidableEq α]
    (p : α) (n : ℕ) (hn : 1 ≤ n) :
    #((univ.powersetCard n).filter ({p} ⊆ ·)) =
      (Fintype.card α - 1).choose (n - 1) := by
  have hst : ({p} : Finset α) ⊆ univ := by simp
  have hsn : #({p} : Finset α) ≤ n := by simp [hn]
  simpa [card_singleton, card_univ] using
    card_filter_powersetCard_subset ({p} : Finset α) univ n hst hsn

lemma sum_ite_eq_support {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) (f : Finset α → ℂ) :
    (∑ s : Finset α, if s = σ.support then f s else 0) = f σ.support := by
  rw [sum_ite_eq' (s := univ), if_pos (mem_univ _)]

open scoped Classical in
/-- Paper (3.5) for `k ≥ 2`: the sum of Cayley weights of `2k`-cycles through `p`
equals `\binom{N-1}{2k-1} s_k`. -/
lemma sum_cayleyWeight_even_cycles_through {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) (hx : Function.Injective x) (p : α) {k : ℕ}
    (hk : 2 ≤ k) :
    (∑ σ : Perm α,
        if σ.IsCycle ∧ p ∈ σ.support ∧ σ.support.card = 2 * k then
          cayleyWeight x σ else 0) =
      ((Fintype.card α - 1).choose (2 * k - 1) : ℂ) * cayleyHamConst k := by
  have hsplit :
      (∑ σ : Perm α,
          if σ.IsCycle ∧ p ∈ σ.support ∧ σ.support.card = 2 * k then
            cayleyWeight x σ else 0) =
        ∑ s : Finset α, ∑ σ : Perm α,
          if σ.IsCycle ∧ σ.support = s ∧ p ∈ s ∧ s.card = 2 * k then
            cayleyWeight x σ else 0 := by
    rw [sum_comm]
    refine Fintype.sum_congr _ _ fun σ => ?_
    trans ∑ s : Finset α,
        if s = σ.support then
          (if σ.IsCycle ∧ p ∈ σ.support ∧ s.card = 2 * k then cayleyWeight x σ else 0)
        else 0
    · exact (sum_ite_eq_support σ fun s =>
        if σ.IsCycle ∧ p ∈ σ.support ∧ s.card = 2 * k then cayleyWeight x σ else 0).symm
    · refine Fintype.sum_congr _ _ fun s => ?_
      by_cases hsσ : s = σ.support
      · subst hsσ
        simp
      · have hne : ¬ (σ.IsCycle ∧ σ.support = s ∧ p ∈ s ∧ s.card = 2 * k) :=
          fun h => hsσ h.2.1.symm
        simp [hsσ, hne]
  rw [hsplit]
  have hfiber :
      (∑ s : Finset α, ∑ σ : Perm α,
          if σ.IsCycle ∧ σ.support = s ∧ p ∈ s ∧ s.card = 2 * k then
            cayleyWeight x σ else 0) =
        ∑ s : Finset α,
          if p ∈ s ∧ s.card = 2 * k then
            hamiltonianCayleySum (fun a : {a // a ∈ s} => x a.1)
          else 0 := by
    refine Fintype.sum_congr _ _ fun s => ?_
    by_cases hps : p ∈ s ∧ s.card = 2 * k
    · have hs2 : 2 ≤ s.card := by omega
      have hsum := sum_cayleyWeight_cycles_support x s hs2
      have hterm : ∀ σ : Perm α,
          (if σ.IsCycle ∧ σ.support = s ∧ p ∈ s ∧ s.card = 2 * k then
              cayleyWeight x σ else 0) =
            if σ.IsCycle ∧ σ.support = s then cayleyWeight x σ else 0 := by
        intro σ
        simp [hps]
      simp_rw [hterm, hsum, if_pos hps]
    · simp only [if_neg hps]
      refine Fintype.sum_eq_zero _ fun σ => ?_
      have hterm : ¬ (σ.IsCycle ∧ σ.support = s ∧ p ∈ s ∧ s.card = 2 * k) :=
        fun h => hps ⟨h.2.2.1, h.2.2.2⟩
      simp [hterm]
  rw [hfiber]
  have hconst :
      (∑ s : Finset α,
          if p ∈ s ∧ s.card = 2 * k then
            hamiltonianCayleySum (fun a : {a // a ∈ s} => x a.1)
          else 0) =
        ∑ s : Finset α,
          if p ∈ s ∧ s.card = 2 * k then cayleyHamConst k else 0 := by
    refine Fintype.sum_congr _ _ fun s => ?_
    by_cases hps : p ∈ s ∧ s.card = 2 * k
    · have hs3 : 3 ≤ s.card := by omega
      rw [if_pos hps, if_pos hps,
        hamiltonianCayleySum_subtype_eq_cayleyHamConst s x hx hs3 hps.2]
    · simp [hps]
  rw [hconst]
  have hfinal :
      (∑ s : Finset α, if p ∈ s ∧ s.card = 2 * k then cayleyHamConst k else 0) =
        ((Fintype.card α - 1).choose (2 * k - 1) : ℂ) * cayleyHamConst k := by
    rw [← sum_filter (fun s : Finset α => p ∈ s ∧ s.card = 2 * k),
      sum_const, nsmul_eq_mul]
    have hfeq :
        (univ : Finset (Finset α)).filter (fun s => p ∈ s ∧ s.card = 2 * k) =
          (univ.powersetCard (2 * k)).filter ({p} ⊆ ·) := by
      ext s
      simp [mem_powersetCard, singleton_subset_iff, and_comm]
    have hn : 1 ≤ 2 * k := by omega
    have hcard := card_powersetCard_mem p (2 * k) hn
    rw [hfeq, hcard]
  exact hfinal

open scoped Classical in
lemma cayleyHamConst_one : cayleyHamConst 1 = -1 := by
  have hfin : hamiltonianCayleySum (fun i : Fin (2 * 1) => (i.val : ℂ)) =
      hamiltonianCayleySum (fun i : Fin 2 => (i.val : ℂ)) := rfl
  rw [cayleyHamConst, hfin, sum_hamiltonian_eq_sum_ite]
  rw [show (univ : Finset (Perm (Fin 2))) = {1, Equiv.swap 0 1} from
    univ_perm_fin_two]
  rw [sum_insert (by simp [one_ne_swap_fin_two]), sum_singleton]
  have h1 : ¬ ((1 : Perm (Fin 2)).IsCycle ∧ (1 : Perm (Fin 2)).support = univ) :=
    fun h => h.1.ne_one rfl
  have hsw : (Equiv.swap (0 : Fin 2) 1).IsCycle ∧
      (Equiv.swap (0 : Fin 2) 1).support = univ := by
    refine ⟨Equiv.Perm.isCycle_swap Fin.zero_ne_one, ?_⟩
    rw [Equiv.Perm.support_swap Fin.zero_ne_one]
    ext i
    simp
    fin_cases i <;> simp
  rw [if_neg h1, if_pos hsw, cayleyWeight_swap_sq _ Fin.zero_ne_one]
  norm_num

lemma oddLongPoints_isCycle {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} (hσ : σ.IsCycle) :
    (oddLongPoints σ).Nonempty ↔ Odd σ.support.card := by
  constructor
  · intro hne
    obtain ⟨c, hc, hodd⟩ := (oddLongPoints_nonempty_iff (σ := σ)).mp hne
    have hcσ : c = σ := by
      simpa [hσ.cycleFactorsFinset_eq_singleton] using hc
    rwa [hcσ] at hodd
  · intro hodd
    refine (oddLongPoints_nonempty_iff (σ := σ)).mpr ⟨σ, ?_, hodd⟩
    simp [hσ.cycleFactorsFinset_eq_singleton]

lemma cayleySum_term_isCycle {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (x : α → ℂ) {σ : Perm α} (hσ : σ.IsCycle) :
    (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ) =
      if Odd σ.support.card then 0 else cayleyWeight x σ := by
  by_cases h : Odd σ.support.card
  · have hne : (oddLongPoints σ).Nonempty := (oddLongPoints_isCycle hσ).mpr h
    simp [hne, h]
  · have hne : ¬ (oddLongPoints σ).Nonempty :=
      fun h' => h ((oddLongPoints_isCycle hσ).mp h')
    simp [hne, h]

open scoped Classical in
lemma sum_cayleyWeight_long_even_cycles_through {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) (hx : Function.Injective x) (p : α) :
    (∑ σ : Perm α,
        if σ.IsCycle ∧ p ∈ σ.support ∧ 4 ≤ σ.support.card ∧ Even σ.support.card then
          cayleyWeight x σ else 0) =
      ∑ k ∈ Icc (2 : ℕ) (Fintype.card α / 2),
        ((Fintype.card α - 1).choose (2 * k - 1) : ℂ) * cayleyHamConst k := by
  have hswap :
      (∑ σ : Perm α, ∑ k ∈ Icc (2 : ℕ) (Fintype.card α / 2),
          if σ.IsCycle ∧ p ∈ σ.support ∧ σ.support.card = 2 * k then
            cayleyWeight x σ else 0) =
        ∑ k ∈ Icc (2 : ℕ) (Fintype.card α / 2), ∑ σ : Perm α,
          if σ.IsCycle ∧ p ∈ σ.support ∧ σ.support.card = 2 * k then
            cayleyWeight x σ else 0 :=
    sum_comm
  have hfiber : ∀ σ : Perm α,
      (∑ k ∈ Icc (2 : ℕ) (Fintype.card α / 2),
          if σ.IsCycle ∧ p ∈ σ.support ∧ σ.support.card = 2 * k then
            cayleyWeight x σ else 0) =
        if σ.IsCycle ∧ p ∈ σ.support ∧ 4 ≤ σ.support.card ∧ Even σ.support.card then
          cayleyWeight x σ else 0 := by
    intro σ
    by_cases hP : σ.IsCycle ∧ p ∈ σ.support
    · have hsum :
          (∑ k ∈ Icc (2 : ℕ) (Fintype.card α / 2),
              if σ.IsCycle ∧ p ∈ σ.support ∧ σ.support.card = 2 * k then
                cayleyWeight x σ else 0) =
            ∑ k ∈ Icc (2 : ℕ) (Fintype.card α / 2),
              if σ.support.card = 2 * k then cayleyWeight x σ else 0 :=
        sum_congr rfl fun k _ => by simp only [hP, true_and]
      rw [hsum]
      by_cases hE : Even σ.support.card
      · have hiff : ∀ k : ℕ, σ.support.card = 2 * k ↔ k = σ.support.card / 2 := by
          intro k
          constructor
          · intro hk
            have : 2 * (σ.support.card / 2) = σ.support.card :=
              Nat.two_mul_div_two_of_even hE
            omega
          · intro hk
            rw [hk, Nat.two_mul_div_two_of_even hE]
        simp_rw [hiff]
        rw [sum_ite_eq' (Icc (2 : ℕ) (Fintype.card α / 2)) (σ.support.card / 2)
          (fun _ => cayleyWeight x σ)]
        have hmem :
            σ.support.card / 2 ∈ Icc (2 : ℕ) (Fintype.card α / 2) ↔
              4 ≤ σ.support.card := by
          simp only [mem_Icc]
          have hle : σ.support.card / 2 ≤ Fintype.card α / 2 := by
            have : σ.support.card ≤ Fintype.card α := Finset.card_le_univ _
            omega
          constructor
          · intro h
            omega
          · intro h4
            exact ⟨by omega, hle⟩
        simp [hP, hE, hmem]
      · have hnone : ∀ k : ℕ, ¬ σ.support.card = 2 * k := by
          intro k hk
          exact hE (by rw [hk]; exact even_two_mul k)
        have hR : ¬ (σ.IsCycle ∧ p ∈ σ.support ∧ 4 ≤ σ.support.card ∧ Even σ.support.card) :=
          fun h => hE h.2.2.2
        rw [sum_eq_zero fun k _ => if_neg (hnone k), if_neg hR]
    · have hnone : ∀ k : ℕ,
          ¬ (σ.IsCycle ∧ p ∈ σ.support ∧ σ.support.card = 2 * k) := by
        intro k h
        exact hP ⟨h.1, h.2.1⟩
      have hR : ¬ (σ.IsCycle ∧ p ∈ σ.support ∧ 4 ≤ σ.support.card ∧ Even σ.support.card) :=
        fun h => hP ⟨h.1, h.2.1⟩
      rw [sum_eq_zero fun k _ => if_neg (hnone k), if_neg hR]
  have hleft :
      (∑ σ : Perm α,
          if σ.IsCycle ∧ p ∈ σ.support ∧ 4 ≤ σ.support.card ∧ Even σ.support.card then
            cayleyWeight x σ else 0) =
        ∑ k ∈ Icc (2 : ℕ) (Fintype.card α / 2), ∑ σ : Perm α,
          if σ.IsCycle ∧ p ∈ σ.support ∧ σ.support.card = 2 * k then
            cayleyWeight x σ else 0 := by
    rw [← hswap]
    exact Fintype.sum_congr _ _ fun σ => (hfiber σ).symm
  rw [hleft]
  refine sum_congr rfl fun k hk => ?_
  have hk2 : 2 ≤ k := (mem_Icc.mp hk).1
  exact sum_cayleyWeight_even_cycles_through x hx p hk2

/-- Sign matrix of size `m`, She–Sun–Xia (3.1) without the even-size constraint. -/
noncomputable def signMatrixOf (m : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => if j.val ≤ i.val then (1 : ℂ) else -1

/-- Sign matrix `A_n` from She–Sun–Xia (3.1), 0-based. -/
noncomputable def signMatrix (n : ℕ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ :=
  signMatrixOf (2 * n)

lemma signMatrix_apply (n : ℕ) (i j : Fin (2 * n)) :
    signMatrix n i j = if j.val ≤ i.val then (1 : ℂ) else -1 :=
  rfl

lemma signMatrixOf_eq_iverson {m : ℕ} (i j : Fin m) :
    signMatrixOf m i j = if i.val < j.val then (-1 : ℂ) else 1 := by
  simp only [signMatrixOf]
  by_cases h : j.val ≤ i.val
  · have : ¬ i.val < j.val := not_lt.mpr h
    simp [h, this]
  · have : i.val < j.val := Nat.lt_of_not_ge h
    simp [h, this]

lemma signMatrixOf_col_zero {m : ℕ} [NeZero m] (i : Fin m) :
    signMatrixOf m i 0 = 1 := by
  simp [signMatrixOf]

lemma signMatrix_one : (signMatrix 1).permanent = 0 := by
  have h : (signMatrix 1).permanent = (signMatrixOf 2).permanent := rfl
  rw [h, permanent_fin_two]
  simp [signMatrixOf]

lemma permanent_submatrix_equiv {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {R : Type*} [CommSemiring R]
    (e : α ≃ β) (M : Matrix β β R) :
    (M.submatrix e e).permanent = M.permanent := by
  simp only [permanent, submatrix_apply]
  refine Fintype.sum_equiv e.permCongr
    (fun σ : Perm α => ∏ i, M (e (σ i)) (e i))
    (fun ρ : Perm β => ∏ j, M (ρ j) j) fun σ => ?_
  exact Fintype.prod_equiv e
    (fun i => M (e (σ i)) (e i))
    (fun j => M (e.permCongr σ j) j)
    (fun i => by simp [permCongr_apply])

/-- Laplace expansion of a permanent along column 0. -/
lemma permanent_succ_column_zero {n : ℕ} {R : Type*} [CommSemiring R]
    (A : Matrix (Fin n.succ) (Fin n.succ) R) :
    A.permanent =
      ∑ i, A i 0 * (A.submatrix i.succAbove Fin.succ).permanent := by
  rw [permanent, univ_perm_fin_succ, ← univ_product_univ]
  simp only [sum_map, Equiv.toEmbedding_apply, sum_product]
  refine sum_congr rfl fun i _ => ?_
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [permanent, mul_sum]
    refine sum_congr rfl fun σ _ => ?_
    rw [Fin.prod_univ_succ]
    simp [Perm.decomposeFin_symm_apply_zero, Perm.decomposeFin_symm_apply_succ,
      Fin.succAbove_zero]
  · have hr :
        (A.submatrix i.succ.succAbove Fin.succ).permanent =
          ((A.submatrix i.succ.succAbove Fin.succ).submatrix (Fin.cycleRange i) id).permanent :=
      (permanent_permute_cols (Fin.cycleRange i) _).symm
    rw [hr]
    simp only [permanent, mul_sum]
    refine sum_congr rfl fun σ _ => ?_
    rw [Fin.prod_univ_succ, Perm.decomposeFin_symm_apply_zero]
    simp_rw [Perm.decomposeFin_symm_apply_succ, ← Fin.succAbove_cycleRange]
    rfl

lemma signMatrixOf_minor_eq_iverson {k : ℕ} (t : Fin k.succ) (r c : Fin k) :
    signMatrixOf k.succ (t.succAbove r) c.succ =
      if r.val < c.val ∨ (r = c ∧ r.val < t.val) then (-1 : ℂ) else 1 := by
  rw [signMatrixOf_eq_iverson]
  simp only [Fin.val_succ]
  by_cases h : r.castSucc < t
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.val_castSucc]
    have hr : r.val < t.val := by
      simpa [Fin.lt_def, Fin.val_castSucc] using h
    by_cases hij : r = c
    · subst hij
      simp [hr]
    · have hne : r.val ≠ c.val := Fin.val_injective.ne hij
      have hiff : (r.val < c.val + 1) ↔ r.val < c.val := by omega
      simp [hij, hr, hiff]
  · have hle : t ≤ r.castSucc := le_of_not_gt h
    rw [Fin.succAbove_of_le_castSucc _ _ hle, Fin.val_succ]
    have hr : ¬ r.val < t.val := by
      have : t.val ≤ r.val := by
        simpa [Fin.le_def, Fin.val_castSucc] using hle
      omega
    have hiff : (r.val + 1 < c.val + 1) ↔ r.val < c.val := by omega
    simp [hr, hiff]

open scoped Classical in
lemma prod_signMatrixOf_minor {k : ℕ} (t : Fin k.succ) (σ : Perm (Fin k)) :
    (∏ i, signMatrixOf k.succ (t.succAbove (σ i)) i.succ) =
      (-1 : ℂ) ^ #{i | (σ i).val < i.val ∨ (σ i = i ∧ i.val < t.val)} := by
  have hterm : ∀ i, signMatrixOf k.succ (t.succAbove (σ i)) i.succ =
      if (σ i).val < i.val ∨ (σ i = i ∧ i.val < t.val) then (-1 : ℂ) else 1 := by
    intro i
    rw [signMatrixOf_minor_eq_iverson]
    by_cases hf : σ i = i
    · simp [hf]
    · simp [hf]
  simp_rw [hterm]
  rw [prod_ite, prod_const, prod_const, one_pow, mul_one]

lemma signInv_rev_iff {k : ℕ} (t : Fin k.succ) (τ : Perm (Fin k)) (i : Fin k) :
    (((Fin.revPerm.permCongr τ) i).val < i.val ∨
      ((Fin.revPerm.permCongr τ) i = i ∧ i.val < t.val)) ↔
      ((Fin.rev i).val < (τ (Fin.rev i)).val ∨
        (τ (Fin.rev i) = Fin.rev i ∧ (Fin.rev t).val ≤ (Fin.rev i).val)) := by
  have hσ : (Fin.revPerm.permCongr τ) i = Fin.rev (τ (Fin.rev i)) := by
    simp [Fin.revPerm]
  constructor
  · intro h
    rw [hσ] at h
    rcases h with hlt | ⟨heq, hlt⟩
    · left
      have : k - ((τ (Fin.rev i)).val + 1) < i.val := by
        simpa [Fin.val_rev] using hlt
      have : (Fin.rev i).val < (τ (Fin.rev i)).val := by
        simp only [Fin.val_rev] at this ⊢
        omega
      exact this
    · right
      have hfix : τ (Fin.rev i) = Fin.rev i := Fin.rev_eq_iff.mp heq
      refine ⟨hfix, ?_⟩
      simp only [Fin.val_rev]
      omega
  · intro h
    rw [hσ]
    rcases h with hlt | ⟨hfix, hge⟩
    · left
      have : (Fin.rev i).val < (τ (Fin.rev i)).val := hlt
      simp only [Fin.val_rev] at this ⊢
      omega
    · right
      refine ⟨?_, ?_⟩
      · simp [hfix]
      · simp only [Fin.val_rev] at hge ⊢
        omega

open scoped Classical in
lemma card_signInv_add_rev {k : ℕ} (t : Fin k.succ) (τ : Perm (Fin k)) :
    #{i | ((Fin.revPerm.permCongr τ) i).val < i.val ∨
            ((Fin.revPerm.permCongr τ) i = i ∧ i.val < t.val)} +
      #{i | (τ i).val < i.val ∨ (τ i = i ∧ i.val < (Fin.rev t).val)} = k := by
  let Pσ : Fin k → Prop := fun i =>
    ((Fin.revPerm.permCongr τ) i).val < i.val ∨
      ((Fin.revPerm.permCongr τ) i = i ∧ i.val < t.val)
  let Q : Fin k → Prop := fun q =>
    q.val < (τ q).val ∨ (τ q = q ∧ (Fin.rev t).val ≤ q.val)
  let R : Fin k → Prop := fun q =>
    (τ q).val < q.val ∨ (τ q = q ∧ q.val < (Fin.rev t).val)
  have hPQ : ∀ i, Pσ i ↔ Q (Fin.rev i) := by
    intro i
    exact signInv_rev_iff t τ i
  have hQR : ∀ q, Q q ↔ ¬ R q := by
    intro q
    by_cases hf : τ q = q
    · simp [Q, R, hf]
    · have hne : (τ q).val ≠ q.val := Fin.val_injective.ne hf
      simp [Q, R, hf]
      omega
  have hcardP : #{i | Pσ i} = #{q | Q q} := by
    have e := Equiv.subtypeEquiv Fin.revPerm fun i => (hPQ i)
    have hc := Fintype.card_congr e
    simpa [Fintype.card_subtype] using hc
  have hadd : #{q | Q q} + #{q | R q} = k := by
    have : (univ : Finset (Fin k)).filter Q = univ.filter fun q => ¬ R q := by
      ext q
      simp [hQR]
    rw [this, add_comm, card_filter_add_card_filter_not (s := (univ : Finset (Fin k))) (p := R),
      card_univ, Fintype.card_fin]
  rw [hcardP, hadd]

open scoped Classical in
lemma permanent_signMatrixOf_minor_rev {k : ℕ} (t : Fin k.succ) :
    (signMatrixOf k.succ |>.submatrix t.succAbove Fin.succ).permanent =
      (-1 : ℂ) ^ k *
        (signMatrixOf k.succ |>.submatrix (Fin.rev t).succAbove Fin.succ).permanent := by
  simp only [permanent, submatrix_apply]
  rw [show
      (∑ σ : Perm (Fin k), (∏ i, signMatrixOf k.succ (t.succAbove (σ i)) i.succ : ℂ)) =
        ∑ τ : Perm (Fin k),
          ∏ i, signMatrixOf k.succ (t.succAbove ((Fin.revPerm.permCongr τ) i)) i.succ from
      Fintype.sum_equiv Fin.revPerm.permCongr
        (fun σ : Perm (Fin k) => (∏ i, signMatrixOf k.succ (t.succAbove (σ i)) i.succ : ℂ))
        (fun τ => ∏ i, signMatrixOf k.succ (t.succAbove ((Fin.revPerm.permCongr τ) i)) i.succ)
        (fun σ => by
          simp [Fin.revPerm])]
  rw [mul_sum]
  refine Fintype.sum_congr _ _ fun τ => ?_
  rw [prod_signMatrixOf_minor, prod_signMatrixOf_minor]
  set nP := #{i | ((Fin.revPerm.permCongr τ) i).val < i.val ∨
      ((Fin.revPerm.permCongr τ) i = i ∧ i.val < t.val)}
  set nR := #{i | (τ i).val < i.val ∨ (τ i = i ∧ i.val < (Fin.rev t).val)}
  have hsum : nP + nR = k := card_signInv_add_rev t τ
  have hsq : ((-1 : ℂ) ^ nR) ^ 2 = 1 := by
    rw [pow_two, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  calc
    (-1 : ℂ) ^ nP = (-1) ^ nP * 1 := (mul_one _).symm
    _ = (-1) ^ nP * ((-1) ^ nR * (-1) ^ nR) := by rw [← pow_two, hsq]
    _ = ((-1) ^ nP * (-1) ^ nR) * (-1) ^ nR := by ring
    _ = (-1) ^ (nP + nR) * (-1) ^ nR := by rw [← pow_add]
    _ = (-1) ^ k * (-1) ^ nR := by rw [hsum]

lemma odd_two_mul_pred {n : ℕ} (hn : 1 ≤ n) : Odd (2 * n - 1) := by
  have : 2 * n - 1 = 2 * (n - 1) + 1 := by omega
  rw [this]
  exact odd_two_mul_add_one _

lemma two_mul_eq_succ_pred {n : ℕ} (hn : 1 ≤ n) : (2 * n - 1).succ = 2 * n := by
  omega

open scoped Classical in
lemma sum_permanent_signMatrixOf_minor {k : ℕ} (hk : Odd k) :
    (∑ t : Fin k.succ,
        (signMatrixOf k.succ |>.submatrix t.succAbove Fin.succ).permanent) = 0 := by
  have hneg : (-1 : ℂ) ^ k = -1 := Odd.neg_one_pow hk
  have hpair : ∀ t : Fin k.succ,
      (signMatrixOf k.succ |>.submatrix t.succAbove Fin.succ).permanent +
        (signMatrixOf k.succ |>.submatrix (Fin.rev t).succAbove Fin.succ).permanent = 0 := by
    intro t
    have h := permanent_signMatrixOf_minor_rev (k := k) t
    rw [h, hneg]
    ring
  have hsum :
      ∑ t : Fin k.succ,
          ((signMatrixOf k.succ |>.submatrix t.succAbove Fin.succ).permanent +
            (signMatrixOf k.succ |>.submatrix (Fin.rev t).succAbove Fin.succ).permanent) = 0 :=
    sum_eq_zero fun t _ => hpair t
  have hrev :
      ∑ t : Fin k.succ,
          (signMatrixOf k.succ |>.submatrix (Fin.rev t).succAbove Fin.succ).permanent =
        ∑ t : Fin k.succ,
          (signMatrixOf k.succ |>.submatrix t.succAbove Fin.succ).permanent := by
    refine (Fintype.sum_equiv Fin.revPerm
      (fun t => (signMatrixOf k.succ |>.submatrix t.succAbove Fin.succ).permanent)
      (fun t => (signMatrixOf k.succ |>.submatrix (Fin.rev t).succAbove Fin.succ).permanent)
      fun t => ?_).symm
    simp [Fin.revPerm]
  rw [sum_add_distrib, hrev, ← two_mul] at hsum
  exact (mul_eq_zero.mp hsum).resolve_left (by exact two_ne_zero)

/-- She–Sun–Xia Lemma 3.1: `per(A_n) = 0` for `n ≥ 1`. -/
lemma permanent_signMatrix {n : ℕ} (hn : 1 ≤ n) :
    (signMatrix n).permanent = 0 := by
  have hsz : (2 * n - 1).succ = 2 * n := two_mul_eq_succ_pred hn
  have hM :
      (signMatrixOf (2 * n)).submatrix (finCongr hsz) (finCongr hsz) =
        signMatrixOf (2 * n - 1).succ := by
    ext i j
    simp [signMatrixOf, submatrix_apply]
  have hper : (signMatrix n).permanent = (signMatrixOf (2 * n - 1).succ).permanent := by
    have hs : signMatrix n = signMatrixOf (2 * n) := rfl
    rw [hs, ← hM]
    exact (permanent_submatrix_equiv (finCongr hsz) _).symm
  rw [hper, permanent_succ_column_zero]
  simp_rw [signMatrixOf_col_zero, one_mul]
  exact sum_permanent_signMatrixOf_minor (odd_two_mul_pred hn)

lemma cayleyWeight_swap_of_zero {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {p q : α} (hpq : p ≠ q) (hxp : x p = 0) (hxq : x q ≠ 0) :
    cayleyWeight x (Equiv.swap p q) = -1 := by
  rw [cayleyWeight_swap_sq x hpq, hxp]
  have hden : (0 : ℂ) - x q ≠ 0 := sub_ne_zero.2 (Ne.symm hxq)
  field_simp [hden]
  ring

lemma choose_two_mul_pred_one {n : ℕ} :
    (2 * n - 1).choose 1 = 2 * n - 1 :=
  Nat.choose_one_right _

lemma cayleyHamConst_one_mul_choose (n : ℕ) :
    ((2 * n - 1).choose (2 * 1 - 1) : ℂ) * cayleyHamConst 1 = - (2 * n - 1 : ℕ) := by
  rw [cayleyHamConst_one, choose_two_mul_pred_one]
  simp

/-- Paper (3.8) rewritten with `s_1 = -1`: the `k ≥ 2` sum is `2n-2` iff
`1 + ∑_{k=1}^n \binom{2n-1}{2k-1} s_k = 0`. -/
lemma cayleyHamConst_binom_sum_rewrite {n : ℕ} (hn : 1 ≤ n) :
    (1 + ∑ k ∈ Icc (1 : ℕ) n,
        ((2 * n - 1).choose (2 * k - 1) : ℂ) * cayleyHamConst k) =
      (∑ k ∈ Icc (2 : ℕ) n,
        ((2 * n - 1).choose (2 * k - 1) : ℂ) * cayleyHamConst k) -
      (2 * n - 2 : ℕ) := by
  have hsplit :
      (Icc (1 : ℕ) n) = insert 1 (Icc (2 : ℕ) n) := by
    ext k
    simp [mem_Icc]
    omega
  have h1 : 1 ∉ Icc (2 : ℕ) n := by simp [mem_Icc]
  rw [hsplit, sum_insert h1, cayleyHamConst_one_mul_choose]
  have : (1 : ℂ) + (-(2 * n - 1 : ℕ) +
      ∑ k ∈ Icc (2 : ℕ) n,
        ((2 * n - 1).choose (2 * k - 1) : ℂ) * cayleyHamConst k) =
      (∑ k ∈ Icc (2 : ℕ) n,
        ((2 * n - 1).choose (2 * k - 1) : ℂ) * cayleyHamConst k) -
        (2 * n - 2 : ℕ) := by
    have : (2 * n - 1 : ℕ) = (2 * n - 2 : ℕ) + 1 := by omega
    simp [this]
    ring
  rw [this]

lemma cayleySum_fin_two_of_zero {x : Fin 2 → ℂ} (h0 : x 0 = 0) (h1 : x 1 ≠ 0) :
    cayleySum x = 0 := by
  rw [cayleySum_fin_two, cayleyWeight_swap_of_zero x Fin.zero_ne_one h0 h1]
  simp

lemma sameCycle_permCongr {α β : Type*} (e : α ≃ β) {σ : Perm α} {a x : α} :
    (e.permCongr σ).SameCycle (e a) (e x) ↔ σ.SameCycle a x := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simpa [permCongr_zpow, permCongr_apply] using congrArg e.symm hi
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simp [permCongr_zpow, permCongr_apply, hi]

open scoped Classical in
lemma cycleOf_permCongr {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (σ : Perm α) (a : α) :
    (e.permCongr σ).cycleOf (e a) = e.permCongr (σ.cycleOf a) := by
  ext b
  obtain ⟨x, rfl⟩ := e.surjective b
  have hL := Equiv.Perm.cycleOf_apply (e.permCongr σ) (e a) (e x)
  have hR := Equiv.Perm.cycleOf_apply σ a x
  have hS := sameCycle_permCongr (e := e) (σ := σ) (a := a) (x := x)
  change (e.permCongr σ).cycleOf (e a) (e x) = e.permCongr (σ.cycleOf a) (e x)
  rw [hL, permCongr_apply, Equiv.symm_apply_apply, permCongr_apply, Equiv.symm_apply_apply]
  rw [hR]
  simp only [hS]
  split_ifs <;> rfl

lemma support_cycleOf_permCongr {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (σ : Perm α) (a : α) :
    ((e.permCongr σ).cycleOf (e a)).support =
      (σ.cycleOf a).support.map e.toEmbedding := by
  ext b
  constructor
  · intro hb
    obtain ⟨x, rfl⟩ := e.surjective b
    rw [mem_map]
    refine ⟨x, ?_, rfl⟩
    rw [Equiv.Perm.mem_support_cycleOf_iff] at hb ⊢
    refine ⟨(sameCycle_permCongr (e := e) (σ := σ) (a := a) (x := x)).1 hb.1, ?_⟩
    have hsup : e a ∈ (e.permCongr σ).support := hb.2
    rw [support_permCongr, mem_map] at hsup
    obtain ⟨a', ha', hea⟩ := hsup
    exact (e.injective hea).symm ▸ ha'
  · intro hb
    rw [mem_map] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    rw [Equiv.Perm.mem_support_cycleOf_iff] at hx ⊢
    refine ⟨(sameCycle_permCongr (e := e) (σ := σ) (a := a) (x := x)).2 hx.1, ?_⟩
    rw [support_permCongr, mem_map]
    exact ⟨a, hx.2, rfl⟩

lemma oddLongPoints_permCongr_nonempty_iff {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (σ : Perm α) :
    (oddLongPoints (e.permCongr σ)).Nonempty ↔ (oddLongPoints σ).Nonempty := by
  constructor
  · intro ⟨b, hb⟩
    obtain ⟨a, rfl⟩ := e.surjective b
    have hb' : Odd ((σ.cycleOf a).support.card) := by
      rw [mem_oddLongPoints, support_cycleOf_permCongr, card_map] at hb
      exact hb
    exact ⟨a, mem_oddLongPoints.mpr hb'⟩
  · intro ⟨a, ha⟩
    refine ⟨e a, mem_oddLongPoints.mpr ?_⟩
    have hb : Odd ((σ.cycleOf a).support.card) := mem_oddLongPoints.mp ha
    rw [support_cycleOf_permCongr, card_map]
    exact hb

lemma cayleySum_permCongr {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [LinearOrder α] [LinearOrder β]
    (e : α ≃ β) (y : β → ℂ) :
    cayleySum (y ∘ e) = cayleySum y := by
  unfold cayleySum
  refine Fintype.sum_equiv e.permCongr
    (fun σ => if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight (y ∘ e) σ)
    (fun ρ => if (oddLongPoints ρ).Nonempty then 0 else cayleyWeight y ρ) fun σ => ?_
  rw [cayleyWeight_permCongr]
  by_cases h : (oddLongPoints σ).Nonempty
  · have h' : (oddLongPoints (e.permCongr σ)).Nonempty :=
      (oddLongPoints_permCongr_nonempty_iff e σ).2 h
    simp [h, h']
  · have h' : ¬ (oddLongPoints (e.permCongr σ)).Nonempty := fun hne =>
      h ((oddLongPoints_permCongr_nonempty_iff e σ).1 hne)
    simp [h, h']

def pairSubtypeEquiv {α : Type*} [DecidableEq α] {p q : α} (hpq : p ≠ q) :
    Fin 2 ≃ {a // a ∈ ({p, q} : Finset α)} where
  toFun i := if i = 0 then ⟨p, by simp⟩ else ⟨q, by simp⟩
  invFun a := if a.1 = p then 0 else 1
  left_inv i := by
    fin_cases i
    · simp
    · simp [hpq.symm]
  right_inv a := by
    have hmem : a.1 = p ∨ a.1 = q := by
      have := a.2
      simp only [mem_insert, mem_singleton] at this
      exact this
    rcases hmem with h | h
    · simp [h]
      exact Subtype.ext h.symm
    · have hq : q ≠ p := hpq.symm
      simp [h, hq]
      exact Subtype.ext h.symm

lemma cayleySumOn_pair {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {p q : α} (hpq : p ≠ q) (x : α → ℂ) (hxp : x p = 0) (hxq : x q ≠ 0) :
    cayleySumOn ({p, q} : Finset α) x = 0 := by
  let e := pairSubtypeEquiv hpq
  have hy : cayleySum (fun a : {a // a ∈ ({p, q} : Finset α)} => x a.1) =
      cayleySum ((fun a : {a // a ∈ ({p, q} : Finset α)} => x a.1) ∘ e) :=
    (cayleySum_permCongr e (fun a => x a.1)).symm
  rw [cayleySumOn, hy]
  have h0 : ((fun a : {a // a ∈ ({p, q} : Finset α)} => x a.1) ∘ e) 0 = 0 := by
    simp [e, pairSubtypeEquiv, hxp]
  have h1 : ((fun a : {a // a ∈ ({p, q} : Finset α)} => x a.1) ∘ e) 1 ≠ 0 := by
    simp [e, pairSubtypeEquiv, hxq]
  exact cayleySum_fin_two_of_zero h0 h1

lemma eq_swap_of_isCycle_card_two {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} {p : α} (hσ : σ.IsCycle) (hp : p ∈ σ.support)
    (h2 : σ.support.card = 2) :
    σ = Equiv.swap p (σ p) := by
  have hcy : σ.cycleOf p = σ :=
    Equiv.Perm.IsCycle.cycleOf_eq hσ (Equiv.Perm.mem_support.mp hp)
  have hcard : (σ.cycleOf p).support.card = 2 := by rw [hcy, h2]
  have hswap := cycleOf_eq_swap_of_card_two hcard
  rwa [hcy] at hswap

lemma isCycle_swap_mem_card_two {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (hpq : p ≠ q) :
    (Equiv.swap p q).IsCycle ∧ p ∈ (Equiv.swap p q).support ∧
      (Equiv.swap p q).support.card = 2 := by
  refine ⟨Equiv.Perm.isCycle_swap hpq, ?_, ?_⟩
  · simp [Equiv.Perm.support_swap hpq]
  · rw [Equiv.Perm.support_swap hpq, card_insert_of_notMem (by simp [hpq]),
      card_singleton]

open scoped Classical in
lemma sum_cayleyWeight_transpositions_through {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) (p : α) :
    (∑ σ : Perm α,
        if σ.IsCycle ∧ p ∈ σ.support ∧ σ.support.card = 2 then
          cayleyWeight x σ else 0) =
      ∑ q : α, if q = p then 0 else cayleyWeight x (Equiv.swap p q) := by
  have hsplit : ∀ σ : Perm α,
      (if σ.IsCycle ∧ p ∈ σ.support ∧ σ.support.card = 2 then
        cayleyWeight x σ else 0) =
        ∑ q : α, if q = p then 0 else
          if σ = Equiv.swap p q then cayleyWeight x σ else 0 := by
    intro σ
    by_cases h : σ.IsCycle ∧ p ∈ σ.support ∧ σ.support.card = 2
    · have hsw : σ = Equiv.swap p (σ p) :=
        eq_swap_of_isCycle_card_two h.1 h.2.1 h.2.2
      have hp : σ p ≠ p := Equiv.Perm.mem_support.mp h.2.1
      rw [if_pos h]
      have hsum :
          (∑ q : α, if q = p then (0 : ℂ) else
            if σ = Equiv.swap p q then cayleyWeight x σ else 0) =
            if σ p = p then 0 else
              if σ = Equiv.swap p (σ p) then cayleyWeight x σ else 0 :=
        Fintype.sum_eq_single (σ p) fun q hq => by
          by_cases hqp : q = p
          · simp [hqp]
          · have hne : σ ≠ Equiv.swap p q := by
              intro hf
              apply hq
              have hcongr :=
                congr_fun (congr_arg (fun f : Perm α => (f : α → α)) (hsw.symm.trans hf)) p
              simpa [swap_apply_left] using hcongr.symm
            simp [hqp, hne]
      rw [hsum, if_neg hp, if_pos hsw]
    · rw [if_neg h]
      refine (sum_eq_zero fun q _ => ?_).symm
      by_cases hqp : q = p
      · simp [hqp]
      · have hpq : p ≠ q := fun heq => hqp heq.symm
        simp only [hqp, ↓reduceIte]
        by_cases hsw : σ = Equiv.swap p q
        · exact (h (by rw [hsw]; exact isCycle_swap_mem_card_two hpq)).elim
        · simp [hsw]
  refine (Fintype.sum_congr _ _ hsplit).trans ?_
  rw [sum_comm]
  refine Fintype.sum_congr _ _ fun q => ?_
  by_cases hqp : q = p
  · simp [hqp]
  · simp only [hqp, ↓reduceIte]
    rw [sum_ite_eq' (s := univ) (a := Equiv.swap p q)]
    simp

open scoped Classical in
lemma sum_cayleyWeight_transpositions_through_of_zero {α : Type*}
    [Fintype α] [DecidableEq α] (x : α → ℂ) (p : α)
    (hx : Function.Injective x) (hxp : x p = 0) :
    (∑ σ : Perm α,
        if σ.IsCycle ∧ p ∈ σ.support ∧ σ.support.card = 2 then
          cayleyWeight x σ else 0) =
      -((Fintype.card α - 1 : ℕ) : ℂ) := by
  rw [sum_cayleyWeight_transpositions_through]
  have hterm : ∀ q : α,
      (if q = p then (0 : ℂ) else cayleyWeight x (Equiv.swap p q)) =
        if q = p then 0 else -1 := by
    intro q
    by_cases hqp : q = p
    · simp [hqp]
    · have hpq : p ≠ q := fun heq => hqp heq.symm
      have hxq : x q ≠ 0 := fun hxq => hpq (hx (by rw [hxp, hxq]))
      simp [hqp, cayleyWeight_swap_of_zero x hpq hxp hxq]
  simp_rw [hterm]
  rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hpos : #(univ.filter (fun q : α => q = p)) = 1 := by
    simp [filter_eq']
  have hneg : #(univ.filter (fun q : α => ¬ q = p)) = Fintype.card α - 1 := by
    have hdis := card_filter_add_card_filter_not (s := univ) (p := fun q : α => q = p)
    have : #(univ.filter (fun q : α => q = p)) +
        #(univ.filter (fun q : α => ¬ q = p)) = Fintype.card α := by
      simpa [card_univ] using hdis
    omega
  rw [hpos, hneg]
  simp

open scoped Classical in
noncomputable def evenCycleSumThrough {α : Type*} [Fintype α] [DecidableEq α]
    (p : α) (x : α → ℂ) : ℂ :=
  ∑ σ : Perm α,
    if σ.IsCycle ∧ p ∈ σ.support ∧ Even σ.support.card then
      cayleyWeight x σ else 0

open scoped Classical in
lemma evenCycleSumThrough_split {α : Type*} [Fintype α] [DecidableEq α]
    (p : α) (x : α → ℂ) :
    evenCycleSumThrough p x =
      (∑ σ : Perm α,
          if σ.IsCycle ∧ p ∈ σ.support ∧ σ.support.card = 2 then
            cayleyWeight x σ else 0) +
      (∑ σ : Perm α,
          if σ.IsCycle ∧ p ∈ σ.support ∧ 4 ≤ σ.support.card ∧ Even σ.support.card then
            cayleyWeight x σ else 0) := by
  unfold evenCycleSumThrough
  rw [← sum_add_distrib]
  refine Fintype.sum_congr _ _ fun σ => ?_
  by_cases hcy : σ.IsCycle ∧ p ∈ σ.support ∧ Even σ.support.card
  · have hparity : σ.support.card = 2 ∨ 4 ≤ σ.support.card := by
      have he : Even σ.support.card := hcy.2.2
      have hpos : 0 < σ.support.card := card_pos.mpr ⟨p, hcy.2.1⟩
      have hne1 : σ.support.card ≠ 1 := by
        intro h1
        have hodd : Odd σ.support.card := ⟨0, by simp [h1]⟩
        exact Nat.not_even_iff_odd.mpr hodd he
      have hne3 : σ.support.card ≠ 3 := by
        intro h3
        have hodd : Odd σ.support.card := ⟨1, by simp [h3]⟩
        exact Nat.not_even_iff_odd.mpr hodd he
      omega
    rcases hparity with h2 | h4
    · have h2' : σ.IsCycle ∧ p ∈ σ.support ∧ σ.support.card = 2 :=
        ⟨hcy.1, hcy.2.1, h2⟩
      have h4' : ¬ (σ.IsCycle ∧ p ∈ σ.support ∧ 4 ≤ σ.support.card ∧ Even σ.support.card) := by
        intro h
        omega
      rw [if_pos hcy, if_pos h2', if_neg h4']
      simp
    · have h2' : ¬ (σ.IsCycle ∧ p ∈ σ.support ∧ σ.support.card = 2) := by
        intro h
        omega
      have h4' : σ.IsCycle ∧ p ∈ σ.support ∧ 4 ≤ σ.support.card ∧ Even σ.support.card :=
        ⟨hcy.1, hcy.2.1, h4, hcy.2.2⟩
      rw [if_pos hcy, if_neg h2', if_pos h4']
      simp
  · have h2' : ¬ (σ.IsCycle ∧ p ∈ σ.support ∧ σ.support.card = 2) := by
      intro h2
      exact hcy ⟨h2.1, h2.2.1, by simp [h2.2.2]⟩
    have h4' : ¬ (σ.IsCycle ∧ p ∈ σ.support ∧ 4 ≤ σ.support.card ∧ Even σ.support.card) :=
      fun h4 => hcy ⟨h4.1, h4.2.1, h4.2.2.2⟩
    rw [if_neg hcy, if_neg h2', if_neg h4']
    simp

open scoped Classical in
lemma evenCycleSumThrough_eq_binom {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) (hx : Function.Injective x) (p : α) (hxp : x p = 0) :
    evenCycleSumThrough p x =
      ∑ k ∈ Icc (1 : ℕ) (Fintype.card α / 2),
        ((Fintype.card α - 1).choose (2 * k - 1) : ℂ) * cayleyHamConst k := by
  rw [evenCycleSumThrough_split, sum_cayleyWeight_transpositions_through_of_zero x p hx hxp,
    sum_cayleyWeight_long_even_cycles_through x hx p]
  by_cases hI : 1 ≤ Fintype.card α / 2
  · have hsplit : Icc (1 : ℕ) (Fintype.card α / 2) =
        insert 1 (Icc (2 : ℕ) (Fintype.card α / 2)) := by
      ext k
      simp [mem_Icc]
      omega
    have h1 : 1 ∉ Icc (2 : ℕ) (Fintype.card α / 2) := by simp [mem_Icc]
    rw [hsplit, sum_insert h1]
    have hcho : ((Fintype.card α - 1).choose (2 * 1 - 1) : ℂ) * cayleyHamConst 1 =
        -((Fintype.card α - 1 : ℕ) : ℂ) := by
      rw [cayleyHamConst_one]
      simp
    rw [hcho]
  · have h0 : Fintype.card α / 2 = 0 := by omega
    have hIcc2 : Icc (2 : ℕ) (Fintype.card α / 2) = ∅ := by
      simp [h0]
    have hIcc1 : Icc (1 : ℕ) (Fintype.card α / 2) = ∅ := by
      simp [h0]
    have hcard : Fintype.card α - 1 = 0 := by
      have : Fintype.card α ≤ 1 := by omega
      omega
    simp [hIcc1, hIcc2, hcard]

lemma remainder_fixes_cycle_base {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) (p : α) :
    (σ * (σ.cycleOf p)⁻¹) p = p := by
  by_cases hp : σ p = p
  · have h1 : σ.cycleOf p = 1 := (Equiv.Perm.cycleOf_eq_one_iff σ).mpr hp
    simp [h1, hp]
  · have hc : σ.cycleOf p ∈ σ.cycleFactorsFinset :=
      (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff).2 (Equiv.Perm.mem_support.mpr hp)
    have hmem : p ∈ (σ.cycleOf p).support :=
      Equiv.Perm.mem_support.mpr (by
        rw [Equiv.Perm.cycleOf_apply_self]
        exact hp)
    exact remainder_apply_eq_self_of_mem hc hmem

lemma disjoint_cycleOf_remainder {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) (p : α) :
    Equiv.Perm.Disjoint (σ.cycleOf p) (σ * (σ.cycleOf p)⁻¹) := by
  by_cases hp : σ p = p
  · have h1 : σ.cycleOf p = 1 := (Equiv.Perm.cycleOf_eq_one_iff σ).mpr hp
    rw [h1]
    exact Equiv.Perm.disjoint_one_left _
  · have hc : σ.cycleOf p ∈ σ.cycleFactorsFinset :=
      (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff).2 (Equiv.Perm.mem_support.mpr hp)
    exact (Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc).symm

lemma eq_cycleOf_mul_remainder {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) (p : α) :
    σ = σ.cycleOf p * (σ * (σ.cycleOf p)⁻¹) := by
  by_cases hp : σ p = p
  · have h1 : σ.cycleOf p = 1 := (Equiv.Perm.cycleOf_eq_one_iff σ).mpr hp
    simp [h1]
  · exact eq_mul_remainder_of_mem_cycleFactorsFinset
      ((Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff).2 (Equiv.Perm.mem_support.mpr hp))

lemma oddLongPoints_mul_disjoint {α : Type*} [Fintype α] [DecidableEq α]
    {σ τ : Perm α} (h : Equiv.Perm.Disjoint σ τ) :
    (oddLongPoints (σ * τ)).Nonempty ↔
      (oddLongPoints σ).Nonempty ∨ (oddLongPoints τ).Nonempty := by
  rw [oddLongPoints_nonempty_iff, oddLongPoints_nonempty_iff, oddLongPoints_nonempty_iff,
    h.cycleFactorsFinset_mul_eq_union]
  constructor
  · rintro ⟨c, hc, hodd⟩
    rw [mem_union] at hc
    rcases hc with hσ | hτ
    · exact Or.inl ⟨c, hσ, hodd⟩
    · exact Or.inr ⟨c, hτ, hodd⟩
  · rintro (⟨c, hc, hodd⟩ | ⟨c, hc, hodd⟩)
    · exact ⟨c, mem_union.mpr (Or.inl hc), hodd⟩
    · exact ⟨c, mem_union.mpr (Or.inr hc), hodd⟩

lemma cayleyWeight_cycleOf_mul_remainder {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) (σ : Perm α) (p : α) :
    cayleyWeight x σ =
      cayleyWeight x (σ.cycleOf p) * cayleyWeight x (σ * (σ.cycleOf p)⁻¹) := by
  nth_rw 1 [eq_cycleOf_mul_remainder σ p]
  exact cayleyWeight_mul_disjoint x (disjoint_cycleOf_remainder σ p)

lemma oddLongPoints_cycleOf_mul_remainder {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) (p : α) :
    (oddLongPoints σ).Nonempty ↔
      (oddLongPoints (σ.cycleOf p)).Nonempty ∨
        (oddLongPoints (σ * (σ.cycleOf p)⁻¹)).Nonempty := by
  nth_rw 1 [eq_cycleOf_mul_remainder σ p]
  exact oddLongPoints_mul_disjoint (disjoint_cycleOf_remainder σ p)

lemma remainderThrough_eq_one_iff {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) (p : α) :
    σ * (σ.cycleOf p)⁻¹ = 1 ↔ σ = σ.cycleOf p := by
  constructor
  · intro h
    calc σ
        = σ.cycleOf p * (σ * (σ.cycleOf p)⁻¹) := eq_cycleOf_mul_remainder σ p
      _ = σ.cycleOf p * 1 := by rw [h]
      _ = σ.cycleOf p := by simp
  · intro h
    have h' : σ.cycleOf p = σ := h.symm
    rw [h']
    exact mul_inv_cancel σ

lemma eq_cycleOf_of_isCycle_mem {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} {p : α} (hσ : σ.IsCycle) (hp : p ∈ σ.support) :
    σ = σ.cycleOf p :=
  (Equiv.Perm.IsCycle.cycleOf_eq hσ (Equiv.Perm.mem_support.mp hp)).symm

open scoped Classical in
lemma cayleySum_term_remainder_one {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] (p : α) (x : α → ℂ) (σ : Perm α)
    (h1 : σ * (σ.cycleOf p)⁻¹ = 1) :
    (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ) =
      if σ = 1 then 1
      else if σ.IsCycle ∧ p ∈ σ.support ∧ Even σ.support.card then
        cayleyWeight x σ else 0 := by
  have hσ : σ = σ.cycleOf p := (remainderThrough_eq_one_iff σ p).1 h1
  by_cases hσ1 : σ = 1
  · subst hσ1
    simp [oddLongPoints_one, cayleyWeight_one]
  · have hp : σ p ≠ p := by
      intro hp
      have : σ.cycleOf p = 1 := (Equiv.Perm.cycleOf_eq_one_iff σ).mpr hp
      exact hσ1 (hσ.trans this)
    have hcy : σ.IsCycle := by
      rw [hσ]
      exact Equiv.Perm.isCycle_cycleOf σ hp
    have hmem : p ∈ σ.support := Equiv.Perm.mem_support.mpr hp
    have hterm := cayleySum_term_isCycle x hcy
    rw [hterm]
    by_cases hodd : Odd σ.support.card
    · have hn : ¬ Even σ.support.card := Nat.not_even_iff_odd.mpr hodd
      simp [hσ1, hcy, hmem, hodd, hn]
    · have he : Even σ.support.card := Nat.not_odd_iff_even.mp hodd
      simp [hσ1, hcy, hmem, he]

open scoped Classical in
lemma cayleySum_remainder_one {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] (p : α) (x : α → ℂ) :
    (∑ σ : Perm α,
        if σ * (σ.cycleOf p)⁻¹ = 1 then
          (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
        else 0) =
      1 + evenCycleSumThrough p x := by
  have hterm : ∀ σ : Perm α,
      (if σ * (σ.cycleOf p)⁻¹ = 1 then
        (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
      else 0) =
        (if σ = 1 then (1 : ℂ) else 0) +
          (if σ.IsCycle ∧ p ∈ σ.support ∧ Even σ.support.card then
            cayleyWeight x σ else 0) := by
    intro σ
    by_cases h1 : σ * (σ.cycleOf p)⁻¹ = 1
    · rw [if_pos h1, cayleySum_term_remainder_one p x σ h1]
      by_cases hσ1 : σ = 1
      · simp [hσ1]
      · simp [hσ1]
    · rw [if_neg h1]
      have hσ1 : σ ≠ 1 := by
        intro hσ1
        subst hσ1
        exact h1 (by simp [Equiv.Perm.cycleOf_one])
      have hn : ¬ (σ.IsCycle ∧ p ∈ σ.support ∧ Even σ.support.card) := by
        intro hcy
        exact h1 ((remainderThrough_eq_one_iff σ p).2
          (eq_cycleOf_of_isCycle_mem hcy.1 hcy.2.1))
      rw [if_neg hσ1, if_neg hn, zero_add]
  rw [Fintype.sum_congr _ _ hterm, sum_add_distrib]
  refine congr_arg₂ (· + ·) ?_ rfl
  rw [sum_ite_eq' (s := univ) (a := (1 : Perm α))]
  simp

open scoped Classical in
lemma cayleySum_eq_one_add_even_cycles_add_complementary {α : Type*}
    [Fintype α] [DecidableEq α] [LinearOrder α] (p : α) (x : α → ℂ) :
    cayleySum x =
      1 + evenCycleSumThrough p x +
      (∑ σ : Perm α,
          if σ * (σ.cycleOf p)⁻¹ = 1 then 0
          else if (oddLongPoints σ).Nonempty then 0 else cayleyWeight x σ) := by
  unfold cayleySum
  have hsplit : ∀ σ : Perm α,
      (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ) =
        (if σ * (σ.cycleOf p)⁻¹ = 1 then
          (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
        else 0) +
        (if σ * (σ.cycleOf p)⁻¹ = 1 then 0
          else if (oddLongPoints σ).Nonempty then 0 else cayleyWeight x σ) := by
    intro σ
    by_cases h1 : σ * (σ.cycleOf p)⁻¹ = 1
    · simp [h1]
    · simp [h1]
  rw [Fintype.sum_congr _ _ hsplit, sum_add_distrib, cayleySum_remainder_one p x]

lemma remainderThrough_eq_one_of_card_two {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 2) (σ : Perm α) (p : α) :
    σ * (σ.cycleOf p)⁻¹ = 1 := by
  by_cases hp : σ p = p
  · have hfix : p ∉ σ.support := Equiv.Perm.notMem_support.mpr hp
    have hσ : σ.support = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro q hq
      have hq_ne : q ≠ p := fun hqp => hfix (hqp ▸ hq)
      have hσq_ne_q : σ q ≠ q := Equiv.Perm.mem_support.mp hq
      have hσq_ne_p : σ q ≠ p := fun h => hq_ne (σ.injective (h.trans hp.symm))
      have htrip : ({p, q, σ q} : Finset α).card = 3 := by
        have hpq : p ∉ ({q, σ q} : Finset α) := by
          intro h
          simp only [mem_insert, mem_singleton] at h
          rcases h with h | h
          · exact hq_ne h.symm
          · exact hσq_ne_p h.symm
        have hqσ : q ∉ ({σ q} : Finset α) := by
          simp only [mem_singleton]
          exact hσq_ne_q.symm
        rw [card_insert_of_notMem hpq, card_insert_of_notMem hqσ, card_singleton]
      have : 3 ≤ Fintype.card α := by
        have hsub : ({p, q, σ q} : Finset α) ⊆ univ := by simp
        simpa [htrip] using card_le_card hsub
      omega
    have : σ = 1 := Equiv.Perm.support_eq_empty_iff.mp hσ
    simp [this, Equiv.Perm.cycleOf_one]
  · have hcy : (σ.cycleOf p).IsCycle := Equiv.Perm.isCycle_cycleOf σ hp
    have h2 : 2 ≤ (σ.cycleOf p).support.card := hcy.two_le_card_support
    have hle : (σ.cycleOf p).support.card ≤ Fintype.card α := card_le_univ _
    have hsup : (σ.cycleOf p).support = univ :=
      eq_univ_of_card _ (by omega)
    refine Equiv.ext fun a =>
      (disjoint_cycleOf_remainder σ p a).resolve_left ?_
    exact Equiv.Perm.mem_support.mp (by rw [hsup]; exact mem_univ a)

open scoped Classical in
lemma cayleySum_eq_one_add_even_cycles_of_card_two {α : Type*}
    [Fintype α] [DecidableEq α] [LinearOrder α] (p : α) (x : α → ℂ)
    (hcard : Fintype.card α = 2) :
    cayleySum x = 1 + evenCycleSumThrough p x := by
  rw [cayleySum_eq_one_add_even_cycles_add_complementary p x]
  have h0 :
      (∑ σ : Perm α,
          if σ * (σ.cycleOf p)⁻¹ = 1 then (0 : ℂ)
          else if (oddLongPoints σ).Nonempty then 0 else cayleyWeight x σ) = 0 := by
    refine Fintype.sum_eq_zero _ fun σ => ?_
    simp [remainderThrough_eq_one_of_card_two hcard σ p]
  rw [h0, add_zero]

lemma cycleOf_mul_of_fixes {α : Type*} [Fintype α] [DecidableEq α]
    {c τ : Perm α} (hd : Equiv.Perm.Disjoint c τ) {p : α} (hp : τ p = p) :
    (c * τ).cycleOf p = c.cycleOf p :=
  Equiv.Perm.cycleOf_mul_of_apply_right_eq_self hd.commute p hp

lemma remainder_mul_of_cycleOf_eq {α : Type*} [Fintype α] [DecidableEq α]
    {c τ : Perm α} (hd : Equiv.Perm.Disjoint c τ) {p : α} (hp : τ p = p)
    (hc : c.cycleOf p = c) :
    (c * τ) * ((c * τ).cycleOf p)⁻¹ = τ := by
  rw [cycleOf_mul_of_fixes hd hp, hc, hd.commute.eq, mul_assoc, mul_inv_cancel, mul_one]

lemma disjoint_ofSubtype_support_compl {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} (u : Perm {a // a ∈ s}) {τ : Perm α}
    (hτ : τ.support ⊆ sᶜ) :
    Equiv.Perm.Disjoint (Equiv.Perm.ofSubtype u) τ := by
  intro x
  by_cases hx : x ∈ s
  · right
    refine Equiv.Perm.notMem_support.mp ?_
    intro hmem
    exact (mem_compl.mp (hτ hmem)) hx
  · left
    exact Equiv.Perm.ofSubtype_apply_of_not_mem u hx

lemma cayleyWeight_ofSubtype_mul_of_support_compl {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} (x : α → ℂ) (u : Perm {a // a ∈ s}) {τ : Perm α}
    (hτ : τ.support ⊆ sᶜ) :
    cayleyWeight x (Equiv.Perm.ofSubtype u * τ) =
      cayleyWeight (fun a : {a // a ∈ s} => x a.1) u * cayleyWeight x τ := by
  rw [cayleyWeight_mul_disjoint x (disjoint_ofSubtype_support_compl u hτ),
    cayleyWeight_ofSubtype_finset]

lemma mem_support_compl_of_fixes {α : Type*} [Fintype α] [DecidableEq α]
    {τ : Perm α} {p : α} (hp : τ p = p) : p ∈ τ.supportᶜ :=
  mem_compl.mpr (Equiv.Perm.notMem_support.mpr hp)

lemma support_cycleOf_subset_remainder_compl {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) (p : α) :
    (σ.cycleOf p).support ⊆ (σ * (σ.cycleOf p)⁻¹).supportᶜ := by
  intro x hx
  exact mem_compl.mpr
    (Finset.disjoint_left.1 (disjoint_cycleOf_remainder σ p).disjoint_support hx)

lemma cycleOf_eq_self_of_support_eq {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} {p : α} (h : (σ.cycleOf p).support = σ.support) :
    σ.cycleOf p = σ := by
  ext y
  by_cases hsame : Equiv.Perm.SameCycle σ p y
  · exact hsame.cycleOf_apply
  · have hns : y ∉ (σ.cycleOf p).support := fun hy =>
      hsame (Equiv.Perm.mem_support_cycleOf_iff.mp hy).1
    have hnsσ : y ∉ σ.support := by rwa [← h]
    rw [Equiv.Perm.notMem_support.mp hns, Equiv.Perm.notMem_support.mp hnsσ]

lemma cycleOf_cycleOf {α : Type*} [Fintype α] [DecidableEq α] (σ : Perm α) (p : α) :
    (σ.cycleOf p).cycleOf p = σ.cycleOf p := by
  by_cases hp : σ p = p
  · have h1 : σ.cycleOf p = 1 := (Equiv.Perm.cycleOf_eq_one_iff σ).mpr hp
    simp [h1, Equiv.Perm.cycleOf_one]
  · exact (eq_cycleOf_of_isCycle_mem (Equiv.Perm.isCycle_cycleOf σ hp)
      (Equiv.Perm.mem_support.mpr (by
        rw [Equiv.Perm.cycleOf_apply_self]
        exact hp))).symm

lemma cycleOf_eq_self_iff {α : Type*} [Fintype α] [DecidableEq α] (σ : Perm α) (p : α) :
    σ.cycleOf p = σ ↔ σ = 1 ∨ (σ.IsCycle ∧ p ∈ σ.support) := by
  constructor
  · intro h
    by_cases hp : σ p = p
    · have h1 : σ.cycleOf p = 1 := (Equiv.Perm.cycleOf_eq_one_iff σ).mpr hp
      exact Or.inl (h.symm.trans h1)
    · refine Or.inr ⟨?_, Equiv.Perm.mem_support.mpr hp⟩
      rw [← h]
      exact Equiv.Perm.isCycle_cycleOf σ hp
  · rintro (h1 | ⟨hcy, hmem⟩)
    · simp [h1, Equiv.Perm.cycleOf_one]
    · exact (eq_cycleOf_of_isCycle_mem hcy hmem).symm

lemma cycleOf_ofSubtype_eq_of_cycleOf_eq {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} (u : Perm {a // a ∈ s}) {p : α} (hp : p ∈ s)
    (h : u.cycleOf ⟨p, hp⟩ = u) :
    (Equiv.Perm.ofSubtype u).cycleOf p = Equiv.Perm.ofSubtype u := by
  rcases (cycleOf_eq_self_iff u ⟨p, hp⟩).mp h with h1 | ⟨hcy, hmem⟩
  · rw [h1, map_one, Equiv.Perm.cycleOf_one]
  · refine (eq_cycleOf_of_isCycle_mem (ofSubtype_isCycle hcy) ?_).symm
    have hne : u ⟨p, hp⟩ ≠ ⟨p, hp⟩ := Equiv.Perm.mem_support.mp hmem
    refine Equiv.Perm.mem_support.mpr ?_
    rw [Equiv.Perm.ofSubtype_apply_of_mem u hp]
    exact fun hf => hne (Subtype.ext hf)

lemma cycleOf_eq_self_of_ofSubtype_cycleOf_eq {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} (u : Perm {a // a ∈ s}) {p : α} (hp : p ∈ s)
    (h : (Equiv.Perm.ofSubtype u).cycleOf p = Equiv.Perm.ofSubtype u) :
    u.cycleOf ⟨p, hp⟩ = u := by
  rcases (cycleOf_eq_self_iff (Equiv.Perm.ofSubtype u) p).mp h with h1 | ⟨hcy, hmem⟩
  · have hu : u = 1 :=
      Equiv.Perm.ofSubtype_injective (h1.trans (map_one Equiv.Perm.ofSubtype).symm)
    simp [hu, Equiv.Perm.cycleOf_one]
  · have hne : u ⟨p, hp⟩ ≠ ⟨p, hp⟩ := by
      have : Equiv.Perm.ofSubtype u p ≠ p := Equiv.Perm.mem_support.mp hmem
      exact fun hf => this (by
        rw [Equiv.Perm.ofSubtype_apply_of_mem u hp, hf])
    obtain ⟨a, ha, hall⟩ := hcy
    have has : a ∈ s := by
      by_contra hns
      exact ha (Equiv.Perm.ofSubtype_apply_of_not_mem u hns)
    have hcyu : u.IsCycle := by
      refine ⟨⟨a, has⟩, ?_, fun y hy => ?_⟩
      · intro hf
        exact ha (by
          rw [Equiv.Perm.ofSubtype_apply_of_mem u has, hf])
      · exact (sameCycle_ofSubtype_coe u).mp (hall (by
          rw [Equiv.Perm.ofSubtype_apply_coe]
          exact fun hf => hy (Subtype.ext hf)))
    exact (eq_cycleOf_of_isCycle_mem hcyu
      (Equiv.Perm.mem_support.mpr hne)).symm

lemma remainder_ofSubtype_mul {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} (u : Perm {a // a ∈ s}) {τ : Perm α} {p : α}
    (hp : p ∈ s) (hτ : τ.support ⊆ sᶜ)
    (hc : u.cycleOf ⟨p, hp⟩ = u) :
    (Equiv.Perm.ofSubtype u * τ) * ((Equiv.Perm.ofSubtype u * τ).cycleOf p)⁻¹ = τ :=
  remainder_mul_of_cycleOf_eq (disjoint_ofSubtype_support_compl u hτ)
    (not_mem_support_of_mem_of_subset_compl hτ hp)
    (cycleOf_ofSubtype_eq_of_cycleOf_eq u hp hc)

lemma remainder_ofSubtype_mul_iff {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} (u : Perm {a // a ∈ s}) {τ : Perm α} {p : α}
    (hp : p ∈ s) (hτ : τ.support ⊆ sᶜ) :
    (Equiv.Perm.ofSubtype u * τ) * ((Equiv.Perm.ofSubtype u * τ).cycleOf p)⁻¹ = τ ↔
      u.cycleOf ⟨p, hp⟩ = u := by
  constructor
  · intro hrem
    have hd := disjoint_ofSubtype_support_compl u hτ
    have hfix : τ p = p := not_mem_support_of_mem_of_subset_compl hτ hp
    have hcyc : (Equiv.Perm.ofSubtype u * τ).cycleOf p =
        (Equiv.Perm.ofSubtype u).cycleOf p :=
      cycleOf_mul_of_fixes hd hfix
    have hself : Equiv.Perm.ofSubtype u *
        ((Equiv.Perm.ofSubtype u).cycleOf p)⁻¹ = 1 := by
      have hcalc :
          τ * (Equiv.Perm.ofSubtype u * ((Equiv.Perm.ofSubtype u).cycleOf p)⁻¹) = τ := by
        calc τ * (Equiv.Perm.ofSubtype u * ((Equiv.Perm.ofSubtype u).cycleOf p)⁻¹)
            = Equiv.Perm.ofSubtype u * τ *
                ((Equiv.Perm.ofSubtype u).cycleOf p)⁻¹ := by
              rw [hd.commute.eq, mul_assoc]
          _ = Equiv.Perm.ofSubtype u * τ *
                ((Equiv.Perm.ofSubtype u * τ).cycleOf p)⁻¹ := by
              rw [hcyc]
          _ = τ := hrem
      exact mul_left_cancel hcalc
    have : (Equiv.Perm.ofSubtype u).cycleOf p = Equiv.Perm.ofSubtype u :=
      ((remainderThrough_eq_one_iff (Equiv.Perm.ofSubtype u) p).mp hself).symm
    exact cycleOf_eq_self_of_ofSubtype_cycleOf_eq u hp this
  · intro hc
    exact remainder_ofSubtype_mul u hp hτ hc

lemma cycleOf_subtypePerm_eq_self {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} {c : Perm α} (hsub : c.support ⊆ s) {p : α} (hp : p ∈ s)
    (hc : c.cycleOf p = c) :
    (c.subtypePerm fun x => (mem_of_support_subset (s := s) hsub x).symm).cycleOf ⟨p, hp⟩ =
      c.subtypePerm fun x => (mem_of_support_subset (s := s) hsub x).symm := by
  refine cycleOf_eq_self_of_ofSubtype_cycleOf_eq
      (c.subtypePerm fun x => (mem_of_support_subset (s := s) hsub x).symm) hp ?_
  rw [ofSubtype_subtypePerm_of_support_subset hsub, hc]

lemma cayleyWeight_ofSubtype_mul_oddLong {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} (x : α → ℂ) (u : Perm {a // a ∈ s}) {τ : Perm α}
    (hτ : τ.support ⊆ sᶜ) :
    (if (oddLongPoints (Equiv.Perm.ofSubtype u * τ)).Nonempty then (0 : ℂ)
      else cayleyWeight x (Equiv.Perm.ofSubtype u * τ)) =
      (if (oddLongPoints τ).Nonempty then 0 else cayleyWeight x τ) *
        (if (oddLongPoints u).Nonempty then 0
          else cayleyWeight (fun a : {a // a ∈ s} => x a.1) u) := by
  have hd := disjoint_ofSubtype_support_compl u hτ
  have hodd := oddLongPoints_mul_disjoint hd
  have hwt := cayleyWeight_ofSubtype_mul_of_support_compl x u hτ
  by_cases hτo : (oddLongPoints τ).Nonempty
  · have hne : (oddLongPoints (Equiv.Perm.ofSubtype u * τ)).Nonempty :=
      hodd.mpr (Or.inr hτo)
    simp [hne, hτo]
  · by_cases huo : (oddLongPoints u).Nonempty
    · have hne : (oddLongPoints (Equiv.Perm.ofSubtype u * τ)).Nonempty :=
        hodd.mpr (Or.inl ((oddLongPoints_ofSubtype_nonempty_iff u).2 huo))
      simp [hne, hτo, huo]
    · have hne : ¬ (oddLongPoints (Equiv.Perm.ofSubtype u * τ)).Nonempty := fun h =>
        (hodd.mp h).elim
          (fun h' => huo ((oddLongPoints_ofSubtype_nonempty_iff u).1 h'))
          (fun h' => hτo h')
      rw [if_neg hne, if_neg hτo, if_neg huo, hwt, mul_comm]

open scoped Classical in
lemma sum_ite_cycleOf_eq_self {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] (p : α) (x : α → ℂ) :
    (∑ σ : Perm α,
        if σ.cycleOf p = σ then
          (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
        else 0) =
      1 + evenCycleSumThrough p x := by
  have hterm : ∀ σ : Perm α,
      (if σ.cycleOf p = σ then
        (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
      else 0) =
        if σ * (σ.cycleOf p)⁻¹ = 1 then
          (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
        else 0 := by
    intro σ
    have hiff : σ.cycleOf p = σ ↔ σ * (σ.cycleOf p)⁻¹ = 1 := by
      rw [remainderThrough_eq_one_iff, eq_comm]
    simp [hiff]
  rw [Fintype.sum_congr _ _ hterm, cayleySum_remainder_one p x]

lemma remainderFibre_support_cycleOf {α : Type*} [Fintype α] [DecidableEq α]
    {σ τ : Perm α} {p : α} (h : σ * (σ.cycleOf p)⁻¹ = τ) :
    (σ.cycleOf p).support ⊆ τ.supportᶜ := by
  have : (σ.cycleOf p).support ⊆ (σ * (σ.cycleOf p)⁻¹).supportᶜ :=
    support_cycleOf_subset_remainder_compl σ p
  rwa [h] at this

noncomputable def remainderFibreEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (p : α) (τ : Perm α) (hp : τ p = p) :
    {u : Perm {a // a ∈ τ.supportᶜ} //
        u.cycleOf ⟨p, mem_support_compl_of_fixes hp⟩ = u} ≃
      {σ : Perm α // σ * (σ.cycleOf p)⁻¹ = τ} where
  toFun u :=
    ⟨Equiv.Perm.ofSubtype u.1 * τ,
      remainder_ofSubtype_mul u.1 (mem_support_compl_of_fixes hp)
        (by rw [compl_compl]) u.2⟩
  invFun σ :=
    ⟨(σ.1.cycleOf p).subtypePerm fun x =>
        (mem_of_support_subset (remainderFibre_support_cycleOf σ.2) x).symm,
      cycleOf_subtypePerm_eq_self (remainderFibre_support_cycleOf σ.2)
        (mem_support_compl_of_fixes hp) (cycleOf_cycleOf σ.1 p)⟩
  left_inv := fun u => by
    apply Subtype.ext
    apply Equiv.ext
    intro q
    apply Subtype.ext
    change ((Equiv.Perm.ofSubtype u.1 * τ).cycleOf p) q.1 = (u.1 q).1
    have hcy : (Equiv.Perm.ofSubtype u.1 * τ).cycleOf p =
        Equiv.Perm.ofSubtype u.1 := by
      rw [cycleOf_mul_of_fixes
          (disjoint_ofSubtype_support_compl u.1 (by rw [compl_compl])) hp,
        cycleOf_ofSubtype_eq_of_cycleOf_eq u.1 (mem_support_compl_of_fixes hp) u.2]
    rw [hcy]
    exact Equiv.Perm.ofSubtype_apply_coe u.1 q
  right_inv := fun σ => by
    apply Subtype.ext
    change Equiv.Perm.ofSubtype
        ((σ.1.cycleOf p).subtypePerm fun x =>
          (mem_of_support_subset (remainderFibre_support_cycleOf σ.2) x).symm) * τ =
      σ.1
    rw [ofSubtype_subtypePerm_of_support_subset (remainderFibre_support_cycleOf σ.2)]
    have hσ : σ.1 = σ.1.cycleOf p * (σ.1 * (σ.1.cycleOf p)⁻¹) :=
      eq_cycleOf_mul_remainder σ.1 p
    have hc : σ.1.cycleOf p * τ =
        σ.1.cycleOf p * (σ.1 * (σ.1.cycleOf p)⁻¹) :=
      congrArg (fun ρ => σ.1.cycleOf p * ρ) σ.2.symm
    exact hc.trans hσ.symm

open scoped Classical in
lemma cayleySum_fibre_remainder {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] (x : α → ℂ) (p : α) (τ : Perm α) (hp : τ p = p) :
    (∑ σ : Perm α,
        if σ * (σ.cycleOf p)⁻¹ = τ then
          (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
        else 0) =
      (if (oddLongPoints τ).Nonempty then 0 else cayleyWeight x τ) *
        (1 + evenCycleSumThrough
          (⟨p, mem_support_compl_of_fixes hp⟩ : {a // a ∈ τ.supportᶜ})
          (fun a => x a.1)) := by
  have hp' : p ∈ τ.supportᶜ := mem_support_compl_of_fixes hp
  have hτs : τ.support ⊆ (τ.supportᶜ)ᶜ := by
    rw [compl_compl]
  let g : Perm α → ℂ := fun σ =>
    if (oddLongPoints σ).Nonempty then 0 else cayleyWeight x σ
  have hL :
      (∑ σ : Perm α,
          if σ * (σ.cycleOf p)⁻¹ = τ then g σ else 0) =
        ∑ u : {u : Perm {a // a ∈ τ.supportᶜ} // u.cycleOf ⟨p, hp'⟩ = u},
          g (Equiv.Perm.ofSubtype u.1 * τ) := by
    calc
      (∑ σ : Perm α,
          if σ * (σ.cycleOf p)⁻¹ = τ then g σ else 0) =
          ∑ σ ∈ univ.filter (fun σ : Perm α => σ * (σ.cycleOf p)⁻¹ = τ), g σ := by
        rw [sum_filter]
      _ = ∑ σ : {σ : Perm α // σ * (σ.cycleOf p)⁻¹ = τ}, g σ.1 := by
        rw [sum_subtype (p := fun σ : Perm α => σ * (σ.cycleOf p)⁻¹ = τ)
          (univ.filter (fun σ : Perm α => σ * (σ.cycleOf p)⁻¹ = τ))
          (fun σ => by simp) g]
      _ = ∑ u : {u : Perm {a // a ∈ τ.supportᶜ} // u.cycleOf ⟨p, hp'⟩ = u},
            g (Equiv.Perm.ofSubtype u.1 * τ) := by
        rw [← Equiv.sum_comp (remainderFibreEquiv p τ hp) (fun σ => g σ.1)]
        rfl
  have hU :
      (∑ u : {u : Perm {a // a ∈ τ.supportᶜ} // u.cycleOf ⟨p, hp'⟩ = u},
          g (Equiv.Perm.ofSubtype u.1 * τ)) =
        ∑ u : Perm {a // a ∈ τ.supportᶜ},
          if u.cycleOf ⟨p, hp'⟩ = u then
            g (Equiv.Perm.ofSubtype u * τ) else 0 := by
    rw [← sum_subtype
        (p := fun u : Perm {a // a ∈ τ.supportᶜ} => u.cycleOf ⟨p, hp'⟩ = u)
        (univ.filter (fun u : Perm {a // a ∈ τ.supportᶜ} => u.cycleOf ⟨p, hp'⟩ = u))
        (fun u => by simp)
        (fun u => g (Equiv.Perm.ofSubtype u * τ)),
      sum_filter]
  have hterm : ∀ u : Perm {a // a ∈ τ.supportᶜ},
      (if u.cycleOf ⟨p, hp'⟩ = u then
        g (Equiv.Perm.ofSubtype u * τ) else 0) =
        (if (oddLongPoints τ).Nonempty then (0 : ℂ) else cayleyWeight x τ) *
          (if u.cycleOf ⟨p, hp'⟩ = u then
            (if (oddLongPoints u).Nonempty then 0
              else cayleyWeight (fun a : {a // a ∈ τ.supportᶜ} => x a.1) u)
          else 0) := by
    intro u
    by_cases hc : u.cycleOf ⟨p, hp'⟩ = u
    · rw [if_pos hc, if_pos hc]
      change (if (oddLongPoints (Equiv.Perm.ofSubtype u * τ)).Nonempty then (0 : ℂ)
          else cayleyWeight x (Equiv.Perm.ofSubtype u * τ)) =
        (if (oddLongPoints τ).Nonempty then 0 else cayleyWeight x τ) *
          (if (oddLongPoints u).Nonempty then 0
            else cayleyWeight (fun a : {a // a ∈ τ.supportᶜ} => x a.1) u)
      exact cayleyWeight_ofSubtype_mul_oddLong x u hτs
    · simp [hc]
  rw [hL, hU, Fintype.sum_congr _ _ hterm, ← mul_sum, sum_ite_cycleOf_eq_self]

lemma cayleySum_fibre_remainder_of_moves {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] (x : α → ℂ) (p : α) (τ : Perm α) (hp : τ p ≠ p) :
    (∑ σ : Perm α,
        if σ * (σ.cycleOf p)⁻¹ = τ then
          (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
        else 0) = 0 := by
  refine Fintype.sum_eq_zero _ fun σ => ?_
  have hne : σ * (σ.cycleOf p)⁻¹ ≠ τ := fun h =>
    hp (h ▸ remainder_fixes_cycle_base σ p)
  simp [hne]

open scoped Classical in
lemma cayleySum_complementary_eq_sum_fibres {α : Type*}
    [Fintype α] [DecidableEq α] [LinearOrder α] (p : α) (x : α → ℂ) :
    (∑ σ : Perm α,
        if σ * (σ.cycleOf p)⁻¹ = 1 then 0
        else if (oddLongPoints σ).Nonempty then 0 else cayleyWeight x σ) =
      ∑ τ : Perm α,
        if τ = 1 then 0
        else (∑ σ : Perm α,
          if σ * (σ.cycleOf p)⁻¹ = τ then
            (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
          else 0) := by
  have hsplit : ∀ σ : Perm α,
      (if σ * (σ.cycleOf p)⁻¹ = 1 then (0 : ℂ)
        else if (oddLongPoints σ).Nonempty then 0 else cayleyWeight x σ) =
        ∑ τ : Perm α,
          if σ * (σ.cycleOf p)⁻¹ = τ then
            (if τ = 1 then 0
              else if (oddLongPoints σ).Nonempty then 0 else cayleyWeight x σ)
          else 0 := by
    intro σ
    have hsum :
        (∑ τ : Perm α,
            if σ * (σ.cycleOf p)⁻¹ = τ then
              (if τ = 1 then (0 : ℂ)
                else if (oddLongPoints σ).Nonempty then 0 else cayleyWeight x σ)
            else 0) =
          if σ * (σ.cycleOf p)⁻¹ = σ * (σ.cycleOf p)⁻¹ then
            (if σ * (σ.cycleOf p)⁻¹ = 1 then 0
              else if (oddLongPoints σ).Nonempty then 0 else cayleyWeight x σ)
          else 0 :=
      Fintype.sum_eq_single _ (fun τ hτ => if_neg (Ne.symm hτ))
    rw [hsum, if_pos rfl]
  rw [Fintype.sum_congr _ _ hsplit, sum_comm]
  refine Fintype.sum_congr _ _ fun τ => ?_
  by_cases h1 : τ = 1
  · rw [if_pos h1]
    refine Fintype.sum_eq_zero _ fun σ => ?_
    simp [h1]
  · rw [if_neg h1]
    refine Fintype.sum_congr _ _ fun σ => ?_
    simp [h1]

open scoped Classical in
lemma cayleySum_complementary_eq_inner {α : Type*}
    [Fintype α] [DecidableEq α] [LinearOrder α] (p : α) (x : α → ℂ) :
    (∑ σ : Perm α,
        if σ * (σ.cycleOf p)⁻¹ = 1 then 0
        else if (oddLongPoints σ).Nonempty then 0 else cayleyWeight x σ) =
      ∑ τ : Perm α,
        if h : τ p = p then
          if τ = 1 then 0
          else (if (oddLongPoints τ).Nonempty then 0 else cayleyWeight x τ) *
            (1 + evenCycleSumThrough
              (⟨p, mem_support_compl_of_fixes h⟩ : {a // a ∈ τ.supportᶜ})
              (fun a => x a.1))
        else 0 := by
  rw [cayleySum_complementary_eq_sum_fibres]
  refine Fintype.sum_congr _ _ fun τ => ?_
  by_cases hpτ : τ p = p
  · rw [dif_pos hpτ]
    by_cases h1 : τ = 1
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1, cayleySum_fibre_remainder x p τ hpτ]
  · rw [dif_neg hpτ]
    have hne1 : τ ≠ 1 := fun hτ1 => hpτ (by simp [hτ1])
    rw [if_neg hne1, cayleySum_fibre_remainder_of_moves x p τ hpτ]

/-- Cayley kernel matrix. Off-diagonal entries are `(x_j + x_i)/(x_j - x_i)`
so that Mathlib's permanent `∏_i M (σ i) i` matches `cayleyWeight`. -/
noncomputable def cayleyMatrix {α : Type*} [DecidableEq α] (x : α → ℂ) :
    Matrix α α ℂ :=
  fun i j => if i = j then (1 : ℂ) else (x j + x i) / (x j - x i)

lemma cayleyMatrix_apply_eq {α : Type*} [DecidableEq α] (x : α → ℂ) (i : α) :
    cayleyMatrix x i i = 1 := by
  simp [cayleyMatrix]

lemma cayleyMatrix_apply_ne {α : Type*} [DecidableEq α] (x : α → ℂ) {i j : α}
    (hij : i ≠ j) :
    cayleyMatrix x i j = (x j + x i) / (x j - x i) := by
  simp [cayleyMatrix, hij]

lemma prod_cayleyMatrix_eq_cayleyWeight {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) (σ : Perm α) :
    (∏ i, cayleyMatrix x (σ i) i) = cayleyWeight x σ := by
  unfold cayleyWeight
  rw [← union_compl σ.support, prod_union disjoint_compl_right]
  have hfix : ∏ i ∈ σ.supportᶜ, cayleyMatrix x (σ i) i = 1 := by
    refine prod_eq_one fun i hi => ?_
    have : σ i = i := Equiv.Perm.notMem_support.mp (mem_compl.mp hi)
    rw [this, cayleyMatrix_apply_eq]
  rw [hfix, mul_one]
  refine prod_congr rfl fun i hi => ?_
  have hne : σ i ≠ i := Equiv.Perm.mem_support.mp hi
  rw [cayleyMatrix_apply_ne x hne]

lemma permanent_cayleyMatrix {α : Type*} [Fintype α] [DecidableEq α] (x : α → ℂ) :
    (cayleyMatrix x).permanent = ∑ σ : Perm α, cayleyWeight x σ := by
  unfold Matrix.permanent
  refine Fintype.sum_congr _ _ fun σ => prod_cayleyMatrix_eq_cayleyWeight x σ

lemma permanent_cayleyMatrix_eq_cayleySum {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] (x : α → ℂ) :
    (cayleyMatrix x).permanent = cayleySum x := by
  rw [permanent_cayleyMatrix, cayleySum]
  exact sum_cayleyWeight_eq_sum_no_odd x

lemma sunMatrix_eq_cayleyMatrix {n : ℕ} [NeZero n] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n)) :
    sunMatrix n ζ = cayleyMatrix (fun i : Fin (2 * n) => ζ ^ i.val) := by
  ext i j
  by_cases hij : i = j
  · simp [hij, sunMatrix, cayleyMatrix]
  · rw [sunMatrix_apply_ne hζ hij, cayleyMatrix_apply_ne _ hij]
    exact (cayley_eq_sunFactor (N := 2 * n) hζ (Ne.symm hij)).symm

/-- Assignment with a zero coordinate and geometric off-zero values.
Paper sequential limits use `0 < ε < 1`. -/
noncomputable def cayleyPowZero (n : ℕ) (ε : ℂ) : Fin n → ℂ :=
  fun i => if i.val = 0 then 0 else ε ^ (n - i.val)

lemma cayleyPowZero_zero {n : ℕ} [NeZero n] (ε : ℂ) :
    cayleyPowZero n ε 0 = 0 := by
  simp [cayleyPowZero]

lemma cayleyPowZero_of_ne_zero {n : ℕ} {ε : ℂ} {i : Fin n} (hi : i.val ≠ 0) :
    cayleyPowZero n ε i = ε ^ (n - i.val) := by
  simp [cayleyPowZero, hi]

lemma cayleyPowZero_ne_zero {n : ℕ} {ε : ℂ} {i : Fin n}
    (hi : i.val ≠ 0) (hε : ε ≠ 0) :
    cayleyPowZero n ε i ≠ 0 := by
  rw [cayleyPowZero_of_ne_zero hi]
  exact pow_ne_zero _ hε

lemma cayleyMatrix_powZero_col_zero {n : ℕ} [NeZero n] {ε : ℂ} {i : Fin n}
    (hi : i ≠ 0) (hε : ε ≠ 0) :
    cayleyMatrix (cayleyPowZero n ε) i 0 = -1 := by
  rw [cayleyMatrix_apply_ne _ hi, cayleyPowZero_zero, zero_add, zero_sub, div_neg]
  have hx : cayleyPowZero n ε i ≠ 0 :=
    cayleyPowZero_ne_zero (Fin.val_ne_of_ne hi) hε
  rw [div_self hx]

lemma cayleyMatrix_powZero_row_zero {n : ℕ} [NeZero n] {ε : ℂ} {j : Fin n}
    (hj : j ≠ 0) (hε : ε ≠ 0) :
    cayleyMatrix (cayleyPowZero n ε) 0 j = 1 := by
  rw [cayleyMatrix_apply_ne _ hj.symm, cayleyPowZero_zero, add_zero, sub_zero]
  have hx : cayleyPowZero n ε j ≠ 0 :=
    cayleyPowZero_ne_zero (Fin.val_ne_of_ne hj) hε
  rw [div_self hx]

lemma injective_pow_of_lt_one {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Function.Injective (fun k : ℕ => ε ^ k) := by
  intro a b h
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · exact absurd h
      ((pow_lt_pow_iff_right_of_lt_one₀ hε0 hε1).mpr hlt).ne.symm
  · rfl
  · exact absurd h.symm
      ((pow_lt_pow_iff_right_of_lt_one₀ hε0 hε1).mpr hgt).ne.symm

lemma injective_cayleyPowZero {n : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Function.Injective (cayleyPowZero n (ε : ℂ)) := by
  intro i j hij
  have hεC : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε0.ne'
  by_cases hi : i.val = 0
  · have hzi : cayleyPowZero n (ε : ℂ) i = 0 := by simp [cayleyPowZero, hi]
    have hzj : cayleyPowZero n (ε : ℂ) j = 0 := by rw [← hij, hzi]
    have hj : j.val = 0 := by
      by_contra hj
      exact cayleyPowZero_ne_zero hj hεC hzj
    exact Fin.eq_of_val_eq (hi.trans hj.symm)
  · by_cases hj : j.val = 0
    · have hzj : cayleyPowZero n (ε : ℂ) j = 0 := by simp [cayleyPowZero, hj]
      have hzi : cayleyPowZero n (ε : ℂ) i = 0 := by rw [hij, hzj]
      exact (cayleyPowZero_ne_zero hi hεC hzi).elim
    · have hpow : ((ε : ℂ) ^ (n - i.val)) = (ε : ℂ) ^ (n - j.val) := by
        rwa [cayleyPowZero_of_ne_zero hi, cayleyPowZero_of_ne_zero hj] at hij
      have hre : ε ^ (n - i.val) = ε ^ (n - j.val) := by
        apply Complex.ofReal_injective
        rw [Complex.ofReal_pow, Complex.ofReal_pow, hpow]
      have hidx : n - i.val = n - j.val := injective_pow_of_lt_one hε0 hε1 hre
      have hival : i.val = j.val := by
        have hi' : i.val ≤ n := Nat.le_of_lt i.isLt
        have hj' : j.val ≤ n := Nat.le_of_lt j.isLt
        omega
      exact Fin.eq_of_val_eq hival

lemma cayleyMatrix_powZero_of_val_lt {n : ℕ} {ε : ℂ} {i j : Fin n}
    (hi : i.val ≠ 0) (hj : j.val ≠ 0) (hij : i.val < j.val) (hε : ε ≠ 0) :
    cayleyMatrix (cayleyPowZero n ε) i j =
      (1 + ε ^ (j.val - i.val)) / (1 - ε ^ (j.val - i.val)) := by
  have hne : i ≠ j := Fin.ne_of_val_ne (ne_of_lt hij)
  rw [cayleyMatrix_apply_ne _ hne, cayleyPowZero_of_ne_zero hi,
    cayleyPowZero_of_ne_zero hj]
  have hsub : n - i.val = (n - j.val) + (j.val - i.val) := by
    have : i.val ≤ n := Nat.le_of_lt i.isLt
    have : j.val ≤ n := Nat.le_of_lt j.isLt
    omega
  rw [hsub, pow_add]
  have hden : ε ^ (n - j.val) ≠ 0 := pow_ne_zero _ hε
  field_simp [hden]

lemma cayleyMatrix_powZero_of_val_gt {n : ℕ} {ε : ℂ} {i j : Fin n}
    (hi : i.val ≠ 0) (hj : j.val ≠ 0) (hji : j.val < i.val) (hε : ε ≠ 0) :
    cayleyMatrix (cayleyPowZero n ε) i j =
      (ε ^ (i.val - j.val) + 1) / (ε ^ (i.val - j.val) - 1) := by
  have hne : i ≠ j := Fin.ne_of_val_ne (ne_of_gt hji)
  rw [cayleyMatrix_apply_ne _ hne, cayleyPowZero_of_ne_zero hi,
    cayleyPowZero_of_ne_zero hj]
  have hsub : n - j.val = (n - i.val) + (i.val - j.val) := by
    have : i.val ≤ n := Nat.le_of_lt i.isLt
    have : j.val ≤ n := Nat.le_of_lt j.isLt
    omega
  rw [hsub, pow_add]
  have hden : ε ^ (n - i.val) ≠ 0 := pow_ne_zero _ hε
  field_simp [hden]

lemma tendsto_coe_pow_nhdsWithin_zero {k : ℕ} (hk : 1 ≤ k) :
    Filter.Tendsto (fun ε : ℝ => (ε : ℂ) ^ k)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hcont : Continuous fun ε : ℝ => (ε : ℂ) ^ k :=
    Complex.continuous_ofReal.pow k
  have h0 : Filter.Tendsto (fun ε : ℝ => (ε : ℂ) ^ k)
      (nhds 0) (nhds (((0 : ℝ) : ℂ) ^ k)) :=
    hcont.tendsto 0
  have hz : ((0 : ℝ) : ℂ) ^ k = 0 := by
    rw [Complex.ofReal_zero, zero_pow (Nat.pos_iff_ne_zero.mp hk)]
  rw [hz] at h0
  exact h0.mono_left nhdsWithin_le_nhds

lemma tendsto_one_add_div_one_sub_pow {k : ℕ} (hk : 1 ≤ k) :
    Filter.Tendsto
      (fun ε : ℝ => (1 + (ε : ℂ) ^ k) / (1 - (ε : ℂ) ^ k))
      (nhdsWithin 0 (Set.Ioo 0 1)) (nhds 1) := by
  have hpow :
      Filter.Tendsto (fun ε : ℝ => (ε : ℂ) ^ k)
        (nhdsWithin 0 (Set.Ioo 0 1)) (nhds 0) :=
    (tendsto_coe_pow_nhdsWithin_zero hk).mono_left
      (nhdsWithin_mono _ Set.Ioo_subset_Ioi_self)
  have hnum : Filter.Tendsto (fun ε : ℝ => (1 : ℂ) + (ε : ℂ) ^ k)
      (nhdsWithin 0 (Set.Ioo 0 1)) (nhds (1 + 0)) :=
    tendsto_const_nhds.add hpow
  have hden : Filter.Tendsto (fun ε : ℝ => (1 : ℂ) - (ε : ℂ) ^ k)
      (nhdsWithin 0 (Set.Ioo 0 1)) (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hpow
  have hden0 : (1 : ℂ) - 0 ≠ 0 := by simp
  have hdiv := hnum.div hden hden0
  have heq : (1 + 0 : ℂ) / (1 - 0) = 1 := by simp
  rw [heq] at hdiv
  exact hdiv

lemma tendsto_pow_add_one_div_pow_sub_one {k : ℕ} (hk : 1 ≤ k) :
    Filter.Tendsto
      (fun ε : ℝ => ((ε : ℂ) ^ k + 1) / ((ε : ℂ) ^ k - 1))
      (nhdsWithin 0 (Set.Ioo 0 1)) (nhds (-1)) := by
  have hpow :
      Filter.Tendsto (fun ε : ℝ => (ε : ℂ) ^ k)
        (nhdsWithin 0 (Set.Ioo 0 1)) (nhds 0) :=
    (tendsto_coe_pow_nhdsWithin_zero hk).mono_left
      (nhdsWithin_mono _ Set.Ioo_subset_Ioi_self)
  have hnum : Filter.Tendsto (fun ε : ℝ => (ε : ℂ) ^ k + 1)
      (nhdsWithin 0 (Set.Ioo 0 1)) (nhds (0 + 1)) :=
    hpow.add tendsto_const_nhds
  have hden : Filter.Tendsto (fun ε : ℝ => (ε : ℂ) ^ k - 1)
      (nhdsWithin 0 (Set.Ioo 0 1)) (nhds (0 - 1)) :=
    hpow.sub tendsto_const_nhds
  have hden0 : (0 : ℂ) - 1 ≠ 0 := by simp
  have hdiv := hnum.div hden hden0
  have heq : (0 + 1 : ℂ) / (0 - 1) = -1 := by simp
  rw [heq] at hdiv
  exact hdiv

lemma ofReal_mem_Ioo_ne_zero {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    (ε : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr hε.1.ne'

lemma tendsto_cayleyMatrix_powZero {n : ℕ} [NeZero n] (i j : Fin n) :
    Filter.Tendsto (fun ε : ℝ => cayleyMatrix (cayleyPowZero n (ε : ℂ)) i j)
      (nhdsWithin 0 (Set.Ioo 0 1)) (nhds ((signMatrixOf n)ᵀ i j)) := by
  change Filter.Tendsto (fun ε : ℝ => cayleyMatrix (cayleyPowZero n (ε : ℂ)) i j)
      (nhdsWithin 0 (Set.Ioo 0 1)) (nhds (signMatrixOf n j i))
  by_cases hij : i = j
  · subst hij
    have hfun : (fun ε : ℝ => cayleyMatrix (cayleyPowZero n (ε : ℂ)) i i) =
        fun _ => (1 : ℂ) := by
      funext ε
      exact cayleyMatrix_apply_eq _ i
    have hsign : signMatrixOf n i i = 1 := by
      simp [signMatrixOf]
    rw [hfun, hsign]
    exact tendsto_const_nhds
  · by_cases hj0 : j.val = 0
    · have hj : j = 0 := Fin.eq_of_val_eq (by rw [hj0, Fin.val_zero])
      have hi : i ≠ 0 := fun hi => hij (hi.trans hj.symm)
      have hsign : signMatrixOf n j i = -1 := by
        rw [signMatrixOf, hj]
        have : ¬ i.val ≤ 0 :=
          not_le.mpr (Nat.pos_of_ne_zero (Fin.val_ne_of_ne hi))
        simp [this]
      have hf :
          Filter.Tendsto (fun _ : ℝ => (-1 : ℂ))
            (nhdsWithin 0 (Set.Ioo 0 1)) (nhds (-1)) :=
        tendsto_const_nhds
      subst hj
      rw [hsign]
      refine tendsto_nhdsWithin_congr ?_ hf
      intro ε hε
      exact (cayleyMatrix_powZero_col_zero hi (ofReal_mem_Ioo_ne_zero hε)).symm
    · by_cases hi0 : i.val = 0
      · have hi : i = 0 := Fin.eq_of_val_eq (by rw [hi0, Fin.val_zero])
        have hj : j ≠ 0 := fun hj => hij (hi.trans hj.symm)
        have hsign : signMatrixOf n j i = 1 := by
          rw [signMatrixOf, hi]
          simp
        have hf :
            Filter.Tendsto (fun _ : ℝ => (1 : ℂ))
              (nhdsWithin 0 (Set.Ioo 0 1)) (nhds 1) :=
          tendsto_const_nhds
        subst hi
        rw [hsign]
        refine tendsto_nhdsWithin_congr ?_ hf
        intro ε hε
        exact (cayleyMatrix_powZero_row_zero hj (ofReal_mem_Ioo_ne_zero hε)).symm
      · rcases lt_trichotomy i.val j.val with hlt | hval | hgt
        · have hk : 1 ≤ j.val - i.val := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hlt)
          have hsign : signMatrixOf n j i = 1 := by
            rw [signMatrixOf, if_pos (Nat.le_of_lt hlt)]
          rw [hsign]
          refine tendsto_nhdsWithin_congr ?_ (tendsto_one_add_div_one_sub_pow hk)
          intro ε hε
          exact (cayleyMatrix_powZero_of_val_lt hi0 hj0 hlt
            (ofReal_mem_Ioo_ne_zero hε)).symm
        · exact (hij (Fin.eq_of_val_eq hval)).elim
        · have hk : 1 ≤ i.val - j.val := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hgt)
          have hsign : signMatrixOf n j i = -1 := by
            rw [signMatrixOf, if_neg (not_le.mpr hgt)]
          rw [hsign]
          refine tendsto_nhdsWithin_congr ?_ (tendsto_pow_add_one_div_pow_sub_one hk)
          intro ε hε
          exact (cayleyMatrix_powZero_of_val_gt hi0 hj0 hgt
            (ofReal_mem_Ioo_ne_zero hε)).symm

lemma tendsto_permanent {α : Type*} [Fintype α] [DecidableEq α]
    {ι : Type*} {f : ι → Matrix α α ℂ} {M : Matrix α α ℂ} {l : Filter ι}
    (h : ∀ i j, Filter.Tendsto (fun ε => f ε i j) l (nhds (M i j))) :
    Filter.Tendsto (fun ε => (f ε).permanent) l (nhds M.permanent) := by
  simp only [Matrix.permanent]
  exact tendsto_finsetSum _ fun σ _ =>
    tendsto_finsetProd _ fun k _ => h (σ k) k

lemma tendsto_permanent_cayleyMatrix_powZero {n : ℕ} [NeZero n] :
    Filter.Tendsto (fun ε : ℝ => (cayleyMatrix (cayleyPowZero n (ε : ℂ))).permanent)
      (nhdsWithin 0 (Set.Ioo 0 1)) (nhds (signMatrixOf n)ᵀ.permanent) :=
  tendsto_permanent fun i j => tendsto_cayleyMatrix_powZero i j

lemma permanent_signMatrixOf_even {n : ℕ} (hn2 : 2 ≤ n) (he : Even n) :
    (signMatrixOf n).permanent = 0 := by
  have hk : 1 ≤ n / 2 := by omega
  have hsz : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even he
  have hmat :
      signMatrixOf (2 * (n / 2)) =
        (signMatrixOf n).submatrix (finCongr hsz) (finCongr hsz) := by
    ext i j
    simp [signMatrixOf, submatrix_apply]
  have hper := permanent_signMatrix (n := n / 2) hk
  have hs : signMatrix (n / 2) = signMatrixOf (2 * (n / 2)) := rfl
  rw [hs] at hper
  rw [hmat, permanent_submatrix_equiv] at hper
  exact hper

lemma tendsto_cayleySum_powZero {n : ℕ} (hn2 : 2 ≤ n) (he : Even n) :
    Filter.Tendsto (fun ε : ℝ => cayleySum (cayleyPowZero n (ε : ℂ)))
      (nhdsWithin 0 (Set.Ioo 0 1)) (nhds 0) := by
  have : NeZero n := ⟨by omega⟩
  have hper := tendsto_permanent_cayleyMatrix_powZero (n := n)
  have h0 : (signMatrixOf n)ᵀ.permanent = 0 := by
    rw [permanent_transpose]
    exact permanent_signMatrixOf_even hn2 he
  rw [h0] at hper
  exact hper.congr fun ε =>
    permanent_cayleyMatrix_eq_cayleySum (cayleyPowZero n (ε : ℂ))

lemma isCycle_permCongr_iff {α β : Type*} (e : α ≃ β) {σ : Perm α} :
    (e.permCongr σ).IsCycle ↔ σ.IsCycle := by
  constructor
  · intro h
    have hσ : e.symm.permCongr (e.permCongr σ) = σ := by
      ext x
      simp
    have := isCycle_permCongr e.symm h
    rwa [hσ] at this
  · exact isCycle_permCongr e

open scoped Classical in
lemma evenCycleSumThrough_permCongr {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (p : α) (y : β → ℂ) :
    evenCycleSumThrough p (y ∘ e) = evenCycleSumThrough (e p) y := by
  unfold evenCycleSumThrough
  refine Fintype.sum_equiv e.permCongr
    (fun σ =>
      if σ.IsCycle ∧ p ∈ σ.support ∧ Even σ.support.card then
        cayleyWeight (y ∘ e) σ else 0)
    (fun ρ =>
      if ρ.IsCycle ∧ e p ∈ ρ.support ∧ Even ρ.support.card then
        cayleyWeight y ρ else 0) fun σ => ?_
  rw [cayleyWeight_permCongr]
  have hcy : (e.permCongr σ).IsCycle ↔ σ.IsCycle := isCycle_permCongr_iff e
  have hmem : e p ∈ (e.permCongr σ).support ↔ p ∈ σ.support := by
    simp [support_permCongr]
  have hcard : Even (e.permCongr σ).support.card ↔ Even σ.support.card := by
    simp [support_permCongr]
  refine if_congr ?_ rfl rfl
  exact ⟨fun h => ⟨hcy.mpr h.1, hmem.mpr h.2.1, hcard.mpr h.2.2⟩,
    fun h => ⟨hcy.mp h.1, hmem.mp h.2.1, hcard.mp h.2.2⟩⟩

lemma even_sum_of_even_mem {m : Multiset ℕ} (h : ∀ n ∈ m, Even n) : Even m.sum := by
  induction m using Multiset.induction with
  | empty =>
    simp
  | cons n m ih =>
    rw [Multiset.sum_cons]
    obtain ⟨a, ha⟩ := h n (Multiset.mem_cons_self n m)
    obtain ⟨b, hb⟩ := ih fun k hk => h k (Multiset.mem_cons_of_mem hk)
    exact ⟨a + b, by omega⟩

lemma even_card_support_of_oddLongPoints_empty {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} (h : ¬ (oddLongPoints σ).Nonempty) :
    Even σ.support.card := by
  rw [← Equiv.Perm.sum_cycleType]
  refine even_sum_of_even_mem fun m hm => ?_
  obtain ⟨c, hc, rfl⟩ : ∃ c ∈ σ.cycleFactorsFinset, c.support.card = m := by
    simp only [Equiv.Perm.cycleType_def, Multiset.mem_map, Function.comp_apply] at hm
    obtain ⟨c, hc, rfl⟩ := hm
    exact ⟨c, Finset.mem_def.mp hc, rfl⟩
  have : ¬ Odd c.support.card := fun hodd =>
    h ((oddLongPoints_nonempty_iff (σ := σ)).mpr ⟨c, hc, hodd⟩)
  exact Nat.not_odd_iff_even.mp this

noncomputable def equivFinZero {α : Type*} [Fintype α] [NeZero (Fintype.card α)] (p : α) :
    α ≃ Fin (Fintype.card α) :=
  (Fintype.equivFin α).trans (Equiv.swap (Fintype.equivFin α p) 0)

lemma equivFinZero_apply {α : Type*} [Fintype α] [NeZero (Fintype.card α)] (p : α) :
    equivFinZero p p = 0 := by
  change Equiv.swap (Fintype.equivFin α p) 0 (Fintype.equivFin α p) = 0
  simp

lemma cayleySum_comp_equivFinZero {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    [NeZero (Fintype.card α)] (x : α → ℂ) (p : α) :
    cayleySum x = cayleySum (x ∘ (equivFinZero p).symm) := by
  have h := cayleySum_permCongr (equivFinZero p) (x ∘ (equivFinZero p).symm)
  have hx : (x ∘ (equivFinZero p).symm) ∘ equivFinZero p = x := by
    funext a
    simp
  rw [hx] at h
  exact h

lemma evenCycleSumThrough_comp_equivFinZero {α : Type*} [Fintype α] [DecidableEq α]
    [NeZero (Fintype.card α)] (x : α → ℂ) (p : α) :
    evenCycleSumThrough p x =
      evenCycleSumThrough (0 : Fin (Fintype.card α)) (x ∘ (equivFinZero p).symm) := by
  have h := evenCycleSumThrough_permCongr (equivFinZero p) p (x ∘ (equivFinZero p).symm)
  have hx : (x ∘ (equivFinZero p).symm) ∘ equivFinZero p = x := by
    funext a
    simp
  rw [hx, equivFinZero_apply] at h
  exact h

lemma injective_comp_equivFinZero {α : Type*} [Fintype α] [NeZero (Fintype.card α)]
    {x : α → ℂ} (hx : Function.Injective x) (p : α) :
    Function.Injective (x ∘ (equivFinZero p).symm) :=
  hx.comp (equivFinZero p).symm.injective

lemma equivFinZero_symm_zero {α : Type*} [Fintype α] [NeZero (Fintype.card α)] (p : α) :
    (equivFinZero p).symm 0 = p :=
  (Equiv.symm_apply_eq (equivFinZero p)).mpr (equivFinZero_apply p).symm

def finZero {n : ℕ} (hn2 : 2 ≤ n) : Fin n :=
  ⟨0, Nat.zero_lt_of_lt (Nat.succ_le_iff.mp hn2)⟩

lemma finZero_val {n : ℕ} (hn2 : 2 ≤ n) : (finZero hn2).val = 0 := rfl

lemma finZero_eq_zero {n : ℕ} [NeZero n] (hn2 : 2 ≤ n) : finZero hn2 = 0 :=
  Fin.eq_of_val_eq (by simp [finZero])

open scoped Classical in
lemma cayleySum_eq_zero_fin :
    ∀ (n : ℕ) (hn2 : 2 ≤ n), Even n →
      ∀ (x : Fin n → ℂ), Function.Injective x → x (finZero hn2) = 0 →
        cayleySum x = 1 + evenCycleSumThrough (finZero hn2) x ∧
          cayleySum x = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn2 heven x hx hx0
    have : NeZero n := ⟨by omega⟩
    rw [finZero_eq_zero hn2] at hx0 ⊢
    by_cases h2 : n = 2
    · subst h2
      have hcard : Fintype.card (Fin 2) = 2 := Fintype.card_fin 2
      have hsum := cayleySum_eq_one_add_even_cycles_of_card_two (0 : Fin 2) x hcard
      have hx1 : x 1 ≠ 0 := fun h1 =>
        Fin.zero_ne_one (hx (hx0.trans h1.symm))
      exact ⟨hsum, cayleySum_fin_two_of_zero hx0 hx1⟩
    · have hcomp : ∀ (y : Fin n → ℂ), Function.Injective y → y 0 = 0 →
          (∑ σ : Perm (Fin n),
              if σ * (σ.cycleOf 0)⁻¹ = 1 then (0 : ℂ)
              else if (oddLongPoints σ).Nonempty then 0 else cayleyWeight y σ) = 0 := by
        intro y hy hy0
        rw [cayleySum_complementary_eq_inner (0 : Fin n) y]
        refine Fintype.sum_eq_zero _ fun τ => ?_
        by_cases hpτ : τ 0 = 0
        · rw [dif_pos hpτ]
          by_cases hτ1 : τ = 1
          · simp [hτ1]
          · rw [if_neg hτ1]
            by_cases hodd : (oddLongPoints τ).Nonempty
            · simp [hodd]
            · rw [if_neg hodd]
              let p0 : {a // a ∈ τ.supportᶜ} :=
                ⟨0, mem_support_compl_of_fixes hpτ⟩
              suffices hinter :
                  1 + evenCycleSumThrough p0 (fun a => y a.1) = 0 by
                rw [hinter, mul_zero]
              let β := {a // a ∈ τ.supportᶜ}
              let k := Fintype.card β
              have hkcoe : k = τ.supportᶜ.card := Fintype.card_coe _
              have hsup_even : Even τ.support.card :=
                even_card_support_of_oddLongPoints_empty hodd
              have hk_even : Even k := by
                rw [hkcoe, card_compl, Fintype.card_fin]
                obtain ⟨a, ha⟩ := heven
                obtain ⟨b, hb⟩ := hsup_even
                refine ⟨a - b, ?_⟩
                omega
              have hk_ge : 2 ≤ k := by
                have hpos : 1 ≤ τ.supportᶜ.card :=
                  Finset.card_pos.mpr ⟨0, mem_support_compl_of_fixes hpτ⟩
                have hk1 : k ≠ 1 := by
                  intro hk1
                  have : Odd k := ⟨0, by simp [hk1]⟩
                  exact Nat.not_odd_iff_even.mpr hk_even this
                omega
              have hk_lt : k < n := by
                rw [hkcoe, card_compl, Fintype.card_fin]
                have hne : τ.support.Nonempty := by
                  rw [Finset.nonempty_iff_ne_empty]
                  intro hempty
                  exact hτ1 (Equiv.Perm.support_eq_empty_iff.mp hempty)
                have hpos : 0 < τ.support.card := Finset.card_pos.mpr hne
                have hle : τ.support.card ≤ n := by
                  simpa [Fintype.card_fin] using card_le_univ τ.support
                omega
              have : NeZero k := ⟨by omega⟩
              have htr := evenCycleSumThrough_comp_equivFinZero
                (fun a : β => y a.1) p0
              rw [htr]
              let z : Fin k → ℂ :=
                (fun a : β => y a.1) ∘ (equivFinZero p0).symm
              have hz0' : z 0 = 0 := by
                change y ((equivFinZero p0).symm 0).1 = 0
                rw [equivFinZero_symm_zero]
                exact hy0
              have hz0 : z (finZero hk_ge) = 0 := by
                rwa [finZero_eq_zero hk_ge]
              have hzinj : Function.Injective z := by
                intro i j hij
                have hval : ((equivFinZero p0).symm i).1 =
                    ((equivFinZero p0).symm j).1 := hy hij
                exact (equivFinZero p0).symm.injective (Subtype.ext hval)
              have hih := ih k hk_lt hk_ge hk_even z hzinj hz0
              have : 1 + evenCycleSumThrough (0 : Fin k) z = 0 := by
                rw [finZero_eq_zero hk_ge] at hih
                rw [← hih.1]
                exact hih.2
              simpa [z] using this
        · rw [dif_neg hpτ]
      have h1e : cayleySum x = 1 + evenCycleSumThrough (0 : Fin n) x := by
        rw [cayleySum_eq_one_add_even_cycles_add_complementary (0 : Fin n) x, hcomp x hx hx0,
          add_zero]
      refine ⟨h1e, ?_⟩
      have hbin : evenCycleSumThrough (0 : Fin n) x =
          ∑ t ∈ Icc (1 : ℕ) (n / 2),
            ((n - 1).choose (2 * t - 1) : ℂ) * cayleyHamConst t := by
        have h := evenCycleSumThrough_eq_binom x hx (0 : Fin n) hx0
        simpa [Fintype.card_fin] using h
      have hC : cayleySum x =
          1 + ∑ t ∈ Icc (1 : ℕ) (n / 2),
            ((n - 1).choose (2 * t - 1) : ℂ) * cayleyHamConst t := by
        rw [h1e, hbin]
      have hgeom : ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
          cayleySum (cayleyPowZero n (ε : ℂ)) =
            1 + ∑ t ∈ Icc (1 : ℕ) (n / 2),
              ((n - 1).choose (2 * t - 1) : ℂ) * cayleyHamConst t := by
        intro ε hε
        have hyinj := injective_cayleyPowZero (n := n) hε.1 hε.2
        have hy0 : cayleyPowZero n (ε : ℂ) 0 = 0 := cayleyPowZero_zero _
        have h1e' : cayleySum (cayleyPowZero n (ε : ℂ)) =
            1 + evenCycleSumThrough (0 : Fin n) (cayleyPowZero n (ε : ℂ)) := by
          rw [cayleySum_eq_one_add_even_cycles_add_complementary (0 : Fin n)
              (cayleyPowZero n (ε : ℂ)),
            hcomp _ hyinj hy0, add_zero]
        have hbin' := evenCycleSumThrough_eq_binom
          (cayleyPowZero n (ε : ℂ)) hyinj (0 : Fin n) hy0
        rw [h1e']
        apply congrArg (fun t : ℂ => 1 + t)
        simpa [Fintype.card_fin] using hbin'
      have hlim0 := tendsto_cayleySum_powZero hn2 heven
      have hCval :
          (1 + ∑ t ∈ Icc (1 : ℕ) (n / 2),
              ((n - 1).choose (2 * t - 1) : ℂ) * cayleyHamConst t) = 0 := by
        have hlimC :
            Filter.Tendsto (fun ε : ℝ => cayleySum (cayleyPowZero n (ε : ℂ)))
              (nhdsWithin 0 (Set.Ioo 0 1))
              (nhds (1 + ∑ t ∈ Icc (1 : ℕ) (n / 2),
                ((n - 1).choose (2 * t - 1) : ℂ) * cayleyHamConst t)) :=
          tendsto_nhdsWithin_congr (fun ε hε => (hgeom ε hε).symm) tendsto_const_nhds
        have : Filter.NeBot (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) :=
          left_nhdsWithin_Ioo_neBot (by norm_num : (0 : ℝ) < 1)
        exact tendsto_nhds_unique hlimC hlim0
      rw [hC, hCval]

lemma identity_three_nine {n : ℕ} (hn2 : 2 ≤ n) (he : Even n) :
    1 + ∑ k ∈ Icc (1 : ℕ) (n / 2),
      ((n - 1).choose (2 * k - 1) : ℂ) * cayleyHamConst k = 0 := by
  have : NeZero n := ⟨by omega⟩
  have hx := injective_cayleyPowZero (n := n)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hx0 : cayleyPowZero n ((1 / 2 : ℝ) : ℂ) (finZero hn2) = 0 := by
    rw [finZero_eq_zero hn2, cayleyPowZero_zero]
  have h := cayleySum_eq_zero_fin n hn2 he _ hx hx0
  have hbin : evenCycleSumThrough (finZero hn2) (cayleyPowZero n ((1 / 2 : ℝ) : ℂ)) =
      ∑ k ∈ Icc (1 : ℕ) (n / 2),
        ((n - 1).choose (2 * k - 1) : ℂ) * cayleyHamConst k := by
    rw [finZero_eq_zero hn2]
    have hb := evenCycleSumThrough_eq_binom
      (cayleyPowZero n ((1 / 2 : ℝ) : ℂ)) hx (0 : Fin n)
      (by rw [← finZero_eq_zero hn2]; exact hx0)
    simpa [Fintype.card_fin] using hb
  have : cayleySum (cayleyPowZero n ((1 / 2 : ℝ) : ℂ)) =
      1 + ∑ k ∈ Icc (1 : ℕ) (n / 2),
        ((n - 1).choose (2 * k - 1) : ℂ) * cayleyHamConst k := by
    rw [h.1, hbin]
  rw [← this]
  exact h.2

lemma cayleySum_eq_zero_of_zero {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (x : α → ℂ) (hx : Function.Injective x) (p : α) (hxp : x p = 0)
    (heven : Even (Fintype.card α)) (h2 : 2 ≤ Fintype.card α) :
    cayleySum x = 0 := by
  have : NeZero (Fintype.card α) := ⟨by omega⟩
  have hz : (x ∘ (equivFinZero p).symm) (finZero h2) = 0 := by
    rw [finZero_eq_zero h2, Function.comp_apply, equivFinZero_symm_zero]
    exact hxp
  have h := cayleySum_eq_zero_fin (Fintype.card α) h2 heven
    (x ∘ (equivFinZero p).symm) (injective_comp_equivFinZero hx p) hz
  rw [cayleySum_comp_equivFinZero x p]
  exact h.2

/-- Paper (3.9): the `k ≥ 2` Hamiltonian sum is `n-2`. -/
lemma identity_three_nine_tail {n : ℕ} (hn2 : 2 ≤ n) (he : Even n) :
    (∑ k ∈ Icc (2 : ℕ) (n / 2),
      ((n - 1).choose (2 * k - 1) : ℂ) * cayleyHamConst k) =
      (n - 2 : ℕ) := by
  have hfull := identity_three_nine hn2 he
  have hsplit : Icc (1 : ℕ) (n / 2) = insert 1 (Icc (2 : ℕ) (n / 2)) := by
    ext k
    simp [mem_Icc]
    omega
  have h1 : 1 ∉ Icc (2 : ℕ) (n / 2) := by simp [mem_Icc]
  have hcho : ((n - 1).choose (2 * 1 - 1) : ℂ) * cayleyHamConst 1 =
      -((n - 1 : ℕ) : ℂ) := by
    rw [cayleyHamConst_one]
    simp
  have hrew :
      (1 : ℂ) + (-((n - 1 : ℕ) : ℂ) +
        ∑ k ∈ Icc (2 : ℕ) (n / 2),
          ((n - 1).choose (2 * k - 1) : ℂ) * cayleyHamConst k) =
        (∑ k ∈ Icc (2 : ℕ) (n / 2),
          ((n - 1).choose (2 * k - 1) : ℂ) * cayleyHamConst k) -
          (n - 2 : ℕ) := by
    have hn12 : (n - 1 : ℕ) = (n - 2 : ℕ) + 1 := by omega
    simp [hn12]
    ring
  rw [hsplit, sum_insert h1, hcho] at hfull
  rw [hrew] at hfull
  exact sub_eq_zero.mp hfull

open scoped Classical in
lemma sum_cayleyWeight_long_even_cycles_through_eq_card_sub_two
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) (hx : Function.Injective x) (p : α)
    (heven : Even (Fintype.card α)) (h2 : 2 ≤ Fintype.card α) :
    (∑ σ : Perm α,
        if σ.IsCycle ∧ p ∈ σ.support ∧ 4 ≤ σ.support.card ∧ Even σ.support.card then
          cayleyWeight x σ else 0) =
      (Fintype.card α - 2 : ℕ) := by
  rw [sum_cayleyWeight_long_even_cycles_through x hx p]
  simpa using identity_three_nine_tail (n := Fintype.card α) h2 heven

open scoped Classical in
lemma sum_long_even_subtype {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) (hx : Function.Injective x) {s : Finset α} {p : α} (hp : p ∈ s)
    (he : Even s.card) (h2 : 2 ≤ s.card) :
    (∑ u : Perm {a // a ∈ s},
        if u.IsCycle ∧ ⟨p, hp⟩ ∈ u.support ∧ 4 ≤ u.support.card ∧ Even u.support.card then
          cayleyWeight (fun a => x a.1) u else 0) =
      (s.card - 2 : ℕ) := by
  have hx' : Function.Injective (fun a : {a // a ∈ s} => x a.1) :=
    hx.comp Subtype.val_injective
  have hcard : Fintype.card {a // a ∈ s} = s.card := Fintype.card_coe s
  have he' : Even (Fintype.card {a // a ∈ s}) := by rwa [hcard]
  have h2' : 2 ≤ Fintype.card {a // a ∈ s} := by rwa [hcard]
  have h := sum_cayleyWeight_long_even_cycles_through_eq_card_sub_two
    (fun a : {a // a ∈ s} => x a.1) hx' ⟨p, hp⟩ he' h2'
  simpa [hcard] using h

lemma card_support_ofSubtype {α : Type*} [Fintype α] [DecidableEq α] {s : Finset α}
    (u : Perm {a // a ∈ s}) :
    (Equiv.Perm.ofSubtype u).support.card = u.support.card :=
  Finset.card_eq_of_equiv
    { toFun := fun x =>
        ⟨⟨x.1, support_ofSubtype_subset u x.2⟩, by
          have hne : Equiv.Perm.ofSubtype u x.1 ≠ x.1 := Equiv.Perm.mem_support.mp x.2
          have hx' : x.1 ∈ s := support_ofSubtype_subset u x.2
          rw [Equiv.Perm.ofSubtype_apply_of_mem u hx'] at hne
          exact Equiv.Perm.mem_support.mpr fun hf => hne (congrArg Subtype.val hf)⟩
      invFun := fun q =>
        ⟨q.1.1, by
          have hne : u q.1 ≠ q.1 := Equiv.Perm.mem_support.mp q.2
          refine Equiv.Perm.mem_support.mpr ?_
          rw [Equiv.Perm.ofSubtype_apply_coe]
          exact fun hx => hne (Subtype.ext hx)⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext (Subtype.ext rfl) }

lemma cycleOf_ofSubtype_mul_eq {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} (u : Perm {a // a ∈ s}) {τ : Perm α} {p : α}
    (hp : p ∈ s) (hτ : τ.support ⊆ sᶜ) (hc : u.cycleOf ⟨p, hp⟩ = u) :
    (Equiv.Perm.ofSubtype u * τ).cycleOf p = Equiv.Perm.ofSubtype u := by
  have hd := disjoint_ofSubtype_support_compl u hτ
  have hfix : τ p = p := not_mem_support_of_mem_of_subset_compl hτ hp
  rw [cycleOf_mul_of_fixes hd hfix, cycleOf_ofSubtype_eq_of_cycleOf_eq u hp hc]

lemma support_subset_compl_of_fixed_pair {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} {σ : Perm α} (hp : σ p = p) (hq : σ q = q) :
    σ.support ⊆ ({p, q} : Finset α)ᶜ := by
  intro x hx
  simp only [mem_compl, mem_insert, mem_singleton, not_or]
  refine ⟨?_, ?_⟩
  · intro hxp
    subst hxp
    exact Equiv.Perm.mem_support.mp hx hp
  · intro hxq
    subst hxq
    exact Equiv.Perm.mem_support.mp hx hq

noncomputable def equiv_remainder_of_fixed_pair {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (_hpq : p ≠ q) :
    Perm {a // a ∈ ({p, q} : Finset α)ᶜ} ≃ {σ : Perm α // σ p = p ∧ σ q = q} :=
  Equiv.ofBijective
    (fun u => ⟨Equiv.Perm.ofSubtype u, ofSubtype_fixes_pair u⟩)
    ⟨fun u v h => Equiv.Perm.ofSubtype_injective (congrArg Subtype.val h),
      fun σ => by
        have hsub : σ.1.support ⊆ ({p, q} : Finset α)ᶜ :=
          support_subset_compl_of_fixed_pair σ.2.1 σ.2.2
        refine ⟨σ.1.subtypePerm fun x => (mem_of_support_subset hsub x).symm, ?_⟩
        exact Subtype.ext (ofSubtype_subtypePerm_of_support_subset hsub)⟩

lemma sum_fiber_fixed_pair {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (hpq : p ≠ q) (f : Perm α → ℂ) :
    (∑ σ : Perm α, if σ p = p ∧ σ q = q then f σ else 0) =
      ∑ u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ},
        f (Equiv.Perm.ofSubtype u) := by
  have hsub :
      (∑ σ ∈ univ.filter (fun σ : Perm α => σ p = p ∧ σ q = q), f σ) =
        ∑ σ : {σ : Perm α // σ p = p ∧ σ q = q}, f σ.1 :=
    sum_subtype (univ.filter (fun σ : Perm α => σ p = p ∧ σ q = q))
      (fun σ => by simp) f
  calc (∑ σ : Perm α, if σ p = p ∧ σ q = q then f σ else 0)
      = ∑ σ ∈ univ.filter (fun σ : Perm α => σ p = p ∧ σ q = q), f σ :=
        (sum_filter (fun σ : Perm α => σ p = p ∧ σ q = q) f).symm
    _ = ∑ σ : {σ : Perm α // σ p = p ∧ σ q = q}, f σ.1 := hsub
    _ = ∑ u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ},
          f (equiv_remainder_of_fixed_pair hpq u).1 :=
        (Equiv.sum_comp (equiv_remainder_of_fixed_pair hpq) (fun σ => f σ.1)).symm
    _ = ∑ u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ}, f (Equiv.Perm.ofSubtype u) :=
        rfl

lemma cayleySumOn_eq_sum_fixed_pair {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] {p q : α} (hpq : p ≠ q) (x : α → ℂ) :
    cayleySumOn ({p, q} : Finset α)ᶜ x =
      ∑ σ : Perm α,
        if σ p = p ∧ σ q = q then
          (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
        else 0 := by
  unfold cayleySumOn cayleySum
  rw [sum_fiber_fixed_pair hpq
    (fun σ => if (oddLongPoints σ).Nonempty then 0 else cayleyWeight x σ)]
  refine Fintype.sum_congr _ _ fun u => (cayleySum_ofSubtype x u).symm

lemma filter_fixed_erase {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) (p : α) :
    univ.filter (fun q : α => q ≠ p ∧ σ q = q) = σ.supportᶜ.erase p := by
  ext q
  constructor
  · intro hq
    simp only [mem_filter, mem_univ, true_and] at hq
    exact mem_erase.mpr ⟨hq.1, mem_compl.mpr (Equiv.Perm.notMem_support.mpr hq.2)⟩
  · intro hq
    obtain ⟨hqp, hqfix⟩ := mem_erase.mp hq
    exact mem_filter.mpr ⟨mem_univ q, hqp, Equiv.Perm.notMem_support.mp (mem_compl.mp hqfix)⟩

lemma sum_boole_fixed_erase {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} {p : α} (hp : σ p = p) :
    (∑ q : α, if q ≠ p ∧ σ q = q then (1 : ℂ) else 0) =
      (σ.supportᶜ.card : ℂ) - 1 := by
  have hp' : p ∈ σ.supportᶜ := mem_support_compl_of_fixes hp
  have hpos : 1 ≤ σ.supportᶜ.card := Finset.card_pos.mpr ⟨p, hp'⟩
  have hsum :
      (∑ q : α, if q ≠ p ∧ σ q = q then (1 : ℂ) else 0) =
        ∑ q ∈ univ.filter (fun q : α => q ≠ p ∧ σ q = q), (1 : ℂ) :=
    (sum_filter (fun q : α => q ≠ p ∧ σ q = q) (fun _ => (1 : ℂ))).symm
  rw [hsum, sum_const, nsmul_eq_mul, mul_one, filter_fixed_erase σ p,
    card_erase_of_mem hp']
  rw [Nat.cast_sub hpos, Nat.cast_one]

open scoped Classical in
lemma sum_cayleySumOn_omit_pair {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] (p : α) (x : α → ℂ) :
    (∑ q : α, if q = p then 0 else cayleySumOn ({p, q} : Finset α)ᶜ x) =
      ∑ σ : Perm α,
        if σ p = p then
          (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ) *
            ((σ.supportᶜ.card : ℂ) - 1)
        else 0 := by
  let g : Perm α → ℂ := fun σ =>
    if (oddLongPoints σ).Nonempty then 0 else cayleyWeight x σ
  have hsplit : ∀ q : α,
      (if q = p then (0 : ℂ) else cayleySumOn ({p, q} : Finset α)ᶜ x) =
        ∑ σ : Perm α, if q ≠ p ∧ σ p = p ∧ σ q = q then g σ else 0 := by
    intro q
    by_cases hq : q = p
    · simp [hq]
    · have hpq : p ≠ q := fun h => hq h.symm
      rw [if_neg hq, cayleySumOn_eq_sum_fixed_pair hpq x]
      refine Fintype.sum_congr _ _ fun σ => ?_
      by_cases hfix : σ p = p ∧ σ q = q
      · simp [hq, hfix, g]
      · simp [hq, hfix]
  rw [Fintype.sum_congr _ _ hsplit, sum_comm]
  refine Fintype.sum_congr _ _ fun σ => ?_
  by_cases hpσ : σ p = p
  · have hinner :
        (∑ q : α, if q ≠ p ∧ σ p = p ∧ σ q = q then g σ else 0) =
          g σ * ∑ q : α, if q ≠ p ∧ σ q = q then (1 : ℂ) else 0 := by
      rw [mul_sum]
      refine Fintype.sum_congr _ _ fun q => ?_
      by_cases hcond : q ≠ p ∧ σ q = q
      · have hcond' : q ≠ p ∧ σ p = p ∧ σ q = q := ⟨hcond.1, hpσ, hcond.2⟩
        rw [if_pos hcond', if_pos hcond, mul_one]
      · have hcond' : ¬ (q ≠ p ∧ σ p = p ∧ σ q = q) := fun h =>
          hcond ⟨h.1, h.2.2⟩
        rw [if_neg hcond', if_neg hcond, mul_zero]
    rw [hinner, sum_boole_fixed_erase hpσ]
    simp only [hpσ, ↓reduceIte]
    rfl
  · have hnone : ∀ q : α, ¬ (q ≠ p ∧ σ p = p ∧ σ q = q) := fun q h => hpσ h.2.1
    refine (sum_eq_zero fun q _ => if_neg (hnone q)).trans ?_
    simp only [hpσ, ↓reduceIte]

lemma cayleySum_sigma1_eq_omit_sub_extra {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] (p : α) (x : α → ℂ) :
    cayleySumOn ({p} : Finset α)ᶜ x =
      (∑ q : α, if q = p then 0 else cayleySumOn ({p, q} : Finset α)ᶜ x) -
        ∑ τ : Perm α,
          if τ p = p then
            (if (oddLongPoints τ).Nonempty then (0 : ℂ) else cayleyWeight x τ) *
              ((τ.supportᶜ.card : ℂ) - 2)
          else 0 := by
  rw [sum_cayleySumOn_omit_pair p x, ← cayleySum_sigma1 p x]
  rw [← sum_sub_distrib]
  refine Fintype.sum_congr _ _ fun σ => ?_
  by_cases hpσ : σ p = p
  · simp only [hpσ, ↓reduceIte]
    ring
  · simp only [hpσ, ↓reduceIte]
    ring

open scoped Classical in
lemma cayleySum_sigma3_inner_term {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} (x : α → ℂ) (u : Perm {a // a ∈ s}) {τ : Perm α} {p : α}
    (hp : p ∈ s) (hτ : τ.support ⊆ sᶜ) :
    (if u.cycleOf ⟨p, hp⟩ = u then
      (if 4 ≤ ((Equiv.Perm.ofSubtype u * τ).cycleOf p).support.card then
        (if (oddLongPoints (Equiv.Perm.ofSubtype u * τ)).Nonempty then (0 : ℂ)
          else cayleyWeight x (Equiv.Perm.ofSubtype u * τ))
      else 0)
    else 0) =
      (if (oddLongPoints τ).Nonempty then 0 else cayleyWeight x τ) *
        (if u.IsCycle ∧ ⟨p, hp⟩ ∈ u.support ∧ 4 ≤ u.support.card ∧ Even u.support.card then
          cayleyWeight (fun a => x a.1) u else 0) := by
  by_cases hc : u.cycleOf ⟨p, hp⟩ = u
  · have hcy := cycleOf_ofSubtype_mul_eq u hp hτ hc
    have hcard : ((Equiv.Perm.ofSubtype u * τ).cycleOf p).support.card =
        u.support.card := by
      rw [hcy, card_support_ofSubtype]
    have hmul := cayleyWeight_ofSubtype_mul_oddLong x u hτ
    by_cases h4 : 4 ≤ u.support.card
    · have h4' : 4 ≤ ((Equiv.Perm.ofSubtype u * τ).cycleOf p).support.card := by
        rwa [hcard]
      rw [if_pos hc, if_pos h4', hmul]
      by_cases hcyu : u.IsCycle ∧ ⟨p, hp⟩ ∈ u.support ∧ Even u.support.card
      · have hodd_u : ¬ (oddLongPoints u).Nonempty := fun hne =>
          Nat.not_even_iff_odd.mpr ((oddLongPoints_isCycle hcyu.1).mp hne) hcyu.2.2
        have hR : u.IsCycle ∧ ⟨p, hp⟩ ∈ u.support ∧ 4 ≤ u.support.card ∧
            Even u.support.card := ⟨hcyu.1, hcyu.2.1, h4, hcyu.2.2⟩
        rw [if_neg hodd_u, if_pos hR]
      · have hR : ¬ (u.IsCycle ∧ ⟨p, hp⟩ ∈ u.support ∧ 4 ≤ u.support.card ∧
            Even u.support.card) := fun h => hcyu ⟨h.1, h.2.1, h.2.2.2⟩
        have hcases := (cycleOf_eq_self_iff u ⟨p, hp⟩).mp hc
        rcases hcases with h1 | hcy'
        · have : ¬ 4 ≤ u.support.card := by
            subst h1
            simp
          exact (this h4).elim
        · have hneE : ¬ Even u.support.card := fun he =>
            hcyu ⟨hcy'.1, hcy'.2, he⟩
          have hodd : Odd u.support.card := Nat.not_even_iff_odd.mp hneE
          have hne : (oddLongPoints u).Nonempty :=
            (oddLongPoints_isCycle hcy'.1).mpr hodd
          rw [if_pos hne, if_neg hR]
    · have h4' : ¬ 4 ≤ ((Equiv.Perm.ofSubtype u * τ).cycleOf p).support.card := by
        rwa [hcard]
      have hR : ¬ (u.IsCycle ∧ ⟨p, hp⟩ ∈ u.support ∧ 4 ≤ u.support.card ∧
          Even u.support.card) := fun h => h4 h.2.2.1
      rw [if_pos hc, if_neg h4', if_neg hR, mul_zero]
  · have hR : ¬ (u.IsCycle ∧ ⟨p, hp⟩ ∈ u.support ∧ 4 ≤ u.support.card ∧
        Even u.support.card) := fun h =>
      hc ((cycleOf_eq_self_iff u ⟨p, hp⟩).mpr (Or.inr ⟨h.1, h.2.1⟩))
    rw [if_neg hc, if_neg hR, mul_zero]

open scoped Classical in
lemma cayleySum_sigma3_fibre {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (x : α → ℂ) (p : α) (τ : Perm α) (hp : τ p = p) :
    (∑ σ : Perm α,
        if σ * (σ.cycleOf p)⁻¹ = τ then
          (if 4 ≤ (σ.cycleOf p).support.card then
            (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
          else 0)
        else 0) =
      (if (oddLongPoints τ).Nonempty then 0 else cayleyWeight x τ) *
        (∑ u : Perm {a // a ∈ τ.supportᶜ},
          if u.IsCycle ∧ ⟨p, mem_support_compl_of_fixes hp⟩ ∈ u.support ∧
              4 ≤ u.support.card ∧ Even u.support.card then
            cayleyWeight (fun a => x a.1) u else 0) := by
  have hp' : p ∈ τ.supportᶜ := mem_support_compl_of_fixes hp
  have hτs : τ.support ⊆ (τ.supportᶜ)ᶜ := by
    rw [compl_compl]
  let g3 : Perm α → ℂ := fun σ =>
    if 4 ≤ (σ.cycleOf p).support.card then
      (if (oddLongPoints σ).Nonempty then 0 else cayleyWeight x σ)
    else 0
  have hL :
      (∑ σ : Perm α, if σ * (σ.cycleOf p)⁻¹ = τ then g3 σ else 0) =
        ∑ u : {u : Perm {a // a ∈ τ.supportᶜ} // u.cycleOf ⟨p, hp'⟩ = u},
          g3 (Equiv.Perm.ofSubtype u.1 * τ) := by
    calc
      (∑ σ : Perm α, if σ * (σ.cycleOf p)⁻¹ = τ then g3 σ else 0) =
          ∑ σ ∈ univ.filter (fun σ : Perm α => σ * (σ.cycleOf p)⁻¹ = τ), g3 σ := by
        rw [sum_filter]
      _ = ∑ σ : {σ : Perm α // σ * (σ.cycleOf p)⁻¹ = τ}, g3 σ.1 := by
        rw [sum_subtype (p := fun σ : Perm α => σ * (σ.cycleOf p)⁻¹ = τ)
          (univ.filter (fun σ : Perm α => σ * (σ.cycleOf p)⁻¹ = τ))
          (fun σ => by simp) g3]
      _ = ∑ u : {u : Perm {a // a ∈ τ.supportᶜ} // u.cycleOf ⟨p, hp'⟩ = u},
            g3 (Equiv.Perm.ofSubtype u.1 * τ) := by
        rw [← Equiv.sum_comp (remainderFibreEquiv p τ hp) (fun σ => g3 σ.1)]
        rfl
  have hU :
      (∑ u : {u : Perm {a // a ∈ τ.supportᶜ} // u.cycleOf ⟨p, hp'⟩ = u},
          g3 (Equiv.Perm.ofSubtype u.1 * τ)) =
        ∑ u : Perm {a // a ∈ τ.supportᶜ},
          if u.cycleOf ⟨p, hp'⟩ = u then
            g3 (Equiv.Perm.ofSubtype u * τ) else 0 := by
    rw [← sum_subtype
        (p := fun u : Perm {a // a ∈ τ.supportᶜ} => u.cycleOf ⟨p, hp'⟩ = u)
        (univ.filter (fun u : Perm {a // a ∈ τ.supportᶜ} => u.cycleOf ⟨p, hp'⟩ = u))
        (fun u => by simp)
        (fun u => g3 (Equiv.Perm.ofSubtype u * τ)),
      sum_filter]
  have hterm : ∀ u : Perm {a // a ∈ τ.supportᶜ},
      (if u.cycleOf ⟨p, hp'⟩ = u then g3 (Equiv.Perm.ofSubtype u * τ) else 0) =
        (if (oddLongPoints τ).Nonempty then 0 else cayleyWeight x τ) *
          (if u.IsCycle ∧ ⟨p, hp'⟩ ∈ u.support ∧ 4 ≤ u.support.card ∧
              Even u.support.card then
            cayleyWeight (fun a => x a.1) u else 0) :=
    fun u => cayleySum_sigma3_inner_term x u hp' hτs
  rw [hL, hU, Fintype.sum_congr _ _ hterm, ← mul_sum]

lemma cayleySum_sigma3_fibre_of_moves {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] (x : α → ℂ) (p : α) (τ : Perm α) (hp : τ p ≠ p) :
    (∑ σ : Perm α,
        if σ * (σ.cycleOf p)⁻¹ = τ then
          (if 4 ≤ (σ.cycleOf p).support.card then
            (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
          else 0)
        else 0) = 0 := by
  refine Fintype.sum_eq_zero _ fun σ => ?_
  have hne : σ * (σ.cycleOf p)⁻¹ ≠ τ := fun h =>
    hp (h ▸ remainder_fixes_cycle_base σ p)
  simp [hne]

lemma even_card_compl_of_oddLongPoints_empty {α : Type*} [Fintype α] [DecidableEq α]
    {τ : Perm α} (heven : Even (Fintype.card α))
    (h : ¬ (oddLongPoints τ).Nonempty) :
    Even τ.supportᶜ.card := by
  rw [card_compl]
  obtain ⟨a, ha⟩ := heven
  obtain ⟨b, hb⟩ := even_card_support_of_oddLongPoints_empty h
  refine ⟨a - b, ?_⟩
  have hle : τ.support.card ≤ Fintype.card α := card_le_univ _
  omega

open scoped Classical in
lemma cayleySum_sigma3 {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (p : α) (x : α → ℂ) (hx : Function.Injective x)
    (heven : Even (Fintype.card α)) (_h2 : 2 ≤ Fintype.card α) :
    (∑ σ : Perm α,
        if 4 ≤ (σ.cycleOf p).support.card then
          (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
        else 0) =
      ∑ τ : Perm α,
        if τ p = p then
          (if (oddLongPoints τ).Nonempty then 0 else cayleyWeight x τ) *
            ((τ.supportᶜ.card : ℂ) - 2)
        else 0 := by
  have hsplit : ∀ σ : Perm α,
      (if 4 ≤ (σ.cycleOf p).support.card then
        (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
      else 0) =
        ∑ τ : Perm α,
          if σ * (σ.cycleOf p)⁻¹ = τ then
            (if 4 ≤ (σ.cycleOf p).support.card then
              (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
            else 0)
          else 0 := by
    intro σ
    have hsum :
        (∑ τ : Perm α,
            if σ * (σ.cycleOf p)⁻¹ = τ then
              (if 4 ≤ (σ.cycleOf p).support.card then
                (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
              else 0)
            else 0) =
          if σ * (σ.cycleOf p)⁻¹ = σ * (σ.cycleOf p)⁻¹ then
            (if 4 ≤ (σ.cycleOf p).support.card then
              (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
            else 0)
          else 0 :=
      Fintype.sum_eq_single _ (fun τ hτ => if_neg (Ne.symm hτ))
    rw [hsum, if_pos rfl]
  rw [Fintype.sum_congr _ _ hsplit, sum_comm]
  refine Fintype.sum_congr _ _ fun τ => ?_
  by_cases hpτ : τ p = p
  · rw [if_pos hpτ, cayleySum_sigma3_fibre x p τ hpτ]
    by_cases hodd : (oddLongPoints τ).Nonempty
    · simp [hodd]
    · rw [if_neg hodd]
      have hm_even : Even τ.supportᶜ.card :=
        even_card_compl_of_oddLongPoints_empty heven hodd
      have hm_ge : 2 ≤ τ.supportᶜ.card := by
        have hpos : 1 ≤ τ.supportᶜ.card :=
          Finset.card_pos.mpr ⟨p, mem_support_compl_of_fixes hpτ⟩
        have hne1 : τ.supportᶜ.card ≠ 1 := by
          intro hk1
          have : Odd τ.supportᶜ.card := ⟨0, by simp [hk1]⟩
          exact Nat.not_odd_iff_even.mpr hm_even this
        omega
      have hinter := sum_long_even_subtype x hx (mem_support_compl_of_fixes hpτ)
        hm_even hm_ge
      have hcast : ((τ.supportᶜ.card - 2 : ℕ) : ℂ) =
          (τ.supportᶜ.card : ℂ) - 2 :=
        Nat.cast_sub hm_ge
      rw [hinter, hcast]
  · rw [if_neg hpτ, cayleySum_sigma3_fibre_of_moves x p τ hpτ]

/-- She–Sun–Xia (4.8). -/
lemma cayleySum_eq_recurrence {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (p : α) (x : α → ℂ) (hx : Function.Injective x)
    (heven : Even (Fintype.card α)) (h2 : 2 ≤ Fintype.card α) :
    cayleySum x =
      ∑ q : α, if q = p then 0 else
        (1 + cayleyWeight x (Equiv.swap p q)) *
          cayleySumOn ({p, q} : Finset α)ᶜ x := by
  rw [cayleySum_eq_sigma1_add_sigma2_add p x, cayleySum_sigma1_eq_omit_sub_extra p x,
    cayleySum_sigma3 p x hx heven h2]
  have hcancel :
      (∑ q : α, if q = p then 0 else cayleySumOn ({p, q} : Finset α)ᶜ x) -
          (∑ τ : Perm α,
            if τ p = p then
              (if (oddLongPoints τ).Nonempty then (0 : ℂ) else cayleyWeight x τ) *
                ((τ.supportᶜ.card : ℂ) - 2)
            else 0) +
        (∑ q : α, if q = p then 0 else
          cayleyWeight x (Equiv.swap p q) * cayleySumOn ({p, q} : Finset α)ᶜ x) +
        (∑ τ : Perm α,
          if τ p = p then
            (if (oddLongPoints τ).Nonempty then (0 : ℂ) else cayleyWeight x τ) *
              ((τ.supportᶜ.card : ℂ) - 2)
          else 0) =
        (∑ q : α, if q = p then 0 else cayleySumOn ({p, q} : Finset α)ᶜ x) +
          ∑ q : α, if q = p then 0 else
            cayleyWeight x (Equiv.swap p q) * cayleySumOn ({p, q} : Finset α)ᶜ x := by
    ring
  rw [hcancel, ← sum_add_distrib]
  refine Fintype.sum_congr _ _ fun q => ?_
  by_cases hq : q = p
  · simp [hq]
  · simp [hq]
    ring

/-- Pair-inverse weight of a permutation. On a fixed-point-free involution this is
`(-1)^{n}` times the paper matching product `\prod 1/(x_i-x_j)^2`. -/
noncomputable def matchingWeight {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) (σ : Perm α) : ℂ :=
  ∏ a, if σ a = a then (1 : ℂ) else (x a - x (σ a))⁻¹

noncomputable def matchingSum {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) : ℂ :=
  ∑ σ : Perm α,
    if σ.support = univ ∧ σ * σ = 1 then matchingWeight x σ else 0

lemma matchingWeight_one {α : Type*} [Fintype α] [DecidableEq α] (x : α → ℂ) :
    matchingWeight x (1 : Perm α) = 1 := by
  unfold matchingWeight
  refine prod_eq_one fun a _ => ?_
  simp

lemma matchingWeight_eq_prod_support {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) (σ : Perm α) :
    matchingWeight x σ = ∏ i ∈ σ.support, (x i - x (σ i))⁻¹ := by
  unfold matchingWeight
  rw [← union_compl σ.support, prod_union disjoint_compl_right]
  have hfix : ∏ i ∈ σ.supportᶜ,
      (if σ i = i then (1 : ℂ) else (x i - x (σ i))⁻¹) = 1 :=
    prod_eq_one fun i hi => by
      have : σ i = i := Equiv.Perm.notMem_support.mp (mem_compl.mp hi)
      simp [this]
  have hsup : (∏ i ∈ σ.support,
      if σ i = i then (1 : ℂ) else (x i - x (σ i))⁻¹) =
      ∏ i ∈ σ.support, (x i - x (σ i))⁻¹ :=
    prod_congr rfl fun i hi => by
      have : σ i ≠ i := Equiv.Perm.mem_support.mp hi
      simp [this]
  rw [hfix, mul_one, hsup]

lemma matchingWeight_swap {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {a b : α} (h : a ≠ b) :
    matchingWeight x (Equiv.swap a b) =
      (x a - x b)⁻¹ * (x b - x a)⁻¹ := by
  rw [matchingWeight_eq_prod_support, Equiv.Perm.support_swap h,
    prod_insert (by simp [h]), prod_singleton]
  simp [swap_apply_left, swap_apply_right]

lemma matchingWeight_swap_inv_sq {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {a b : α} (h : a ≠ b) (hx : x a ≠ x b) :
    matchingWeight x (Equiv.swap a b) = -((x a - x b) ^ 2)⁻¹ := by
  have hden : x a - x b ≠ 0 := sub_ne_zero.2 hx
  rw [matchingWeight_swap x h]
  have hba : x b - x a = -(x a - x b) := by ring
  rw [hba]
  field_simp [hden]

lemma one_add_cayleyWeight_eq_matching {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {a b : α} (hab : a ≠ b) (hx : x a ≠ x b) :
    1 + cayleyWeight x (Equiv.swap a b) =
      (4 : ℂ) * x a * x b * matchingWeight x (Equiv.swap a b) := by
  rw [one_add_cayleyWeight_swap x hab hx, matchingWeight_swap_inv_sq x hab hx]
  have hden : x a - x b ≠ 0 := sub_ne_zero.2 hx
  field_simp [hden]

lemma matchingWeight_mul_disjoint {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {σ τ : Perm α} (h : Equiv.Perm.Disjoint σ τ) :
    matchingWeight x (σ * τ) = matchingWeight x σ * matchingWeight x τ := by
  rw [matchingWeight_eq_prod_support, matchingWeight_eq_prod_support,
    matchingWeight_eq_prod_support, h.support_mul, prod_union h.disjoint_support]
  refine congr_arg₂ (· * ·) ?_ ?_
  · refine prod_congr rfl fun i hi => ?_
    have hτi : τ i = i := Equiv.Perm.notMem_support.mp (h.mem_imp hi)
    simp [hτi]
  · refine prod_congr rfl fun i hi => ?_
    have hσi : σ (τ i) = τ i := by
      have : τ i ∈ τ.support := (Equiv.Perm.apply_mem_support (f := τ)).2 hi
      exact Equiv.Perm.notMem_support.mp (h.symm.mem_imp this)
    simp [hσi]

lemma matchingWeight_ofSubtype {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} (x : α → ℂ) (u : Perm {a // a ∈ s}) :
    matchingWeight x (Equiv.Perm.ofSubtype u) =
      matchingWeight (fun a : {a // a ∈ s} => x a.1) u := by
  rw [matchingWeight_eq_prod_support, matchingWeight_eq_prod_support]
  refine prod_bij (fun y hy => ⟨y, support_ofSubtype_subset u hy⟩) ?_ ?_ ?_ ?_
  · intro y hy
    have hne : Equiv.Perm.ofSubtype u y ≠ y := Equiv.Perm.mem_support.mp hy
    have hy' : y ∈ s := support_ofSubtype_subset u hy
    rw [Equiv.Perm.ofSubtype_apply_of_mem u hy'] at hne
    exact Equiv.Perm.mem_support.mpr fun hf => hne (congrArg Subtype.val hf)
  · intro y1 _ y2 _ h
    exact Subtype.ext_iff.mp h
  · intro q hq
    have hne : u q ≠ q := Equiv.Perm.mem_support.mp hq
    refine ⟨q.1, ?_, Subtype.ext rfl⟩
    refine Equiv.Perm.mem_support.mpr ?_
    rw [Equiv.Perm.ofSubtype_apply_coe]
    exact fun hx => hne (Subtype.ext hx)
  · intro y hy
    have hy' : y ∈ s := support_ofSubtype_subset u hy
    simp [Equiv.Perm.ofSubtype_apply_of_mem u hy']

lemma cayleySum_of_isEmpty {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    [IsEmpty α] (x : α → ℂ) :
    cayleySum x = 1 := by
  have : Unique (Perm α) := Equiv.permUnique
  unfold cayleySum
  rw [Fintype.sum_eq_single (1 : Perm α)
    (fun σ hσ => (hσ (Subsingleton.elim σ 1)).elim)]
  simp [oddLongPoints_one, cayleyWeight_one]

lemma matchingSum_of_isEmpty {α : Type*} [Fintype α] [DecidableEq α]
    [IsEmpty α] (x : α → ℂ) :
    matchingSum x = 1 := by
  have : Unique (Perm α) := Equiv.permUnique
  unfold matchingSum
  rw [Fintype.sum_eq_single (1 : Perm α)
    (fun σ hσ => (hσ (Subsingleton.elim σ 1)).elim)]
  have hsup : (1 : Perm α).support = univ := by
    rw [Equiv.Perm.support_one, univ_eq_empty]
  rw [if_pos ⟨hsup, by simp⟩, matchingWeight_one]

lemma matchingSum_fin_two (x : Fin 2 → ℂ) :
    matchingSum x = matchingWeight x (Equiv.swap (0 : Fin 2) 1) := by
  unfold matchingSum
  rw [show (univ : Finset (Perm (Fin 2))) = {1, Equiv.swap 0 1} from univ_perm_fin_two]
  rw [sum_insert (by simp [one_ne_swap_fin_two]), sum_singleton]
  have h1 : ¬ ((1 : Perm (Fin 2)).support = univ) := by
    rw [Equiv.Perm.support_one]
    intro h
    have : (0 : Fin 2) ∈ (∅ : Finset (Fin 2)) := by
      rw [h]
      exact mem_univ _
    exact notMem_empty _ this
  have hsw : (Equiv.swap (0 : Fin 2) 1).support = univ := by
    rw [Equiv.Perm.support_swap Fin.zero_ne_one]
    ext i
    fin_cases i <;> simp
  have hsq : Equiv.swap (0 : Fin 2) 1 * Equiv.swap (0 : Fin 2) 1 = 1 := by
    simp
  rw [if_neg (mt And.left h1), if_pos ⟨hsw, hsq⟩, zero_add]

lemma cayleySum_eq_matching_fin_two {x : Fin 2 → ℂ} (hx : x 0 ≠ x 1) :
    cayleySum x = (4 : ℂ) * (∏ i, x i) * matchingSum x := by
  rw [cayleySum_fin_two, matchingSum_fin_two,
    one_add_cayleyWeight_eq_matching x Fin.zero_ne_one hx, Fin.prod_univ_two]
  ring

lemma matchingWeight_permCongr {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (y : β → ℂ) (σ : Perm α) :
    matchingWeight (y ∘ e) σ = matchingWeight y (e.permCongr σ) := by
  unfold matchingWeight
  conv_rhs =>
    rw [← Equiv.prod_comp e (fun b =>
      if e.permCongr σ b = b then (1 : ℂ) else (y b - y (e.permCongr σ b))⁻¹)]
  refine Fintype.prod_congr _ _ fun a => ?_
  simp [Function.comp, Equiv.permCongr_apply]

lemma permCongr_mul_self {α β : Type*} (e : α ≃ β) (σ : Perm α) :
    e.permCongr σ * e.permCongr σ = e.permCongr (σ * σ) :=
  (e.permCongr_mul σ σ).symm

lemma support_eq_univ_permCongr_iff {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (σ : Perm α) :
    (e.permCongr σ).support = univ ↔ σ.support = univ := by
  constructor
  · intro h
    have hmap : σ.support.map e.toEmbedding = univ := by
      rw [← support_permCongr, h]
    refine eq_univ_of_card _ ?_
    have hc := card_map (s := σ.support) e.toEmbedding
    rw [hmap, card_univ] at hc
    simpa [Fintype.card_congr e] using hc.symm
  · exact support_univ_permCongr e

lemma matchingSum_permCongr {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (y : β → ℂ) :
    matchingSum (y ∘ e) = matchingSum y := by
  unfold matchingSum
  refine Fintype.sum_equiv e.permCongr
    (fun σ => if σ.support = univ ∧ σ * σ = 1 then matchingWeight (y ∘ e) σ else 0)
    (fun ρ => if ρ.support = univ ∧ ρ * ρ = 1 then matchingWeight y ρ else 0)
    fun σ => ?_
  rw [matchingWeight_permCongr]
  have hsup := support_eq_univ_permCongr_iff e σ
  have h1 := permCongr_one e
  have hsq : e.permCongr σ * e.permCongr σ = 1 ↔ σ * σ = 1 := by
    rw [permCongr_mul_self, ← h1]
    exact (Equiv.injective e.permCongr).eq_iff
  by_cases h : σ.support = univ ∧ σ * σ = 1
  · have h' : (e.permCongr σ).support = univ ∧ e.permCongr σ * e.permCongr σ = 1 :=
      ⟨hsup.2 h.1, hsq.2 h.2⟩
    simp [h, h']
  · have h' : ¬ ((e.permCongr σ).support = univ ∧
        e.permCongr σ * e.permCongr σ = 1) := by
      intro hne
      exact h ⟨hsup.1 hne.1, hsq.1 hne.2⟩
    simp [h, h']

noncomputable def matchingSumOn {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (x : α → ℂ) : ℂ :=
  matchingSum (fun a : {a // a ∈ s} => x a.1)

lemma card_pair {α : Type*} [DecidableEq α] {p q : α} (hpq : p ≠ q) :
    ({p, q} : Finset α).card = 2 := by
  rw [card_insert_of_notMem (notMem_singleton.2 hpq), card_singleton]

lemma card_compl_pair {α : Type*} [Fintype α] [DecidableEq α] {p q : α}
    (hpq : p ≠ q) :
    ({p, q} : Finset α)ᶜ.card = Fintype.card α - 2 := by
  rw [card_compl, card_pair hpq]

lemma prod_omit_pair {α : Type*} [Fintype α] [DecidableEq α] {p q : α}
    (hpq : p ≠ q) (x : α → ℂ) :
    (∏ a, x a) =
      x p * x q * ∏ a : {a // a ∈ ({p, q} : Finset α)ᶜ}, x a.1 := by
  calc (∏ a, x a)
      = ∏ a ∈ ({p, q} : Finset α) ∪ ({p, q} : Finset α)ᶜ, x a := by
          rw [union_compl]
    _ = (∏ a ∈ ({p, q} : Finset α), x a) *
          ∏ a ∈ ({p, q} : Finset α)ᶜ, x a :=
        prod_union disjoint_compl_right
    _ = x p * x q * ∏ a ∈ ({p, q} : Finset α)ᶜ, x a := by
          rw [prod_insert (notMem_singleton.2 hpq), prod_singleton]
    _ = x p * x q * ∏ a : {a // a ∈ ({p, q} : Finset α)ᶜ}, x a.1 := by
          rw [← prod_coe_sort]

lemma injective_restrict {α : Type*} {s : Finset α} {x : α → ℂ}
    (hx : Function.Injective x) :
    Function.Injective (fun a : {a // a ∈ s} => x a.1) :=
  hx.comp Subtype.val_injective

lemma support_eq_univ_iff {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α} :
    σ.support = univ ↔ ∀ a, σ a ≠ a := by
  simp [eq_univ_iff_forall, Equiv.Perm.mem_support]

lemma zpow_even_of_mul_self {α : Type*} {σ : Perm α} (hσ : σ * σ = 1)
    {k : ℤ} (hk : Even k) : σ ^ k = 1 := by
  obtain ⟨m, rfl⟩ := even_iff_exists_two_mul.mp hk
  rw [_root_.zpow_mul, zpow_two, hσ]
  exact (_root_.one_zpow (α := Perm α) m)

lemma zpow_odd_of_mul_self {α : Type*} {σ : Perm α} (hσ : σ * σ = 1)
    {k : ℤ} (hk : Odd k) : σ ^ k = σ := by
  obtain ⟨m, hm⟩ := odd_iff_exists_bit1.mp hk
  rw [hm, add_comm, _root_.zpow_add, zpow_one, _root_.zpow_mul, zpow_two, hσ]
  change σ * ((1 : Perm α) ^ m) = σ
  rw [_root_.one_zpow, mul_one]

lemma sameCycle_of_mul_self {α : Type*} {σ : Perm α} (hσ : σ * σ = 1)
    {p x : α} : σ.SameCycle p x ↔ x = p ∨ x = σ p := by
  constructor
  · rintro ⟨k, rfl⟩
    rcases Int.even_or_odd k with hk | hk
    · left
      rw [zpow_even_of_mul_self hσ hk]
      simp
    · right
      rw [zpow_odd_of_mul_self hσ hk]
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

lemma support_cycleOf_eq_pair {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} (hσ : σ * σ = 1) {p : α} (hp : σ p ≠ p) :
    (σ.cycleOf p).support = ({p, σ p} : Finset α) := by
  ext x
  simp [Equiv.Perm.mem_support_cycleOf_iff' hp, sameCycle_of_mul_self hσ]

lemma cycleOf_support_card_eq_two_of_mul_self {α : Type*} [Fintype α]
    [DecidableEq α] {σ : Perm α} (hσ : σ * σ = 1) {p : α} (hp : σ p ≠ p) :
    (σ.cycleOf p).support.card = 2 := by
  rw [support_cycleOf_eq_pair hσ hp, card_pair hp.symm]

lemma cycleOf_eq_swap_of_mul_self {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} (hσ : σ * σ = 1) {p : α} (hp : σ p ≠ p) :
    σ.cycleOf p = Equiv.swap p (σ p) :=
  cycleOf_eq_swap_of_card_two (cycleOf_support_card_eq_two_of_mul_self hσ hp)

lemma ofSubtype_mul_self {α : Type*} [DecidableEq α] {s : Finset α}
    (u : Perm {a // a ∈ s}) :
    Equiv.Perm.ofSubtype u * Equiv.Perm.ofSubtype u =
      Equiv.Perm.ofSubtype (u * u) :=
  (map_mul (Equiv.Perm.ofSubtype : Perm {a // a ∈ s} →* Perm α) u u).symm

lemma ofSubtype_eq_one_iff {α : Type*} [DecidableEq α] {s : Finset α}
    {u : Perm {a // a ∈ s}} :
    Equiv.Perm.ofSubtype u = 1 ↔ u = 1 := by
  rw [← map_one (Equiv.Perm.ofSubtype : Perm {a // a ∈ s} →* Perm α)]
  exact Equiv.Perm.ofSubtype_injective.eq_iff

lemma swap_mul_ofSubtype_mul_self {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (hpq : p ≠ q) (u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ}) :
    (Equiv.swap p q * Equiv.Perm.ofSubtype u) *
        (Equiv.swap p q * Equiv.Perm.ofSubtype u) =
      Equiv.Perm.ofSubtype (u * u) := by
  have hdisj := disjoint_swap_ofSubtype_pair hpq u
  have hss : Equiv.swap p q * Equiv.swap p q = 1 := by
    ext x
    simp
  calc (Equiv.swap p q * Equiv.Perm.ofSubtype u) *
          (Equiv.swap p q * Equiv.Perm.ofSubtype u)
      = Equiv.swap p q * (Equiv.Perm.ofSubtype u * Equiv.swap p q) *
          Equiv.Perm.ofSubtype u := by
        ac_rfl
    _ = Equiv.swap p q * (Equiv.swap p q * Equiv.Perm.ofSubtype u) *
          Equiv.Perm.ofSubtype u := by rw [← hdisj.commute]
    _ = (Equiv.swap p q * Equiv.swap p q) *
          (Equiv.Perm.ofSubtype u * Equiv.Perm.ofSubtype u) := by
        ac_rfl
    _ = Equiv.Perm.ofSubtype (u * u) := by
        rw [hss, ofSubtype_mul_self, one_mul]

lemma swap_mul_ofSubtype_mul_self_eq_one_iff {α : Type*} [Fintype α]
    [DecidableEq α] {p q : α} (hpq : p ≠ q)
    (u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ}) :
    (Equiv.swap p q * Equiv.Perm.ofSubtype u) *
        (Equiv.swap p q * Equiv.Perm.ofSubtype u) = 1 ↔ u * u = 1 := by
  rw [swap_mul_ofSubtype_mul_self hpq u, ofSubtype_eq_one_iff]

lemma support_ofSubtype_eq_iff {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} (u : Perm {a // a ∈ s}) :
    (Equiv.Perm.ofSubtype u).support = s ↔ u.support = univ := by
  constructor
  · intro h
    rw [eq_univ_iff_forall]
    intro q
    have : q.1 ∈ (Equiv.Perm.ofSubtype u).support := by
      rw [h]
      exact q.2
    have hne : Equiv.Perm.ofSubtype u q.1 ≠ q.1 := Equiv.Perm.mem_support.mp this
    rw [Equiv.Perm.ofSubtype_apply_coe] at hne
    exact Equiv.Perm.mem_support.mpr fun hf => hne (congrArg Subtype.val hf)
  · exact support_ofSubtype_eq

lemma support_swap_mul_ofSubtype {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (hpq : p ≠ q) (u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ}) :
    (Equiv.swap p q * Equiv.Perm.ofSubtype u).support =
      ({p, q} : Finset α) ∪ (Equiv.Perm.ofSubtype u).support :=
  (disjoint_swap_ofSubtype_pair hpq u).support_mul.trans
    (by rw [Equiv.Perm.support_swap hpq])

lemma support_swap_mul_ofSubtype_eq_univ_iff {α : Type*} [Fintype α]
    [DecidableEq α] {p q : α} (hpq : p ≠ q)
    (u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ}) :
    (Equiv.swap p q * Equiv.Perm.ofSubtype u).support = univ ↔
      u.support = univ := by
  constructor
  · intro h
    refine (support_ofSubtype_eq_iff u).1 ?_
    have hunion : ({p, q} : Finset α) ∪ (Equiv.Perm.ofSubtype u).support = univ := by
      rw [← support_swap_mul_ofSubtype hpq u, h]
    have hsub : (Equiv.Perm.ofSubtype u).support ⊆ ({p, q} : Finset α)ᶜ :=
      support_ofSubtype_subset u
    refine Subset.antisymm hsub ?_
    intro x hx
    have hxuniv : x ∈ ({p, q} : Finset α) ∪ (Equiv.Perm.ofSubtype u).support := by
      rw [hunion]
      exact mem_univ x
    exact (mem_union.mp hxuniv).resolve_left (mem_compl.mp hx)
  · intro h
    rw [support_swap_mul_ofSubtype hpq u, (support_ofSubtype_eq_iff u).2 h,
      union_compl]

lemma matchingWeight_swap_mul_ofSubtype {α : Type*} [Fintype α]
    [DecidableEq α] {p q : α} (hpq : p ≠ q) (x : α → ℂ)
    (u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ}) :
    matchingWeight x (Equiv.swap p q * Equiv.Perm.ofSubtype u) =
      matchingWeight x (Equiv.swap p q) *
        matchingWeight (fun a : {a // a ∈ ({p, q} : Finset α)ᶜ} => x a.1) u := by
  rw [matchingWeight_mul_disjoint x (disjoint_swap_ofSubtype_pair hpq u),
    matchingWeight_ofSubtype]

lemma matching_swap_mul_ofSubtype_iff {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (hpq : p ≠ q)
    (u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ}) :
    (Equiv.swap p q * Equiv.Perm.ofSubtype u).support = univ ∧
        (Equiv.swap p q * Equiv.Perm.ofSubtype u) *
          (Equiv.swap p q * Equiv.Perm.ofSubtype u) = 1 ↔
      u.support = univ ∧ u * u = 1 := by
  rw [support_swap_mul_ofSubtype_eq_univ_iff hpq u,
    swap_mul_ofSubtype_mul_self_eq_one_iff hpq u]

open scoped Classical in
lemma matchingSum_eq_recurrence {α : Type*} [Fintype α] [DecidableEq α]
    (p : α) (x : α → ℂ) :
    matchingSum x =
      ∑ q : α, if q = p then 0 else
        matchingWeight x (Equiv.swap p q) *
          matchingSumOn ({p, q} : Finset α)ᶜ x := by
  have hsplit : ∀ σ : Perm α,
      (if σ.support = univ ∧ σ * σ = 1 then matchingWeight x σ else 0) =
        ∑ q : α, if q = p then 0 else
          if σ.cycleOf p = Equiv.swap p q then
            (if σ.support = univ ∧ σ * σ = 1 then matchingWeight x σ else 0)
          else 0 := by
    intro σ
    by_cases hσ : σ.support = univ ∧ σ * σ = 1
    · have hpσ : σ p ≠ p := (support_eq_univ_iff.mp hσ.1) p
      have hcy : σ.cycleOf p = Equiv.swap p (σ p) :=
        cycleOf_eq_swap_of_mul_self hσ.2 hpσ
      rw [Fintype.sum_eq_single (σ p)]
      · rw [if_neg hpσ, if_pos hcy, if_pos hσ]
      · intro q hq
        by_cases hqp : q = p
        · rw [if_pos hqp]
        · rw [if_neg hqp]
          have hne : σ.cycleOf p ≠ Equiv.swap p q := fun hsw =>
            hq (swap_eq_swap_iff_right hpσ.symm (hcy.symm.trans hsw)).symm
          rw [if_neg hne]
    · rw [if_neg hσ, Fintype.sum_eq_zero]
      intro q
      simp
  unfold matchingSum
  rw [Fintype.sum_congr _ _ hsplit, sum_comm]
  refine Fintype.sum_congr _ _ fun q => ?_
  by_cases hq : q = p
  · simp [hq]
  · simp_rw [if_neg hq]
    rw [sum_fiber_swap_ofSubtype (Ne.symm hq)
      (fun σ => if σ.support = univ ∧ σ * σ = 1 then matchingWeight x σ else 0)]
    unfold matchingSumOn matchingSum
    have hinner :
        ∀ u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ},
          (if (Equiv.swap p q * Equiv.Perm.ofSubtype u).support = univ ∧
              (Equiv.swap p q * Equiv.Perm.ofSubtype u) *
                (Equiv.swap p q * Equiv.Perm.ofSubtype u) = 1 then
            matchingWeight x (Equiv.swap p q * Equiv.Perm.ofSubtype u)
          else 0) =
            matchingWeight x (Equiv.swap p q) *
              (if u.support = univ ∧ u * u = 1 then
                matchingWeight (fun a : {a // a ∈ ({p, q} : Finset α)ᶜ} => x a.1) u
              else 0) := by
      intro u
      have hiff := matching_swap_mul_ofSubtype_iff (Ne.symm hq) u
      by_cases hu : u.support = univ ∧ u * u = 1
      · have hσ : (Equiv.swap p q * Equiv.Perm.ofSubtype u).support = univ ∧
            (Equiv.swap p q * Equiv.Perm.ofSubtype u) *
              (Equiv.swap p q * Equiv.Perm.ofSubtype u) = 1 := hiff.2 hu
        rw [if_pos hσ, if_pos hu, matchingWeight_swap_mul_ofSubtype (Ne.symm hq) x u]
      · have hσ : ¬ ((Equiv.swap p q * Equiv.Perm.ofSubtype u).support = univ ∧
            (Equiv.swap p q * Equiv.Perm.ofSubtype u) *
              (Equiv.swap p q * Equiv.Perm.ofSubtype u) = 1) := fun h => hu (hiff.1 h)
        rw [if_neg hσ, if_neg hu, mul_zero]
    rw [Fintype.sum_congr _ _ hinner, ← mul_sum]

lemma cycleType_replicate_two_of_mul_self {n : ℕ} {σ : Perm (Fin (2 * n))}
    (hsup : σ.support = univ) (hsq : σ * σ = 1) :
    σ.cycleType = Multiset.replicate n 2 := by
  have hpow : σ ^ 2 = 1 := by rw [pow_two, hsq]
  have hrep := Equiv.Perm.cycleType_of_pow_prime_eq_one (p := 2) hpow
  exact cycleType_eq_replicate_two hsup fun m hm =>
    (Multiset.mem_replicate.mp (hrep ▸ hm)).2

lemma mul_self_of_cycleType_replicate {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} {k : ℕ} (h : σ.cycleType = Multiset.replicate k 2) :
    σ * σ = 1 := by
  have hdvd : orderOf σ ∣ 2 := by
    rw [← Equiv.Perm.lcm_cycleType, h]
    exact Multiset.lcm_dvd.mpr fun m hm => by
      rw [(Multiset.mem_replicate.mp hm).2]
  exact (pow_two σ).symm.trans (orderOf_dvd_iff_pow_eq_one.mp hdvd)

lemma fpfinv_iff_cycleType {n : ℕ} {σ : Perm (Fin (2 * n))} :
    (σ.support = univ ∧ σ * σ = 1) ↔
      ((∀ i, σ i ≠ i) ∧ σ.cycleType = Multiset.replicate n 2) := by
  constructor
  · intro ⟨hsup, hsq⟩
    exact ⟨support_eq_univ_iff.mp hsup, cycleType_replicate_two_of_mul_self hsup hsq⟩
  · intro ⟨hder, hct⟩
    exact ⟨support_eq_univ_iff.mpr hder, mul_self_of_cycleType_replicate hct⟩

lemma matchingWeight_eq_prod {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {σ : Perm α} (h : σ.support = univ) :
    matchingWeight x σ = ∏ a, (x a - x (σ a))⁻¹ := by
  rw [matchingWeight_eq_prod_support, h]

lemma matchingWeight_zeta_mul {N : ℕ} [NeZero N] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) {σ : Perm (Fin N)} (hsup : σ.support = univ) :
    (∏ i : Fin N, ζ ^ i.val) * matchingWeight (fun i : Fin N => ζ ^ i.val) σ =
      ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹ := by
  rw [matchingWeight_eq_prod _ hsup]
  have hfac : ∀ a : Fin N, ζ ^ a.val - ζ ^ (σ a).val =
      ζ ^ a.val * (1 - ζ ^ ((σ a).val - a.val : ℤ)) :=
    fun a => cayley_sub_eq hζ a (σ a)
  have hprod :
      (∏ a : Fin N, (ζ ^ a.val - ζ ^ (σ a).val)⁻¹) =
        (∏ a : Fin N, (ζ ^ a.val)⁻¹) *
          ∏ a : Fin N, (1 - ζ ^ ((σ a).val - a.val : ℤ))⁻¹ := by
    simp_rw [hfac, mul_inv]
    rw [prod_mul_distrib]
  rw [hprod, ← mul_assoc]
  have hz : ∀ a : Fin N, ζ ^ a.val ≠ 0 := fun a => pow_ne_zero _ (zeta_ne_zero hζ)
  have hcancel : (∏ i : Fin N, ζ ^ i.val) * ∏ a : Fin N, (ζ ^ a.val)⁻¹ = 1 := by
    rw [← prod_mul_distrib]
    refine prod_eq_one fun a _ => mul_inv_cancel₀ (hz a)
  rw [hcancel, one_mul]

lemma matchingSum_zeta {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n)) :
    (4 : ℂ) ^ n * (∏ i : Fin (2 * n), ζ ^ i.val) *
      matchingSum (fun i : Fin (2 * n) => ζ ^ i.val) = (a n : ℂ) := by
  have : NeZero n := ⟨by omega⟩
  have : NeZero (2 * n) := ⟨by omega⟩
  unfold matchingSum
  rw [mul_assoc, mul_sum]
  have hterm : ∀ σ : Perm (Fin (2 * n)),
      (∏ i : Fin (2 * n), ζ ^ i.val) *
        (if σ.support = univ ∧ σ * σ = 1 then
          matchingWeight (fun i : Fin (2 * n) => ζ ^ i.val) σ else 0) =
        if (∀ i, σ i ≠ i) ∧ σ.cycleType = Multiset.replicate n 2 then
          ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
        else 0 := by
    intro σ
    by_cases h : σ.support = univ ∧ σ * σ = 1
    · have h' : (∀ i, σ i ≠ i) ∧ σ.cycleType = Multiset.replicate n 2 :=
        (fpfinv_iff_cycleType (n := n) (σ := σ)).1 h
      rw [if_pos h, if_pos h', matchingWeight_zeta_mul hζ h.1]
    · have h' : ¬ ((∀ i, σ i ≠ i) ∧ σ.cycleType = Multiset.replicate n 2) := by
        intro h2
        exact h ((fpfinv_iff_cycleType (n := n) (σ := σ)).2 h2)
      rw [if_neg h, if_neg h', mul_zero]
  rw [Fintype.sum_congr _ _ hterm]
  have hinv :
      (∑ σ : Perm (Fin (2 * n)),
        if (∀ i, σ i ≠ i) ∧ σ.cycleType = Multiset.replicate n 2 then
          ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
        else 0) =
        (a n : ℂ) / (2 : ℂ) ^ (2 * n) :=
    (derangement_inv_one_sub_eq_involution hn hζ).symm.trans
      (unsigned_derangement_inv_sum hn hζ)
  have h4 : (2 : ℂ) ^ (2 * n) = (4 : ℂ) ^ n := by
    rw [pow_mul]
    norm_num
  rw [hinv, h4, mul_div_cancel₀ _ (pow_ne_zero _ (by norm_num : (4 : ℂ) ≠ 0))]

lemma cayleySumOn_permCongr {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] (s : Finset α) (x : α → ℂ)
    (e : {a // a ∈ s} ≃ Fin (Fintype.card {a // a ∈ s})) :
    cayleySumOn s x =
      cayleySum ((fun a : {a // a ∈ s} => x a.1) ∘ e.symm) := by
  have h : ((fun a : {a // a ∈ s} => x a.1) ∘ e.symm) ∘ e =
      fun a : {a // a ∈ s} => x a.1 := by
    funext a
    simp
  rw [cayleySumOn]
  conv_lhs => rw [← h]
  exact cayleySum_permCongr e ((fun a : {a // a ∈ s} => x a.1) ∘ e.symm)

lemma matchingSumOn_permCongr {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (x : α → ℂ)
    (e : {a // a ∈ s} ≃ Fin (Fintype.card {a // a ∈ s})) :
    matchingSumOn s x =
      matchingSum ((fun a : {a // a ∈ s} => x a.1) ∘ e.symm) := by
  have h : ((fun a : {a // a ∈ s} => x a.1) ∘ e.symm) ∘ e =
      fun a : {a // a ∈ s} => x a.1 := by
    funext a
    simp
  rw [matchingSumOn]
  conv_lhs => rw [← h]
  exact matchingSum_permCongr e ((fun a : {a // a ∈ s} => x a.1) ∘ e.symm)

lemma prod_restrict_permCongr {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (x : α → ℂ)
    (e : {a // a ∈ s} ≃ Fin (Fintype.card {a // a ∈ s})) :
    (∏ a : {a // a ∈ s}, x a.1) =
      ∏ i, ((fun a : {a // a ∈ s} => x a.1) ∘ e.symm) i :=
  (Equiv.prod_comp e.symm (fun a : {a // a ∈ s} => x a.1)).symm

lemma cayleySum_eq_matching_fin :
    ∀ n : ℕ, Even n → ∀ (x : Fin n → ℂ), Function.Injective x →
      cayleySum x =
        (4 : ℂ) ^ (n / 2) * (∏ i, x i) * matchingSum x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro heven x hx
    by_cases h0 : n = 0
    · subst h0
      have : IsEmpty (Fin 0) := inferInstance
      rw [cayleySum_of_isEmpty, matchingSum_of_isEmpty]
      simp
    · by_cases h2 : n = 2
      · subst h2
        have hx01 : x 0 ≠ x 1 := fun h => Fin.zero_ne_one (hx h)
        have h := cayleySum_eq_matching_fin_two hx01
        simpa using h
      · have hn4 : 4 ≤ n := by
          obtain ⟨t, ht⟩ := heven
          have hn0 : n ≠ 0 := h0
          have hn2 : n ≠ 2 := h2
          omega
        have : NeZero n := ⟨by omega⟩
        have hcard2 : 2 ≤ Fintype.card (Fin n) := by
          rw [Fintype.card_fin]
          omega
        have heven' : Even (Fintype.card (Fin n)) := by
          simpa [Fintype.card_fin] using heven
        rw [cayleySum_eq_recurrence (0 : Fin n) x hx heven' hcard2]
        have hrec := matchingSum_eq_recurrence (0 : Fin n) x
        have hpow : n / 2 = (n - 2) / 2 + 1 := by omega
        have hterm : ∀ q : Fin n,
            (if q = 0 then (0 : ℂ) else
              (1 + cayleyWeight x (Equiv.swap 0 q)) *
                cayleySumOn ({0, q} : Finset (Fin n))ᶜ x) =
              if q = 0 then 0 else
                (4 : ℂ) ^ (n / 2) * (∏ i, x i) *
                  (matchingWeight x (Equiv.swap 0 q) *
                    matchingSumOn ({0, q} : Finset (Fin n))ᶜ x) := by
          intro q
          by_cases hq : q = 0
          · simp [hq]
          · have hpq : (0 : Fin n) ≠ q := Ne.symm hq
            have hxq : x 0 ≠ x q := fun h => hq (hx h).symm
            rw [if_neg hq, if_neg hq,
              one_add_cayleyWeight_eq_matching x hpq hxq]
            set s := ({0, q} : Finset (Fin n))ᶜ
            have hk : Fintype.card {a // a ∈ s} = n - 2 := by
              dsimp [s]
              rw [Fintype.card_coe, card_compl_pair hpq, Fintype.card_fin]
            have hk_lt : Fintype.card {a // a ∈ s} < n := by omega
            have hk_even : Even (Fintype.card {a // a ∈ s}) := by
              rw [hk]
              obtain ⟨t, ht⟩ := heven
              refine ⟨t - 1, ?_⟩
              omega
            have he := Fintype.equivFin {a // a ∈ s}
            let y := (fun a : {a // a ∈ s} => x a.1) ∘ he.symm
            have hy : Function.Injective y :=
              (injective_restrict hx).comp he.symm.injective
            have hih := ih _ hk_lt hk_even y hy
            have hcy : cayleySumOn s x = cayleySum y :=
              cayleySumOn_permCongr s x he
            have hms : matchingSumOn s x = matchingSum y :=
              matchingSumOn_permCongr s x he
            have hpr : (∏ a : {a // a ∈ s}, x a.1) = ∏ i, y i :=
              prod_restrict_permCongr s x he
            have hkdiv : Fintype.card {a // a ∈ s} / 2 = (n - 2) / 2 := by omega
            have hcs : cayleySumOn s x =
                (4 : ℂ) ^ ((n - 2) / 2) * (∏ a : {a // a ∈ s}, x a.1) *
                  matchingSumOn s x := by
              rw [hcy, hih, hkdiv, ← hpr, ← hms]
            rw [hcs, prod_omit_pair hpq x, hpow, pow_succ]
            ring
        refine Eq.trans (Fintype.sum_congr _ _ hterm) ?_
        have hfac :
            (∑ q : Fin n, if q = 0 then (0 : ℂ) else
              (4 : ℂ) ^ (n / 2) * (∏ i, x i) *
                (matchingWeight x (Equiv.swap 0 q) *
                  matchingSumOn ({0, q} : Finset (Fin n))ᶜ x)) =
              (4 : ℂ) ^ (n / 2) * (∏ i, x i) *
                ∑ q : Fin n, if q = 0 then 0 else
                  matchingWeight x (Equiv.swap 0 q) *
                    matchingSumOn ({0, q} : Finset (Fin n))ᶜ x := by
          rw [mul_sum]
          refine Fintype.sum_congr _ _ fun q => ?_
          by_cases hq : q = 0
          · simp [hq]
          · simp [hq]
        rw [hfac, ← hrec]

lemma cayleySum_eq_matching {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] (x : α → ℂ) (hx : Function.Injective x)
    (heven : Even (Fintype.card α)) :
    cayleySum x =
      (4 : ℂ) ^ (Fintype.card α / 2) * (∏ a, x a) * matchingSum x := by
  let e := Fintype.equivFin α
  let y : Fin (Fintype.card α) → ℂ := x ∘ e.symm
  have hy : Function.Injective y := hx.comp e.symm.injective
  have hfin := cayleySum_eq_matching_fin (Fintype.card α) heven y hy
  have hcomp : y ∘ e = x := by
    funext a
    simp [y]
  have hcs : cayleySum x = cayleySum y := by
    conv_lhs => rw [← hcomp]
    exact cayleySum_permCongr e y
  have hms : matchingSum x = matchingSum y := by
    conv_lhs => rw [← hcomp]
    exact matchingSum_permCongr e y
  have hpr : (∏ a, x a) = ∏ i, y i := by
    conv_lhs => rw [← hcomp]
    exact Equiv.prod_comp e y
  rw [hcs, hms, hpr, hfin]

theorem conjecture1 (n : ℕ) (hn : 1 ≤ n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n)) :
    (sunMatrix n ζ).permanent = (a n : ℂ) := by
  have : NeZero n := ⟨by omega⟩
  have hx := zeta_pow_fin_injective (N := 2 * n) hζ
  have heven : Even (Fintype.card (Fin (2 * n))) := by
    rw [Fintype.card_fin]
    exact even_two_mul n
  have hmatch := cayleySum_eq_matching (fun i : Fin (2 * n) => ζ ^ i.val) hx heven
  have hpow : Fintype.card (Fin (2 * n)) / 2 = n := by
    rw [Fintype.card_fin, Nat.mul_div_right _ (by omega : 0 < 2)]
  rw [permanent_sunMatrix_eq_cayleySum hn hζ, hmatch, hpow, matchingSum_zeta hn hζ]

theorem conjecture1_frozen (n : ℕ) (hn : 1 ≤ n) :
    ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then (1 : ℂ)
        else (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ)))
      = (a n : ℂ) := by
  intro ζ hζ
  rw [← sunMatrix_eq_frozen]
  exact conjecture1 n hn hζ

#print axioms conjecture1_of_one
#print axioms zpow_sub_ne_one
#print axioms inv_one_sub_eq_sum
#print axioms denom_ne_zero
#print axioms calogero_kernel_sum
#print axioms det_calogero
#print axioms prod_zeta_perm
#print axioms sunMatrix_sub_ones_off
#print axioms permanent_of_zero_diag
#print axioms det_of_zero_diag
#print axioms det_calogero_eq_signed_sum
#print axioms permanent_sunMatrix_sub_ones
#print axioms signed_derangement_inv_sum
#print axioms two_three_cycles_cancel
#print axioms sum_insert_kernel
#print axioms cycleEdgeWeight_formPerm
#print axioms cycleEdgeWeight_mul_disjoint
#print axioms cycleEdgeWeight_formPerm_cons
#print axioms sum_cycleEdgeWeight_cons_rotate
#print axioms ofFn_rotate
#print axioms sum_cycleEdgeWeight_ncycles
#print axioms zeta_pow_sub
#print axioms cycleEdgeWeight_zeta
#print axioms listing_isCycle
#print axioms listing_support_univ
#print axioms listing_inv_one_sub_sum
#print axioms cycleEdgeWeight_zeta_univ
#print axioms ncycleToListingFun_injective
#print axioms ncycleToListingFun_surjective
#print axioms ncycleToListing_listingPerm
#print axioms listingPerm_ncycleToListing
#print axioms ncycle_inv_one_sub_sum
#print axioms cycleEdgeWeight_ofSubtype
#print axioms ofSubtype_isCycle
#print axioms sum_cycleEdgeWeight_replace_cycle
#print axioms coe_units_neg_one_pow
#print axioms sign_of_cycleType_replicate_two
#print axioms cycleType_eq_replicate_two
#print axioms derangement_long_cycle_or_replicate_two
#print axioms inv_one_sub_prod_of_univ
#print axioms involution_unsigned_eq_neg_signed
#print axioms ofSubtype_subtypePerm_of_support_subset
#print axioms support_ofSubtype_listing
#print axioms support_mul_listing_τ
#print axioms inv_one_sub_replace_cycle
#print axioms longPoints_nonempty_iff
#print axioms remainder_support_eq_compl
#print axioms ofSubtype_mul_remainder
#print axioms cycleOf_mul_listing
#print axioms longPoints_mul_listing
#print axioms sum_eq_sum_longKey
#print axioms longKey_of_listing
#print axioms isCycle_subtypePerm_of_support
#print axioms eq_listing_of_longKey
#print axioms long_fiber_inv_one_sub
#print axioms long_cycle_inv_one_sub_sum
#print axioms long_fiber_signed_inv_one_sub
#print axioms long_cycle_signed_inv_one_sub_sum
#print axioms unsigned_derangement_inv_sum
#print axioms permanent_sunMatrix_sub_ones_eq_a
#print axioms cayleyWeight_inv
#print axioms prod_sunMatrix_eq_cayleyWeight
#print axioms permanent_sunMatrix_eq_sum_cayleyWeight
#print axioms cayleyWeight_reverse_odd_cycle
#print axioms reverseOddCycle_involutive
#print axioms sum_cayleyWeight_eq_sum_no_odd
#print axioms permanent_sunMatrix_eq_sum_no_odd
#print axioms one_add_cayleyWeight_swap
#print axioms cayleySum_fin_two_eq
#print axioms cayleyWeight_ofSubtype
#print axioms oddLongPoints_mul_swap
#print axioms oddLongPoints_ofSubtype_nonempty_iff
#print axioms cayleySum_ofSubtype
#print axioms cayleySum_term_swap_ofSubtype
#print axioms sum_cayleySum_term_swap_ofSubtype
#print axioms cycleOf_eq_swap_of_card_two
#print axioms exists_eq_swap_mul_ofSubtype
#print axioms sum_fiber_swap_ofSubtype
#print axioms cayleySum_sigma2
#print axioms cayley_triple_identity
#print axioms cayleyWeight_formPerm
#print axioms cayleyWeight_formPerm_cons
#print axioms sum_fiber_fixed
#print axioms cayleySum_sigma1
#print axioms cayleySum_split
#print axioms cayleySum_eq_sigma1_add_sigma2_add

#print axioms cayleyPathWeight_eq_prod_range
#print axioms cayleyWeight_formPerm_eq_path_mul_wrap
#print axioms cayleyWeight_formPerm_cons_eq_path
#print axioms path_mul_add_eq_weight_mul_sub
#print axioms cayleyWeight_cons_rotate_eq
#print axioms path_mul_add_eq_weight_mul_sub_of_length
#print axioms cayleyWeight_cons_rotate_eq_neg_path
#print axioms sum_cayleyWeight_cons_rotate
#print axioms cayleyPathWeight_eq_of_eqOn
#print axioms cayleyPathWeight_rotate_eq_of_eqOn_compl
#print axioms sum_cayleyWeight_listings_eq_of_eqOn_compl
#print axioms sum_cayleyWeight_hamiltonian_eq_listings
#print axioms sum_cayleyWeight_hamiltonian_eq_of_eqOn_compl
#print axioms exists_natCast_notMem
#print axioms exists_injective_off
#print axioms injective_update
#print axioms sum_cayleyWeight_hamiltonian_eq_update
#print axioms sum_cayleyWeight_hamiltonian_eq_updateOn
#print axioms sum_cayleyWeight_hamiltonian_eq_of_injective
#print axioms cayleyWeight_permCongr
#print axioms isCycle_permCongr
#print axioms sum_cayleyWeight_hamiltonian_permCongr
#print axioms sum_cayleyWeight_hamiltonian_eq_of_card_eq
#print axioms sum_cayleyWeight_hamiltonian_subtype_eq_fin
#print axioms support_ofSubtype_eq
#print axioms cayleyWeight_ofSubtype_finset
#print axioms cycleSupportEquiv
#print axioms sum_cayleyWeight_cycles_support
#print axioms hamiltonianCayleySum_eq_cayleyHamConst
#print axioms hamiltonianCayleySum_subtype_eq_cayleyHamConst
#print axioms card_powersetCard_mem
#print axioms sum_cayleyWeight_even_cycles_through
#print axioms cayleyHamConst_one
#print axioms oddLongPoints_isCycle
#print axioms cayleySum_term_isCycle
#print axioms sum_cayleyWeight_long_even_cycles_through
#print axioms signMatrix_one
#print axioms permanent_succ_column_zero
#print axioms permanent_signMatrixOf_minor_rev
#print axioms permanent_signMatrix
#print axioms cayleyWeight_swap_of_zero
#print axioms cayleyHamConst_binom_sum_rewrite
#print axioms cayleySum_fin_two_of_zero
#print axioms cayleySum_permCongr
#print axioms cayleySumOn_pair
#print axioms sum_cayleyWeight_transpositions_through_of_zero
#print axioms evenCycleSumThrough_eq_binom
#print axioms cayleyWeight_cycleOf_mul_remainder
#print axioms oddLongPoints_cycleOf_mul_remainder
#print axioms cayleySum_remainder_one
#print axioms cayleySum_eq_one_add_even_cycles_add_complementary
#print axioms remainderThrough_eq_one_of_card_two
#print axioms cayleySum_eq_one_add_even_cycles_of_card_two
#print axioms cycleOf_mul_of_fixes
#print axioms remainder_mul_of_cycleOf_eq
#print axioms disjoint_ofSubtype_support_compl
#print axioms cayleyWeight_ofSubtype_mul_of_support_compl
#print axioms mem_support_compl_of_fixes
#print axioms support_cycleOf_subset_remainder_compl
#print axioms cycleOf_eq_self_of_support_eq
#print axioms cycleOf_eq_self_iff
#print axioms cycleOf_cycleOf
#print axioms cycleOf_ofSubtype_eq_of_cycleOf_eq
#print axioms cycleOf_eq_self_of_ofSubtype_cycleOf_eq
#print axioms remainder_ofSubtype_mul
#print axioms remainder_ofSubtype_mul_iff
#print axioms cycleOf_subtypePerm_eq_self
#print axioms remainderFibre_support_cycleOf
#print axioms remainderFibreEquiv
#print axioms cayleyWeight_ofSubtype_mul_oddLong
#print axioms sum_ite_cycleOf_eq_self
#print axioms cayleySum_fibre_remainder
#print axioms cayleySum_fibre_remainder_of_moves
#print axioms cayleySum_complementary_eq_sum_fibres
#print axioms cayleySum_complementary_eq_inner
#print axioms cayleyMatrix_apply_eq
#print axioms prod_cayleyMatrix_eq_cayleyWeight
#print axioms permanent_cayleyMatrix
#print axioms permanent_cayleyMatrix_eq_cayleySum
#print axioms sunMatrix_eq_cayleyMatrix
#print axioms cayleyPowZero_zero
#print axioms cayleyMatrix_powZero_col_zero
#print axioms cayleyMatrix_powZero_row_zero
#print axioms injective_cayleyPowZero
#print axioms cayleyMatrix_powZero_of_val_lt
#print axioms cayleyMatrix_powZero_of_val_gt
#print axioms tendsto_coe_pow_nhdsWithin_zero
#print axioms tendsto_one_add_div_one_sub_pow
#print axioms tendsto_pow_add_one_div_pow_sub_one
#print axioms tendsto_cayleyMatrix_powZero
#print axioms tendsto_permanent
#print axioms tendsto_permanent_cayleyMatrix_powZero
#print axioms permanent_signMatrixOf_even
#print axioms tendsto_cayleySum_powZero
#print axioms isCycle_permCongr_iff
#print axioms evenCycleSumThrough_permCongr
#print axioms even_card_support_of_oddLongPoints_empty
#print axioms equivFinZero_apply
#print axioms cayleySum_comp_equivFinZero
#print axioms evenCycleSumThrough_comp_equivFinZero
#print axioms cayleySum_eq_zero_fin
#print axioms identity_three_nine
#print axioms cayleySum_eq_zero_of_zero
#print axioms identity_three_nine_tail
#print axioms sum_cayleyWeight_long_even_cycles_through_eq_card_sub_two
#print axioms sum_long_even_subtype
#print axioms card_support_ofSubtype
#print axioms cycleOf_ofSubtype_mul_eq
#print axioms support_subset_compl_of_fixed_pair
#print axioms sum_fiber_fixed_pair
#print axioms cayleySumOn_eq_sum_fixed_pair
#print axioms filter_fixed_erase
#print axioms sum_boole_fixed_erase
#print axioms sum_cayleySumOn_omit_pair
#print axioms cayleySum_sigma1_eq_omit_sub_extra
#print axioms cayleySum_sigma3_inner_term
#print axioms cayleySum_sigma3_fibre
#print axioms cayleySum_sigma3_fibre_of_moves
#print axioms even_card_compl_of_oddLongPoints_empty
#print axioms cayleySum_sigma3
#print axioms cayleySum_eq_recurrence
#print axioms matchingWeight_one
#print axioms matchingWeight_swap
#print axioms matchingWeight_swap_inv_sq
#print axioms one_add_cayleyWeight_eq_matching
#print axioms matchingWeight_mul_disjoint
#print axioms matchingWeight_ofSubtype
#print axioms cayleySum_of_isEmpty
#print axioms matchingSum_of_isEmpty
#print axioms matchingSum_fin_two
#print axioms cayleySum_eq_matching_fin_two
#print axioms matchingWeight_permCongr
#print axioms matchingSum_permCongr
#print axioms matchingSum_eq_recurrence
#print axioms fpfinv_iff_cycleType
#print axioms matchingWeight_zeta_mul
#print axioms matchingSum_zeta
#print axioms cayleySum_eq_matching_fin
#print axioms cayleySum_eq_matching
#print axioms conjecture1
#print axioms conjecture1_frozen

end A001818C1
