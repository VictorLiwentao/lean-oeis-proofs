/-
Copyright (c) 2026 AI4Math Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
import Mathlib

/-!
# OEIS A381355

Hanna (11 Mar 2025): let `F` be the g.f. of A381353, defined by `F(0)=1`,
`[x^1] F = 1`, and `[x^n] F^{prime(n)} = 0` for `n > 1`. Let
`A = X · F' / F` (g.f. of A381355). Then `prime(n) ∣ a(n)` for every `n > 1`.

OEIS `prime(n)` is 1-indexed: `primeN n = Nat.nth Nat.Prime (n-1)`.

This is the exact OEIS comment, not a special case.
-/

open Finset Nat PowerSeries

namespace A381355

/-- 1-indexed `prime(n)` as on OEIS (`prime(1)=2`). -/
noncomputable def primeN (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

lemma primeN_prime {n : ℕ} (_hn : 1 ≤ n) : (primeN n).Prime :=
  Nat.prime_nth_prime (n - 1)

lemma n_lt_primeN {n : ℕ} (hn : 1 ≤ n) : n < primeN n := by
  have h := add_two_le_nth_prime (n - 1)
  have : n - 1 + 2 = n + 1 := by omega
  have : n + 1 ≤ primeN n := by simpa [primeN, this] using h
  omega

lemma C_natCast (k : ℕ) : (k : ℤ⟦X⟧) = C (k : ℤ) := by
  simp

lemma eq_one_add_X_mul (G : ℤ⟦X⟧) (h : constantCoeff G = 1) :
    G = 1 + X * PowerSeries.mk fun n => coeff (n + 1) G := by
  ext k
  cases k with
  | zero =>
    simp [coeff_zero_eq_constantCoeff, h, map_add, map_mul, constantCoeff_X]
  | succ k =>
    simp [map_add, coeff_one, coeff_succ_X_mul, PowerSeries.coeff_mk]

lemma coeff_pow_X_mul_of_lt {H : ℤ⟦X⟧} {p n : ℕ} (hn : n < p) :
    coeff n ((X * H) ^ p) = 0 := by
  rw [mul_pow, coeff_X_pow_mul']
  simp [not_le.mpr hn]

/-- If `F(0) = 1` and `0 < n < p` with `p` prime, then `p` divides `[x^n] F^p`. -/
lemma dvd_coeff_pow_of_lt {G : ℤ⟦X⟧} (hG : constantCoeff G = 1)
    {p n : ℕ} (hp : p.Prime) (hn0 : 0 < n) (hn : n < p) :
    (p : ℤ) ∣ coeff n (G ^ p) := by
  set y := X * PowerSeries.mk fun k => coeff (k + 1) G
  rw [eq_one_add_X_mul G hG, Commute.add_pow (Commute.one_left y),
    map_sum (coeff n)]
  refine dvd_sum fun m hm => ?_
  have hmle : m ≤ p := Nat.le_of_lt_succ (mem_range.mp hm)
  simp only [one_pow, one_mul]
  rw [C_natCast, mul_comm, coeff_C_mul]
  rcases eq_or_ne m 0 with hm0 | hm0
  · subst hm0
    simp [Nat.choose_zero_right]
    rw [coeff_pow_X_mul_of_lt (H := PowerSeries.mk fun k => coeff (k + 1) G) hn]
    simp
  · rcases eq_or_lt_of_le hmle with hme | hmlt
    · subst hme
      simp [coeff_one, hn0.ne']
    · exact (Int.natCast_dvd_natCast.mpr (hp.dvd_choose_self hm0 hmlt)).mul_right _

def truncAt (g : ℕ → ℤ) (n : ℕ) : ℕ → ℤ := fun k => if k < n then g k else 0

/-- Coefficient sequence of A381353. -/
noncomputable def f : ℕ → ℤ :=
  Nat.strongRec fun n ih =>
    if n = 0 then (1 : ℤ)
    else if n = 1 then 1
    else
      -(coeff n
          (PowerSeries.mk (fun k => if h : k < n then ih k h else 0) ^ primeN n) /
        (primeN n : ℤ))

lemma f_zero : f 0 = 1 := by
  rw [f, strongRec_eq]; simp

lemma f_one : f 1 = 1 := by
  rw [f, strongRec_eq]; simp

lemma f_ge_two (n : ℕ) (hn : 2 ≤ n) :
    f n =
      -(coeff n (PowerSeries.mk (truncAt f n) ^ primeN n) / (primeN n : ℤ)) := by
  have hne0 : n ≠ 0 := by omega
  have hne1 : n ≠ 1 := by omega
  have hinter :
      (fun k =>
        if k < n then
          Nat.strongRec
            (fun n ih =>
              if n = 0 then (1 : ℤ)
              else if n = 1 then 1
              else
                -(coeff n
                    (PowerSeries.mk (fun k => if h : k < n then ih k h else 0) ^ primeN n) /
                  (primeN n : ℤ)))
            k
        else 0) =
        truncAt f n := by
    funext k
    simp [truncAt, f]
  nth_rw 1 [f]
  rw [strongRec_eq]
  simp [hne0, hne1]
  rw [hinter]

lemma constantCoeff_mk_trunc {n : ℕ} (hn : 0 < n) :
    constantCoeff (PowerSeries.mk (truncAt f n)) = 1 := by
  simp [truncAt, hn, f_zero]

lemma dvd_trunc_pow {n : ℕ} (hn : 2 ≤ n) :
    (primeN n : ℤ) ∣ coeff n (PowerSeries.mk (truncAt f n) ^ primeN n) :=
  dvd_coeff_pow_of_lt (constantCoeff_mk_trunc (by omega))
    (primeN_prime (by omega)) (by omega) (n_lt_primeN (by omega))

lemma primeN_ne_zero {n : ℕ} (hn : 1 ≤ n) : (primeN n : ℤ) ≠ 0 :=
  Int.natCast_ne_zero.mpr (primeN_prime hn).ne_zero

lemma f_mul_prime (n : ℕ) (hn : 2 ≤ n) :
    (primeN n : ℤ) * f n + coeff n (PowerSeries.mk (truncAt f n) ^ primeN n) = 0 := by
  have hp := primeN_ne_zero (by omega : 1 ≤ n)
  obtain ⟨c, hc⟩ := dvd_trunc_pow hn
  have hdiv :
      coeff n (PowerSeries.mk (truncAt f n) ^ primeN n) / (primeN n : ℤ) = c := by
    rw [hc, Int.mul_ediv_cancel_left c hp]
  rw [f_ge_two n hn, hdiv, hc]
  ring

noncomputable def F : ℤ⟦X⟧ := PowerSeries.mk f

lemma coeff_F (n : ℕ) : coeff n F = f n := by
  simp [F, PowerSeries.coeff_mk]

lemma constantCoeff_F : constantCoeff F = 1 := by
  simpa [F, coeff_zero_eq_constantCoeff, coeff_F] using f_zero

lemma coeff_mul_congr {G₁ G₂ H₁ H₂ : ℤ⟦X⟧} {n : ℕ}
    (hG : ∀ k ≤ n, coeff k G₁ = coeff k G₂)
    (hH : ∀ k ≤ n, coeff k H₁ = coeff k H₂) :
    coeff n (G₁ * H₁) = coeff n (G₂ * H₂) := by
  simp only [coeff_mul]
  refine sum_congr rfl fun ij hij => ?_
  have := mem_antidiagonal.mp hij
  have hi : ij.1 ≤ n := by omega
  have hj : ij.2 ≤ n := by omega
  rw [hG _ hi, hH _ hj]

lemma coeff_pow_congr {G H : ℤ⟦X⟧} {n : ℕ}
    (h : ∀ k ≤ n, coeff k G = coeff k H) (p : ℕ) :
    coeff n (G ^ p) = coeff n (H ^ p) := by
  have hle : ∀ t k, k ≤ n → coeff k (G ^ t) = coeff k (H ^ t) := by
    intro t
    induction t with
    | zero =>
      intro k hk; simp [coeff_one]
    | succ t ih =>
      intro k hk
      have hGt : ∀ i ≤ k, coeff i (G ^ t) = coeff i (H ^ t) :=
        fun i hi => ih i (hi.trans hk)
      have hG' : ∀ i ≤ k, coeff i G = coeff i H :=
        fun i hi => h i (hi.trans hk)
      rw [pow_succ, pow_succ]
      exact coeff_mul_congr (n := k) hGt hG'
  exact hle p n le_rfl

lemma C_X_pow_pow (c : ℤ) (n k : ℕ) :
    (C c * X ^ n) ^ k = C (c ^ k) * X ^ (n * k) := by
  rw [mul_pow, map_pow, ← pow_mul]

lemma coeff_pow_add_C_X_pow (ψ : ℤ⟦X⟧) (c : ℤ) {n p : ℕ} (hn : 1 ≤ n) :
    coeff n ((ψ + C c * X ^ n) ^ p) =
      coeff n (ψ ^ p) + (p : ℤ) * c * constantCoeff ψ ^ (p - 1) := by
  rcases Nat.eq_zero_or_pos p with hp0 | hppos
  · subst hp0
    simp [coeff_one, (show n ≠ 0 by omega)]
  set θ := C c * X ^ n
  rw [Commute.add_pow (Commute.all ψ θ), map_sum (coeff n)]
  let t : ℕ → ℤ := fun m => coeff n (ψ ^ m * θ ^ (p - m) * (p.choose m : ℤ⟦X⟧))
  change ∑ m ∈ range (p + 1), t m = _
  have ht_p : t p = coeff n (ψ ^ p) := by
    simp [t, θ, pow_zero]
  have hsub : p - (p - 1) = 1 := by omega
  have ht_pred : t (p - 1) = (p : ℤ) * c * constantCoeff (ψ ^ (p - 1)) := by
    have hch : p.choose (p - 1) = p := by
      cases p with
      | zero => omega
      | succ p => simp [Nat.choose_succ_self_right]
    simp only [t, hsub, pow_one]
    rw [hch]
    have hperm : ψ ^ (p - 1) * θ * (p : ℤ⟦X⟧) =
        C (p : ℤ) * (ψ ^ (p - 1) * C c * X ^ n) := by
      calc
        ψ ^ (p - 1) * θ * (p : ℤ⟦X⟧)
            = ψ ^ (p - 1) * (C c * X ^ n) * C (p : ℤ) := by
              simp only [θ]; rw [C_natCast]
        _ = C (p : ℤ) * (ψ ^ (p - 1) * C c * X ^ n) := by
              simp [mul_assoc, mul_left_comm, mul_comm]
    rw [hperm, coeff_C_mul]
    have hassoc : ψ ^ (p - 1) * C c * X ^ n = (ψ ^ (p - 1) * C c) * X ^ n := by
      simp [mul_assoc]
    rw [hassoc, coeff_mul_X_pow']
    simp [coeff_zero_eq_constantCoeff, map_mul]
    ring
  have hother : ∀ m ∈ range (p + 1), m ≠ p → m ≠ p - 1 → t m = 0 := by
    intro m hm hmne hmne'
    have hmle : m ≤ p := Nat.le_of_lt_succ (mem_range.mp hm)
    have hk : 2 ≤ p - m := by omega
    simp only [t]
    have hpow : θ ^ (p - m) = C (c ^ (p - m)) * X ^ (n * (p - m)) :=
      C_X_pow_pow c n (p - m)
    have hperm : ψ ^ m * θ ^ (p - m) * (p.choose m : ℤ⟦X⟧) =
        (ψ ^ m * C (c ^ (p - m)) * (p.choose m : ℤ⟦X⟧)) * X ^ (n * (p - m)) := by
      rw [hpow]
      simp [mul_assoc, mul_left_comm, mul_comm]
    rw [hperm, coeff_mul_X_pow']
    have hdeg : ¬ n * (p - m) ≤ n := by
      have hnpos : 0 < n := hn
      have : n < n * (p - m) := by
        have hmul : 1 * n < (p - m) * n :=
          Nat.mul_lt_mul_of_pos_right (by omega) hnpos
        simpa [mul_comm, one_mul] using hmul
      exact not_le.mpr this
    simp [hdeg]
  have hp_mem : p ∈ range (p + 1) := mem_range.mpr (by omega)
  have hpred_mem : p - 1 ∈ (range (p + 1)).erase p := by
    simp [mem_erase, mem_range]
    omega
  rw [← sum_erase_add (range (p + 1)) t hp_mem, ← sum_erase_add _ t hpred_mem]
  simp only [ht_p, ht_pred, map_pow constantCoeff]
  have hrest :
      ∑ m ∈ ((range (p + 1)).erase p).erase (p - 1), t m = 0 := by
    refine sum_eq_zero fun m hm => ?_
    have hne_pred : m ≠ p - 1 := (mem_erase.mp hm).1
    have hm2 := (mem_erase.mp hm).2
    have hne_p : m ≠ p := (mem_erase.mp hm2).1
    have hmrange : m ∈ range (p + 1) := (mem_erase.mp hm2).2
    exact hother m hmrange hne_p hne_pred
  rw [hrest, zero_add]
  ring

lemma F_agree_trunc_add {n : ℕ} (hn : 1 ≤ n) :
    ∀ k ≤ n,
      coeff k F =
        coeff k (PowerSeries.mk (truncAt f n) + C (f n) * X ^ n) := by
  intro k hk
  simp only [map_add, coeff_F, PowerSeries.coeff_mk, truncAt]
  rw [coeff_C_mul_X_pow]
  by_cases hkn : k = n
  · subst hkn
    simp
  · have hklt : k < n := lt_of_le_of_ne hk hkn
    simp [hklt, hkn]

lemma coeff_F_pow_prime {n : ℕ} (hn : 2 ≤ n) :
    coeff n (F ^ primeN n) = 0 := by
  set ψ := PowerSeries.mk (truncAt f n)
  have hagree := F_agree_trunc_add (n := n) (by omega)
  have hcongr := coeff_pow_congr (G := F) (H := ψ + C (f n) * X ^ n) hagree (primeN n)
  have hadd := coeff_pow_add_C_X_pow ψ (f n) (n := n) (p := primeN n) (by omega)
  have hψ0 : constantCoeff ψ = 1 := constantCoeff_mk_trunc (by omega)
  have hppos : 1 ≤ primeN n := (primeN_prime (by omega)).one_lt.le
  have : constantCoeff ψ ^ (primeN n - 1) = 1 := by
    simp [hψ0]
  rw [hcongr, hadd, this, mul_one]
  have hrel := f_mul_prime n hn
  linear_combination hrel

/-- The initial coefficients and defining prime-power coefficient equations uniquely
specify the integral generating function used in OEIS A381353. -/
theorem F_unique {G : ℤ⟦X⟧} (h0 : constantCoeff G = 1)
    (h1 : coeff 1 G = 1)
    (hpow : ∀ n, 2 ≤ n → coeff n (G ^ primeN n) = 0) : G = F := by
  ext n
  rw [coeff_F]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      simpa [coeff_zero_eq_constantCoeff, f_zero] using h0
    by_cases hn1 : n = 1
    · subst n
      simpa [f_one] using h1
    have hn : 2 ≤ n := by omega
    have hagree : ∀ k ≤ n, coeff k G =
        coeff k (PowerSeries.mk (truncAt f n) + C (coeff n G) * X ^ n) := by
      intro k hk
      simp only [map_add, PowerSeries.coeff_mk, truncAt, coeff_C_mul_X_pow]
      by_cases hkn : k = n
      · subst k; simp
      · have hlt : k < n := lt_of_le_of_ne hk hkn
        simpa [hlt, hkn] using ih k hlt
    have heq := coeff_pow_congr hagree (primeN n)
    rw [coeff_pow_add_C_X_pow _ _ (by omega),
      constantCoeff_mk_trunc (by omega), one_pow, mul_one, hpow n hn] at heq
    have hrel := f_mul_prime n hn
    have hmul : (primeN n : ℤ) * coeff n G = (primeN n : ℤ) * f n := by
      linear_combination -heq - hrel
    exact mul_left_cancel₀ (primeN_ne_zero (by omega)) hmul

noncomputable def A : ℤ⟦X⟧ :=
  X * derivative ℤ F * invOfUnit F 1

/-- Logarithmic derivative series: coefficients of A381355 (`a 0 = 0`). -/
noncomputable def a (n : ℕ) : ℤ := coeff n A

lemma mul_invOfUnit_F : F * invOfUnit F 1 = 1 :=
  mul_invOfUnit F 1 constantCoeff_F

lemma invOfUnit_mul_F : invOfUnit F 1 * F = 1 :=
  invOfUnit_mul F 1 constantCoeff_F

lemma A_mul_F : A * F = X * derivative ℤ F := by
  simp [A, mul_assoc, invOfUnit_mul_F]

lemma coeff_X_derivative (G : ℤ⟦X⟧) {n : ℕ} (hn : 0 < n) :
    coeff n (X * derivative ℤ G) = (n : ℤ) * coeff n G := by
  cases n with
  | zero => omega
  | succ n =>
    rw [coeff_succ_X_mul, coeff_derivative, Nat.cast_succ]
    ring

lemma X_derivative_pow (p : ℕ) :
    X * derivative ℤ (F ^ p) = (p : ℤ⟦X⟧) * A * F ^ p := by
  rw [derivative_pow]
  have hAF : X * derivative ℤ F = A * F := A_mul_F.symm
  calc
    X * ((p : ℤ⟦X⟧) * F ^ (p - 1) * derivative ℤ F)
        = (p : ℤ⟦X⟧) * F ^ (p - 1) * (X * derivative ℤ F) := by
          simp [mul_assoc, mul_left_comm]
    _ = (p : ℤ⟦X⟧) * F ^ (p - 1) * (A * F) := by rw [hAF]
    _ = (p : ℤ⟦X⟧) * A * (F ^ (p - 1) * F) := by
          simp [mul_assoc, mul_left_comm, mul_comm A]
    _ = (p : ℤ⟦X⟧) * A * F ^ p := by
          cases p with
          | zero => simp
          | succ p => simp [pow_succ]

lemma a_zero : a 0 = 0 := by
  simp [a, A, coeff_zero_eq_constantCoeff, map_mul, constantCoeff_X]

lemma coeff_A_mul_pow (p n : ℕ) :
    coeff n (A * F ^ p) = ∑ k ∈ range (n + 1), a k * coeff (n - k) (F ^ p) := by
  simp [a, coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i A * coeff j (F ^ p)) n

lemma a_eq_neg_sum {n : ℕ} (hn : 2 ≤ n) :
    a n = -∑ k ∈ range n, a k * coeff (n - k) (F ^ primeN n) := by
  set p := primeN n
  have hcoeff : coeff n (A * F ^ p) = 0 := by
    have hL : coeff n (X * derivative ℤ (F ^ p)) = 0 := by
      rw [coeff_X_derivative (F ^ p) (by omega), coeff_F_pow_prime hn, mul_zero]
    have hR : coeff n ((p : ℤ⟦X⟧) * A * F ^ p) = (p : ℤ) * coeff n (A * F ^ p) := by
      rw [C_natCast, mul_assoc, coeff_C_mul]
    have heq := congrArg (coeff n) (X_derivative_pow p)
    have hmul : (p : ℤ) * coeff n (A * F ^ p) = 0 := by
      rw [← hR, ← heq, hL]
    exact (Int.mul_eq_zero.mp hmul).resolve_left (primeN_ne_zero (by omega))
  have hsum := coeff_A_mul_pow p n
  rw [hsum] at hcoeff
  rw [sum_range_succ] at hcoeff
  have hg0 : coeff 0 (F ^ p) = 1 := by
    simp [coeff_zero_eq_constantCoeff, map_pow, constantCoeff_F]
  simp [hg0] at hcoeff
  linarith

/-- OEIS A381355 conjecture: `prime(n)` divides `a(n)` for `n > 1`. -/
theorem primeN_dvd_a {n : ℕ} (hn : 1 < n) : (primeN n : ℤ) ∣ a n := by
  have hn2 : 2 ≤ n := by omega
  have hsum := a_eq_neg_sum hn2
  refine hsum ▸ dvd_neg.mpr ?_
  refine dvd_sum fun k hk => dvd_mul_of_dvd_right ?_ _
  have hk' : k < n := mem_range.mp hk
  have hnk : 0 < n - k := by omega
  have hnklt : n - k < primeN n :=
    Nat.lt_of_le_of_lt (Nat.sub_le n k) (n_lt_primeN (by omega))
  exact dvd_coeff_pow_of_lt constantCoeff_F (primeN_prime (by omega)) hnk hnklt

example : a 0 = 0 := a_zero
example : f 0 = 1 := f_zero
example : f 1 = 1 := f_one

#print axioms primeN_dvd_a
#print axioms coeff_F_pow_prime
#print axioms F_unique

end A381355

