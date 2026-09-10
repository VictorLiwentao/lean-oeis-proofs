/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
import Mathlib

/-!
# OEIS A098275: `(n+1) ∣ Σ_{i,j=0}^{n} C(n,i)^2 C(n,j)^2 C(n+i,n) C(i+j,i)`

`a098275 n` is the exact OEIS A098275 double binomial sum

    a(n) = Sum_{i=0..n} Sum_{j=0..n} C(n,i)^2 * C(n,j)^2 * C(n+i,n) * C(i+j,i).

The theorem `a098275_divisible` is the exact OEIS conjecture
(F. Chapoton, Jan 28 2026): for every `n : ℕ`, `n + 1 ∣ a098275 n`.

## Proof sketch (see `proofs/A098275/PROOF.md`)

1. Vandermonde: `C(i+j,i) = Σ_{k≤n} C(i,k) C(j,k)` for `i, j ≤ n`
   (`choose_add_eq_sum_choose_mul_choose`).
2. `Σ_j C(n,j)^2 C(j,k) = C(n,k) C(2n-k,n)` (`sum_choose_sq_mul_choose`).
3. Ballot identity: `n+1 ∣ (k+1) C(2n-k,n)` (`succ_dvd_succ_mul_choose`).
4. Catalan factor, termwise:
   `C(n,i)^2 C(n+i,n) C(i,k) = (k+1) · C(n,i) C(n+i,2i) Cat(i) C(i+1,k+1)`
   (`choose_sq_mul_choose_mul_choose_eq`).

Then every term of the reorganised sum
`a(n) = Σ_i Σ_k [C(n,i)^2 C(n+i,n) C(i,k)] · [C(n,k) C(2n-k,n)]`
is divisible by `n+1`.
-/

open Finset Nat

/-- The OEIS A098275 double binomial sum, exactly as on OEIS. -/
def a098275 (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
    n.choose i ^ 2 * n.choose j ^ 2 * (n + i).choose n * (i + j).choose i

/-- Symmetric Vandermonde: `C(i+j, i) = Σ_{k=0}^{n} C(i,k) C(j,k)` when `i, j ≤ n`. -/
lemma choose_add_eq_sum_choose_mul_choose (n i j : ℕ) (_hi : i ≤ n) (hj : j ≤ n) :
    (i + j).choose i = ∑ k ∈ range (n + 1), i.choose k * j.choose k := by
  rw [Nat.choose_symm_add, Nat.add_choose_eq,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => i.choose a * j.choose b)]
  have h1 : ∑ k ∈ range (j + 1), i.choose k * j.choose (j - k)
      = ∑ k ∈ range (j + 1), i.choose k * j.choose k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [Nat.choose_symm (by omega)]
  have h2 : ∑ k ∈ range (j + 1), i.choose k * j.choose k
      = ∑ k ∈ range (n + 1), i.choose k * j.choose k := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro k hk hk'
    simp only [Finset.mem_range, not_lt] at hk hk'
    rw [Nat.choose_eq_zero_of_lt (by omega : j < k), mul_zero]
  rw [Nat.succ_eq_add_one, h1, h2]

/-- `Σ_{j=0}^{n} C(n,j)^2 C(j,k) = C(n,k) C(2n-k, n)` for `k ≤ n`. -/
lemma sum_choose_sq_mul_choose (n k : ℕ) (hk : k ≤ n) :
    ∑ j ∈ range (n + 1), n.choose j ^ 2 * j.choose k = n.choose k * (2 * n - k).choose n := by
  have hV : (2 * n - k).choose n
      = ∑ a ∈ range (n - k + 1), n.choose a * (n - k).choose (n - k - a) := by
    have h2 : 2 * n - k = n + (n - k) := by omega
    rw [h2, Nat.choose_symm_add, Nat.add_choose_eq,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => n.choose a * (n - k).choose b)]
  calc ∑ j ∈ range (n + 1), n.choose j ^ 2 * j.choose k
      = ∑ a ∈ range (n + 1), n.choose (n - a) ^ 2 * (n - a).choose k := by
        rw [← Finset.sum_range_reflect]
        simp only [Nat.add_sub_cancel]
    _ = ∑ a ∈ range (n - k + 1), n.choose (n - a) ^ 2 * (n - a).choose k := by
        symm
        apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
        intro a ha ha'
        simp only [Finset.mem_range, not_lt] at ha ha'
        rw [Nat.choose_eq_zero_of_lt (by omega : n - a < k), mul_zero]
    _ = ∑ a ∈ range (n - k + 1), n.choose k * (n.choose a * (n - k).choose (n - k - a)) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mem_range] at ha
        have h1 : n.choose (n - a) * (n - a).choose k = n.choose k * (n - k).choose (n - a - k) :=
          Nat.choose_mul (by omega)
        have h2 : n.choose (n - a) = n.choose a := Nat.choose_symm (by omega)
        have h3 : n - a - k = n - k - a := by omega
        rw [h3] at h1
        calc n.choose (n - a) ^ 2 * (n - a).choose k
            = n.choose (n - a) * (n.choose (n - a) * (n - a).choose k) := by ring
          _ = n.choose a * (n.choose k * (n - k).choose (n - k - a)) := by rw [h1, h2]
          _ = n.choose k * (n.choose a * (n - k).choose (n - k - a)) := by ring
    _ = n.choose k * ∑ a ∈ range (n - k + 1), n.choose a * (n - k).choose (n - k - a) := by
        rw [Finset.mul_sum]
    _ = n.choose k * (2 * n - k).choose n := by rw [hV]

/-- Ballot identity in divisibility form: `n + 1 ∣ (k + 1) C(2n-k, n)` for `k ≤ n`. -/
lemma succ_dvd_succ_mul_choose (n k : ℕ) (hk : k ≤ n) :
    n + 1 ∣ (k + 1) * (2 * n - k).choose n := by
  have h := Nat.choose_succ_right_eq (2 * n - k) n
  rw [show 2 * n - k - n = n - k by omega] at h
  -- h : (2n-k).choose (n+1) * (n+1) = (2n-k).choose n * (n-k)
  have key : (k + 1) * (2 * n - k).choose n + (n + 1) * (2 * n - k).choose (n + 1)
      = (n + 1) * (2 * n - k).choose n := by
    have h' : (n + 1) * (2 * n - k).choose (n + 1) = (n - k) * (2 * n - k).choose n := by
      rw [mul_comm, h, mul_comm]
    rw [h', ← add_mul, show k + 1 + (n - k) = n + 1 by omega]
  have hdvd : n + 1 ∣ (k + 1) * (2 * n - k).choose n + (n + 1) * (2 * n - k).choose (n + 1) := by
    rw [key]
    exact dvd_mul_right _ _
  exact (Nat.dvd_add_left (dvd_mul_right (n + 1) ((2 * n - k).choose (n + 1)))).mp hdvd

/-- Catalan factor, termwise:
`C(n,i)^2 C(n+i,n) C(i,k) = (k+1) · C(n,i) C(n+i,2i) Cat(i) C(i+1,k+1)`. -/
lemma choose_sq_mul_choose_mul_choose_eq (n i k : ℕ) :
    n.choose i ^ 2 * (n + i).choose n * i.choose k
      = (k + 1) * (n.choose i * (n + i).choose (2 * i) * catalan i * (i + 1).choose (k + 1)) := by
  have hc : (k + 1) * (i + 1).choose (k + 1) = (i + 1) * i.choose k := by
    rw [Nat.add_one_mul_choose_eq]
    ring
  have hcat : (i + 1) * catalan i = (2 * i).choose i := by
    rw [succ_mul_catalan_eq_centralBinom, Nat.centralBinom_eq_two_mul_choose]
  have hb : (n + i).choose (2 * i) * (2 * i).choose i = (n + i).choose i * n.choose i := by
    have h := Nat.choose_mul (n := n + i) (k := 2 * i) (s := i) (by omega)
    rwa [show n + i - i = n by omega, show 2 * i - i = i by omega] at h
  have ha : (n + i).choose n = (n + i).choose i := Nat.choose_symm_add
  symm
  calc (k + 1) * (n.choose i * (n + i).choose (2 * i) * catalan i * (i + 1).choose (k + 1))
      = n.choose i * (n + i).choose (2 * i) * catalan i * ((k + 1) * (i + 1).choose (k + 1)) := by
        ring
    _ = n.choose i * (n + i).choose (2 * i) * ((i + 1) * catalan i) * i.choose k := by
        rw [hc]; ring
    _ = n.choose i * ((n + i).choose (2 * i) * (2 * i).choose i) * i.choose k := by
        rw [hcat]; ring
    _ = n.choose i * ((n + i).choose i * n.choose i) * i.choose k := by rw [hb]
    _ = n.choose i ^ 2 * (n + i).choose n * i.choose k := by rw [ha]; ring

/-- Reorganisation of the double sum via Vandermonde and `sum_choose_sq_mul_choose`. -/
lemma a098275_eq_reorg (n : ℕ) :
    a098275 n = ∑ i ∈ range (n + 1), ∑ k ∈ range (n + 1),
      (n.choose i ^ 2 * (n + i).choose n * i.choose k) * (n.choose k * (2 * n - k).choose n) := by
  unfold a098275
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  calc ∑ j ∈ range (n + 1), n.choose i ^ 2 * n.choose j ^ 2 * (n + i).choose n * (i + j).choose i
      = ∑ j ∈ range (n + 1), ∑ k ∈ range (n + 1),
          (n.choose i ^ 2 * (n + i).choose n * i.choose k) * (n.choose j ^ 2 * j.choose k) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_range] at hj
        rw [choose_add_eq_sum_choose_mul_choose n i j (by omega) (by omega), Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ = ∑ k ∈ range (n + 1), ∑ j ∈ range (n + 1),
          (n.choose i ^ 2 * (n + i).choose n * i.choose k) * (n.choose j ^ 2 * j.choose k) :=
        Finset.sum_comm
    _ = ∑ k ∈ range (n + 1),
          (n.choose i ^ 2 * (n + i).choose n * i.choose k)
            * (n.choose k * (2 * n - k).choose n) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        rw [← Finset.mul_sum, sum_choose_sq_mul_choose n k (by omega)]

/-- **OEIS A098275 conjecture (F. Chapoton, 2026):** `n + 1` divides
`Σ_{i=0}^{n} Σ_{j=0}^{n} C(n,i)^2 C(n,j)^2 C(n+i,n) C(i+j,i)` for every `n : ℕ`. -/
theorem a098275_divisible (n : ℕ) : n + 1 ∣ a098275 n := by
  rw [a098275_eq_reorg]
  apply Finset.dvd_sum
  intro i _
  apply Finset.dvd_sum
  intro k hk
  rw [Finset.mem_range] at hk
  rw [choose_sq_mul_choose_mul_choose_eq n i k]
  have h := succ_dvd_succ_mul_choose n k (by omega)
  have hre : (k + 1) * (n.choose i * (n + i).choose (2 * i) * catalan i * (i + 1).choose (k + 1))
        * (n.choose k * (2 * n - k).choose n)
      = (n.choose i * (n + i).choose (2 * i) * catalan i * (i + 1).choose (k + 1) * n.choose k)
        * ((k + 1) * (2 * n - k).choose n) := by ring
  rw [hre]
  exact Dvd.dvd.mul_left h _

example : a098275 0 = 1 := by decide
example : a098275 1 = 8 := by decide
example : a098275 2 = 264 := by decide
example : a098275 3 = 13040 := by decide

#print axioms a098275_divisible
