/-
Copyright 2026 The Formal Conjectures Authors.
Copyright (c) 2026 Wentao Li.
Authors: Wentao Li

The original statements and Wentao Li's contributions are licensed under Apache 2.0.
The binomial helper and its refinement are adapted from Epoch Research's
LeanOpenProblems-results; their provenance is recorded at the relevant sections
and in the accompanying SOURCE.md. No new license is asserted for those portions.
-/
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

namespace OeisA3161

/-- A binomial coefficient sum:
$a(n) = \sum_{k=0}^{\lfloor n/2 \rfloor} (\binom{n}{k} - \binom{n}{k-1})^3$. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    let diff : ℤ := (n.choose k : ℤ) - (if k = 0 then 0 else (n.choose (k - 1) : ℤ))
    (diff ^ 3).toNat

/-- Auxiliary sequence $b(n) = a(2n-1)$. -/
def b (n : ℕ) : ℕ :=
  a (2 * n - 1)

end OeisA3161

section
/-!
# Cubic ballot-sum normalization

Known identities of Miana–Ohtsuka–Romero (2016), Theorem 4.1, reduced to
Ohtsuka–Tauraso's Monthly Problem 11844. The telescoping certificates follow
Amdeberhan and Ekhad's published solution, with their evident typographical errors
resolved by direct polynomial identities.

References:
* https://arxiv.org/abs/1602.04347
* https://www.math.tulane.edu/~tamdeberhan/solutions/11844.PDF

Lean development: Wentao Li, with AI assistance.
-/

namespace B02R2Ballot

open Finset

/-- The adjacent binomial-coefficient relation, with integer subtraction. -/
theorem choose_step (m k : ℕ) :
    ((m : ℤ) - k) * (m.choose k : ℤ) =
      ((k : ℤ) + 1) * (m.choose (k + 1) : ℤ) := by
  by_cases h : k ≤ m
  · have hh := congrArg (fun a : ℕ => (a : ℤ)) (Nat.choose_succ_right_eq m k)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub h, mul_comm]
      using hh.symm
  · have hmk : m < k := by omega
    simp [Nat.choose_eq_zero_of_lt hmk, Nat.choose_eq_zero_of_lt (by omega : m < k + 1)]

/-- The cubic summand in Monthly Problem 11844. -/
def weightedTerm (m k : ℕ) : ℤ := ((m : ℤ) - 2 * k) * (m.choose k : ℤ) ^ 3

/-- The left telescoping certificate, written without negative binomial indices. -/
def leftCertificate (m : ℕ) : ℕ → ℤ
  | 0 => 0
  | k + 1 => (2 * (m : ℤ) - k + 1) * (m.choose k : ℤ) ^ 3

/-- One step of the left telescoping identity. -/
theorem weightedTerm_step (m k : ℕ) :
    weightedTerm (m + 1) k + weightedTerm m k =
      leftCertificate m (k + 1) - leftCertificate m k := by
  cases k with
  | zero => simp [weightedTerm, leftCertificate]; ring
  | succ k =>
    have hh := choose_step m k
    simp only [weightedTerm, leftCertificate, Nat.choose_succ_succ, Nat.cast_add,
      Nat.cast_one]
    linear_combination 3 * ((m.choose (k + 1) : ℤ) ^ 2 +
      (m.choose (k + 1) : ℤ) * m.choose k + (m.choose k : ℤ) ^ 2) * hh

/-- The truncated weighted sum. -/
def weightedSum (m n : ℕ) : ℤ := ∑ k ∈ range (n + 1), weightedTerm m k

/-- Telescoping gives a recurrence in the upper binomial index. -/
theorem weightedSum_step (m n : ℕ) :
    weightedSum (m + 1) n + weightedSum m n =
      (2 * (m : ℤ) - n + 1) * (m.choose n : ℤ) ^ 3 := by
  rw [weightedSum, weightedSum, ← sum_add_distrib]
  simp_rw [weightedTerm_step]
  rw [sum_range_sub]
  simp [leftCertificate]

/-- The full weighted cubic sum vanishes by reflection. -/
theorem weightedSum_self (n : ℕ) : weightedSum n n = 0 := by
  have href := sum_range_reflect (weightedTerm n) (n + 1)
  have hneg : ∀ k ∈ range (n + 1), weightedTerm n (n - k) = -weightedTerm n k := by
    intro k hk
    have hkn : k ≤ n := by simpa using hk
    simp only [weightedTerm, Nat.choose_symm hkn, Nat.cast_sub hkn]
    ring
  simp only [Nat.add_sub_cancel] at href
  rw [sum_congr rfl hneg, sum_neg_distrib] at href
  unfold weightedSum
  omega

/-- The adjacent relation in the upper binomial index, with integer subtraction. -/
theorem choose_upper_step (m n : ℕ) :
    ((m : ℤ) + 1 - n) * ((m + 1).choose n : ℤ) =
      ((m : ℤ) + 1) * (m.choose n : ℤ) := by
  by_cases h : n ≤ m + 1
  · have hh := congrArg (fun a : ℕ => (a : ℤ)) (Nat.choose_mul_succ_eq m n)
    simpa only [Nat.cast_mul, Nat.cast_sub h, Nat.cast_add, Nat.cast_one, mul_comm]
      using hh.symm
  · have hmn : m < n := by omega
    simp [Nat.choose_eq_zero_of_lt hmn,
      Nat.choose_eq_zero_of_lt (by omega : m + 1 < n)]

/-- The product summand on the right of Monthly Problem 11844. -/
def rightTerm (m n j : ℕ) : ℤ :=
  ((m : ℤ) - n) * (m.choose n : ℤ) * (j.choose n : ℤ) *
    (j.choose (m - n - 1) : ℤ)

/-- The right telescoping certificate. -/
def rightCertificate (m n j : ℕ) : ℤ :=
  ((n : ℤ) + 1) * (m.choose n : ℤ) * (j.choose (n + 1) : ℤ) *
    (j.choose (m - n) : ℤ)

/-- One step of the right telescoping identity. -/
theorem rightTerm_step (n t j : ℕ) :
    rightTerm (n + t + 1) n j + rightTerm (n + t) n j =
      rightCertificate (n + t) n (j + 1) - rightCertificate (n + t) n j := by
  cases t with
  | zero =>
    simp [rightTerm, rightCertificate, Nat.choose_succ_succ]
    ring
  | succ t =>
    have htop := choose_upper_step (n + (t + 1)) n
    have hnstep := choose_step j n
    have htstep := choose_step j t
    have hm1 : n + (t + 1) - n = t + 1 := by omega
    have hm2 : n + (t + 1) + 1 - n - 1 = t + 1 := by omega
    simp only [rightTerm, rightCertificate, hm1, hm2, Nat.add_sub_cancel, Nat.choose_succ_succ,
      Nat.cast_add, Nat.cast_one]
    push_cast at htop
    linear_combination
      (j.choose n : ℤ) * (j.choose (t + 1) : ℤ) * htop +
      ((n + (t + 1)).choose n : ℤ) * (j.choose t : ℤ) * hnstep -
      ((n + (t + 1)).choose n : ℤ) * (j.choose n : ℤ) * htstep

/-- The right-hand product sum. -/
def rightSum (m n : ℕ) : ℤ := ∑ j ∈ range m, rightTerm m n j

/-- Telescoping gives the same recurrence for the product sum. -/
theorem rightSum_step (n t : ℕ) :
    rightSum (n + t + 1) n + rightSum (n + t) n =
      (2 * ((n + t : ℕ) : ℤ) - n + 1) * ((n + t).choose n : ℤ) ^ 3 := by
  rw [rightSum, rightSum, sum_range_succ, add_right_comm, ← sum_add_distrib]
  simp_rw [rightTerm_step]
  rw [sum_range_sub]
  have hle : n ≤ n + t := by omega
  have hsub : n + t + 1 - n - 1 = n + t - n := by omega
  have htop := choose_upper_step (n + t) n
  have hstep := choose_step (n + t) n
  simp only [rightCertificate, rightTerm, hsub, Nat.choose_symm hle,
    Nat.choose_zero_succ, Nat.cast_zero, mul_zero, Nat.cast_add, Nat.cast_one]
  push_cast at htop hstep
  linear_combination ((n + t).choose n : ℤ) ^ 2 * htop -
    ((n + t).choose n : ℤ) ^ 2 * hstep

/-- The product sum vanishes when its two parameters agree. -/
theorem rightSum_self (n : ℕ) : rightSum n n = 0 := by
  simp [rightSum, rightTerm]

/-- The two sums agree by their common recurrence and initial value. -/
theorem weightedSum_eq_rightSum (n t : ℕ) : weightedSum (n + t) n = rightSum (n + t) n := by
  induction t with
  | zero => simp [weightedSum_self, rightSum_self]
  | succ t ih =>
    have hleft := weightedSum_step (n + t) n
    have hright := rightSum_step n t
    have hh : weightedSum (n + t + 1) n = rightSum (n + t + 1) n := by omega
    simpa [Nat.add_assoc] using hh

/-- Ohtsuka–Tauraso's weighted cubic identity (Monthly Problem 11844). -/
theorem weighted_identity {m n : ℕ} (hnm : n ≤ m) :
    (∑ k ∈ range (n + 1), ((m : ℤ) - 2 * k) * (m.choose k : ℤ) ^ 3) =
      ((m : ℤ) - n) * (m.choose n : ℤ) *
        ∑ j ∈ range m, (j.choose n : ℤ) * (j.choose (m - n - 1) : ℤ) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hnm
  change weightedSum (n + t) n = _
  rw [weightedSum_eq_rightSum]
  simp [rightSum, rightTerm, mul_sum, mul_assoc]

/-- A ballot-triangle entry, using zero for the preceding coefficient at rank zero. -/
def ballotTerm (m k : ℕ) : ℤ :=
  (m.choose k : ℤ) - if k = 0 then 0 else (m.choose (k - 1) : ℤ)

/-- The cubic telescoping certificate. -/
def cubeCertificate (m : ℕ) : ℕ → ℤ
  | 0 => 0
  | k + 1 => (m.choose k : ℤ) ^ 3

/-- Polynomial telescoping reduces ballot cubes to weighted binomial cubes. -/
theorem ballot_cubic_step (m k : ℕ) :
    ((m : ℤ) + 1) * ballotTerm m k ^ 3 + 3 * weightedTerm (m + 1) k =
      (4 * ((m : ℤ) + 1)) * (cubeCertificate m (k + 1) - cubeCertificate m k) := by
  cases k with
  | zero => simp [ballotTerm, weightedTerm, cubeCertificate]; ring
  | succ k =>
    have hh := choose_step m k
    simp only [ballotTerm, weightedTerm, cubeCertificate, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel, Nat.choose_succ_succ,
      Nat.cast_add, Nat.cast_one]
    linear_combination 6 * ((m.choose (k + 1) : ℤ) + m.choose k) ^ 2 * hh

/-- Summed cubic telescoping identity before cancelling the positive upper index. -/
theorem ballot_sum_scaled (m n : ℕ) :
    ((m : ℤ) + 1) * (∑ k ∈ range (n + 1), ballotTerm m k ^ 3) +
      3 * weightedSum (m + 1) n =
        4 * ((m : ℤ) + 1) * (m.choose n : ℤ) ^ 3 := by
  rw [weightedSum, mul_sum, mul_sum, ← sum_add_distrib]
  simp_rw [ballot_cubic_step]
  rw [← mul_sum, sum_range_sub]
  simp [cubeCertificate]

/-- The cubic ballot identity of Miana–Ohtsuka–Romero, with integer binomial entries. -/
theorem cubic_identity {m n : ℕ} (hnm : n ≤ m) :
    (∑ k ∈ range (n + 1), ballotTerm m k ^ 3) =
      4 * (m.choose n : ℤ) ^ 3 - 3 * (m.choose n : ℤ) *
        ∑ j ∈ range (m + 1), (j.choose n : ℤ) * (j.choose (m - n) : ℤ) := by
  have hweighted := weighted_identity (Nat.le_succ_of_le hnm)
  simp only [Nat.succ_eq_add_one] at hweighted
  have hsub : m + 1 - n - 1 = m - n := by omega
  have hw : weightedSum (m + 1) n =
      ((m : ℤ) + 1) * (m.choose n : ℤ) *
        ∑ j ∈ range (m + 1), (j.choose n : ℤ) * (j.choose (m - n) : ℤ) := by
    simp only [weightedSum, weightedTerm]
    rw [hweighted, hsub, Nat.cast_add, Nat.cast_one, choose_upper_step]
  have hc := ballot_sum_scaled m n
  rw [hw] at hc
  apply mul_left_cancel₀ (show (m : ℤ) + 1 ≠ 0 by omega)
  linear_combination hc

/-- Half the central binomial coefficient at index $n+1$. -/
def halfCentral (n : ℕ) : ℤ := (2 * n + 1).choose n

/-- The shifted square sum at index $n+1$. -/
def shiftedSquares (n : ℕ) : ℤ := ∑ j ∈ range (n + 1), ((n + j).choose j : ℤ) ^ 2

/-- The product sum in the odd-index cubic ballot identity. -/
def crossSum (n : ℕ) : ℤ :=
  ∑ j ∈ range (2 * n + 2), (j.choose n : ℤ) * (j.choose (n + 1) : ℤ)

/-- Pascal's identity telescopes the square difference. -/
theorem square_telescope (n M : ℕ) :
    2 * (∑ j ∈ range M, (j.choose n : ℤ) * (j.choose (n + 1) : ℤ)) +
      (∑ j ∈ range M, (j.choose n : ℤ) ^ 2) = (M.choose (n + 1) : ℤ) ^ 2 := by
  have hterm (j : ℕ) :
      2 * (j.choose n : ℤ) * (j.choose (n + 1) : ℤ) + (j.choose n : ℤ) ^ 2 =
        ((j + 1).choose (n + 1) : ℤ) ^ 2 - (j.choose (n + 1) : ℤ) ^ 2 := by
    rw [Nat.choose_succ_succ, Nat.cast_add]
    ring
  simp only [mul_sum, ← sum_add_distrib, ← mul_assoc]
  simp_rw [hterm]
  rw [sum_range_sub (fun j => (j.choose (n + 1) : ℤ) ^ 2)]
  simp

/-- Split the square sum at the first nonzero binomial coefficient. -/
theorem square_sum_split (n : ℕ) :
    (∑ j ∈ range (2 * n + 2), (j.choose n : ℤ) ^ 2) =
      shiftedSquares n + halfCentral n ^ 2 := by
  have hzero : (∑ j ∈ range n, (j.choose n : ℤ) ^ 2) = 0 := by
    apply sum_eq_zero
    intro j hj
    simp [Nat.choose_eq_zero_of_lt (mem_range.mp hj)]
  rw [show 2 * n + 2 = n + (n + 1 + 1) by omega, sum_range_add, hzero, zero_add,
    sum_range_succ]
  have hlast : n + (n + 1) = 2 * n + 1 := by omega
  simp only [hlast, halfCentral, shiftedSquares]
  congr 1
  apply sum_congr rfl
  intro j _hj
  rw [Nat.choose_symm_add]

/-- The central binomial coefficient is twice its adjacent half coefficient. -/
theorem central_eq_two_half (n : ℕ) :
    ((2 * n + 2).choose (n + 1) : ℤ) = 2 * halfCentral n := by
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, Nat.choose_succ_succ,
    Nat.choose_symm_half, Nat.cast_add]
  simp [halfCentral, two_mul]

/-- The elementary telescope connecting the product and shifted-square sums. -/
theorem crossSum_normalization (n : ℕ) :
    2 * crossSum n = 3 * halfCentral n ^ 2 - shiftedSquares n := by
  have hh := square_telescope n (2 * n + 2)
  rw [square_sum_split, central_eq_two_half] at hh
  change 2 * crossSum n + (shiftedSquares n + halfCentral n ^ 2) =
    (2 * halfCentral n) ^ 2 at hh
  nlinarith

/-- The odd-index cubic sum factors by its normalization denominator. -/
theorem cubic_odd (n : ℕ) :
    (∑ k ∈ range (n + 1), ballotTerm (2 * n + 1) k ^ 3) =
      halfCentral n * (4 * halfCentral n ^ 2 - 3 * crossSum n) := by
  have hh := cubic_identity (m := 2 * n + 1) (n := n) (by omega)
  have hsub : 2 * n + 1 - n = n + 1 := by omega
  rw [hsub] at hh
  change _ = 4 * halfCentral n ^ 3 - 3 * halfCentral n * crossSum n at hh
  rw [hh]
  ring


end B02R2Ballot
end

section
/-!
# Shared prime-power congruence interface

The tower quantifies over all positive multipliers and levels. Cancellation of two
uses only the prime bound. This continues the b01 conditional-transfer interface.
Lean development: Wentao Li, with AI assistance.
-/

namespace B02R2A003161

/-- Cubic supercongruences for a sequence at every prime-power level. -/
def CubicTower (f : ℕ → ℤ) : Prop :=
  ∀ (n k p : ℕ), 0 < n → 0 < k → p.Prime → 5 ≤ p →
    f (n * p ^ k) ≡ f (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)]

/-- Cancel two modulo a power of a prime at least five. -/
theorem cancel_two {p e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {a b : ℤ}
    (h : 2 * a ≡ 2 * b [ZMOD (p : ℤ) ^ e]) :
    a ≡ b [ZMOD (p : ℤ) ^ e] := by
  have hcop : (p ^ e).Coprime 2 :=
    (Nat.coprime_of_lt_prime (by decide : 2 ≠ 0) (by omega : 2 < p) hp).pow_left e
  rw [Int.modEq_iff_dvd] at h ⊢
  rw [← mul_sub] at h
  apply Int.dvd_of_dvd_mul_right_of_gcd_one h
  rw [← Nat.cast_pow]
  exact_mod_cast hcop


end B02R2A003161
end

section
/-!
## Binomial scaling helper from Epoch Research

Adapted from `kazan` and its supporting lemmas in Epoch Research's A141057 solution:
https://github.com/epoch-research/LeanOpenProblems-results/blob/fd09021e79869476ef83cda231312f1a2a89c8d7/runs/oeis-full-50usd-ant-j0j0g4uzligm1k41/oeis_a141057_supercongruence_conjecture/Submission/Spec.lean

The original source identifies the run as Claude Opus 4.8. Compatibility changes
and integration: Wentao Li. The source supplies this shared helper, while the
A003161 and A003162 target proofs are developed here.
-/

namespace B02R2EpochKazan

open Nat Finset

lemma isUnit_unit_mul {M:Type*}[CommMonoid M](u:Mˣ)(x:M): IsUnit ((u:M)*x) ↔ IsUnit x := by
  constructor
  · intro h; have hx : x = (↑u⁻¹) * ((u:M)*x) := by rw [← mul_assoc]; simp
    rw [hx]; exact (u⁻¹).isUnit.mul h
  · exact fun h => u.isUnit.mul h

lemma US_zero (m : ℕ) [NeZero m] (u : (ZMod m)ˣ) (c : ZMod m) (g : ZMod m → ZMod m)
    (hg : ∀ x : ZMod m, IsUnit x → g ((u:ZMod m) * x) = c * g x)
    (hc : IsUnit (c - 1)) :
    ∑ x : ZMod m, (if IsUnit x then g x else 0) = 0 := by
  set F : ZMod m → ZMod m := fun x => if IsUnit x then g x else 0 with hF
  have htoperm : ∀ x, (MulAction.toPerm u) x = (u:ZMod m) * x := fun x => rfl
  have hreind : ∑ x : ZMod m, F ((u:ZMod m) * x) = ∑ x : ZMod m, F x := by
    have h := Equiv.sum_comp (MulAction.toPerm u) F
    simpa only [htoperm] using h
  have hterm : ∀ x : ZMod m, F ((u:ZMod m) * x) = c * F x := by
    intro x
    by_cases hx : IsUnit x
    · have hux : IsUnit ((u:ZMod m) * x) := u.isUnit.mul hx
      simp only [hF, hx, hux, ite_true]
      exact hg x hx
    · have hux : ¬ IsUnit ((u:ZMod m)*x) := fun h => hx ((isUnit_unit_mul u x).mp h)
      simp only [hF, hx, hux, ite_false, mul_zero]
  have e1 : ∑ x, F ((u:ZMod m)*x) = ∑ x, c * F x := Finset.sum_congr rfl (fun x _ => hterm x)
  have heq : ∑ x, c * F x = ∑ x, F x := by rw [← e1, hreind]
  rw [← Finset.mul_sum] at heq
  have key : (c - 1) * (∑ x, F x) = 0 := by linear_combination heq
  rcases hc with ⟨w, hw⟩
  have hw2 : (w:ZMod m) * (∑ x, F x) = 0 := by rw [hw]; exact key
  have h2 := congrArg (fun t => (↑w⁻¹ : ZMod m) * t) hw2
  simp only [mul_zero, ← mul_assoc, Units.inv_mul, one_mul] at h2
  exact h2

lemma zmod_mul_inv (m:ℕ)(u:(ZMod m)ˣ)(x:ZMod m)(hx:IsUnit x):
    ((u:ZMod m)*x)⁻¹ = (u:ZMod m)⁻¹ * x⁻¹ := by
  obtain ⟨v, rfl⟩ := hx
  rw [← Units.val_mul u v, ZMod.inv_coe_unit (u*v), ZMod.inv_coe_unit u, ZMod.inv_coe_unit v,
      mul_inv_rev, Units.val_mul]
  ring

lemma US_inv (m:ℕ)[NeZero m](hu2:IsUnit (2:ZMod m)) :
    ∑ x:ZMod m, (if IsUnit x then x⁻¹ else 0) = 0 := by
  set u := hu2.unit with hu
  have huv : (u:ZMod m) = 2 := hu2.unit_spec
  have hmul : (u:ZMod m)⁻¹ * (u:ZMod m) = 1 := by rw [ZMod.inv_coe_unit]; exact u.inv_mul
  have hinvunit : IsUnit ((u:ZMod m)⁻¹) := by rw [ZMod.inv_coe_unit]; exact (u⁻¹).isUnit
  apply US_zero m u ((u:ZMod m)⁻¹) (fun x => x⁻¹)
  · intro x hx; exact zmod_mul_inv m u x hx
  · have hfac : (u:ZMod m)⁻¹ - 1 = (u:ZMod m)⁻¹ * (1 - (u:ZMod m)) := by
      rw [mul_sub, mul_one, hmul]
    rw [hfac]
    refine hinvunit.mul ?_
    rw [huv, show (1:ZMod m) - 2 = -1 by ring]; exact isUnit_one.neg

lemma US_inv2 (m:ℕ)[NeZero m](hu2:IsUnit (2:ZMod m))(hu3:IsUnit (3:ZMod m)) :
    ∑ x:ZMod m, (if IsUnit x then x⁻¹*x⁻¹ else 0) = 0 := by
  set u := hu2.unit with hu
  have huv : (u:ZMod m) = 2 := hu2.unit_spec
  have hmul : (u:ZMod m)⁻¹ * (u:ZMod m) = 1 := by rw [ZMod.inv_coe_unit]; exact u.inv_mul
  have hinvunit : IsUnit ((u:ZMod m)⁻¹) := by rw [ZMod.inv_coe_unit]; exact (u⁻¹).isUnit
  apply US_zero m u ((u:ZMod m)⁻¹*(u:ZMod m)⁻¹) (fun x => x⁻¹*x⁻¹)
  · intro x hx; rw [zmod_mul_inv m u x hx]; ring
  · have hfac : (u:ZMod m)⁻¹*(u:ZMod m)⁻¹ - 1
        = ((u:ZMod m)⁻¹ - 1) * ((u:ZMod m)⁻¹ + 1) := by ring
    rw [hfac]
    refine IsUnit.mul ?_ ?_
    · have h1 : (u:ZMod m)⁻¹ - 1 = (u:ZMod m)⁻¹ * (1 - (u:ZMod m)) := by
        rw [mul_sub, mul_one, hmul]
      rw [h1]; refine hinvunit.mul ?_
      rw [huv, show (1:ZMod m) - 2 = -1 by ring]; exact isUnit_one.neg
    · have h1 : (u:ZMod m)⁻¹ + 1 = (u:ZMod m)⁻¹ * (1 + (u:ZMod m)) := by
        rw [mul_add, mul_one, hmul]
      rw [h1]; refine hinvunit.mul ?_
      rw [huv, show (1:ZMod m) + 2 = 3 by ring]; exact hu3

lemma sum_block {R : Type*} [AddCommMonoid R] (L n : ℕ) (F : ℕ → R) :
    ∑ a ∈ Finset.range (L * n), F a
      = ∑ c ∈ Finset.range L, ∑ r ∈ Finset.range n, F (c * n + r) := by
  rw [← Finset.sum_product']
  apply Finset.sum_nbij' (fun a => (a / n, a % n)) (fun x => x.1 * n + x.2)
  · intro a ha
    simp only [Finset.mem_range] at ha
    have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at ha)
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.div_lt_of_lt_mul (by rwa [mul_comm] at ha), Nat.mod_lt _ hn⟩
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_range] at hx
    simp only [Finset.mem_range]
    calc x.1 * n + x.2 < x.1 * n + n := by omega
      _ = (x.1 + 1) * n := by ring
      _ ≤ L * n := Nat.mul_le_mul_right n hx.1
  · intro a ha; exact Nat.div_add_mod' a n
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_range] at hx
    have hn : 0 < n := by omega
    have h1 : (x.1 * n + x.2) / n = x.1 := by
      rw [add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hx.2, zero_add]
    have h2 : (x.1 * n + x.2) % n = x.2 := by
      rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx.2]
    exact Prod.ext h1 h2
  · intro a ha; exact congrArg F (Nat.div_add_mod' a n).symm

lemma sum_zmod_eq_sum_range (n:ℕ)[NeZero n](H:ZMod n → ZMod n):
    ∑ x : ZMod n, H x = ∑ r ∈ Finset.range n, H (r:ZMod n) := by
  apply Finset.sum_nbij' (fun x => ZMod.val x) (fun r => (r:ZMod n))
  · intro x _; simp only [Finset.mem_range]; exact ZMod.val_lt x
  · intro r _; exact Finset.mem_univ _
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro r hr; simp only [Finset.mem_range] at hr; exact ZMod.val_natCast_of_lt hr
  · intro x _; rw [ZMod.natCast_zmod_val]

lemma RED (p s N : ℕ) [NeZero (p^s)] (hp : p.Prime) (hs : 1 ≤ s) (hdvd : p^s ∣ N)
    (g : ZMod (p^s) → ZMod (p^s)) :
    ∑ a ∈ (Finset.range N).filter (fun a => ¬ p ∣ a), g (a : ZMod (p^s))
      = ((N/p^s : ℕ) : ZMod (p^s)) * ∑ x : ZMod (p^s), (if IsUnit x then g x else 0) := by
  have hmpos : 0 < p^s := Nat.pos_of_ne_zero (NeZero.ne (p^s))
  have hpm : p ∣ p^s := dvd_pow_self p (by omega)
  obtain ⟨q, hq⟩ := hdvd
  rw [Finset.sum_filter, hq, mul_comm (p^s) q, sum_block q (p^s)]
  have hNdiv : (q * p^s) / p^s = q := Nat.mul_div_cancel q hmpos
  rw [hNdiv]
  have hinner : ∀ c, ∑ r ∈ Finset.range (p^s),
        (if ¬p∣(c*(p^s)+r) then g ((c*(p^s)+r : ℕ):ZMod (p^s)) else 0)
      = ∑ x : ZMod (p^s), (if IsUnit x then g x else 0) := by
    intro c
    rw [sum_zmod_eq_sum_range (p^s) (fun x => if IsUnit x then g x else 0)]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Finset.mem_range] at hr
    have hcast : ((c*(p^s)+r : ℕ) : ZMod (p^s)) = (r:ZMod (p^s)) := by
      have hz : ((p^s : ℕ) : ZMod (p^s)) = 0 := ZMod.natCast_self _
      rw [Nat.cast_add, Nat.cast_mul, hz, mul_zero, zero_add]
    have hdiv : (p ∣ (c*(p^s)+r)) ↔ (p ∣ r) := Nat.dvd_add_right (hpm.mul_left c)
    have hunit : IsUnit ((r:ZMod (p^s))) ↔ ¬ p ∣ r := by
      rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm]
      exact hp.coprime_iff_not_dvd
    rw [hcast, if_congr (not_congr hdiv) rfl rfl, if_congr hunit.symm rfl rfl]
  rw [Finset.sum_congr rfl (fun c _ => hinner c), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]

noncomputable def gg (p M : ℕ) : ℕ := ∏ j ∈ (Finset.Icc 1 (M * p)).filter (fun j => ¬ p ∣ j), j

lemma prod_Icc_id_eq_fac : ∀ n : ℕ, ∏ j ∈ Finset.Icc 1 n, j = n ! := by
  intro n; induction n with
  | zero => simp
  | succ k ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ, mul_comm]

lemma fac_split (p M : ℕ) (hp : 0 < p) : (M * p)! = gg p M * p ^ M * M ! := by
  unfold gg
  have hsplit : (M * p)! = (∏ j ∈ Finset.Icc 1 (M * p), j) := (prod_Icc_id_eq_fac _).symm
  rw [hsplit, ← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (M * p)) (fun j => ¬ p ∣ j)]
  have hdvd : (∏ j ∈ (Finset.Icc 1 (M * p)).filter (fun j => ¬ ¬ p ∣ j), j) = p ^ M * M ! := by
    have himg : (Finset.Icc 1 (M * p)).filter (fun j => ¬ ¬ p ∣ j)
        = (Finset.Icc 1 M).image (fun i => p * i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, not_not]
      constructor
      · rintro ⟨⟨h1, h2⟩, hd⟩
        obtain ⟨i, rfl⟩ := hd
        refine ⟨i, ⟨?_, ?_⟩, by ring⟩
        · rcases Nat.eq_zero_or_pos i with h | h
          · simp [h] at h1
          · exact h
        · refine Nat.le_of_mul_le_mul_right ?_ hp
          rw [mul_comm i p]; exact h2
      · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
        exact ⟨⟨by nlinarith, by rw [mul_comm]; exact Nat.mul_le_mul_right p h2⟩, ⟨i, rfl⟩⟩
    rw [himg, Finset.prod_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hp h)]
    rw [Finset.prod_mul_distrib, Finset.prod_const, prod_Icc_id_eq_fac]
    congr 1
    rw [Nat.card_Icc]; simp
  rw [hdvd]; ring

-- F3: the gg ratio identity
lemma F3 (p A B : ℕ) (hp : 0 < p) (hBA : B ≤ A) :
    Nat.choose (A*p) (B*p) * gg p B * gg p (A-B) = Nat.choose A B * gg p A := by
  set L := A - B with hL
  have hAL : A = B + L := by omega
  have hLp : A*p - B*p = L*p := by rw [hL, Nat.sub_mul]
  -- (Ap)! identity
  have h1 : Nat.choose (A*p) (B*p) * (B*p)! * (A*p - B*p)! = (A*p)! :=
    Nat.choose_mul_factorial_mul_factorial (Nat.mul_le_mul_right p hBA)
  rw [hLp] at h1
  -- A! identity
  have h2 : Nat.choose A B * B ! * (A-B)! = A ! :=
    Nat.choose_mul_factorial_mul_factorial hBA
  rw [← hL] at h2
  -- expand factorials
  rw [fac_split p B hp, fac_split p L hp, fac_split p A hp] at h1
  -- h1 : choose(Ap)(Bp) * (gg B * p^B * B!) * (gg L * p^L * L!) = gg A * p^A * A!
  -- substitute A! = choose A B * B! * L!
  rw [← h2] at h1
  -- p^A = p^B * p^L  (A = B+L)
  have hpow : p^A = p^B * p^L := by rw [hAL, pow_add]
  rw [hpow] at h1
  -- now cancel by casting to ℤ
  have hKn : 0 < p^B * p^L * (B ! * L !) := by positivity
  have hK : (0:ℤ) < ((p^B * p^L * (B ! * L !) : ℕ):ℤ) := by exact_mod_cast hKn
  have h1z : ((Nat.choose (A*p) (B*p) * gg p B * gg p L : ℕ):ℤ)
        * ((p^B * p^L * (B ! * L !) : ℕ):ℤ)
      = ((Nat.choose A B * gg p A : ℕ):ℤ) * ((p^B * p^L * (B ! * L !) : ℕ):ℤ) := by
    have h1z' := congrArg (Nat.cast : ℕ → ℤ) h1
    push_cast at h1z' ⊢
    linear_combination h1z'
  have := mul_right_cancel₀ (ne_of_gt hK) h1z
  exact_mod_cast this

lemma gg_add (p B L : ℕ) :
    gg p (B + L) = gg p B * ∏ a ∈ (Finset.Icc 1 (L * p)).filter (fun a => ¬ p ∣ a), (B * p + a) := by
  unfold gg
  have hexp : (B+L)*p = B*p + L*p := by ring
  have e1 : Finset.Icc 1 (B*p) = Finset.Ioc 0 (B*p) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have e2 : Finset.Icc 1 ((B+L)*p) = Finset.Ioc 0 ((B+L)*p) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hsplit : Finset.Icc 1 ((B+L)*p) = Finset.Icc 1 (B*p) ∪ Finset.Ioc (B*p) ((B+L)*p) := by
    rw [e1, e2, Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (by nlinarith)]
  have hdisj : Disjoint (Finset.Icc 1 (B*p)) (Finset.Ioc (B*p) ((B+L)*p)) := by
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at ha hb; omega
  rw [hsplit, Finset.filter_union, Finset.prod_union (Finset.disjoint_filter_filter hdisj)]
  congr 1
  refine Finset.prod_nbij' (fun j => j - B*p) (fun a => B*p + a) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hj ⊢
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    intro hd; apply hj.2
    have hje : B*p + (j - B*p) = j := by omega
    rw [← hje]; exact (dvd_mul_left p B).add hd
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at ha ⊢
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    intro hd; exact ha.2 ((Nat.dvd_add_right (dvd_mul_left p B)).mp hd)
  · intro j hj; simp only [Finset.mem_filter, Finset.mem_Ioc] at hj; omega
  · intro a ha; omega
  · intro j hj; simp only [Finset.mem_filter, Finset.mem_Ioc] at hj; omega

lemma isUnit_two_zmod (p s:ℕ)[NeZero (p^s)](hp:p.Prime)(hp5:5≤p) : IsUnit (2:ZMod (p^s)) := by
  have h2 : ((2:ℕ):ZMod (p^s)) = 2 := by norm_num
  rw [← h2, ZMod.isUnit_iff_coprime]
  exact ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)).pow_right s

lemma isUnit_three_zmod (p s:ℕ)[NeZero (p^s)](hp:p.Prime)(hp5:5≤p) : IsUnit (3:ZMod (p^s)) := by
  have h3 : ((3:ℕ):ZMod (p^s)) = 3 := by norm_num
  rw [← h3, ZMod.isUnit_iff_coprime]
  exact ((Nat.coprime_primes Nat.prime_three hp).mpr (by omega)).pow_right s

lemma sumAinv (p s N : ℕ) [NeZero (p^s)] (hp : p.Prime) (hp5:5≤p) (hs : 1 ≤ s) (hdvd : p^s ∣ N) :
    ∑ a ∈ (Finset.range N).filter (fun a => ¬ p ∣ a), ((a : ZMod (p^s)))⁻¹ = 0 := by
  rw [RED p s N hp hs hdvd (fun x => x⁻¹), US_inv (p^s) (isUnit_two_zmod p s hp hp5), mul_zero]

lemma sumAinv2 (p s N : ℕ) [NeZero (p^s)] (hp : p.Prime) (hp5:5≤p) (hs : 1 ≤ s) (hdvd : p^s ∣ N) :
    ∑ a ∈ (Finset.range N).filter (fun a => ¬ p ∣ a), ((a : ZMod (p^s)))⁻¹ * ((a : ZMod (p^s)))⁻¹ = 0 := by
  rw [RED p s N hp hs hdvd (fun x => x⁻¹*x⁻¹),
      US_inv2 (p^s) (isUnit_two_zmod p s hp hp5) (isUnit_three_zmod p s hp hp5), mul_zero]

-- generalized product inverse for two units
lemma zmod_mul_inv' (m:ℕ)(a b:ZMod m)(ha:IsUnit a)(hb:IsUnit b): (a*b)⁻¹ = a⁻¹*b⁻¹ := by
  obtain ⟨u,rfl⟩ := ha; obtain ⟨v,rfl⟩ := hb
  rw [← Units.val_mul, ZMod.inv_coe_unit (u*v), ZMod.inv_coe_unit u, ZMod.inv_coe_unit v,
      mul_inv_rev, Units.val_mul]; ring

-- product of inverses = inverse of product, for units
lemma prod_zmod_inv (m:ℕ)(t:Finset ℕ)(f:ℕ→ZMod m)(hf:∀a∈t, IsUnit (f a)):
    (∏ a ∈ t, f a)⁻¹ = ∏ a ∈ t, (f a)⁻¹ := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a₀ s ha₀ ih =>
    rw [Finset.prod_insert ha₀, Finset.prod_insert ha₀,
        zmod_mul_inv' m _ _ (hf a₀ (Finset.mem_insert_self _ _))
          (Finset.prod_induction f IsUnit (fun _ _ => IsUnit.mul) isUnit_one
            (fun a ha => hf a (Finset.mem_insert_of_mem ha))),
        ih (fun a ha => hf a (Finset.mem_insert_of_mem ha))]

-- key2: (∑ x)^2 = ∑ x^2 + 2 * ∑_{pairs} ∏ x
lemma key2 {R:Type*}[CommRing R](s:Finset ℕ)(x:ℕ→R):
    (∑ a ∈ s, x a)^2 = ∑ a ∈ s, (x a)^2 + 2 * ∑ t ∈ s.powersetCard 2, ∏ a ∈ t, x a := by
  classical
  induction s using Finset.induction with
  | empty => rw [show (∅:Finset ℕ).powersetCard 2 = ∅ by rw [Finset.powersetCard_eq_empty]; norm_num]; simp
  | insert a₀ s ha₀ ih =>
    have hinj : ∀ c ∈ s.powersetCard 1, ∀ d ∈ s.powersetCard 1,
        insert a₀ c = insert a₀ d → c = d := by
      intro c hc d hd hcd
      have hc' : a₀ ∉ c := fun h => ha₀ ((Finset.mem_powersetCard.mp hc).1 h)
      have hd' : a₀ ∉ d := fun h => ha₀ ((Finset.mem_powersetCard.mp hd).1 h)
      rw [← Finset.erase_insert hc', ← Finset.erase_insert hd', hcd]
    have hdisj : Disjoint (s.powersetCard 2) ((s.powersetCard 1).image (insert a₀)) := by
      rw [Finset.disjoint_left]; intro c hc hc2
      simp only [Finset.mem_image] at hc2
      obtain ⟨d, hd, rfl⟩ := hc2
      have hsub := (Finset.mem_powersetCard.mp hc).1
      exact ha₀ (hsub (Finset.mem_insert_self _ _))
    rw [Finset.sum_insert ha₀, Finset.sum_insert ha₀,
        Finset.powersetCard_succ_insert ha₀, Finset.sum_union hdisj, Finset.sum_image hinj]
    have h1 : ∀ c ∈ s.powersetCard 1, ∏ a ∈ insert a₀ c, x a = x a₀ * ∏ a ∈ c, x a := by
      intro c hc
      have : a₀ ∉ c := fun h => ha₀ ((Finset.mem_powersetCard.mp hc).1 h)
      rw [Finset.prod_insert this]
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
    have hpc1 : ∑ c ∈ s.powersetCard 1, ∏ a ∈ c, x a = ∑ c ∈ s, x c := by
      rw [Finset.powersetCard_one, Finset.sum_map]
      apply Finset.sum_congr rfl; intro c _; simp
    rw [hpc1]
    linear_combination ih

lemma zmod_unit_mul_inv (m:ℕ)(b:ZMod m)(hb:IsUnit b): b*b⁻¹=1 := by
  obtain ⟨u,rfl⟩ := hb; rw [ZMod.inv_coe_unit]; exact u.mul_inv

lemma prod_compl_eq (m:ℕ)(𝒜 t:Finset ℕ)(f:ℕ→ZMod m)(ht:t⊆𝒜)
    (hunit:∀a∈t, IsUnit (f a)) :
    ∏ a ∈ 𝒜 \ t, f a = (∏ a ∈ 𝒜, f a) * (∏ a ∈ t, f a)⁻¹ := by
  have hB : IsUnit (∏ a ∈ t, f a) :=
    Finset.prod_induction f IsUnit (fun _ _ => IsUnit.mul) isUnit_one hunit
  have hkey := Finset.prod_sdiff ht (f := f)
  calc ∏ a ∈ 𝒜 \ t, f a
      = (∏ a ∈ 𝒜 \ t, f a) * ((∏ a ∈ t, f a) * (∏ a ∈ t, f a)⁻¹) := by
        rw [zmod_unit_mul_inv m _ hB, mul_one]
    _ = (∏ a ∈ 𝒜, f a) * (∏ a ∈ t, f a)⁻¹ := by rw [← mul_assoc, hkey]

-- FACT-T2 : p^s ∣ e2
lemma dvd_e2 (p s L : ℕ) [NeZero (p^s)] (hp:p.Prime)(hp5:5≤p)(hs:1≤s)(hdvd:p^s ∣ L*p) :
    (p:ℤ)^s ∣ ∑ t ∈ ((Finset.range (L*p)).filter (fun a => ¬ p ∣ a)).powersetCard 2,
        ∏ a ∈ ((Finset.range (L*p)).filter (fun a => ¬ p ∣ a)) \ t, (a:ℤ) := by
  set 𝒜 := (Finset.range (L*p)).filter (fun a => ¬ p ∣ a) with h𝒜
  have hunitA : ∀ a ∈ 𝒜, IsUnit ((a:ZMod (p^s))) := by
    intro a ha
    rw [h𝒜, Finset.mem_filter, Finset.mem_range] at ha
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr ha.2
  rw [show ((p:ℤ)^s) = ((p^s:ℕ):ℤ) by push_cast; ring,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  -- reduce each term
  set D₀ := ∏ a ∈ 𝒜, ((a:ZMod (p^s))) with hD₀
  have hstep : ∀ t ∈ 𝒜.powersetCard 2, ∏ a ∈ 𝒜 \ t, ((a:ZMod (p^s)))
      = D₀ * ∏ a ∈ t, ((a:ZMod (p^s)))⁻¹ := by
    intro t ht
    have hts : t ⊆ 𝒜 := (Finset.mem_powersetCard.mp ht).1
    rw [prod_compl_eq (p^s) 𝒜 t _ hts (fun a ha => hunitA a (hts ha)),
        prod_zmod_inv (p^s) t _ (fun a ha => hunitA a (hts ha))]
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  -- now show ∑_t ∏_{a∈t}(↑a)⁻¹ = 0
  have hdoubling : (2:ZMod (p^s)) * ∑ t ∈ 𝒜.powersetCard 2, ∏ a ∈ t, ((a:ZMod (p^s)))⁻¹ = 0 := by
    have hk := key2 𝒜 (fun a => ((a:ZMod (p^s)))⁻¹)
    have hS1 : ∑ a ∈ 𝒜, ((a:ZMod (p^s)))⁻¹ = 0 := sumAinv p s (L*p) hp hp5 hs hdvd
    have hS2 : ∑ a ∈ 𝒜, (((a:ZMod (p^s)))⁻¹)^2 = 0 := by
      have := sumAinv2 p s (L*p) hp hp5 hs hdvd
      rw [← this]; apply Finset.sum_congr rfl; intro a _; rw [sq]
    rw [hS1, hS2] at hk
    linear_combination -hk
  have h2u : IsUnit (2:ZMod (p^s)) := isUnit_two_zmod p s hp hp5
  rcases h2u with ⟨w, hw⟩
  have : (w:ZMod (p^s)) * ∑ t ∈ 𝒜.powersetCard 2, ∏ a ∈ t, ((a:ZMod (p^s)))⁻¹ = 0 := by
    rw [hw]; exact hdoubling
  have h3 := congrArg (fun z => (↑w⁻¹:ZMod (p^s)) * z) this
  simp only [mul_zero, ← mul_assoc, Units.inv_mul, one_mul] at h3
  rw [h3, mul_zero]

lemma neg_zmod_inv (m:ℕ)(y:ZMod m)(hy:IsUnit y): (-y)⁻¹ = -(y⁻¹) := by
  have h1 : (-y) * (-(y⁻¹)) = 1 := by rw [neg_mul_neg]; exact zmod_unit_mul_inv m y hy
  have hu : IsUnit (-y) := hy.neg
  calc (-y)⁻¹ = (-y)⁻¹ * ((-y)*(-(y⁻¹))) := by rw [h1, mul_one]
    _ = ((-y)⁻¹ * (-y)) * (-(y⁻¹)) := by ring
    _ = 1 * (-(y⁻¹)) := by rw [mul_comm ((-y)⁻¹) (-y), zmod_unit_mul_inv m _ hu]
    _ = -(y⁻¹) := by rw [one_mul]

lemma dvd_T1 (p s L : ℕ) [NeZero (p^s)] (hp:p.Prime)(hp5:5≤p)(hs:1≤s)(hdvd:p^s ∣ L*p) :
    (p:ℤ)^(2*s) ∣ ∑ c ∈ ((Finset.range (L*p)).filter (fun a => ¬ p ∣ a)),
        ∏ a ∈ ((Finset.range (L*p)).filter (fun a => ¬ p ∣ a)).erase c, (a:ℤ) := by
  set 𝒜 := (Finset.range (L*p)).filter (fun a => ¬ p ∣ a) with h𝒜
  set Lp := L*p with hLp
  have hmem : ∀ c, c ∈ 𝒜 ↔ (c < Lp ∧ ¬ p ∣ c) := by
    intro c; rw [h𝒜, Finset.mem_filter, Finset.mem_range]
  have hpLp : p ∣ Lp := dvd_mul_left p L
  have hge1 : ∀ c ∈ 𝒜, 1 ≤ c := by
    intro c hc; rw [hmem] at hc
    rcases Nat.eq_zero_or_pos c with h|h
    · exact absurd (h ▸ dvd_zero p) hc.2
    · exact h
  have hunitA : ∀ a ∈ 𝒜, IsUnit ((a:ZMod (p^s))) := by
    intro a ha
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr ((hmem a).mp ha).2
  have hσmem : ∀ c ∈ 𝒜, Lp - c ∈ 𝒜 := by
    intro c hc
    have hc1 := hge1 c hc
    rw [hmem] at hc ⊢
    refine ⟨by omega, ?_⟩
    intro hd
    have hcle : c ≤ Lp := by omega
    have hdc : p ∣ c := by
      have := Nat.dvd_sub hpLp hd
      rwa [Nat.sub_sub_self hcle] at this
    exact hc.2 hdc
  have hσne : ∀ c ∈ 𝒜, Lp - c ≠ c := by
    intro c hc heq
    have hc1 := hge1 c hc
    rw [hmem] at hc
    have h2c : 2 * c = Lp := by omega
    have hpc : p ∣ 2 * c := h2c ▸ hpLp
    rcases (hp.dvd_mul.mp hpc) with h | h
    · rw [Nat.prime_dvd_prime_iff_eq hp Nat.prime_two] at h; omega
    · exact hc.2 h
  have hset : ∀ c, (𝒜.erase c).erase (Lp-c) = 𝒜 \ {c, Lp - c} := by
    intro c; ext x
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hset2 : ∀ c, (𝒜.erase (Lp-c)).erase c = 𝒜 \ {c, Lp - c} := by
    intro c; ext x
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  set T1 := ∑ c ∈ 𝒜, ∏ a ∈ 𝒜.erase c, (a:ℤ) with hT1
  set U := ∑ c ∈ 𝒜, ∏ a ∈ 𝒜 \ {c, Lp - c}, (a:ℤ) with hU
  have hsplit : ∀ c ∈ 𝒜, ∏ a ∈ 𝒜.erase c, (a:ℤ)
      = ((Lp - c : ℕ):ℤ) * ∏ a ∈ 𝒜 \ {c, Lp - c}, (a:ℤ) := by
    intro c hc
    have hσc : Lp - c ∈ 𝒜.erase c := Finset.mem_erase.mpr ⟨hσne c hc, hσmem c hc⟩
    rw [← Finset.mul_prod_erase (𝒜.erase c) (fun a => (a:ℤ)) hσc, hset c]
  have hsplit2 : ∀ c ∈ 𝒜, ∏ a ∈ 𝒜.erase (Lp-c), (a:ℤ)
      = (c:ℤ) * ∏ a ∈ 𝒜 \ {c, Lp - c}, (a:ℤ) := by
    intro c hc
    have hcmem : c ∈ 𝒜.erase (Lp-c) := Finset.mem_erase.mpr ⟨(hσne c hc).symm, hc⟩
    rw [← Finset.mul_prod_erase (𝒜.erase (Lp-c)) (fun a => (a:ℤ)) hcmem, hset2 c]
  have hrei : ∑ c ∈ 𝒜, ∏ a ∈ 𝒜.erase (Lp - c), (a:ℤ) = T1 := by
    rw [hT1]
    refine Finset.sum_nbij' (fun c => Lp - c) (fun c => Lp - c) hσmem hσmem ?_ ?_ ?_
    · intro c hc; have := hge1 c hc; rw [hmem] at hc; omega
    · intro c hc; have := hge1 c hc; rw [hmem] at hc; omega
    · intro c hc; rfl
  have h2T1 : 2 * T1 = (Lp:ℤ) * U := by
    have hsum : 2 * T1 = ∑ c ∈ 𝒜, (∏ a ∈ 𝒜.erase c, (a:ℤ) + ∏ a ∈ 𝒜.erase (Lp-c), (a:ℤ)) := by
      rw [Finset.sum_add_distrib, ← hT1, hrei]; ring
    rw [hsum, hU, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    rw [hsplit c hc, hsplit2 c hc, ← add_mul]
    have hc1 := hge1 c hc
    have hcle : c ≤ Lp := by rw [hmem] at hc; omega
    have hcast : ((Lp - c : ℕ):ℤ) + (c:ℤ) = (Lp:ℤ) := by
      rw [← Nat.cast_add]; congr 1; omega
    rw [hcast]
  -- p^s ∣ U
  have hpU : (p:ℤ)^s ∣ U := by
    rw [show ((p:ℤ)^s)=((p^s:ℕ):ℤ) by push_cast;ring, ← ZMod.intCast_zmod_eq_zero_iff_dvd, hU]
    push_cast
    set D₀ := ∏ a ∈ 𝒜, ((a:ZMod (p^s))) with hD₀
    have hLpzero : ((Lp:ℕ):ZMod (p^s)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]; exact hdvd
    have hstepU : ∀ c ∈ 𝒜, ∏ a ∈ 𝒜 \ {c, Lp - c}, ((a:ZMod (p^s)))
        = - (D₀ * (((c:ZMod (p^s)))⁻¹ * ((c:ZMod (p^s)))⁻¹)) := by
      intro c hc
      have hpair : ({c, Lp - c} : Finset ℕ) ⊆ 𝒜 := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl; exacts [hc, hσmem c hc]
      have hunits : ∀ a ∈ ({c, Lp-c}:Finset ℕ), IsUnit ((a:ZMod (p^s))) :=
        fun a ha => hunitA a (hpair ha)
      rw [prod_compl_eq (p^s) 𝒜 _ (fun a => (a:ZMod (p^s))) hpair hunits,
          Finset.prod_pair (hσne c hc).symm]
      have hcle : c ≤ Lp := by have := hge1 c hc; rw [hmem] at hc; omega
      have hnegc : ((Lp - c : ℕ):ZMod (p^s)) = -((c:ZMod (p^s))) := by
        rw [Nat.cast_sub hcle, hLpzero, zero_sub]
      rw [hnegc, zmod_mul_inv' (p^s) _ _ (hunitA c hc) ((hunitA c hc).neg),
          neg_zmod_inv (p^s) _ (hunitA c hc)]
      ring
    rw [Finset.sum_congr rfl hstepU, Finset.sum_neg_distrib, ← Finset.mul_sum]
    have : ∑ c ∈ 𝒜, ((c:ZMod (p^s)))⁻¹ * ((c:ZMod (p^s)))⁻¹ = 0 :=
      sumAinv2 p s Lp hp hp5 hs hdvd
    rw [this, mul_zero, neg_zero]
  -- combine
  have hpLpZ : (p:ℤ)^s ∣ (Lp:ℤ) := by
    rw [show ((p:ℤ)^s)=((p^s:ℕ):ℤ) by push_cast;ring]; exact_mod_cast hdvd
  have hpow2 : (p:ℤ)^(2*s) ∣ 2 * T1 := by
    rw [h2T1, two_mul, pow_add]
    exact mul_dvd_mul hpLpZ hpU
  -- divide out the 2
  have hcop : Nat.Coprime (p^(2*s)) 2 :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
  have hcopZ : IsCoprime ((p:ℤ)^(2*s)) (2:ℤ) := by
    have := (Nat.isCoprime_iff_coprime).mpr hcop
    push_cast at this; exact this
  exact hcopZ.dvd_of_dvd_mul_left hpow2
lemma prod_const_add_expand (s:Finset ℕ)(y:ℤ):
    ∏ a ∈ s, (y + (a:ℤ))
      = ∑ k ∈ Finset.range (s.card+1), y^k * ∑ t ∈ s.powersetCard k, ∏ a ∈ s\t, (a:ℤ) := by
  rw [Finset.prod_add (fun _ : ℕ => y) (fun a : ℕ => (a:ℤ)) s, Finset.sum_powerset]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.prod_const, (Finset.mem_powersetCard.mp ht).2]

lemma dvd_Delta (p L B : ℕ) (hp:p.Prime)(hp5:5≤p) :
    (p:ℤ)^(3 + 3*min (padicValNat p B) (padicValNat p L)) ∣
      (∏ a ∈ (Finset.range (L*p)).filter (fun a => ¬ p ∣ a), ((B*p:ℤ) + (a:ℤ))
       - ∏ a ∈ (Finset.range (L*p)).filter (fun a => ¬ p ∣ a), (a:ℤ)) := by
  have : Fact p.Prime := ⟨hp⟩
  rcases Nat.eq_zero_or_pos B with hB0 | hBpos
  · subst hB0; simp
  set 𝒜 := (Finset.range (L*p)).filter (fun a => ¬ p ∣ a) with h𝒜
  set vB := padicValNat p B with hvB
  set vL := padicValNat p L with hvL
  set w := min vB vL with hw
  set s := vL + 1 with hs
  have : NeZero (p^s) := ⟨pow_ne_zero s hp.pos.ne'⟩
  have hdvdLp : p^s ∣ L*p := by
    rcases Nat.eq_zero_or_pos L with hL0|hLpos
    · subst hL0; simp
    · have hval : padicValNat p (L*p) = s := by
        rw [padicValNat.mul (by omega) (by omega), hs, hvL, padicValNat.self hp.one_lt]
      rw [← hval]; exact pow_padicValNat_dvd
  have hpB : (p:ℤ)^vB ∣ (B:ℤ) := by rw [hvB]; exact_mod_cast pow_padicValNat_dvd
  have hpBP : (p:ℤ)^(vB+1) ∣ (B*p:ℤ) := by
    rw [pow_succ]; exact mul_dvd_mul hpB (dvd_refl _)
  have hpBP3 : (p:ℤ)^(3*(vB+1)) ∣ (B*p:ℤ)^3 := by
    rw [mul_comm 3 (vB+1), pow_mul]; exact pow_dvd_pow_of_dvd hpBP 3
  have hpc1eq : (∑ t ∈ 𝒜.powersetCard 1, ∏ a ∈ 𝒜\t, (a:ℤ))
      = ∑ c ∈ 𝒜, ∏ a ∈ 𝒜.erase c, (a:ℤ) := by
    rw [Finset.powersetCard_one, Finset.sum_map]
    apply Finset.sum_congr rfl; intro c _; rw [Finset.erase_eq]; rfl
  have hpF1 : (p:ℤ)^(2*s) ∣ (∑ t ∈ 𝒜.powersetCard 1, ∏ a ∈ 𝒜\t, (a:ℤ)) := by
    rw [hpc1eq]; exact dvd_T1 p s L hp hp5 (by omega) hdvdLp
  have hpF2 : (p:ℤ)^s ∣ (∑ t ∈ 𝒜.powersetCard 2, ∏ a ∈ 𝒜\t, (a:ℤ)) :=
    dvd_e2 p s L hp hp5 (by omega) hdvdLp
  rw [prod_const_add_expand 𝒜 (B*p:ℤ), Finset.sum_range_succ']
  have hF0 : (B*p:ℤ)^0 * (∑ t ∈ 𝒜.powersetCard 0, ∏ a ∈ 𝒜\t, (a:ℤ)) = ∏ a ∈ 𝒜, (a:ℤ) := by
    rw [pow_zero, one_mul]; simp [Finset.powersetCard_zero]
  rw [hF0, add_sub_cancel_right]
  apply Finset.dvd_sum
  intro k _
  have hmul : ∀ (A C : ℕ) (x y : ℤ), (p:ℤ)^A ∣ x → (p:ℤ)^C ∣ y →
      (3+3*w) ≤ A + C → (p:ℤ)^(3+3*w) ∣ x * y := by
    intro A C x y hx hy hle
    have h1 : (p:ℤ)^(A+C) ∣ x*y := by rw [pow_add]; exact mul_dvd_mul hx hy
    exact dvd_trans (pow_dvd_pow (p:ℤ) hle) h1
  obtain _ | _ | k := k
  · rw [show (0:ℕ)+1 = 1 by rfl, pow_one]
    exact hmul (vB+1) (2*s) _ _ hpBP hpF1 (by omega)
  · rw [show (1:ℕ)+1 = 2 by rfl]
    refine hmul (2*(vB+1)) s _ _ ?_ hpF2 (by omega)
    rw [mul_comm 2 (vB+1), pow_mul]; exact pow_dvd_pow_of_dvd hpBP 2
  · refine hmul (3*(vB+1)) 0 _ _ ?_ (one_dvd _) (by omega)
    exact dvd_trans hpBP3 (pow_dvd_pow _ (by omega))

lemma kazan (p A B : ℕ) (hp:p.Prime)(hp5:5≤p)(hBA:B≤A) :
    (p:ℤ)^(padicValNat p (A.choose B) + (3 + 3*min (padicValNat p B) (padicValNat p (A-B))))
      ∣ ((A*p).choose (B*p) : ℤ) - (A.choose B : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  set L := A - B with hL
  have hAe : A = B + L := by omega
  set 𝒜 := (Finset.range (L*p)).filter (fun a => ¬ p ∣ a) with h𝒜
  have hpLp : p ∣ L*p := dvd_mul_left p L
  have hIR : (Finset.Icc 1 (L*p)).filter (fun a => ¬p∣a) = 𝒜 := by
    rw [h𝒜]; ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1,h2⟩,hd⟩
      refine ⟨?_,hd⟩
      rcases lt_or_eq_of_le h2 with h|h
      · exact h
      · exact absurd (h ▸ hpLp) hd
    · rintro ⟨h1,hd⟩
      refine ⟨⟨?_,by omega⟩,hd⟩
      rcases Nat.eq_zero_or_pos x with h|h
      · exact absurd (h ▸ dvd_zero p) hd
      · exact h
  -- ℕ identities
  have hF3 := F3 p A B hp.pos hBA
  have hF2 := gg_add p B L
  rw [← hAe] at hF2
  -- gg L = ∏_𝒜 (nat)
  have hggL : gg p L = ∏ a ∈ 𝒜, a := by unfold gg; rw [hIR]
  have hggP : (∏ a ∈ (Finset.Icc 1 (L*p)).filter (fun a=>¬p∣a), (B*p+a))
      = ∏ a ∈ 𝒜, (B*p + a) := by rw [hIR]
  rw [← hL] at hF3
  -- cancel gg B in ℤ
  set c := ((A*p).choose (B*p) : ℤ) with hc
  set d := (A.choose B : ℤ) with hd
  set D₀ := ∏ a ∈ 𝒜, (a:ℤ) with hD₀
  set P := ∏ a ∈ 𝒜, ((B:ℤ)*p + (a:ℤ)) with hP
  have hggBpos : 0 < gg p B := by
    rw [gg]; apply Finset.prod_pos; intro i hi
    rw [Finset.mem_filter, Finset.mem_Icc] at hi; omega
  -- from F3 & F2 : c * ggL = d * P'  (cancel ggB)
  have hcD0 : c * D₀ = d * P := by
    have hF3z : c * (gg p B : ℤ) * (gg p L : ℤ) = d * (gg p A : ℤ) := by
      rw [hc, hd]; exact_mod_cast hF3
    have hF2z : (gg p A : ℤ) = (gg p B : ℤ) * P := by
      have h2 : (gg p A : ℤ) = (gg p B : ℤ) * ∏ a ∈ 𝒜, ((B*p + a : ℕ):ℤ) := by
        rw [hIR] at hF2; exact_mod_cast hF2
      rw [h2, hP]; push_cast; rfl
    rw [hF2z] at hF3z
    have hggLz : (gg p L : ℤ) = D₀ := by rw [hggL, hD₀]; push_cast; rfl
    rw [hggLz] at hF3z
    -- hF3z : c * ggB * D₀ = d * (ggB * P)
    have hggBne : (gg p B : ℤ) ≠ 0 := by exact_mod_cast hggBpos.ne'
    have hcancel : (gg p B : ℤ) * (c * D₀) = (gg p B : ℤ) * (d * P) := by
      ring_nf; ring_nf at hF3z; linarith [hF3z]
    exact mul_left_cancel₀ hggBne hcancel
  -- Δ divisibility
  have hΔ : (p:ℤ)^(3 + 3*min (padicValNat p B) (padicValNat p L)) ∣ (P - D₀) := by
    have := dvd_Delta p L B hp hp5
    rw [← h𝒜] at this
    -- this : ... ∣ (∏_𝒜 (B*p+a) - ∏_𝒜 a) = P - D₀
    exact this
  -- p^vd ∣ d
  have hvd : (p:ℤ)^(padicValNat p (A.choose B)) ∣ d := by
    rw [hd]; exact_mod_cast pow_padicValNat_dvd
  -- (c-d)*D₀ = d*(P-D₀)
  have hkey : (c - d) * D₀ = d * (P - D₀) := by
    have := hcD0; ring_nf; ring_nf at this; linarith [this]
  -- p^N ∣ d*(P-D₀)
  have hNdvd : (p:ℤ)^(padicValNat p (A.choose B) + (3 + 3*min (padicValNat p B) (padicValNat p L)))
      ∣ d * (P - D₀) := by rw [pow_add]; exact mul_dvd_mul hvd hΔ
  rw [← hkey] at hNdvd
  -- cancel D₀ (coprime to p)
  have hcopD0 : IsCoprime ((p:ℤ)^(padicValNat p (A.choose B) + (3 + 3*min (padicValNat p B) (padicValNat p L)))) D₀ := by
    apply IsCoprime.pow_left
    rw [hD₀]
    apply IsCoprime.prod_right
    intro a ha
    rw [h𝒜, Finset.mem_filter, Finset.mem_range] at ha
    exact Nat.isCoprime_iff_coprime.mpr (hp.coprime_iff_not_dvd.mpr ha.2)
  have := hcopD0.dvd_of_dvd_mul_right hNdvd
  rw [hL] at this ⊢
  exact this



end B02R2EpochKazan
end

section
/-!
# Refined valuation bound for the reused binomial helper

This refinement follows the credited Epoch binomial proof above, retaining the
separate valuations of B and L. Valuation refinement and target integration:
Wentao Li, with AI assistance. See the accompanying SOURCE.md for provenance.
-/

namespace B02R2RefinedKazan

open Nat Finset B02R2EpochKazan

theorem dvd_Delta_refined (p L B : ℕ) (hp:p.Prime)(hp5:5≤p)
    (hLB : padicValNat p L ≤ padicValNat p B) :
    (p:ℤ)^(3 + padicValNat p B + 2 * padicValNat p L) ∣
      (∏ a ∈ (Finset.range (L*p)).filter (fun a => ¬ p ∣ a), ((B*p:ℤ) + (a:ℤ))
       - ∏ a ∈ (Finset.range (L*p)).filter (fun a => ¬ p ∣ a), (a:ℤ)) := by
  have : Fact p.Prime := ⟨hp⟩
  rcases Nat.eq_zero_or_pos B with hB0 | hBpos
  · subst hB0; simp
  set 𝒜 := (Finset.range (L*p)).filter (fun a => ¬ p ∣ a) with h𝒜
  set vB := padicValNat p B with hvB
  set vL := padicValNat p L with hvL
  set s := vL + 1 with hs
  have : NeZero (p^s) := ⟨pow_ne_zero s hp.pos.ne'⟩
  have hdvdLp : p^s ∣ L*p := by
    rcases Nat.eq_zero_or_pos L with hL0|hLpos
    · subst hL0; simp
    · have hval : padicValNat p (L*p) = s := by
        rw [padicValNat.mul (by omega) (by omega), hs, hvL, padicValNat.self hp.one_lt]
      rw [← hval]; exact pow_padicValNat_dvd
  have hpB : (p:ℤ)^vB ∣ (B:ℤ) := by rw [hvB]; exact_mod_cast pow_padicValNat_dvd
  have hpBP : (p:ℤ)^(vB+1) ∣ (B*p:ℤ) := by
    rw [pow_succ]; exact mul_dvd_mul hpB (dvd_refl _)
  have hpBP3 : (p:ℤ)^(3*(vB+1)) ∣ (B*p:ℤ)^3 := by
    rw [mul_comm 3 (vB+1), pow_mul]; exact pow_dvd_pow_of_dvd hpBP 3
  have hpc1eq : (∑ t ∈ 𝒜.powersetCard 1, ∏ a ∈ 𝒜\t, (a:ℤ))
      = ∑ c ∈ 𝒜, ∏ a ∈ 𝒜.erase c, (a:ℤ) := by
    rw [Finset.powersetCard_one, Finset.sum_map]
    apply Finset.sum_congr rfl; intro c _; rw [Finset.erase_eq]; rfl
  have hpF1 : (p:ℤ)^(2*s) ∣ (∑ t ∈ 𝒜.powersetCard 1, ∏ a ∈ 𝒜\t, (a:ℤ)) := by
    rw [hpc1eq]; exact dvd_T1 p s L hp hp5 (by omega) hdvdLp
  have hpF2 : (p:ℤ)^s ∣ (∑ t ∈ 𝒜.powersetCard 2, ∏ a ∈ 𝒜\t, (a:ℤ)) :=
    dvd_e2 p s L hp hp5 (by omega) hdvdLp
  rw [prod_const_add_expand 𝒜 (B*p:ℤ), Finset.sum_range_succ']
  have hF0 : (B*p:ℤ)^0 * (∑ t ∈ 𝒜.powersetCard 0, ∏ a ∈ 𝒜\t, (a:ℤ)) = ∏ a ∈ 𝒜, (a:ℤ) := by
    rw [pow_zero, one_mul]; simp [Finset.powersetCard_zero]
  rw [hF0, add_sub_cancel_right]
  apply Finset.dvd_sum
  intro k _
  have hmul : ∀ (A C : ℕ) (x y : ℤ), (p:ℤ)^A ∣ x → (p:ℤ)^C ∣ y →
      (3+vB+2*vL) ≤ A + C → (p:ℤ)^(3+vB+2*vL) ∣ x * y := by
    intro A C x y hx hy hle
    have h1 : (p:ℤ)^(A+C) ∣ x*y := by rw [pow_add]; exact mul_dvd_mul hx hy
    exact dvd_trans (pow_dvd_pow (p:ℤ) hle) h1
  obtain _ | _ | k := k
  · rw [show (0:ℕ)+1 = 1 by rfl, pow_one]
    exact hmul (vB+1) (2*s) _ _ hpBP hpF1 (by omega)
  · rw [show (1:ℕ)+1 = 2 by rfl]
    refine hmul (2*(vB+1)) s _ _ ?_ hpF2 (by omega)
    rw [mul_comm 2 (vB+1), pow_mul]; exact pow_dvd_pow_of_dvd hpBP 2
  · refine hmul (3*(vB+1)) 0 _ _ ?_ (one_dvd _) (by omega)
    exact dvd_trans hpBP3 (pow_dvd_pow _ (by omega))

theorem kazan_asymmetric (p A B : ℕ) (hp:p.Prime)(hp5:5≤p)(hBA:B≤A)
    (hLB : padicValNat p (A - B) ≤ padicValNat p B) :
    (p:ℤ)^(padicValNat p (A.choose B) + (3 + padicValNat p B + 2 * padicValNat p (A-B)))
      ∣ ((A*p).choose (B*p) : ℤ) - (A.choose B : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  set L := A - B with hL
  have hAe : A = B + L := by omega
  set 𝒜 := (Finset.range (L*p)).filter (fun a => ¬ p ∣ a) with h𝒜
  have hpLp : p ∣ L*p := dvd_mul_left p L
  have hIR : (Finset.Icc 1 (L*p)).filter (fun a => ¬p∣a) = 𝒜 := by
    rw [h𝒜]; ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1,h2⟩,hd⟩
      refine ⟨?_,hd⟩
      rcases lt_or_eq_of_le h2 with h|h
      · exact h
      · exact absurd (h ▸ hpLp) hd
    · rintro ⟨h1,hd⟩
      refine ⟨⟨?_,by omega⟩,hd⟩
      rcases Nat.eq_zero_or_pos x with h|h
      · exact absurd (h ▸ dvd_zero p) hd
      · exact h
  -- ℕ identities
  have hF3 := F3 p A B hp.pos hBA
  have hF2 := gg_add p B L
  rw [← hAe] at hF2
  -- gg L = ∏_𝒜 (nat)
  have hggL : gg p L = ∏ a ∈ 𝒜, a := by unfold gg; rw [hIR]
  have hggP : (∏ a ∈ (Finset.Icc 1 (L*p)).filter (fun a=>¬p∣a), (B*p+a))
      = ∏ a ∈ 𝒜, (B*p + a) := by rw [hIR]
  rw [← hL] at hF3
  -- cancel gg B in ℤ
  set c := ((A*p).choose (B*p) : ℤ) with hc
  set d := (A.choose B : ℤ) with hd
  set D₀ := ∏ a ∈ 𝒜, (a:ℤ) with hD₀
  set P := ∏ a ∈ 𝒜, ((B:ℤ)*p + (a:ℤ)) with hP
  have hggBpos : 0 < gg p B := by
    rw [gg]; apply Finset.prod_pos; intro i hi
    rw [Finset.mem_filter, Finset.mem_Icc] at hi; omega
  -- from F3 & F2 : c * ggL = d * P'  (cancel ggB)
  have hcD0 : c * D₀ = d * P := by
    have hF3z : c * (gg p B : ℤ) * (gg p L : ℤ) = d * (gg p A : ℤ) := by
      rw [hc, hd]; exact_mod_cast hF3
    have hF2z : (gg p A : ℤ) = (gg p B : ℤ) * P := by
      have h2 : (gg p A : ℤ) = (gg p B : ℤ) * ∏ a ∈ 𝒜, ((B*p + a : ℕ):ℤ) := by
        rw [hIR] at hF2; exact_mod_cast hF2
      rw [h2, hP]; push_cast; rfl
    rw [hF2z] at hF3z
    have hggLz : (gg p L : ℤ) = D₀ := by rw [hggL, hD₀]; push_cast; rfl
    rw [hggLz] at hF3z
    -- hF3z : c * ggB * D₀ = d * (ggB * P)
    have hggBne : (gg p B : ℤ) ≠ 0 := by exact_mod_cast hggBpos.ne'
    have hcancel : (gg p B : ℤ) * (c * D₀) = (gg p B : ℤ) * (d * P) := by
      ring_nf; ring_nf at hF3z; linarith [hF3z]
    exact mul_left_cancel₀ hggBne hcancel
  -- Δ divisibility
  have hΔ : (p:ℤ)^(3 + padicValNat p B + 2 * padicValNat p L) ∣ (P - D₀) := by
    have := dvd_Delta_refined p L B hp hp5 hLB
    rw [← h𝒜] at this
    -- this : ... ∣ (∏_𝒜 (B*p+a) - ∏_𝒜 a) = P - D₀
    exact this
  -- p^vd ∣ d
  have hvd : (p:ℤ)^(padicValNat p (A.choose B)) ∣ d := by
    rw [hd]; exact_mod_cast pow_padicValNat_dvd
  -- (c-d)*D₀ = d*(P-D₀)
  have hkey : (c - d) * D₀ = d * (P - D₀) := by
    have := hcD0; ring_nf; ring_nf at this; linarith [this]
  -- p^N ∣ d*(P-D₀)
  have hNdvd : (p:ℤ)^(padicValNat p (A.choose B) + (3 + padicValNat p B + 2 * padicValNat p L))
      ∣ d * (P - D₀) := by rw [pow_add]; exact mul_dvd_mul hvd hΔ
  rw [← hkey] at hNdvd
  -- cancel D₀ (coprime to p)
  have hcopD0 : IsCoprime ((p:ℤ)^(padicValNat p (A.choose B) + (3 + padicValNat p B + 2 * padicValNat p L))) D₀ := by
    apply IsCoprime.pow_left
    rw [hD₀]
    apply IsCoprime.prod_right
    intro a ha
    rw [h𝒜, Finset.mem_filter, Finset.mem_range] at ha
    exact Nat.isCoprime_iff_coprime.mpr (hp.coprime_iff_not_dvd.mpr ha.2)
  have := hcopD0.dvd_of_dvd_mul_right hNdvd
  rw [hL] at this ⊢
  exact this



/-- Symmetry puts the larger valuation in the expansion parameter. -/
theorem kazan_refined (p A B : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hBA : B ≤ A) :
    (p : ℤ) ^ (padicValNat p (A.choose B) +
      (3 + max (padicValNat p B) (padicValNat p (A - B)) +
        2 * min (padicValNat p B) (padicValNat p (A - B)))) ∣
      ((A * p).choose (B * p) : ℤ) - (A.choose B : ℤ) := by
  by_cases h : padicValNat p (A - B) ≤ padicValNat p B
  · simpa only [max_eq_left h, min_eq_right h] using kazan_asymmetric p A B hp hp5 hBA h
  · have hh := kazan_asymmetric p A (A - B) hp hp5 (Nat.sub_le _ _)
      (by rw [Nat.sub_sub_self hBA]; omega)
    have hs : A.choose (A - B) = A.choose B := Nat.choose_symm hBA
    have hsp : (A * p).choose ((A - B) * p) = (A * p).choose (B * p) := by
      rw [Nat.sub_mul, Nat.choose_symm (Nat.mul_le_mul_right p hBA)]
    rw [Nat.sub_sub_self hBA, hs, hsp] at hh
    simpa only [max_eq_right (by omega : padicValNat p B ≤ padicValNat p (A - B)),
      min_eq_left (by omega : padicValNat p B ≤ padicValNat p (A - B))] using hh


end B02R2RefinedKazan
end

section
/-!
# Unit-index cancellation for the shifted-square sum

This develops the elementary inverse-square and summation-by-parts part of the
Coster route for A003161/A003162. It reuses the credited inverse-square helper in
the Epoch helper section above. New Lean development: Wentao Li, with AI assistance.
-/

namespace B02R2ShiftedUnits

open Finset B02R2EpochKazan

/-- An integer representative of an inverse modulo a prime power. -/
def invLift (p R j : ℕ) : ℤ := ((j : ZMod (p ^ R))⁻¹).val

/-- The inverse representative satisfies its defining congruence. -/
theorem invLift_spec (p R j : ℕ) (hp : p.Prime) (hj : ¬p ∣ j) :
    (p : ℤ) ^ R ∣ (j : ℤ) * invLift p R j - 1 := by
  have : NeZero (p ^ R) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hu : IsUnit (j : ZMod (p ^ R)) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (hp.coprime_iff_not_dvd.mpr hj).symm.pow_right R
  rw [← Nat.cast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_one, invLift,
    ZMod.natCast_zmod_val, zmod_unit_mul_inv _ _ hu, sub_self]

/-- Reducing an inverse representative to a smaller modulus preserves the inverse. -/
theorem invLift_cast (p R s j : ℕ) (hp : p.Prime) (hsR : s ≤ R) (hj : ¬p ∣ j) :
    (invLift p R j : ZMod (p ^ s)) = (j : ZMod (p ^ s))⁻¹ := by
  have hu : IsUnit (j : ZMod (p ^ s)) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (hp.coprime_iff_not_dvd.mpr hj).symm.pow_right s
  have hd := dvd_trans (pow_dvd_pow (p : ℤ) hsR) (invLift_spec p R j hp hj)
  rw [← Nat.cast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at hd
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_one,
    sub_eq_zero] at hd
  obtain ⟨u, hu⟩ := hu
  have hh := congrArg (fun x : ZMod (p ^ s) => (↑u⁻¹ : ZMod (p ^ s)) * x) hd
  rw [← hu, ← mul_assoc, Units.inv_mul, one_mul, mul_one] at hh
  rw [hh, ← hu, ZMod.inv_coe_unit]

/-- Inverse-square weights, with zero weight at indices divisible by the prime. -/
def inverseSquare (p R j : ℕ) : ℤ := if p ∣ j then 0 else invLift p R j ^ 2

/-- Each complete prime-power block has a divisible inverse-square sum. -/
theorem inverseSquare_prefix_dvd (p R s L : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hsR : s ≤ R) (hL : p ^ s ∣ L) :
    (p : ℤ) ^ s ∣ ∑ j ∈ range L, inverseSquare p R j := by
  rcases s with _ | s
  · simp
  have : NeZero (p ^ (s + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [← Nat.cast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  have hh := sumAinv2 p (s + 1) L hp hp5 (by omega) hL
  rw [sum_filter] at hh
  convert hh using 1
  apply sum_congr rfl
  intro j _hj
  by_cases hj : p ∣ j
  · simp [inverseSquare, hj]
  · simp [inverseSquare, hj, invLift_cast p R (s + 1) j hp hsR hj, sq]

/-- Shifted binomial coefficients appearing in the square sum. -/
def shiftedBinomial (N j : ℕ) : ℕ := (N + j - 1).choose j

/-- Prefix products used as weights in summation by parts. -/
def prefixBinomial (N j : ℕ) : ℕ := (N + j).choose j

/-- The adjacent-binomial identity with natural subtraction made explicit. -/
theorem shifted_mul (N j : ℕ) (hj : 0 < j) :
    shiftedBinomial N j * j = N * prefixBinomial N (j - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  simpa [shiftedBinomial, prefixBinomial, Nat.succ_eq_add_one, Nat.add_sub_cancel,
    Nat.add_sub_cancel_right, mul_comm] using Nat.choose_succ_right_eq (N + k) k

/-- The valuation bound for each shifted coefficient. -/
theorem shifted_dvd (p r N j : ℕ) (hp : p.Prime) (hN : 0 < N) (hj : 0 < j)
    (hNr : p ^ r ∣ N) : p ^ (r - padicValNat p j) ∣ shiftedBinomial N j := by
  have : Fact p.Prime := ⟨hp⟩
  have hb : shiftedBinomial N j ≠ 0 := Nat.choose_ne_zero (by omega)
  have hd : prefixBinomial N (j - 1) ≠ 0 := Nat.choose_ne_zero (by omega)
  have hh := congrArg (padicValNat p) (shifted_mul N j hj)
  rw [padicValNat.mul hb hj.ne', padicValNat.mul hN.ne' hd] at hh
  have hnval := (padicValNat_dvd_iff_le hN.ne').mp hNr
  apply (padicValNat_dvd_iff_le hb).mpr
  omega

/-- Successive prefix products differ by the shifted coefficient. -/
theorem prefix_step (N j : ℕ) (hj : 0 < j) :
    prefixBinomial N j = prefixBinomial N (j - 1) + shiftedBinomial N j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  simp only [prefixBinomial, shiftedBinomial, Nat.succ_eq_add_one, Nat.add_sub_cancel]
  exact Nat.choose_succ_succ (N + k) k

/-- Squared prefix products are the integer weights for inverse-square cancellation. -/
def squareWeight (N j : ℕ) : ℤ := (prefixBinomial N (j - 1) : ℤ) ^ 2

/-- A weight jump retains the needed prime-power divisibility. -/
theorem squareWeight_step_dvd (p r N j : ℕ) (hp : p.Prime) (hN : 0 < N)
    (hNr : p ^ r ∣ N) :
    (p : ℤ) ^ (r - padicValNat p j) ∣ squareWeight N (j + 1) - squareWeight N j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [squareWeight]
  have hh : (p : ℤ) ^ (r - padicValNat p j) ∣ (shiftedBinomial N j : ℤ) := by
    exact_mod_cast shifted_dvd p r N j hp hN hj hNr
  have heq : squareWeight N (j + 1) - squareWeight N j =
      (shiftedBinomial N j : ℤ) *
        ((prefixBinomial N j : ℤ) + (prefixBinomial N (j - 1) : ℤ)) := by
    simp only [squareWeight, Nat.add_sub_cancel, prefix_step N j hj, Nat.cast_add]
    ring
  rw [heq]
  exact dvd_mul_of_dvd_left hh _

/-- Summation by parts gives the extra factor missing from termwise estimates. -/
theorem weighted_inverseSquare_dvd (p R r N : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hrR : r ≤ R) (hN : 0 < N) (hNr : p ^ r ∣ N) :
    (p : ℤ) ^ r ∣ ∑ j ∈ range N, squareWeight N j * inverseSquare p R j := by
  have hparts := sum_range_by_parts (squareWeight N) (inverseSquare p R) N
  simp only [smul_eq_mul] at hparts
  rw [hparts]
  apply dvd_sub
  · exact dvd_mul_of_dvd_right (inverseSquare_prefix_dvd p R r N hp hp5 hrR hNr) _
  · apply dvd_sum
    intro j _hj
    let s := min r (padicValNat p j)
    have hsR : s ≤ R := le_trans (min_le_left _ _) hrR
    have hsval : s ≤ padicValNat p j := min_le_right _ _
    have hsr : s ≤ r := min_le_left _ _
    have hjpow : p ^ s ∣ j := dvd_trans (pow_dvd_pow p hsval) pow_padicValNat_dvd
    have hg : (p : ℤ) ^ s ∣ ∑ k ∈ range (j + 1), inverseSquare p R k := by
      by_cases hs : s = 0
      · simp [hs]
      have hpj : p ∣ j := dvd_trans (dvd_pow_self p hs) hjpow
      rw [sum_range_succ, inverseSquare, ite_eq_left hpj, add_zero]
      exact inverseSquare_prefix_dvd p R s j hp hp5 hsR hjpow
    have hw := squareWeight_step_dvd p r N j hp hN hNr
    have he : r - s = r - padicValNat p j := by dsimp [s]; omega
    rw [← he] at hw
    have hh := mul_dvd_mul hw hg
    rw [← pow_add, Nat.sub_add_cancel hsr] at hh
    exact hh

/-- At unit indices the square is the product of its integer weight and inverse square. -/
theorem shifted_unit_cast (p R N j : ℕ) (hp : p.Prime) (hj : ¬p ∣ j) :
    (shiftedBinomial N j : ZMod (p ^ R)) ^ 2 =
      (N : ZMod (p ^ R)) ^ 2 * (squareWeight N j : ZMod (p ^ R)) *
        (inverseSquare p R j : ZMod (p ^ R)) := by
  have hjpos : 0 < j := Nat.pos_of_ne_zero (by rintro rfl; exact hj (dvd_zero _))
  have hu : IsUnit (j : ZMod (p ^ R)) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (hp.coprime_iff_not_dvd.mpr hj).symm.pow_right R
  have hh : (shiftedBinomial N j : ZMod (p ^ R)) * j =
      (N : ZMod (p ^ R)) * prefixBinomial N (j - 1) := by
    simpa only [Nat.cast_mul] using congrArg (fun x : ℕ => (x : ZMod (p ^ R)))
      (shifted_mul N j hjpos)
  have hc : (shiftedBinomial N j : ZMod (p ^ R)) =
      (N : ZMod (p ^ R)) * prefixBinomial N (j - 1) * (j : ZMod (p ^ R))⁻¹ := by
    calc
      (shiftedBinomial N j : ZMod (p ^ R)) =
          (shiftedBinomial N j : ZMod (p ^ R)) * ((j : ZMod (p ^ R)) * (j : ZMod (p ^ R))⁻¹) := by
            rw [zmod_unit_mul_inv _ _ hu, mul_one]
      _ = _ := by rw [← mul_assoc, hh]
  rw [hc]
  simp only [squareWeight, inverseSquare, hj, ↓reduceIte, Int.cast_pow, Int.cast_natCast,
    invLift_cast p R R j hp le_rfl hj]
  ring

/-- The complete sum over indices prime to `p` vanishes to cubic order. -/
theorem shifted_units_dvd (p r N : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) (hNr : p ^ r ∣ N) :
    (p : ℤ) ^ (3 * r) ∣
      ∑ j ∈ (range N).filter (fun j => ¬p ∣ j), (shiftedBinomial N j : ℤ) ^ 2 := by
  have hw := weighted_inverseSquare_dvd p (3 * r) r N hp hp5 (by omega) hN hNr
  have hn : (p : ℤ) ^ r ∣ (N : ℤ) := by exact_mod_cast hNr
  have hn2 : (p : ℤ) ^ (2 * r) ∣ (N : ℤ) ^ 2 := by
    rw [Nat.mul_comm 2 r, pow_mul]
    exact pow_dvd_pow_of_dvd hn 2
  have hh : (p : ℤ) ^ (3 * r) ∣
      (N : ℤ) ^ 2 * ∑ j ∈ range N, squareWeight N j * inverseSquare p (3 * r) j := by
    have hh := mul_dvd_mul hn2 hw
    rw [← pow_add, show 2 * r + r = 3 * r by omega] at hh
    exact hh
  rw [← Nat.cast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at hh ⊢
  push_cast at hh ⊢
  rw [sum_filter]
  calc
    (∑ j ∈ range N, if ¬p ∣ j then (shiftedBinomial N j : ZMod (p ^ (3 * r))) ^ 2 else 0) =
        ∑ j ∈ range N, (N : ZMod (p ^ (3 * r))) ^ 2 *
          (squareWeight N j : ZMod (p ^ (3 * r))) * (inverseSquare p (3 * r) j : ZMod (p ^ (3 * r))) := by
      apply sum_congr rfl
      intro j _hj
      by_cases hj : p ∣ j
      · simp [inverseSquare, hj]
      · simpa only [hj, not_false_eq_true, ↓reduceIte] using shifted_unit_cast p (3 * r) N j hp hj
    _ = (N : ZMod (p ^ (3 * r))) ^ 2 *
        ∑ j ∈ range N, (squareWeight N j : ZMod (p ^ (3 * r))) *
          (inverseSquare p (3 * r) j : ZMod (p ^ (3 * r))) := by rw [mul_sum]; simp only [mul_assoc]
    _ = 0 := hh


end B02R2ShiftedUnits
end

section
/-!
# Scaling the shifted-binomial squares

This specializes the refined binomial congruence to the shifted coefficients.
The arithmetic is part of the known Coster route. The imported general helper's
public proof provenance is documented in the Epoch helper section above and the valuation refinement section above.
New Lean development: Wentao Li, with AI assistance.
-/

namespace B02R2ShiftedScaling

open B02R2ShiftedUnits B02R2RefinedKazan

/-- Relate a shifted coefficient to the adjacent unshifted coefficient. -/
theorem shifted_upper_mul (N j : ℕ) (hN : 0 < N) :
    (N + j) * shiftedBinomial N j = N * (N + j).choose N := by
  have hh := Nat.choose_mul_succ_eq (N + j - 1) j
  rw [show N + j - 1 + 1 = N + j by omega, show N + j - j = N by omega] at hh
  have hs : (N + j).choose j = (N + j).choose N := Nat.choose_symm_add.symm
  rw [hs] at hh
  simpa only [shiftedBinomial, mul_comm] using hh

/-- The same adjacent identity after cancelling the common scale factor. -/
theorem shifted_scaled_upper_mul (p N j : ℕ) (hp : 0 < p) (hN : 0 < N) :
    (N + j) * shiftedBinomial (N * p) (j * p) = N * ((N + j) * p).choose (N * p) := by
  have hh := shifted_upper_mul (N * p) (j * p) (Nat.mul_pos hN hp)
  rw [← Nat.add_mul] at hh
  apply Nat.eq_of_mul_eq_mul_left hp
  calc
    p * ((N + j) * shiftedBinomial (N * p) (j * p)) =
        ((N + j) * p) * shiftedBinomial (N * p) (j * p) := by ring
    _ = (N * p) * ((N + j) * p).choose (N * p) := hh
    _ = p * (N * ((N + j) * p).choose (N * p)) := by ring

/-- The shifted coefficient inherits a relative congruence from the binomial helper. -/
theorem shifted_scale_dvd (p N j : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hN : 0 < N) :
    (p : ℤ) ^ (padicValNat p (shiftedBinomial N j) +
      (3 + max (padicValNat p N) (padicValNat p j) +
        2 * min (padicValNat p N) (padicValNat p j))) ∣
      (shiftedBinomial (N * p) (j * p) : ℤ) - (shiftedBinomial N j : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  let D : ℤ := (shiftedBinomial (N * p) (j * p) : ℤ) - (shiftedBinomial N j : ℤ)
  change _ ∣ D
  by_cases hD : D = 0
  · rw [hD]; exact dvd_zero _
  have hb : shiftedBinomial N j ≠ 0 := Nat.choose_ne_zero (by omega)
  have hc : (N + j).choose N ≠ 0 := Nat.choose_ne_zero (by omega)
  have hA : N + j ≠ 0 := by omega
  have hval := congrArg (padicValNat p) (shifted_upper_mul N j hN)
  rw [padicValNat.mul hA hb, padicValNat.mul hN.ne' hc] at hval
  have hk := kazan_refined p (N + j) N hp hp5 (by omega)
  rw [Nat.add_sub_cancel_left] at hk
  have hn : (p : ℤ) ^ padicValNat p N ∣ (N : ℤ) := by
    exact_mod_cast pow_padicValNat_dvd
  have hprod := mul_dvd_mul hn hk
  rw [← pow_add] at hprod
  have hsmall : ((N + j : ℕ) : ℤ) * (shiftedBinomial N j : ℤ) =
      (N : ℤ) * ((N + j).choose N : ℤ) := by
    exact_mod_cast shifted_upper_mul N j hN
  have hlarge : ((N + j : ℕ) : ℤ) * (shiftedBinomial (N * p) (j * p) : ℤ) =
      (N : ℤ) * (((N + j) * p).choose (N * p) : ℤ) := by
    exact_mod_cast shifted_scaled_upper_mul p N j hp.pos hN
  have heq : ((N + j : ℕ) : ℤ) * D =
      (N : ℤ) * ((((N + j) * p).choose (N * p) : ℤ) - ((N + j).choose N : ℤ)) := by
    change ((N + j : ℕ) : ℤ) *
      ((shiftedBinomial (N * p) (j * p) : ℤ) - (shiftedBinomial N j : ℤ)) = _
    rw [mul_sub, hlarge, hsmall, mul_sub]
  rw [← heq] at hprod
  have hAN : ((N + j : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hA
  have hv := (padicValInt_dvd_iff _ _).mp hprod
  rcases hv with hz | hv
  · exact False.elim ((mul_ne_zero hAN hD) hz)
  · rw [padicValInt.mul hAN hD, padicValInt.of_nat] at hv
    apply (padicValInt_dvd_iff _ _).mpr
    right
    omega

/-- Squaring gives cubic precision at every index, including unequal valuations. -/
theorem shifted_square_scale_dvd (p r N j : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) (hNr : p ^ r ∣ N) :
    (p : ℤ) ^ (3 * (r + 1)) ∣
      (shiftedBinomial (N * p) (j * p) : ℤ) ^ 2 - (shiftedBinomial N j : ℤ) ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [shiftedBinomial]
  let b := padicValNat p (shiftedBinomial N j)
  let E := 3 + max (padicValNat p N) (padicValNat p j) +
    2 * min (padicValNat p N) (padicValNat p j)
  have hD : (p : ℤ) ^ (b + E) ∣
      (shiftedBinomial (N * p) (j * p) : ℤ) - (shiftedBinomial N j : ℤ) :=
    shifted_scale_dvd p N j hp hp5 hN
  have hb : (p : ℤ) ^ b ∣ (shiftedBinomial N j : ℤ) := by
    exact_mod_cast pow_padicValNat_dvd
  have hD' := dvd_trans (pow_dvd_pow (p : ℤ) (Nat.le_add_right b E)) hD
  have hsum : (p : ℤ) ^ b ∣
      (shiftedBinomial (N * p) (j * p) : ℤ) + (shiftedBinomial N j : ℤ) := by
    have hh := hD'.add (dvd_mul_of_dvd_right hb 2)
    have heq : ((shiftedBinomial (N * p) (j * p) : ℤ) - (shiftedBinomial N j : ℤ)) +
        2 * (shiftedBinomial N j : ℤ) =
        (shiftedBinomial (N * p) (j * p) : ℤ) + (shiftedBinomial N j : ℤ) := by ring
    rwa [heq] at hh
  have hmul := mul_dvd_mul hD hsum
  rw [← pow_add] at hmul
  have hbne : shiftedBinomial N j ≠ 0 := Nat.choose_ne_zero (by omega)
  have hbval := (padicValNat_dvd_iff_le hbne).mp (shifted_dvd p r N j hp hN hj hNr)
  have hnval := (padicValNat_dvd_iff_le hN.ne').mp hNr
  have he : 3 * (r + 1) ≤ b + E + b := by dsimp [b, E]; omega
  have hd := dvd_trans (pow_dvd_pow (p : ℤ) he) hmul
  have heq : ((shiftedBinomial (N * p) (j * p) : ℤ) - (shiftedBinomial N j : ℤ)) *
      ((shiftedBinomial (N * p) (j * p) : ℤ) + (shiftedBinomial N j : ℤ)) =
      (shiftedBinomial (N * p) (j * p) : ℤ) ^ 2 - (shiftedBinomial N j : ℤ) ^ 2 := by ring
  rwa [heq] at hd


end B02R2ShiftedScaling
end

section
/-!
# Shifted-square supercongruence

The sum is split into indices divisible by the prime and indices prime to it.
The imported scaling and cancellation lemmas supply cubic precision for both parts.
This is formalization of the known Coster congruence needed for A003161/A003162.
New Lean development: Wentao Li, with AI assistance.
-/

namespace B02R2ShiftedCongruence

open Finset B02R2ShiftedUnits B02R2ShiftedScaling B02R2Ballot

/-- The shifted-square sum indexed by its positive length. -/
def shiftedSum (N : ℕ) : ℤ := ∑ j ∈ range N, (shiftedBinomial N j : ℤ) ^ 2

/-- Reindex the summands whose indices are divisible by the prime. -/
theorem sum_multiples (p N : ℕ) (hp : 0 < p) (f : ℕ → ℤ) :
    ∑ j ∈ (range (N * p)).filter (fun j => p ∣ j), f j =
      ∑ j ∈ range N, f (j * p) := by
  have hset : (range (N * p)).filter (fun j => p ∣ j) = (range N).image (fun j => j * p) := by
    ext j
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hj, ⟨k, rfl⟩⟩
      refine ⟨k, ?_, by ring⟩
      exact (Nat.mul_lt_mul_left hp).mp (by simpa only [mul_comm] using hj)
    · rintro ⟨k, hk, rfl⟩
      exact ⟨Nat.mul_lt_mul_of_pos_right hk hp, dvd_mul_left p k⟩
  rw [hset, sum_image]
  intro a _ha b _hb hab
  exact Nat.eq_of_mul_eq_mul_right hp hab

/-- Cubic precision survives one scaling step for the complete shifted-square sum. -/
theorem shiftedSum_step_dvd (p r N : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) (hNr : p ^ r ∣ N) :
    (p : ℤ) ^ (3 * (r + 1)) ∣ shiftedSum (N * p) - shiftedSum N := by
  have hon : (p : ℤ) ^ (3 * (r + 1)) ∣
      (∑ j ∈ (range (N * p)).filter (fun j => p ∣ j), (shiftedBinomial (N * p) j : ℤ) ^ 2) -
        shiftedSum N := by
    rw [sum_multiples p N hp.pos, shiftedSum, ← sum_sub_distrib]
    apply dvd_sum
    intro j _hj
    exact shifted_square_scale_dvd p r N j hp hp5 hN hNr
  have hNp : p ^ (r + 1) ∣ N * p := by
    rw [pow_succ]
    exact mul_dvd_mul hNr (dvd_refl _)
  have hoff := shifted_units_dvd p (r + 1) (N * p) hp hp5 (Nat.mul_pos hN hp.pos) hNp
  have hsplit : shiftedSum (N * p) =
      (∑ j ∈ (range (N * p)).filter (fun j => p ∣ j), (shiftedBinomial (N * p) j : ℤ) ^ 2) +
      ∑ j ∈ (range (N * p)).filter (fun j => ¬p ∣ j), (shiftedBinomial (N * p) j : ℤ) ^ 2 := by
    exact (sum_filter_add_sum_filter_not (range (N * p)) (fun j => p ∣ j) _).symm
  rw [hsplit]
  have hh := hon.add hoff
  have heq :
      ((∑ j ∈ (range (N * p)).filter (fun j => p ∣ j), (shiftedBinomial (N * p) j : ℤ) ^ 2) - shiftedSum N) +
          (∑ j ∈ (range (N * p)).filter (fun j => ¬p ∣ j), (shiftedBinomial (N * p) j : ℤ) ^ 2) =
      ((∑ j ∈ (range (N * p)).filter (fun j => p ∣ j), (shiftedBinomial (N * p) j : ℤ) ^ 2) +
          (∑ j ∈ (range (N * p)).filter (fun j => ¬p ∣ j), (shiftedBinomial (N * p) j : ℤ) ^ 2)) - shiftedSum N := by
    ring
  rwa [heq] at hh

/-- Match the shifted-square definition used by the normalization files. -/
theorem shiftedSum_eq_shiftedSquares (N : ℕ) (hN : 0 < N) :
    shiftedSum N = shiftedSquares (N - 1) := by
  simp only [shiftedSum, shiftedSquares, Nat.sub_add_cancel (by omega : 1 ≤ N)]
  apply sum_congr rfl
  intro j _hj
  congr 2
  unfold shiftedBinomial
  congr 1
  omega

/-- The full shifted-square tower, with the exact quantifiers required by both targets. -/
theorem shiftedSquares_tower (n k p : ℕ) (hn : 0 < n) (hk : 0 < k)
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    shiftedSquares (n * p ^ k - 1) ≡ shiftedSquares (n * p ^ (k - 1) - 1)
      [ZMOD (p : ℤ) ^ (3 * k)] := by
  let M := n * p ^ (k - 1)
  have hM : 0 < M := Nat.mul_pos hn (pow_pos hp.pos _)
  have hh := shiftedSum_step_dvd p (k - 1) M hp hp5 hM (dvd_mul_left _ _)
  rw [Nat.sub_add_cancel hk] at hh
  have hindex : n * p ^ k = M * p := by
    dsimp [M]
    rw [Nat.mul_assoc, ← pow_succ, Nat.sub_add_cancel hk]
  rw [shiftedSum_eq_shiftedSquares (M * p) (Nat.mul_pos hM hp.pos),
    shiftedSum_eq_shiftedSquares M hM] at hh
  rw [hindex, Int.modEq_iff_dvd]
  simpa only [neg_sub] using (dvd_neg.mpr hh)


end B02R2ShiftedCongruence
end

section
/-!
# Central-binomial arithmetic input for A003161/A003162

This specializes the public Epoch `kazan` helper. The mathematical congruence is
classical (Jacobsthal–Kazandzidis). See the Epoch helper section above for the reused Lean proof's
exact provenance. Target specialization: Wentao Li, with AI assistance.
-/

namespace B02R2Central

open B02R2Ballot B02R2A003161

/-- The central binomial coefficient at a positive index is twice `halfCentral`. -/
theorem central_eq_two_half_pos (N : ℕ) (hN : 0 < N) :
    ((2 * N).choose N : ℤ) = 2 * halfCentral (N - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  simpa [Nat.succ_eq_add_one, Nat.mul_add] using central_eq_two_half n

/-- Central-binomial coefficients satisfy the full cubic prime-power tower. -/
theorem centralBinomial_tower : CubicTower (fun N => ((2 * N).choose N : ℤ)) := by
  intro n k p hn hk hp hp5
  have : Fact p.Prime := ⟨hp⟩
  let M := n * p ^ (k - 1)
  have hM : 0 < M := Nat.mul_pos hn (pow_pos hp.pos _)
  have hval : k - 1 ≤ padicValNat p M := by
    apply (padicValNat_dvd_iff_le hM.ne').mp
    exact dvd_mul_left _ _
  have hstep := B02R2EpochKazan.kazan p (2 * M) M hp hp5 (by omega)
  rw [show 2 * M - M = M by omega, min_self] at hstep
  have hpow : 3 * k ≤ padicValNat p ((2 * M).choose M) +
      (3 + 3 * padicValNat p M) := by omega
  have hdiv := dvd_trans (pow_dvd_pow (p : ℤ) hpow) hstep
  have hindex : n * p ^ k = M * p := by
    dsimp [M]
    rw [Nat.mul_assoc, ← pow_succ, Nat.sub_add_cancel hk]
  change ((2 * (n * p ^ k)).choose (n * p ^ k) : ℤ) ≡ ((2 * M).choose M : ℤ)
    [ZMOD (p : ℤ) ^ (3 * k)]
  rw [hindex, ← Nat.mul_assoc]
  rw [Int.modEq_iff_dvd]
  simpa only [neg_sub] using (dvd_neg.mpr hdiv)

/-- The half-central-binomial input of the joint reduction is unconditional. -/
theorem halfCentral_tower : CubicTower (fun N => halfCentral (N - 1)) := by
  intro n k p hn hk hp hp5
  apply cancel_two hp hp5
  rw [← central_eq_two_half_pos _ (Nat.mul_pos hn (pow_pos hp.pos _)),
    ← central_eq_two_half_pos _ (Nat.mul_pos hn (pow_pos hp.pos _))]
  exact centralBinomial_tower n k p hn hk hp hp5


end B02R2Central
end

section
/-!
# A003161: exact supercongruence

The cubic identity is formalized in the normalization section above. The two arithmetic
towers are proved in the central-binomial section above and the shifted-square section above.
The final theorem uses the exact frozen natural-number source definition.

Known mathematics: Coster; Miana, Ohtsuka and Romero; Amdeberhan and Ekhad.
The conditional-transfer design continues Wentao Li's b01 derivation.
Lean development: Wentao Li, with AI assistance.
-/

namespace B02R2A003161

open Finset B02R2Ballot

/-- Ballot entries in the first half of a binomial row are nonnegative. -/
theorem ballotTerm_nonneg (m k : ℕ) (hk : k ≤ m / 2) : 0 ≤ ballotTerm m k := by
  cases k with
  | zero => simp [ballotTerm]
  | succ k =>
    have hle := Nat.choose_le_succ_of_lt_half_left (by omega : k < m / 2)
    simp only [ballotTerm, Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
    exact sub_nonneg.mpr (by exact_mod_cast hle)

/-- The natural-number source equals the integer cubic sum; no truncation occurs. -/
theorem raw_cast (m : ℕ) :
    (OeisA3161.a m : ℤ) = ∑ k ∈ range (m / 2 + 1), ballotTerm m k ^ 3 := by
  simp only [OeisA3161.a, Nat.cast_sum]
  apply sum_congr rfl
  intro k hk
  change ((ballotTerm m k ^ 3).toNat : ℤ) = ballotTerm m k ^ 3
  exact Int.toNat_of_nonneg (pow_nonneg (ballotTerm_nonneg m k (by simpa using hk)) 3)

/-- The exact odd-index source factors by the central normalization denominator. -/
theorem raw_odd (n : ℕ) :
    (OeisA3161.b (n + 1) : ℤ) =
      halfCentral n * (4 * halfCentral n ^ 2 - 3 * crossSum n) := by
  rw [OeisA3161.b, show 2 * (n + 1) - 1 = 2 * n + 1 by omega, raw_cast,
    show (2 * n + 1) / 2 = n by omega]
  exact cubic_odd n

/-- The unconditional normalization identity required by the supercongruence transfer. -/
theorem raw_normalization (n : ℕ) :
    2 * (OeisA3161.b (n + 1) : ℤ) =
      halfCentral n * (3 * shiftedSquares n - halfCentral n ^ 2) := by
  rw [raw_odd]
  have hh := crossSum_normalization n
  linear_combination -3 * halfCentral n * hh

/-- Rewrite the unconditional normalization at every positive source index. -/
theorem raw_normalization_pos (N : ℕ) (hN : 0 < N) :
    2 * (OeisA3161.b N : ℤ) =
      halfCentral (N - 1) * (3 * shiftedSquares (N - 1) - halfCentral (N - 1) ^ 2) := by
  simpa [Nat.sub_add_cancel (by omega : 1 ≤ N)] using raw_normalization (N - 1)

/-- Two arithmetic towers imply the exact A003161 conclusion. -/
theorem conjecture_of_coster
    (hs : CubicTower (fun N => shiftedSquares (N - 1)))
    (hc : CubicTower (fun N => halfCentral (N - 1))) :
    CubicTower (fun N => (OeisA3161.b N : ℤ)) := by
  intro n k p hn hk hp hp5
  have hu : 0 < n * p ^ k := Nat.mul_pos hn (pow_pos hp.pos _)
  have hl : 0 < n * p ^ (k - 1) := Nat.mul_pos hn (pow_pos hp.pos _)
  apply cancel_two hp hp5
  rw [raw_normalization_pos _ hu, raw_normalization_pos _ hl]
  exact (hc n k p hn hk hp hp5).mul
    (((hs n k p hn hk hp hp5).mul_left 3).sub ((hc n k p hn hk hp hp5).pow 2))

/-- The exact source supercongruence holds at every positive multiplier and level. -/
theorem conjecture (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (OeisA3161.b (n * p ^ k) : ℤ) ≡ (OeisA3161.b (n * p ^ (k - 1)) : ℤ)
      [ZMOD (p : ℤ) ^ (3 * k)] :=
  conjecture_of_coster B02R2ShiftedCongruence.shiftedSquares_tower
    B02R2Central.halfCentral_tower n k p hn hk hp hp_ge


end B02R2A003161
end
