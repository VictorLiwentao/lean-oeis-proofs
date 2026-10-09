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
Mathematical question: Thomas Ordowski, OEIS A051903, 2 December 2019.
Related prior mathematics: the elementary odd-prime order / lifting-the-exponent
obstruction for a universal power congruence; Dutta–Dutta, viXra:2602.0018,
classify universal exponents via the maximum prime exponent and Carmichael
lambda, without an explicit odd-exclusion corollary or Lean proof.
This file formalizes the negative answer to question 2 only. It does not
treat Lehmer's totient problem (question 1) or the fixed-base-2 problem
(question 3). It does not claim new informal mathematics.
AI assistance: Cursor Grok 4.6 Extra High, 2026-09-13.
-/

import Mathlib
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic


namespace OeisA51903

def a (n : ℕ) : ℕ :=
  (n.primeFactorsList.map (n.primeFactorsList.count ·)).foldr max 0

end OeisA51903


/-!
Exact target: `OeisA51903.conjecture2` from the frozen source
`FormalConjectures/OEIS/51903.lean`.

The source asks whether there exists odd `n` with `1 < a n` such that
`b ^ n ≡ b ^ (a n) [MOD n]` for every natural `b`, where `a` is the
existing maximum prime-factor exponent. The answer is negative.
-/

open Nat
open OeisA51903

namespace A051903C2

/-- The foldr-maximum of a nonempty list of natural numbers is attained. -/
lemma exists_eq_foldr_max {l : List ℕ} (h : 0 < l.foldr max 0) :
    ∃ x ∈ l, x = l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.foldr] at h ⊢
    by_cases ha : l.foldr max 0 ≤ a
    · exact ⟨a, List.mem_cons_self, (max_eq_left ha).symm⟩
    · have hpos : 0 < l.foldr max 0 :=
        lt_of_le_of_lt (Nat.zero_le a) (lt_of_not_ge ha)
      obtain ⟨x, hx, hxeq⟩ := ih hpos
      refine ⟨x, List.mem_cons_of_mem _ hx, ?_⟩
      rw [max_eq_right (le_of_not_ge ha), hxeq]

/-- If `1 < a n`, some prime attains the maximum exponent `a n`. -/
lemma exists_prime_max_exponent {n : ℕ} (ha : 1 < a n) :
    ∃ p, p.Prime ∧ n.factorization p = a n := by
  set l := n.primeFactorsList.map (n.primeFactorsList.count ·)
  have hpos : 0 < l.foldr max 0 := lt_trans Nat.zero_lt_one ha
  obtain ⟨k, hk, hk_eq⟩ := exists_eq_foldr_max (l := l) hpos
  obtain ⟨p, hp_mem, hp_count⟩ := List.mem_map.mp hk
  have hp : p.Prime := prime_of_mem_primeFactorsList hp_mem
  refine ⟨p, hp, ?_⟩
  rw [← primeFactorsList_count_eq, hp_count, hk_eq]
  rfl

/-- For `p ≥ 3` and exponent `e ≥ 2`, one has `e < p ^ (e - 1)`. -/
lemma lt_pow_pred {p e : ℕ} (hp : 3 ≤ p) (he : 2 ≤ e) : e < p ^ (e - 1) := by
  induction e, he using Nat.le_induction with
  | base =>
    have : 2 < p := Nat.lt_of_lt_of_le (by decide : (2 : ℕ) < 3) hp
    simpa
  | succ e he ih =>
    have hpow : p ^ e = p * p ^ (e - 1) :=
      calc
        p ^ e = p ^ (e - 1 + 1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ e)]
        _ = p ^ (e - 1) * p := pow_succ _ _
        _ = p * p ^ (e - 1) := mul_comm _ _
    have h1 : e + 1 ≤ 3 * e := by omega
    have h2 : 3 * e < 3 * p ^ (e - 1) :=
      Nat.mul_lt_mul_of_pos_left ih (by decide : (0 : ℕ) < 3)
    have h3 : 3 * p ^ (e - 1) ≤ p * p ^ (e - 1) := Nat.mul_le_mul_right _ hp
    have hlt : e + 1 < p ^ e := (h1.trans_lt h2).trans_le (h3.trans_eq hpow.symm)
    simpa [Nat.add_sub_cancel] using hlt

/-- The original `a` is compatible with `factorization`; this does not replace it. -/
lemma n_ne_zero_of_max_exponent {n p : ℕ} (h : n.factorization p = a n)
    (ha : 1 < a n) : n ≠ 0 := by
  intro hn
  subst hn
  have : (0 : ℕ).factorization p = 0 := by simp [factorization_zero]
  omega

lemma pow_a_dvd {n p : ℕ} (hp : p.Prime) (h : n.factorization p = a n)
    (ha : 1 < a n) : p ^ a n ∣ n :=
  (hp.pow_dvd_iff_le_factorization (n_ne_zero_of_max_exponent h ha)).mpr (le_of_eq h.symm)

lemma a_lt_n {n p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (ha : 1 < a n)
    (h : n.factorization p = a n) : a n < n := by
  have hdvd := pow_a_dvd hp h ha
  have hn0 := n_ne_zero_of_max_exponent h ha
  have hle : p ^ a n ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
  have hpred : a n < p ^ (a n - 1) := lt_pow_pred hp3 (Nat.succ_le_of_lt ha)
  have hpowle : p ^ (a n - 1) ≤ p ^ a n :=
    Nat.pow_le_pow_right hp.pos (Nat.sub_le _ _)
  exact hpred.trans_le (hpowle.trans hle)

lemma not_two_dvd_of_odd {n : ℕ} (hn : Odd n) : ¬ 2 ∣ n := by
  intro h
  obtain ⟨k, hk⟩ := hn
  omega

/-- The unit `1 + p` has order `p ^ (e - 1)` modulo `p ^ e`. -/
lemma orderOf_one_add_prime_exponent {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : 1 ≤ e) :
    orderOf ((1 + p : ℕ) : ZMod (p ^ e)) = p ^ (e - 1) := by
  have hmod : p ^ e = p ^ (e - 1 + 1) := by rw [Nat.sub_add_cancel he]
  rw [hmod, Nat.cast_add, Nat.cast_one]
  exact ZMod.orderOf_one_add_prime hp hp2 (e - 1)

lemma isUnit_one_add_prime {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    IsUnit ((1 + p : ℕ) : ZMod (p ^ e)) := by
  rw [ZMod.isUnit_natCast_iff_not_dvd_pow hp he]
  intro h
  have : p ∣ 1 := (Nat.dvd_add_self_right).mp h
  exact hp.not_dvd_one this

/-- Universal congruence at base `1 + p`, reduced modulo `p ^ e`, forces
`p ^ (e - 1) ∣ n - e`. -/
lemma prime_pow_pred_dvd_sub {n p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : 2 ≤ e) (hle : e ≤ n) (hdvd : p ^ e ∣ n)
    (hall : ∀ b : ℕ, b ^ n ≡ b ^ e [MOD n]) :
    p ^ (e - 1) ∣ n - e := by
  have he1 : 1 ≤ e := le_trans (by decide : (1 : ℕ) ≤ 2) he
  have hepos : 0 < e := Nat.succ_le_iff.mp he1
  set u := ((1 + p : ℕ) : ZMod (p ^ e))
  have hu : IsUnit u := isUnit_one_add_prime hp hepos
  have hmod : (1 + p) ^ n ≡ (1 + p) ^ e [MOD p ^ e] :=
    (hall (1 + p)).of_dvd hdvd
  have hpow : u ^ n = u ^ e := by
    simpa [u, Nat.cast_pow] using
      (ZMod.natCast_eq_natCast_iff ((1 + p) ^ n) ((1 + p) ^ e) (p ^ e)).mpr hmod
  have hcancel : u ^ (n - e) = 1 := by
    have hmul : u ^ e * u ^ (n - e) = u ^ e * 1 := by
      rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel hle, hpow, mul_one]
    exact (hu.pow e).mul_left_cancel hmul
  have hord := orderOf_one_add_prime_exponent hp hp2 he1
  rw [← hord]
  exact (orderOf_dvd_iff_pow_eq_one (x := u)).mpr hcancel

/-- No odd `n` with `1 < a n` satisfies the universal power congruence. -/
theorem no_odd_universal :
    ¬ ∃ n : ℕ, Odd n ∧ 1 < a n ∧ ∀ b : ℕ, b ^ n ≡ b ^ (a n) [MOD n] := by
  rintro ⟨n, hn, ha, hall⟩
  obtain ⟨p, hp, hp_eq⟩ := exists_prime_max_exponent ha
  have hn2 := not_two_dvd_of_odd hn
  have hn0 := n_ne_zero_of_max_exponent hp_eq ha
  have hp_dvd : p ∣ n :=
    (hp.dvd_iff_one_le_factorization hn0).mpr (by omega)
  have hp2 : p ≠ 2 := by
    intro h2
    exact hn2 (h2 ▸ hp_dvd)
  have hp3 : 3 ≤ p := Nat.succ_le_of_lt (lt_of_le_of_ne hp.two_le hp2.symm)
  have he : 2 ≤ a n := Nat.succ_le_of_lt ha
  have hdvd := pow_a_dvd hp hp_eq ha
  have hlt := a_lt_n hp hp3 ha hp_eq
  have hle : a n ≤ n := le_of_lt hlt
  have hdiv :=
    prime_pow_pred_dvd_sub hp hp2 he hle hdvd (by simpa [hp_eq] using hall)
  have hpn : p ^ (a n - 1) ∣ n :=
    dvd_trans (pow_dvd_pow p (Nat.sub_le (a n) 1)) hdvd
  have hpe : p ^ (a n - 1) ∣ a n := by
    have hsub : p ^ (a n - 1) ∣ n - (n - a n) := Nat.dvd_sub hpn hdiv
    rwa [Nat.sub_sub_self hle] at hsub
  have hgt := lt_pow_pred hp3 he
  have hpos : 0 < a n := Nat.succ_le_iff.mp (le_trans (by decide : (1 : ℕ) ≤ 2) he)
  exact (not_le_of_gt hgt) (Nat.le_of_dvd hpos hpe)

/--
Exact answered-type wrapper for `OeisA51903.conjecture2`.
The only change relative to the frozen source statement is
`answer(sorry)` resolved to `False`.
-/
theorem conjecture2 :
    False ↔ ∃ n : ℕ, Odd n ∧ 1 < a n ∧ ∀ b : ℕ, b ^ n ≡ b ^ (a n) [MOD n] := by
  constructor
  · intro h
    exact False.elim h
  · exact no_odd_universal

example :
    False ↔ ∃ n : ℕ, Odd n ∧ 1 < a n ∧ ∀ b : ℕ, b ^ n ≡ b ^ (a n) [MOD n] :=
  conjecture2

#check conjecture2
#print axioms no_odd_universal
#print axioms conjecture2

end A051903C2
