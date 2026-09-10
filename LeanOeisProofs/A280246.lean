/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
import Mathlib

/-!
# OEIS A280246

`psi m` is the sum of totatives of `m`: the sum of positive integers
`k ≤ m` that are coprime to `m` (OEIS A023896).

`a n` is the product of `psi d` over the positive divisors of `n`
(OEIS A280246).

The theorem `odd_a_iff_odd_psi` is the exact OEIS conjecture: for every
positive `n`, `Odd (a n)` if and only if `Odd (psi n)`.
-/

open Finset Nat

/-- Sum of totatives of `m`: `∑ {k | 1 ≤ k ≤ m, Nat.Coprime k m}`. -/
def psi (m : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 m with k.Coprime m, k

/-- `a n = ∏_{d ∣ n} psi d`. -/
def a (n : ℕ) : ℕ :=
  ∏ d ∈ n.divisors, psi d

/-- The finite set of totatives of `m` in `{1, …, m}`. -/
def totatives (m : ℕ) : Finset ℕ :=
  {k ∈ Finset.Icc 1 m | k.Coprime m}

lemma psi_eq_sum_totatives (m : ℕ) : psi m = ∑ k ∈ totatives m, k := rfl

lemma psi_one : psi 1 = 1 := by
  simp [psi]

lemma psi_two : psi 2 = 1 := by
  decide

lemma coprime_eq_one_of_coprime_self {n : ℕ} (h : n.Coprime n) : n = 1 := by
  simpa [Coprime, gcd_self] using h

lemma coprime_eq_one_of_zero_coprime {n : ℕ} (h : (0 : ℕ).Coprime n) : n = 1 := by
  simpa [Coprime] using h

lemma coprime_four_of_odd {n : ℕ} (hn : Odd n) : n.Coprime 4 := by
  rw [show (4 : ℕ) = 2 ^ 2 from rfl, coprime_pow_right_iff (by norm_num)]
  exact (prime_two.coprime_iff_not_dvd.mpr hn.not_two_dvd_nat).symm

lemma totatives_eq_filter_range {n : ℕ} (hn : 1 < n) :
    totatives n = {k ∈ range n | k.Coprime n} := by
  ext k
  simp only [totatives, mem_filter, mem_Icc, mem_range]
  constructor
  · intro ⟨⟨_hk1, hkn⟩, hcop⟩
    have hkne : k ≠ n := by
      intro h
      subst h
      exact hn.ne' (coprime_eq_one_of_coprime_self hcop)
    exact ⟨lt_of_le_of_ne hkn hkne, hcop⟩
  · intro ⟨hklt, hcop⟩
    have hk0 : k ≠ 0 := by
      intro h
      subst h
      exact hn.ne' (coprime_eq_one_of_zero_coprime hcop)
    exact ⟨⟨one_le_iff_ne_zero.mpr hk0, hklt.le⟩, hcop⟩

lemma totient_eq_card_totatives {n : ℕ} (hn : 1 < n) :
    n.totient = #(totatives n) := by
  rw [totient_eq_card_coprime, totatives_eq_filter_range hn]
  congr 1
  ext k
  simp [coprime_comm]

lemma mem_totatives_sub {n k : ℕ} (hn : 1 < n) (hk : k ∈ totatives n) :
    n - k ∈ totatives n := by
  simp only [totatives, mem_filter, mem_Icc] at hk ⊢
  obtain ⟨⟨_hk1, hkn⟩, hcop⟩ := hk
  have hkne : k ≠ n := by
    intro h
    subst h
    exact hn.ne' (coprime_eq_one_of_coprime_self hcop)
  have hkn' : k < n := lt_of_le_of_ne hkn hkne
  refine ⟨⟨?_, Nat.sub_le n k⟩, ?_⟩
  · exact Nat.le_sub_of_add_le (by omega)
  · rwa [coprime_self_sub_left hkn]

lemma sub_mem_totatives_involutive {n k : ℕ} (hk : k ∈ totatives n) :
    n - (n - k) = k := by
  simp only [totatives, mem_filter, mem_Icc] at hk
  exact Nat.sub_sub_self hk.1.2

lemma sum_totatives_n_sub {n : ℕ} (hn : 1 < n) :
    ∑ k ∈ totatives n, (n - k) = ∑ k ∈ totatives n, k := by
  refine sum_nbij' (fun k => n - k) (fun k => n - k)
    (fun k hk => mem_totatives_sub hn hk)
    (fun k hk => mem_totatives_sub hn hk)
    (fun k hk => sub_mem_totatives_involutive hk)
    (fun k hk => sub_mem_totatives_involutive hk)
    (fun _ _ => rfl)

/-- Pairing of totatives: `2 * psi n = n * φ(n)` for `n > 1`. -/
lemma two_mul_psi_eq {n : ℕ} (hn : 1 < n) :
    2 * psi n = n * n.totient := by
  have hs : psi n = ∑ k ∈ totatives n, k := psi_eq_sum_totatives n
  have hφ : n.totient = #(totatives n) := totient_eq_card_totatives hn
  have hadd :
      ∑ k ∈ totatives n, k + ∑ k ∈ totatives n, (n - k) = ∑ k ∈ totatives n, n := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun k hk => ?_
    simp only [totatives, mem_filter, mem_Icc] at hk
    exact Nat.add_sub_of_le hk.1.2
  rw [sum_totatives_n_sub hn] at hadd
  have hconst : ∑ k ∈ totatives n, n = n * #(totatives n) := by
    rw [sum_const, smul_eq_mul, mul_comm]
  rw [hs, two_mul, hadd, hconst, hφ]

lemma even_psi_iff_four_dvd_mul_totient {n : ℕ} (hn : 1 < n) :
    Even (psi n) ↔ 4 ∣ n * n.totient := by
  have h : 2 * psi n = n * n.totient := two_mul_psi_eq hn
  constructor
  · intro he
    rw [even_iff_two_dvd] at he
    have : 4 ∣ 2 * psi n := by
      change 2 * 2 ∣ 2 * psi n
      exact mul_dvd_mul_left 2 he
    rwa [h] at this
  · intro h4
    rw [even_iff_two_dvd]
    have hpos : (2 : ℕ) ≠ 0 := by decide
    rw [← mul_dvd_mul_iff_left hpos]
    change 4 ∣ 2 * psi n
    rwa [h]

lemma odd_psi_iff_not_four_dvd {n : ℕ} (hn : 1 < n) :
    Odd (psi n) ↔ ¬ 4 ∣ n * n.totient := by
  rw [← even_psi_iff_four_dvd_mul_totient hn, ← not_even_iff_odd]

lemma four_dvd_mul_totient_of_even_gt_two {n : ℕ} (hn : 2 < n) (he : Even n) :
    4 ∣ n * n.totient := by
  by_cases h4 : 4 ∣ n
  · exact dvd_mul_of_dvd_left h4 _
  · have hn2 : 2 ∣ n := even_iff_two_dvd.mp he
    obtain ⟨m, rfl⟩ := hn2
    have hm_odd : Odd m := by
      rw [← not_even_iff_odd]
      intro hm
      obtain ⟨t, rfl⟩ := even_iff_two_dvd.mp hm
      exact h4 ⟨t, by ring⟩
    have hm_gt : 2 < m := by omega
    have hφ : (2 * m).totient = m.totient := totient_two_mul_of_odd hm_odd
    have h2φ : 2 ∣ m.totient := even_iff_two_dvd.mp (totient_even hm_gt)
    rw [hφ]
    obtain ⟨k, hk⟩ := h2φ
    refine ⟨m * k, ?_⟩
    rw [hk]
    ring

lemma four_dvd_totient_of_two_odd_primes {n p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hne : p ≠ q)
    (hpn : p ∣ n) (hqn : q ∣ n) :
    4 ∣ n.totient := by
  have hpq : p * q ∣ n := hp.dvd_mul_of_dvd_ne hne hq hpn hqn
  have hφdvd : (p * q).totient ∣ n.totient := totient_dvd_of_dvd hpq
  have hcop : p.Coprime q := (coprime_primes hp hq).mpr hne
  have hφpq : (p * q).totient = (p - 1) * (q - 1) := by
    rw [totient_mul hcop, totient_prime hp, totient_prime hq]
  have h2p : 2 ∣ p - 1 := even_iff_two_dvd.mp (hp.even_sub_one hp2)
  have h2q : 2 ∣ q - 1 := even_iff_two_dvd.mp (hq.even_sub_one hq2)
  have h4 : 4 ∣ (p - 1) * (q - 1) := by
    change 2 * 2 ∣ (p - 1) * (q - 1)
    exact mul_dvd_mul h2p h2q
  rw [← hφpq] at h4
  exact h4.trans hφdvd

lemma four_dvd_totient_prime_pow_iff {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (hp2 : p ≠ 2) :
    4 ∣ (p ^ k).totient ↔ 4 ∣ (p - 1) := by
  rw [totient_prime_pow hp hk]
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hpow : Odd (p ^ (k - 1)) := hpodd.pow
  have hcop : (4 : ℕ).Coprime (p ^ (k - 1)) := (coprime_four_of_odd hpow).symm
  exact hcop.dvd_mul_left

lemma four_dvd_sub_one_iff_mod_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    4 ∣ p - 1 ↔ p % 4 = 1 := by
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have hmod : p % 4 = 1 ∨ p % 4 = 3 := odd_mod_four_iff.mp hodd
  have hppos : 1 ≤ p := hp.one_lt.le
  have hp1 : p = p - 1 + 1 := (Nat.sub_add_cancel hppos).symm
  constructor
  · intro h
    have : (p - 1 + 1) % 4 = 1 := by
      rw [Nat.add_mod, Nat.dvd_iff_mod_eq_zero.mp h, zero_add, Nat.one_mod]
    rwa [← hp1] at this
  · intro h1
    have : ((p - 1) % 4 + 1) % 4 = 1 := by
      have : (p - 1 + 1) % 4 = 1 := by rwa [← hp1]
      rwa [Nat.add_mod, Nat.one_mod] at this
    have hlt : (p - 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have : (p - 1) % 4 = 0 := by omega
    exact Nat.dvd_iff_mod_eq_zero.mpr this

lemma mod_four_eq_three_iff {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p % 4 = 3 ↔ ¬ 4 ∣ p - 1 := by
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have hmod : p % 4 = 1 ∨ p % 4 = 3 := odd_mod_four_iff.mp hodd
  rw [four_dvd_sub_one_iff_mod_four hp hp2]
  constructor
  · intro h3 h1
    omega
  · intro h
    exact hmod.resolve_left h

/-- Characterization of odd `psi`. -/
lemma odd_psi_iff {n : ℕ} (hn : 0 < n) :
    Odd (psi n) ↔
      n = 1 ∨ n = 2 ∨ ∃ p k, p.Prime ∧ p % 4 = 3 ∧ 0 < k ∧ n = p ^ k := by
  rcases eq_or_ne n 1 with rfl | hn1
  · simp [psi_one]
  rcases eq_or_ne n 2 with rfl | hn2
  · simp [psi_two]
  have hgt : 1 < n := by omega
  have hgt2 : 2 < n := by omega
  rw [odd_psi_iff_not_four_dvd hgt]
  constructor
  · intro hnot
    right; right
    by_cases he : Even n
    · exact (hnot (four_dvd_mul_totient_of_even_gt_two hgt2 he)).elim
    · have hodd : Odd n := not_even_iff_odd.mp he
      have h4φ : ¬ 4 ∣ n.totient := by
        intro hφ
        exact hnot ((coprime_four_of_odd hodd).symm.dvd_mul_left.mpr hφ)
      by_cases hpp : IsPrimePow n
      · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
        have hp2 : p ≠ 2 := by
          intro hp2
          subst hp2
          exact he (even_two.pow_of_ne_zero hk.ne')
        refine ⟨p, k, hp, ?_, hk, rfl⟩
        rw [mod_four_eq_three_iff hp hp2]
        intro h4p
        exact h4φ ((four_dvd_totient_prime_pow_iff hp hk hp2).mpr h4p)
      · have hcard : 1 < n.primeFactors.card := by
          have hne1 : n.primeFactors.card ≠ 1 := by
            intro hc
            exact hpp (isPrimePow_iff_card_primeFactors_eq_one.mpr hc)
          have hne0 : n.primeFactors.card ≠ 0 := by
            intro hc
            rw [Finset.card_eq_zero, primeFactors_eq_empty] at hc
            omega
          omega
        obtain ⟨p, q, hp, hq, hpq⟩ := (one_lt_card_iff (s := n.primeFactors)).mp hcard
        have hpP : p.Prime := (mem_primeFactors.mp hp).1
        have hqP : q.Prime := (mem_primeFactors.mp hq).1
        have hpd : p ∣ n := (mem_primeFactors.mp hp).2.1
        have hqd : q ∣ n := (mem_primeFactors.mp hq).2.1
        have hp2 : p ≠ 2 := by
          intro h
          subst h
          exact hodd.not_two_dvd_nat hpd
        have hq2 : q ≠ 2 := by
          intro h
          subst h
          exact hodd.not_two_dvd_nat hqd
        exact (h4φ (four_dvd_totient_of_two_odd_primes hpP hqP hp2 hq2 hpq hpd hqd)).elim
  · intro h
    rcases h with hn1' | hn2' | ⟨p, k, hp, hp3, hk, rfl⟩
    · exact (hn1 hn1').elim
    · exact (hn2 hn2').elim
    · intro h4
      have hp2 : p ≠ 2 := by
        intro h
        subst h
        simp at hp3
      have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
      have hφ : 4 ∣ (p ^ k).totient :=
        (coprime_four_of_odd hodd).symm.dvd_mul_left.mp h4
      have : 4 ∣ p - 1 := (four_dvd_totient_prime_pow_iff hp hk hp2).mp hφ
      exact (mod_four_eq_three_iff hp hp2).mp hp3 this

lemma odd_prod_iff {ι : Type*} {s : Finset ι} {f : ι → ℕ} :
    Odd (∏ i ∈ s, f i) ↔ ∀ i ∈ s, Odd (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [prod_insert hx, odd_mul, forall_mem_insert, ih]

lemma odd_a_iff_forall {n : ℕ} :
    Odd (a n) ↔ ∀ d ∈ n.divisors, Odd (psi d) := by
  simpa [a] using (odd_prod_iff (s := n.divisors) (f := psi))

/-- The set of `n` with `psi n` odd is closed under taking positive divisors. -/
lemma odd_psi_of_dvd {n d : ℕ} (hn : 0 < n) (hdn : d ∣ n) (hψ : Odd (psi n)) :
    Odd (psi d) := by
  have hdpos : 0 < d := pos_of_dvd_of_pos hdn hn
  rw [odd_psi_iff hn] at hψ
  rw [odd_psi_iff hdpos]
  rcases hψ with rfl | rfl | ⟨p, k, hp, hp3, hk, rfl⟩
  · exact Or.inl (dvd_one.mp hdn)
  · rcases (dvd_prime prime_two).mp hdn with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · obtain ⟨j, _hj, rfl⟩ := (dvd_prime_pow hp).mp hdn
    rcases eq_or_ne j 0 with rfl | hj0
    · exact Or.inl (pow_zero p)
    · exact Or.inr (Or.inr ⟨p, j, hp, hp3, pos_iff_ne_zero.mpr hj0, rfl⟩)

/-- OEIS A280246 conjecture: for every positive integer `n`,
`a n` is odd if and only if `psi n` is odd. -/
theorem odd_a_iff_odd_psi {n : ℕ} (hn : 0 < n) : Odd (a n) ↔ Odd (psi n) := by
  constructor
  · intro ha
    rw [odd_a_iff_forall] at ha
    exact ha n (mem_divisors_self n hn.ne')
  · intro hψ
    rw [odd_a_iff_forall]
    intro d hd
    exact odd_psi_of_dvd hn (dvd_of_mem_divisors hd) hψ

example : a 1 = 1 := by decide
example : a 6 = 18 := by decide
example : psi 9 = 27 := by decide

#print axioms odd_a_iff_odd_psi
