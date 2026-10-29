/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Integral construction for Hanna's compositional generating series

The ordinary generating series of OEIS A396843 has constant coefficient zero,
linear coefficient one, and satisfies $A(xA(x)-3xA(x)^2)=x^2$.

Source: [OEIS A396843](https://oeis.org/A396843), Paul D. Hanna (2026).
The characteristic-two uniqueness argument was previously formalized in
[trureturing PR 6773](https://github.com/the-omega-institute/trureturing/pull/6773).
Lean formalization by Wentao Li, including integral existence and uniqueness.
Development assistance: Codex (OpenAI).
-/

namespace A396843Proof
open PowerSeries
noncomputable section
variable {R : Type*} [CommRing R]

/-- The inner argument in Hanna's functional equation. -/
def argument (f : PowerSeries R) : PowerSeries R := X * f - 3 * X * f ^ 2

/-- The left side of Hanna's functional equation. -/
def output (f : PowerSeries R) : PowerSeries R := f.subst (argument f)

lemma argument_constant (f : PowerSeries R) : constantCoeff (argument f) = 0 := by
  simp [argument]

lemma argument_hasSubst (f : PowerSeries R) : HasSubst (argument f) :=
  .of_constantCoeff_zero' (argument_constant f)

lemma argument_dvd {f : PowerSeries R} (h : constantCoeff f = 0) :
    (X : PowerSeries R) ^ 2 ∣ argument f := by
  obtain ⟨q, rfl⟩ := X_dvd_iff.mpr h
  refine ⟨q - 3 * X * q ^ 2, ?_⟩
  dsimp [argument]
  ring

lemma coeff_eq_of_dvd {f g : PowerSeries R} {d n : ℕ}
    (h : (X : PowerSeries R) ^ d ∣ f - g) (hn : n < d) : coeff n f = coeff n g := by
  have := X_pow_dvd_iff.mp h n hn
  simpa only [map_sub, sub_eq_zero] using this

lemma pow_difference_dvd {u v : PowerSeries R} {e k : ℕ}
    (hu : (X : PowerSeries R) ^ 2 ∣ u) (hv : (X : PowerSeries R) ^ 2 ∣ v)
    (he : (X : PowerSeries R) ^ e ∣ u - v) (hk : 2 ≤ k) :
    (X : PowerSeries R) ^ (e + 2) ∣ u ^ k - v ^ k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction k with
  | zero =>
      have h := mul_dvd_mul he (dvd_add hu hv)
      rw [← pow_add] at h
      convert h using 1
      all_goals ring
  | succ k ih =>
      have hvk : X ^ 2 ∣ v ^ (k + 2) := hv.trans (dvd_pow_self v (by omega))
      have hsecond : X ^ (e + 2) ∣ (u - v) * v ^ (k + 2) := by
        simpa only [pow_add] using mul_dvd_mul he hvk
      have h := dvd_add (dvd_mul_of_dvd_right ih u) hsecond
      convert h using 1
      all_goals ring

lemma subst_outer_dvd {f g u : PowerSeries R} {d : ℕ}
    (hu : constantCoeff u = 0) (hu2 : (X : PowerSeries R) ^ 2 ∣ u)
    (h : (X : PowerSeries R) ^ d ∣ f - g) :
    (X : PowerSeries R) ^ (2 * d) ∣ f.subst u - g.subst u := by
  have hs : HasSubst u := .of_constantCoeff_zero' hu
  obtain ⟨q, hq⟩ := h
  have he := congrArg (fun p : PowerSeries R => p.subst u) hq
  rw [subst_sub hs, subst_mul hs, subst_pow hs, subst_X hs] at he
  rw [he]
  have hp : X ^ (2 * d) ∣ u ^ d := by
    simpa only [pow_mul] using pow_dvd_pow_of_dvd hu2 d
  exact hp.mul_right _

lemma subst_tail_dvd {f u v : PowerSeries R} {e : ℕ}
    (hf : coeff 1 f = 1) (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (hu2 : (X : PowerSeries R) ^ 2 ∣ u) (hv2 : (X : PowerSeries R) ^ 2 ∣ v)
    (he : (X : PowerSeries R) ^ e ∣ u - v) :
    (X : PowerSeries R) ^ (e + 2) ∣ f.subst u - f.subst v - (u - v) := by
  have hsu : HasSubst u := .of_constantCoeff_zero' hu
  have hsv : HasSubst v := .of_constantCoeff_zero' hv
  apply X_pow_dvd_iff.mpr
  intro n hn
  have h : coeff n ((f - X).subst u) = coeff n ((f - X).subst v) := by
    rw [coeff_subst' hsu, coeff_subst' hsv]
    apply finsum_congr
    intro k
    rcases k with _ | k
    · simp
    rcases k with _ | k
    · simp [hf]
    · rw [coeff_eq_of_dvd (pow_difference_dvd hu2 hv2 he (by omega : 2 ≤ k + 2)) hn]
  rw [subst_sub hsu, subst_sub hsv, subst_X hsu, subst_X hsv] at h
  simp only [map_sub] at h ⊢
  linear_combination h

/-- Changing a normalized input in degree $d$ changes its output in degree $d+1$
by the same amount, with error divisible by $X^{d+2}$. -/
lemma output_linearization {f g : PowerSeries R} {d : ℕ} (hd : 2 ≤ d)
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) (hf1 : coeff 1 f = 1)
    (h : (X : PowerSeries R) ^ d ∣ f - g) :
    (X : PowerSeries R) ^ (d + 2) ∣ output f - output g - X * (f - g) := by
  have ha : X ^ (d + 1) ∣ argument f - argument g := by
    have ht := mul_dvd_mul (dvd_refl (X : PowerSeries R)) h
    rw [← pow_succ'] at ht
    convert ht.mul_right (1 - 3 * (f + g)) using 1
    all_goals (dsimp [argument]; ring)
  have hb : X ^ (d + 2) ∣ argument f - argument g - X * (f - g) := by
    have hz : X ∣ f + g := X_dvd_iff.mpr (by simp [hf, hg])
    have ht' := mul_dvd_mul (mul_dvd_mul (dvd_refl (X : PowerSeries R)) h) hz
    rw [show X * X ^ d * X = (X : PowerSeries R) ^ (d + 2) by ring] at ht'
    convert ht'.mul_left (-3) using 1
    all_goals (dsimp [argument]; ring)
  have ho := subst_outer_dvd (argument_constant g) (argument_dvd hg) h
  have ho' : X ^ (d + 2) ∣ f.subst (argument g) - g.subst (argument g) :=
    (pow_dvd_pow X (by omega : d + 2 ≤ 2 * d)).trans ho
  have hi := subst_tail_dvd hf1 (argument_constant f) (argument_constant g)
    (argument_dvd hf) (argument_dvd hg) ha
  have hi' : X ^ (d + 2) ∣
      f.subst (argument f) - f.subst (argument g) - (argument f - argument g) :=
    (pow_dvd_pow X (by omega : d + 2 ≤ d + 1 + 2)).trans hi
  convert dvd_add (dvd_add hi' ho') hb using 1
  all_goals (dsimp [output]; ring)

lemma normalized_difference {f g : PowerSeries R}
    (h0 : constantCoeff f = constantCoeff g) (h1 : coeff 1 f = coeff 1 g) :
    (X : PowerSeries R) ^ 2 ∣ f - g := by
  apply X_pow_dvd_iff.mpr
  intro n hn
  interval_cases n <;> simp_all [coeff_zero_eq_constantCoeff]

lemma output_congr {f g : PowerSeries R} {d : ℕ} (hd : 2 ≤ d)
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) (hf1 : coeff 1 f = 1)
    (h : (X : PowerSeries R) ^ d ∣ f - g) :
    (X : PowerSeries R) ^ (d + 1) ∣ output f - output g := by
  have ht := output_linearization hd hf hg hf1 h
  have hs : X ^ (d + 1) ∣ X * (f - g) := by
    simpa only [pow_succ'] using mul_dvd_mul (dvd_refl (X : PowerSeries R)) h
  have ht' := (pow_dvd_pow X (by omega : d + 1 ≤ d + 2)).trans ht
  convert dvd_add ht' hs using 1
  all_goals ring

lemma output_next {f g : PowerSeries R} {d : ℕ} (hd : 2 ≤ d)
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) (hf1 : coeff 1 f = 1)
    (h : (X : PowerSeries R) ^ d ∣ f - g) :
    coeff (d + 1) (output f) - coeff (d + 1) (output g) = coeff d f - coeff d g := by
  have ht := X_pow_dvd_iff.mp (output_linearization hd hf hg hf1 h) (d + 1) (by omega)
  simpa only [map_sub, coeff_succ_X_mul, sub_eq_zero] using ht

/-- The division-free correction sequence, beginning with $X$. -/
def stage : ℕ → PowerSeries R
  | 0 => X
  | n + 1 => stage n - monomial (n + 2) (coeff (n + 3) (output (stage n)))

@[simp] lemma stage_constant (n : ℕ) : constantCoeff (stage n : PowerSeries R) = 0 := by
  induction n with
  | zero => simp [stage]
  | succ n ih =>
      rw [stage, map_sub, ih, zero_sub, neg_eq_zero]
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_monomial]
      simp

@[simp] lemma stage_linear (n : ℕ) : coeff 1 (stage n : PowerSeries R) = 1 := by
  induction n with
  | zero => simp [stage]
  | succ n ih => simp [stage, coeff_monomial, ih]

lemma stage_change (n : ℕ) :
    (X : PowerSeries R) ^ (n + 2) ∣ stage (n + 1) - stage n := by
  refine ⟨- C (coeff (n + 3) (output (stage n))), ?_⟩
  rw [stage, monomial_eq_C_mul_X_pow]
  ring

lemma stage_correct (n : ℕ) :
    (X : PowerSeries R) ^ (n + 3) ∣ output (stage n) - X ^ 2 := by
  induction n with
  | zero =>
      refine ⟨-3, ?_⟩
      change X.subst (argument X) - X ^ 2 = X ^ 3 * (-3 : PowerSeries R)
      rw [subst_X (argument_hasSubst _)]
      dsimp [argument]
      ring
  | succ n ih =>
      have hd := stage_change (R := R) n
      have hl := output_linearization (by omega : 2 ≤ n + 2)
        (stage_constant (n + 1)) (stage_constant n) (stage_linear (n + 1)) hd
      apply X_pow_dvd_iff.mpr
      intro j hj
      have he := X_pow_dvd_iff.mp hl j (by omega)
      simp only [map_sub] at he
      have hc : coeff j (X * (stage (n + 1) - stage n) : PowerSeries R) =
          if j = n + 3 then -coeff (n + 3) (output (stage n) : PowerSeries R) else 0 := by
        cases j with
        | zero => simp
        | succ j =>
            rw [coeff_succ_X_mul]
            simp only [stage, sub_sub_cancel_left, map_neg, coeff_monomial]
            split_ifs <;> simp_all
      rw [hc] at he
      by_cases hj' : j < n + 3
      · rw [ite_eq_right (by omega)] at he
        have hi := X_pow_dvd_iff.mp ih j hj'
        simp only [map_sub] at hi ⊢
        linear_combination he + hi
      · have hje : j = n + 3 := by omega
        subst j
        rw [ite_eq_left rfl] at he
        simp only [map_sub, coeff_X_pow, show ¬ n + 3 = 2 by omega, ite_false]
        linear_combination he

lemma stage_stable {m n k : ℕ} (hmn : m ≤ n) (hk : k < m + 2) :
    coeff k (stage n : PowerSeries R) = coeff k (stage m : PowerSeries R) := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      exact (coeff_eq_of_dvd (stage_change n) (by omega)).trans ih

/-- The integral series obtained by stabilizing each coefficient. -/
def series : PowerSeries R := mk fun n => coeff n (stage n)

lemma series_approximation (n : ℕ) :
    (X : PowerSeries R) ^ (n + 2) ∣ series - stage n := by
  apply X_pow_dvd_iff.mpr
  intro k hk
  simp only [map_sub, coeff_mk, series, sub_eq_zero]
  exact (stage_stable (m := k) (n := max n k) (by omega) (by omega)).symm.trans
    (stage_stable (m := n) (n := max n k) (by omega) hk)

@[simp] lemma series_constant : constantCoeff (series : PowerSeries R) = 0 := by
  simpa using coeff_eq_of_dvd (series_approximation (R := R) 0) (by omega : 0 < 0 + 2)

@[simp] lemma series_linear : coeff 1 (series : PowerSeries R) = 1 := by
  simpa using coeff_eq_of_dvd (series_approximation (R := R) 0) (by omega : 1 < 0 + 2)

/-- Existence of an integral solution of the OEIS generating-function equation. -/
theorem series_equation : output (series : PowerSeries R) = X ^ 2 := by
  ext n
  have h := output_congr (R := R) (by omega : 2 ≤ n + 2) series_constant (stage_constant n)
    series_linear (series_approximation n)
  exact (coeff_eq_of_dvd h (by omega)).trans
    (coeff_eq_of_dvd (stage_correct n) (by omega))

/-- The normalization $A(0)=0$, $a(1)=1$ makes the source equation unique. -/
theorem normalized_unique {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1)
    (he : output f = output g) : f = g := by
  have hall : ∀ n, (X : PowerSeries R) ^ (n + 2) ∣ f - g := by
    intro n
    induction n with
    | zero => exact normalized_difference (hf.trans hg.symm) (hf1.trans hg1.symm)
    | succ n ih =>
        apply X_pow_dvd_iff.mpr
        intro k hk
        by_cases hk' : k < n + 2
        · exact X_pow_dvd_iff.mp ih k hk'
        · have hkn : k = n + 2 := by omega
          subst k
          have ht := output_next (by omega : 2 ≤ n + 2) hf hg hf1 ih
          rw [he, sub_self] at ht
          simpa only [map_sub] using ht.symm
  ext n
  exact coeff_eq_of_dvd (hall n) (by omega)

/-- The source GF equation has exactly one normalized solution over every commutative ring. -/
theorem exists_unique_series : ∃! f : PowerSeries R,
    constantCoeff f = 0 ∧ coeff 1 f = 1 ∧ output f = X ^ 2 := by
  refine ⟨series, ⟨series_constant, series_linear, series_equation⟩, ?_⟩
  rintro f ⟨hf, hf1, he⟩
  exact normalized_unique hf series_constant hf1 series_linear (he.trans series_equation.symm)

lemma output_map {S : Type*} [CommRing S] (h : R →+* S) (f : PowerSeries R) :
    (output f).map h = output (f.map h) := by
  have hm : (output f).map h = (f.map h).subst ((argument f).map h) :=
    map_subst (argument_hasSubst f) f
  rw [hm]
  have hthree : (PowerSeries.map h) (3 : PowerSeries R) = (3 : PowerSeries S) :=
    map_ofNat (PowerSeries.map h) 3
  simp [output, argument, hthree]

/-- The construction commutes with coefficient maps; in particular its rational solution is integral. -/
theorem series_map {S : Type*} [CommRing S] (h : R →+* S) :
    (series : PowerSeries R).map h = (series : PowerSeries S) := by
  have h0 : constantCoeff ((series : PowerSeries R).map h) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      series_constant, map_zero]
  apply normalized_unique h0 series_constant (by simp [series_linear]) series_linear
  rw [← output_map, series_equation, series_equation]
  simp

/-- The series with coefficient one at every positive index over the field with two elements. -/
def allOnes : PowerSeries (ZMod 2) := X * mk 1

lemma allOnes_equation : output allOnes = X ^ 2 := by
  let s := allOnes
  let h := argument s
  have hs : s * (1 - X) = X := by
    dsimp [s, allOnes]
    rw [mul_assoc, mk_one_mul_one_sub_eq_one, mul_one]
  have htwo : (2 : PowerSeries (ZMod 2)) = 0 := by
    calc
      (2 : PowerSeries (ZMod 2)) = C (2 : ZMod 2) := (map_ofNat C 2).symm
      _ = C (0 : ZMod 2) := congrArg C (by decide)
      _ = 0 := map_zero C
  have hh : h * (1 - X) ^ 2 = X ^ 2 := by
    calc
      h * (1 - X) ^ 2 =
          X * (s * (1 - X)) * (1 - X) - 3 * X * (s * (1 - X)) ^ 2 := by
            dsimp [h, argument]
            ring
      _ = X ^ 2 - 4 * X ^ 3 := by rw [hs]; ring
      _ = X ^ 2 := by linear_combination -(2 * X ^ 3) * htwo
  have hi : (1 - h) * (1 - X) ^ 2 = 1 := by
    linear_combination -hh - X * htwo
  have hc : s.subst h * (1 - h) = h := by
    have hsub : HasSubst h := argument_hasSubst s
    have ht := congrArg (substAlgHom hsub) hs
    simpa only [map_mul, map_sub, map_one, coe_substAlgHom, subst_X hsub] using ht
  change s.subst h = X ^ 2
  calc
    s.subst h = s.subst h * ((1 - h) * (1 - X) ^ 2) := by rw [hi, mul_one]
    _ = h * (1 - X) ^ 2 := by rw [← mul_assoc, hc]
    _ = X ^ 2 := hh

/-- Hanna's oddness conclusion for any normalized integral solution of the exact source equation. -/
theorem source_oddness (f : PowerSeries ℤ) (hf : constantCoeff f = 0)
    (hf1 : coeff 1 f = 1) (he : f.subst (X * f - 3 * X * f ^ 2) = X ^ 2) :
    ∀ n : ℕ, 1 ≤ n → Odd (coeff n f) := by
  let hom := Int.castRingHom (ZMod 2)
  let g := f.map hom
  have hg0 : constantCoeff g = 0 := by
    simp [g, ← coeff_zero_eq_constantCoeff_apply, hf]
  have hg1 : coeff 1 g = 1 := by simp [g, hf1]
  have hg : output g = X ^ 2 := by
    change output f = X ^ 2 at he
    have hm := congrArg (PowerSeries.map hom) he
    rw [output_map] at hm
    simpa [g] using hm
  have hgs : g = allOnes := normalized_unique hg0 (by simp [allOnes]) hg1
    (by simp [allOnes]) (hg.trans allOnes_equation.symm)
  intro n hn
  rw [← ZMod.intCast_eq_one_iff_odd]
  have ht := congrArg (coeff n) hgs
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [g, hom, allOnes, Nat.add_comm] using ht

/-- The integer sequence at its official OEIS indices (with $a(0)=0$). -/
def a (n : ℕ) : ℤ := coeff n series

/-- All terms of OEIS A396843 are odd. -/
theorem all_terms_odd (n : ℕ) (hn : 1 ≤ n) : Odd (a n) :=
  source_oddness series series_constant series_linear series_equation n hn

/-- An integral series with the exact OEIS normalization exists and is unique. -/
theorem source_existence : ∃! f : PowerSeries ℤ,
    constantCoeff f = 0 ∧ coeff 1 f = 1 ∧
      f.subst (X * f - 3 * X * f ^ 2) = X ^ 2 := exists_unique_series

/-- Finite polynomial version of the same correction process, for exact initial-value checks. -/
def polynomialStage : ℕ → Polynomial ℤ
  | 0 => Polynomial.X
  | n + 1 =>
      let p := polynomialStage n
      p - Polynomial.monomial (n + 2)
        ((p.comp (Polynomial.X * p - 3 * Polynomial.X * p ^ 2)).coeff (n + 3))

lemma polynomial_substitution (p q : Polynomial ℤ) (hq : q.coeff 0 = 0) :
    (p : PowerSeries ℤ).subst (q : PowerSeries ℤ) = (p.comp q : Polynomial ℤ) := by
  have hq' : constantCoeff (q : PowerSeries ℤ) = 0 := by
    simpa only [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe] using hq
  rw [subst_coe (.of_constantCoeff_zero' hq')]
  have hh : (algebraMap ℤ (PowerSeries ℤ)) = C := Subsingleton.elim _ _
  simp only [Polynomial.aeval_def, hh, ← Polynomial.eval₂_C_X_eq_coe, Polynomial.eval₂_comp]

lemma polynomialStage_coe (n : ℕ) : (polynomialStage n : PowerSeries ℤ) = stage n := by
  induction n with
  | zero => simp [polynomialStage, stage]
  | succ n ih =>
      have harg :
          ((Polynomial.X * polynomialStage n - 3 * Polynomial.X * polynomialStage n ^ 2 :
            Polynomial ℤ) : PowerSeries ℤ) = argument (stage n) := by
        simp only [argument, Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_pow,
          Polynomial.coe_X, ih]
        have hthree : ((3 : Polynomial ℤ) : PowerSeries ℤ) = 3 :=
          map_ofNat Polynomial.coeToPowerSeries.ringHom 3
        rw [hthree]
      have hzero :
          (Polynomial.X * polynomialStage n - 3 * Polynomial.X * polynomialStage n ^ 2).coeff 0 = 0 := by
        simp
      have hsub := polynomial_substitution (polynomialStage n) _ hzero
      rw [harg, ih] at hsub
      simp only [polynomialStage, Polynomial.coe_sub, Polynomial.coe_monomial, stage, ih]
      congr 2
      rw [← Polynomial.coeff_coe, ← hsub]
      rfl

lemma a_eq_polynomial (n : ℕ) : a n = (polynomialStage n).coeff n := by
  have h := coeff_eq_of_dvd (series_approximation (R := ℤ) n) (by omega : n < n + 2)
  rw [← polynomialStage_coe] at h
  simpa only [a, Polynomial.coeff_coe] using h

lemma polynomialStage_0 : polynomialStage 0 = Polynomial.X := rfl

lemma polynomialStage_1 : polynomialStage 1 = Polynomial.X + 3 * Polynomial.X ^ 2 := by
  rw [polynomialStage, polynomialStage_0]
  have hc : ((Polynomial.X : Polynomial ℤ).comp
      (Polynomial.X * Polynomial.X - 3 * Polynomial.X * Polynomial.X ^ 2)).coeff 3 = -3 := by
    conv_lhs => arg 1; ring_nf
    norm_num
  rw [hc]
  simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_neg, map_ofNat]
  ring

lemma polynomialStage_2 : polynomialStage 2 =
    Polynomial.X + 3 * Polynomial.X ^ 2 + 15 * Polynomial.X ^ 3 := by
  rw [polynomialStage, polynomialStage_1]
  have hc : ((Polynomial.X + 3 * Polynomial.X ^ 2 : Polynomial ℤ).comp
      (Polynomial.X * (Polynomial.X + 3 * Polynomial.X ^ 2) -
        3 * Polynomial.X * (Polynomial.X + 3 * Polynomial.X ^ 2) ^ 2)).coeff 4 = -15 := by
    conv_lhs => arg 1; simp; ring_nf
    norm_num
  rw [hc]
  simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_neg, map_ofNat]
  ring

lemma polynomialStage_3 : polynomialStage 3 =
    Polynomial.X + 3 * Polynomial.X ^ 2 + 15 * Polynomial.X ^ 3 + 117 * Polynomial.X ^ 4 := by
  rw [polynomialStage, polynomialStage_2]
  have hc : ((Polynomial.X + 3 * Polynomial.X ^ 2 + 15 * Polynomial.X ^ 3 : Polynomial ℤ).comp
      (Polynomial.X * (Polynomial.X + 3 * Polynomial.X ^ 2 + 15 * Polynomial.X ^ 3) -
        3 * Polynomial.X * (Polynomial.X + 3 * Polynomial.X ^ 2 + 15 * Polynomial.X ^ 3) ^ 2)).coeff 5 =
      -117 := by
    conv_lhs => arg 1; simp; ring_nf
    norm_num
  rw [hc]
  simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_neg, map_ofNat]
  ring

lemma polynomialStage_4 : polynomialStage 4 =
    Polynomial.X + 3 * Polynomial.X ^ 2 + 15 * Polynomial.X ^ 3 +
      117 * Polynomial.X ^ 4 + 975 * Polynomial.X ^ 5 := by
  rw [polynomialStage, polynomialStage_3]
  have hc : ((Polynomial.X + 3 * Polynomial.X ^ 2 + 15 * Polynomial.X ^ 3 +
      117 * Polynomial.X ^ 4 : Polynomial ℤ).comp
      (Polynomial.X * (Polynomial.X + 3 * Polynomial.X ^ 2 + 15 * Polynomial.X ^ 3 +
        117 * Polynomial.X ^ 4) - 3 * Polynomial.X *
          (Polynomial.X + 3 * Polynomial.X ^ 2 + 15 * Polynomial.X ^ 3 + 117 * Polynomial.X ^ 4) ^ 2)).coeff 6 =
      -975 := by
    conv_lhs => arg 1; simp; ring_nf
    norm_num
  rw [hc]
  simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_neg, map_ofNat]
  ring

lemma a_eq_polynomial_of_lt (n m : ℕ) (h : n < m + 2) : a n = (polynomialStage m).coeff n := by
  have ht := coeff_eq_of_dvd (series_approximation (R := ℤ) m) h
  rw [← polynomialStage_coe] at ht
  simpa only [a, Polynomial.coeff_coe] using ht

lemma a_0 : a 0 = 0 := by
  simpa only [a, coeff_zero_eq_constantCoeff_apply] using (series_constant (R := ℤ))
lemma a_1 : a 1 = 1 := series_linear
lemma a_2 : a 2 = 3 := by
  rw [a_eq_polynomial_of_lt 2 1 (by omega), polynomialStage_1]
  norm_num [Polynomial.coeff_X]
lemma a_3 : a 3 = 15 := by
  rw [a_eq_polynomial_of_lt 3 2 (by omega), polynomialStage_2]
  norm_num [Polynomial.coeff_X]
lemma a_4 : a 4 = 117 := by
  rw [a_eq_polynomial_of_lt 4 3 (by omega), polynomialStage_3]
  norm_num [Polynomial.coeff_X]
lemma a_5 : a 5 = 975 := by
  rw [a_eq_polynomial_of_lt 5 4 (by omega), polynomialStage_4]
  norm_num [Polynomial.coeff_X]


end
end A396843Proof

namespace OeisA396843
open PowerSeries

/-- The normalized ordinary generating-function equation defining OEIS A396843. -/
def SourceEquation (A : PowerSeries ℤ) : Prop :=
  constantCoeff A = 0 ∧ coeff 1 A = 1 ∧
    A.subst (X * A - 3 * X * A ^ 2) = X ^ 2

/-- The normalized generating series of OEIS A396843. -/
noncomputable def series : PowerSeries ℤ := Classical.epsilon SourceEquation

/-- OEIS A396843, extended by $a(0)=0$. -/
noncomputable def a (n : ℕ) : ℤ := coeff n series

/-- The normalized defining equation has a unique integral solution. -/
theorem source_existence : ∃! A : PowerSeries ℤ, SourceEquation A :=
  A396843Proof.source_existence

theorem series_spec : SourceEquation series :=
  Classical.epsilon_spec source_existence.exists

theorem series_eq_constructed : series = (A396843Proof.series : PowerSeries ℤ) :=
  A396843Proof.normalized_unique series_spec.1 A396843Proof.series_constant
    series_spec.2.1 A396843Proof.series_linear
    (series_spec.2.2.trans A396843Proof.series_equation.symm)

theorem a_eq_constructed (n : ℕ) : a n = A396843Proof.a n := by
  rw [a, series_eq_constructed]
  rfl

theorem a_0 : a 0 = 0 := by rw [a_eq_constructed]; exact A396843Proof.a_0
theorem a_1 : a 1 = 1 := by rw [a_eq_constructed]; exact A396843Proof.a_1
theorem a_2 : a 2 = 3 := by rw [a_eq_constructed]; exact A396843Proof.a_2
theorem a_3 : a 3 = 15 := by rw [a_eq_constructed]; exact A396843Proof.a_3
theorem a_4 : a 4 = 117 := by rw [a_eq_constructed]; exact A396843Proof.a_4
theorem a_5 : a 5 = 975 := by rw [a_eq_constructed]; exact A396843Proof.a_5

/-- Hanna's oddness conjecture at every positive OEIS index. -/
theorem conjecture (n : ℕ) (hn : 1 ≤ n) : Odd (a n) := by
  rw [a_eq_constructed]
  exact A396843Proof.all_terms_odd n hn

/-- The unique normalized rational solution has integral coefficients. -/
theorem rational_source_integral (f : PowerSeries ℚ)
    (h0 : constantCoeff f = 0) (h1 : coeff 1 f = 1)
    (he : f.subst (X * f - 3 * X * f ^ 2) = X ^ 2) :
    f = series.map (Int.castRingHom ℚ) := by
  rw [series_eq_constructed, A396843Proof.series_map]
  exact A396843Proof.normalized_unique h0 A396843Proof.series_constant h1
    A396843Proof.series_linear (he.trans A396843Proof.series_equation.symm)

end OeisA396843
