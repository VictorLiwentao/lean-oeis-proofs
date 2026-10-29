/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push

/-!
# Exponential series with complementary substitution exponents

The source equations for OEIS A368630 and A368631 use exponent pairs $(2,1)$ and $(1,2)$.
Wentao Li proves all three A368630 congruences, with OpenAI Codex assistance.
The shared development also contains the A368631 modulo-three result.

*References:*
- Paul D. Hanna, [A368630](https://oeis.org/A368630), January 2, 2024.
- Paul D. Hanna, [A368631](https://oeis.org/A368631), January 2, 2024.
-/

namespace OeisA368630
open PowerSeries

/-- The rational exponential generating series of an integer sequence. -/
noncomputable def egf (a : ℕ → ℤ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => (a n : ℚ) / n.factorial

/-- The source equation with constant term one and exponents $r,s$. -/
def Original (r s : ℕ) (F : ℚ⟦X⟧) : Prop :=
  F.constantCoeff = 1 ∧
    F.subst (X * (F⁻¹) ^ r) = (exp ℚ).subst (X * F ^ s)

/-- All three congruences, with the exceptional odd index one excluded. -/
def Congruences (a : ℕ → ℤ) : Prop :=
  (∀ n, a n % 3 = 1) ∧ (∀ n, a (2 * n) % 2 = 1) ∧
    (∀ n, 1 ≤ n → a (2 * n + 1) % 2 = 0)

/-- The full source-faithful obligation, including existence and uniqueness. -/
def Target (r s : ℕ) : Prop :=
  (∃! F : ℚ⟦X⟧, Original r s F) ∧
    ∀ F : ℚ⟦X⟧, Original r s F →
      ∃ a : ℕ → ℤ, egf a = F ∧ Congruences a

lemma constantCoeff_subst_of_zero (F G : ℚ⟦X⟧) (hG : G.constantCoeff = 0) :
    PowerSeries.constantCoeff (F.subst G) = F.constantCoeff := by
  change MvPowerSeries.constantCoeff (F.subst G) = F.constantCoeff
  rw [PowerSeries.constantCoeff_subst (HasSubst.of_constantCoeff_zero' hG)]
  simp only [map_pow]
  change (∑ᶠ d : ℕ, coeff d F • (G.constantCoeff ^ d)) = F.constantCoeff
  rw [finsum_eq_single (a := 0)]
  · simp
  · intro d hd
    simp [hG, hd]

/-- Every solution of the original equation admits the auxiliary series stated in OEIS. -/
theorem original_auxiliary {r s : ℕ} {F : ℚ⟦X⟧} (hF : Original r s F) :
    ∃ B : ℚ⟦X⟧, B.constantCoeff = 1 ∧
      B = F.subst (X * B ^ r) ∧
      F = (exp ℚ).subst (X * B ^ (r + s)) := by
  let G : ℚ⟦X⟧ := X * (F⁻¹) ^ r
  have hG0 : G.constantCoeff = 0 := by simp [G]
  have hG1 : G.coeff 1 = 1 := by
    simp [G, PowerSeries.constantCoeff_inv, hF.1]
  have hGu : IsUnit (G.coeff 1) := hG1 ▸ isUnit_one
  let H := G.substInvOfIsUnit hGu
  have hH0 : H.constantCoeff = 0 := by simp [H]
  have hG : HasSubst G := HasSubst.of_constantCoeff_zero' hG0
  have hH : HasSubst H := HasSubst.of_constantCoeff_zero' hH0
  have hGH : G.subst H = X := PowerSeries.subst_substInvOfIsUnit_right G hG0 hGu
  let B : ℚ⟦X⟧ := F.subst H
  have hB0 : B.constantCoeff = 1 := by
    rw [constantCoeff_subst_of_zero F H hH0, hF.1]
  have hinv : F⁻¹ * F = 1 := PowerSeries.inv_mul_cancel F (by rw [hF.1]; norm_num)
  have hcancel : G * F ^ r = X := by
    dsimp [G]
    rw [mul_assoc, ← mul_pow, hinv, one_pow, mul_one]
  have hHB : H = X * B ^ r := by
    have hc := congrArg (fun K : ℚ⟦X⟧ => K.subst H) hcancel
    rw [subst_mul hH, subst_pow hH, hGH, subst_X hH] at hc
    simpa [B] using hc.symm
  refine ⟨B, hB0, ?_, ?_⟩
  · change F.subst H = F.subst (X * B ^ r)
    rw [hHB]
  · have he := congrArg (fun K : ℚ⟦X⟧ => K.subst H) hF.2
    rw [subst_comp_subst_apply hG hH, hGH, X_subst] at he
    have hS : HasSubst (X * F ^ s) := by
      apply HasSubst.of_constantCoeff_zero'
      simp
    rw [subst_comp_subst_apply hS hH, subst_mul hH, subst_X hH, subst_pow hH] at he
    change F = (exp ℚ).subst (H * B ^ s) at he
    rw [he]
    congr 1
    rw [hHB, pow_add, mul_assoc]

/-- The auxiliary equations imply the original equation, without a recurrence assumption. -/
theorem auxiliary_original {r s : ℕ} {F B : ℚ⟦X⟧}
    (hB0 : B.constantCoeff = 1)
    (hB : B = F.subst (X * B ^ r))
    (hF : F = (exp ℚ).subst (X * B ^ (r + s))) : Original r s F := by
  let H : ℚ⟦X⟧ := X * B ^ r
  have hH0 : H.constantCoeff = 0 := by simp [H]
  have hH : HasSubst H := HasSubst.of_constantCoeff_zero' hH0
  have hF0 : F.constantCoeff = 1 := by
    rw [hF, constantCoeff_subst_of_zero]
    · simp
    · simp
  let G : ℚ⟦X⟧ := X * (F⁻¹) ^ r
  have hG0 : G.constantCoeff = 0 := by simp [G]
  have hG : HasSubst G := HasSubst.of_constantCoeff_zero' hG0
  have hFB : F.subst H = B := hB.symm
  have hi : B * (F⁻¹).subst H = 1 := by
    have he := congrArg (fun K : ℚ⟦X⟧ => K.subst H)
      (PowerSeries.mul_inv_cancel F (by rw [hF0]; norm_num))
    have hone : (1 : ℚ⟦X⟧).subst H = 1 := by
      rw [← coe_substAlgHom hH]
      exact map_one _
    simpa only [subst_mul hH, hFB, hone] using he
  have hGH : G.subst H = X := by
    dsimp [G]
    rw [subst_mul hH, subst_X hH, subst_pow hH]
    change (X * B ^ r) * subst H F⁻¹ ^ r = X
    rw [mul_assoc, ← mul_pow, hi, one_pow, mul_one]
  have hH1 : H.coeff 1 = 1 := by simp [H, hB0]
  have hHu : IsUnit (H.coeff 1) := hH1 ▸ isUnit_one
  let J := H.substInvOfIsUnit hHu
  have hJ : HasSubst J := HasSubst.substInvOfIsUnit H hHu
  have hHJ : H.subst J = X := subst_substInvOfIsUnit_right H hH0 hHu
  have hGJ : G = J := by
    have he := congrArg (fun K : ℚ⟦X⟧ => K.subst J) hGH
    rwa [subst_comp_subst_apply hH hJ, hHJ, X_subst, subst_X hJ] at he
  have hHG : H.subst G = X := by simpa only [hGJ] using hHJ
  have hBG : B.subst G = F := by
    rw [hB, subst_comp_subst_apply hH hG, hHG, X_subst]
  refine ⟨hF0, ?_⟩
  have hK : HasSubst (X * B ^ (r + s)) := by
    apply HasSubst.of_constantCoeff_zero'
    simp
  have he := congrArg (fun K : ℚ⟦X⟧ => K.subst G) hF
  rw [subst_comp_subst_apply hK hG, subst_mul hG, subst_X hG, subst_pow hG, hBG] at he
  rw [he]
  congr 1
  dsimp [G]
  rw [pow_add]
  have hiF : F⁻¹ * F = 1 := PowerSeries.inv_mul_cancel F (by rw [hF0]; norm_num)
  calc
    X * F⁻¹ ^ r * (F ^ r * F ^ s) = X * ((F⁻¹ * F) ^ r) * F ^ s := by ring
    _ = X * F ^ s := by rw [hiF, one_pow, mul_one]

/-- Exact equivalence with the auxiliary-series formulation listed by OEIS. -/
theorem original_iff_auxiliary (r s : ℕ) (F : ℚ⟦X⟧) :
    Original r s F ↔ ∃ B : ℚ⟦X⟧, B.constantCoeff = 1 ∧
      B = F.subst (X * B ^ r) ∧ F = (exp ℚ).subst (X * B ^ (r + s)) := by
  exact ⟨original_auxiliary, fun ⟨_, h0, hB, hF⟩ => auxiliary_original h0 hB hF⟩

namespace Hurwitz
variable {R : Type*} [CommRing R]
/-- Differentiation shifts an EGF coefficient sequence. -/
def shift (a : ℕ → R) (n : ℕ) := a (n + 1)
/-- The EGF product, recursively specified by its constant term and the product rule. -/
def product (a b : ℕ → R) : ℕ → R
  | 0 => a 0 * b 0
  | n + 1 => product (shift a) b n + product a (shift b) n
@[simp] lemma product_zero (a b : ℕ → R) : product a b 0 = a 0 * b 0 := rfl
lemma product_succ (a b : ℕ → R) (n : ℕ) :
    product a b (n + 1) = product (shift a) b n + product a (shift b) n := rfl
lemma shift_product (a b : ℕ → R) :
    shift (product a b) = product (shift a) b + product a (shift b) := rfl
lemma product_comm (a b : ℕ → R) : product a b = product b a := by
  funext n
  induction n generalizing a b with
  | zero => simp [mul_comm]
  | succ n ih => rw [product_succ, product_succ, ih (shift a) b, ih a (shift b), add_comm]
lemma product_add_left (a b c : ℕ → R) :
    product (a + b) c = product a c + product b c := by
  funext n
  induction n generalizing a b c with
  | zero => simp [add_mul]
  | succ n ih =>
    change product (shift a + shift b) c n + product (a + b) (shift c) n = _
    rw [ih, ih]
    simp only [Pi.add_apply, product_succ]
    ring
lemma product_add_right (a b c : ℕ → R) :
    product a (b + c) = product a b + product a c := by
  rw [product_comm, product_add_left]
  rw [product_comm b a, product_comm c a]
lemma product_assoc (a b c : ℕ → R) :
    product (product a b) c = product a (product b c) := by
  funext n
  induction n generalizing a b c with
  | zero => simp [mul_assoc]
  | succ n ih =>
    simp only [product_succ, shift_product, product_add_left, product_add_right, Pi.add_apply]
    rw [ih, ih, ih]
    ring
lemma map_product {S : Type*} [CommRing S] (φ : R →+* S) (a b : ℕ → R) :
    φ ∘ product a b = product (φ ∘ a) (φ ∘ b) := by
  funext n
  change φ (product a b n) = product (φ ∘ a) (φ ∘ b) n
  induction n generalizing a b with
  | zero => simp [Function.comp_apply]
  | succ n ih =>
    change φ (product (shift a) b n + product a (shift b) n) = _
    rw [map_add, ih, ih]
    rfl
lemma square_succ_two (a : ℕ → ZMod 2) (n : ℕ) : product a a (n + 1) = 0 := by
  rw [product_succ, product_comm (shift a) a]
  have h : (2 : ZMod 2) = 0 := by decide
  calc
    product a (shift a) n + product a (shift a) n = 2 * product a (shift a) n := by ring
    _ = 0 := by rw [h, zero_mul]
lemma cube_succ_three (a : ℕ → ZMod 3) (n : ℕ) :
    product (product a a) a (n + 1) = 0 := by
  rw [product_succ, shift_product, product_add_left]
  simp only [Pi.add_apply]
  have ht : product (product (shift a) a) a = product (product a a) (shift a) := by
    rw [product_comm (shift a) a, product_comm (product a (shift a)) a, ← product_assoc]
  have hu : product (product a (shift a)) a = product (product a a) (shift a) := by
    rw [product_comm (product a (shift a)) a, ← product_assoc]
  rw [ht, hu]
  have h : (3 : ZMod 3) = 0 := by decide
  calc
    _ = 3 * product (product a a) (shift a) n := by ring
    _ = 0 := by rw [h, zero_mul]

end Hurwitz

namespace Hurwitz
open PowerSeries
/-- Derivatives at zero, rather than ordinary coefficients. -/
noncomputable def jet (F : ℚ⟦X⟧) (n : ℕ) : ℚ := n.factorial * F.coeff n
lemma jet_zero (F : ℚ⟦X⟧) : jet F 0 = F.constantCoeff := by simp [jet]
lemma jet_derivative (F : ℚ⟦X⟧) : jet (derivative ℚ F) = shift (jet F) := by
  funext n
  simp only [jet, shift, coeff_derivative, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  ring
lemma jet_add (F G : ℚ⟦X⟧) : jet (F + G) = jet F + jet G := by
  funext n
  simp [jet, mul_add]
lemma jet_product (F G : ℚ⟦X⟧) : jet (F * G) = product (jet F) (jet G) := by
  funext n
  induction n generalizing F G with
  | zero => simp [jet_zero]
  | succ n ih =>
    change shift (jet (F * G)) n = _
    rw [← jet_derivative, (derivative ℚ).leibniz]
    simp only [smul_eq_mul]
    rw [jet_add]
    simp only [Pi.add_apply, product_succ]
    rw [ih, ih, jet_derivative, jet_derivative]
    rw [product_comm (jet G) (shift (jet F)), add_comm]
end Hurwitz

namespace Hurwitz
open PowerSeries
lemma jet_egf (a : ℕ → ℤ) : jet (egf a) = Int.castRingHom ℚ ∘ a := by
  funext n
  simp only [jet, egf, coeff_mk, Function.comp_apply, Int.coe_castRingHom]
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp
lemma jet_egf_square (a : ℕ → ℤ) (n : ℕ) :
    jet (egf a ^ 2) n = ((product a a n : ℤ) : ℚ) := by
  rw [pow_two, jet_product, jet_egf, ← map_product]
  rfl
lemma jet_egf_cube (a : ℕ → ℤ) (n : ℕ) :
    jet (egf a ^ 3) n = ((product (product a a) a n : ℤ) : ℚ) := by
  have hp : egf a ^ 3 = (egf a * egf a) * egf a := by ring
  rw [hp, jet_product, jet_product, jet_egf, ← map_product, ← map_product]
  rfl
lemma square_intCast_two (a : ℕ → ℤ) (n : ℕ) :
    ((product a a (n + 1) : ℤ) : ZMod 2) = 0 := by
  change (Int.castRingHom (ZMod 2) ∘ product a a) (n + 1) = 0
  rw [map_product]
  exact square_succ_two _ _
lemma cube_intCast_three (a : ℕ → ℤ) (n : ℕ) :
    ((product (product a a) a (n + 1) : ℤ) : ZMod 3) = 0 := by
  change (Int.castRingHom (ZMod 3) ∘ product (product a a) a) (n + 1) = 0
  rw [map_product, map_product]
  exact cube_succ_three _ _
/-- Every positive EGF coefficient of a square is an even integer. -/
theorem egf_square_positive (a : ℕ → ℤ) (n : ℕ) :
    ∃ c : ℤ, jet (egf a ^ 2) (n + 1) = (c : ℚ) ∧ (c : ZMod 2) = 0 :=
  ⟨product a a (n + 1), jet_egf_square a (n + 1), square_intCast_two a n⟩
/-- Every positive EGF coefficient of a cube is an integer divisible by three. -/
theorem egf_cube_positive (a : ℕ → ℤ) (n : ℕ) :
    ∃ c : ℤ, jet (egf a ^ 3) (n + 1) = (c : ℚ) ∧ (c : ZMod 3) = 0 :=
  ⟨product (product a a) a (n + 1), jet_egf_cube a (n + 1), cube_intCast_three a n⟩
end Hurwitz

namespace Hurwitz
open PowerSeries
variable {R : Type*} [CommRing R]
def unitSequence : ℕ → R := fun n => if n = 0 then 1 else 0
lemma product_zero_right (a : ℕ → R) : product a 0 = 0 := by
  funext n
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    change product (shift a) 0 n + product a 0 n = 0
    rw [ih, ih]
    simp
lemma shift_unit : shift (unitSequence : ℕ → R) = 0 := by
  funext n
  simp [shift, unitSequence]
lemma product_unit (a : ℕ → R) : product a unitSequence = a := by
  funext n
  induction n generalizing a with
  | zero => simp [unitSequence]
  | succ n ih =>
    rw [product_succ, shift_unit, product_zero_right, Pi.zero_apply, add_zero, ih]
    rfl
lemma jet_X_mul_succ (F : ℚ⟦X⟧) (n : ℕ) :
    jet (X * F) (n + 1) = (n + 1) * jet F n := by
  simp only [jet, coeff_succ_X_mul, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  ring
/-- Integer EGF coefficients of the derivative of $xB^3$. -/
def cubeLogDerivative (b : ℕ → ℤ) (n : ℕ) : ℤ :=
  (n + 1) * product (product b b) b n
lemma jet_cube_log_derivative (b : ℕ → ℤ) :
    jet (derivative ℚ (X * egf b ^ 3)) = Int.castRingHom ℚ ∘ cubeLogDerivative b := by
  funext n
  rw [jet_derivative]
  change jet (X * egf b ^ 3) (n + 1) = _
  rw [jet_X_mul_succ, jet_egf_cube]
  simp [cubeLogDerivative, Function.comp_apply]
lemma cube_log_derivative_three (b : ℕ → ℤ) (hb : b 0 = 1) :
    Int.castRingHom (ZMod 3) ∘ cubeLogDerivative b = unitSequence := by
  funext n
  cases n with
  | zero => simp [cubeLogDerivative, product_zero, hb, unitSequence]
  | succ n =>
    change ((cubeLogDerivative b (n + 1) : ℤ) : ZMod 3) = 0
    simp only [cubeLogDerivative, Int.cast_mul, cube_intCast_three, mul_zero]
/-- Conditional modulo-three result for integer EGFs satisfying the auxiliary equation.
This does not assert existence or integrality of the OEIS solutions. -/
theorem exp_cube_mod_three (a b : ℕ → ℤ) (ha : a 0 = 1) (hb : b 0 = 1)
    (h : egf a = (exp ℚ).subst (X * egf b ^ 3)) :
    ∀ n, (a n : ZMod 3) = 1 := by
  let G : ℚ⟦X⟧ := X * egf b ^ 3
  have hG : HasSubst G := by
    apply HasSubst.of_constantCoeff_zero'
    simp [G]
  have hd : derivative ℚ (egf a) = egf a * derivative ℚ G := by
    calc
      derivative ℚ (egf a) = derivative ℚ ((exp ℚ).subst G) := congrArg (derivative ℚ) h
      _ = (exp ℚ).subst G * derivative ℚ G := by rw [derivative_subst hG, derivative_exp]
      _ = egf a * derivative ℚ G := by rw [← h]
  have hj := congrArg jet hd
  rw [jet_derivative, jet_egf, jet_product, jet_egf] at hj
  change shift (Int.castRingHom ℚ ∘ a) =
    product (Int.castRingHom ℚ ∘ a) (jet (derivative ℚ (X * egf b ^ 3))) at hj
  rw [jet_cube_log_derivative, ← map_product] at hj
  have hrec (n : ℕ) : a (n + 1) = product a (cubeLogDerivative b) n := by
    have he := congrFun hj n
    change (a (n + 1) : ℚ) = ((product a (cubeLogDerivative b) n : ℤ) : ℚ) at he
    exact_mod_cast he
  have hmod (n : ℕ) : (a (n + 1) : ZMod 3) = (a n : ZMod 3) := by
    have he := congrArg (Int.castRingHom (ZMod 3)) (hrec n)
    change (a (n + 1) : ZMod 3) =
      (Int.castRingHom (ZMod 3) ∘ product a (cubeLogDerivative b)) n at he
    rw [map_product, cube_log_derivative_three b hb, product_unit] at he
    exact he
  intro n
  induction n with
  | zero => simp [ha]
  | succ n ih => rw [hmod, ih]
end Hurwitz

namespace Causal
variable {R : Type*}

/-- A coefficient operator is causal if output $n$ only uses input indices below $n$. -/
def IsCausal (T : (ℕ → R) → ℕ → R) : Prop :=
  ∀ n a b, (∀ k, k < n → a k = b k) → T a n = T b n

/-- Coefficient recursion for a causal operator. -/
def fixedPoint (T : (ℕ → R) → ℕ → R) (seed : ℕ → R) (n : ℕ) : R :=
  T (fun k => if _h : k < n then fixedPoint T seed k else seed k) n
termination_by n

lemma fixedPoint_eq (T : (ℕ → R) → ℕ → R) (hT : IsCausal T) (seed : ℕ → R)
    (n : ℕ) : fixedPoint T seed n = T (fixedPoint T seed) n := by
  rw [fixedPoint]
  apply hT
  intro k hk
  simp [hk]

/-- A causal coefficient operator has exactly one fixed point. -/
theorem exists_unique_fixed_point (T : (ℕ → R) → ℕ → R) (hT : IsCausal T)
    (seed : ℕ → R) : ∃! a : ℕ → R, T a = a := by
  have hf : T (fixedPoint T seed) = fixedPoint T seed := by
    funext n
    exact (fixedPoint_eq T hT seed n).symm
  refine ⟨fixedPoint T seed, hf, ?_⟩
  intro a ha
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    calc
      a n = T a n := (congrFun ha n).symm
      _ = T (fixedPoint T seed) n := hT n a (fixedPoint T seed) (fun k hk => ih k hk)
      _ = fixedPoint T seed n := congrFun hf n
end Causal

namespace Hurwitz
open PowerSeries Finset
variable {R : Type*} [CommRing R]

lemma product_congr (a b c d : ℕ → R) (n : ℕ)
    (ha : ∀ k ≤ n, a k = c k) (hb : ∀ k ≤ n, b k = d k) :
    product a b n = product c d n := by
  induction n generalizing a b c d with
  | zero => simp [ha 0 le_rfl, hb 0 le_rfl]
  | succ n ih =>
    rw [product_succ, product_succ]
    congr 1
    · apply ih
      · intro k hk; exact ha (k + 1) (Nat.succ_le_succ hk)
      · intro k hk; exact hb k (Nat.le_succ_of_le hk)
    · apply ih
      · intro k hk; exact ha k (Nat.le_succ_of_le hk)
      · intro k hk; exact hb (k + 1) (Nat.succ_le_succ hk)

/-- Powers in the integer EGF algebra. -/
def power (a : ℕ → R) : ℕ → ℕ → R
  | 0 => unitSequence
  | k + 1 => product (power a k) a

lemma power_congr (a b : ℕ → R) (k n : ℕ) (h : ∀ i ≤ n, a i = b i) :
    power a k n = power b k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    apply product_congr
    · intro i hi; exact ih i (fun j hj => h j (hj.trans hi))
    · exact h

lemma map_power {S : Type*} [CommRing S] (φ : R →+* S) (a : ℕ → R) (k : ℕ) :
    φ ∘ power a k = power (φ ∘ a) k := by
  induction k with
  | zero => funext n; simp [power, unitSequence, Function.comp_apply]
  | succ k ih => change φ ∘ product (power a k) a = _; rw [map_product, ih]; rfl

/-- Rational series reconstructed from its derivatives at zero. -/
noncomputable def qegf (a : ℕ → ℚ) : ℚ⟦X⟧ := mk fun n => a n / n.factorial

lemma jet_qegf (a : ℕ → ℚ) : jet (qegf a) = a := by
  funext n
  simp only [jet, qegf, coeff_mk]
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

lemma jet_injective : Function.Injective jet := by
  intro F G h
  ext n
  have he := congrFun h n
  exact mul_left_cancel₀ (by exact_mod_cast n.factorial_ne_zero) he

lemma qegf_jet (F : ℚ⟦X⟧) : qegf (jet F) = F :=
  jet_injective (jet_qegf _)

lemma jet_one : jet (1 : ℚ⟦X⟧) = unitSequence := by
  funext n
  cases n <;> simp [jet, unitSequence]

lemma jet_pow (F : ℚ⟦X⟧) (k : ℕ) : jet (F ^ k) = power (jet F) k := by
  induction k with
  | zero => simpa [power] using jet_one
  | succ k ih => rw [pow_succ, jet_product, ih]; rfl

/-- Finite ordinary coefficient formula for substitution by $xD(x)$. -/
theorem coeff_subst_X_mul (F D : ℚ⟦X⟧) (n : ℕ) :
    coeff n (F.subst (X * D)) =
      ∑ k ∈ range (n + 1), coeff k F * coeff (n - k) (D ^ k) := by
  classical
  have hg : HasSubst (X * D) := HasSubst.of_constantCoeff_zero' (by simp)
  rw [coeff_subst' hg]
  have hs : Function.support (fun k : ℕ => coeff k F • coeff n ((X * D) ^ k)) ⊆
      (range (n + 1) : Set ℕ) := by
    intro k hk
    by_contra hkn
    have hle : ¬k ≤ n := fun hk => hkn (mem_range.mpr (Nat.lt_succ_of_le hk))
    exact hk (by simp [mul_pow, coeff_X_pow_mul', hle])
  rw [finsum_eq_sum_of_support_subset _ hs]
  apply sum_congr rfl
  intro k hk
  have hle : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  simp [mul_pow, coeff_X_pow_mul', hle, smul_eq_mul]

/-- The finite substitution formula with factorials absorbed into integer EGF coefficients. -/
theorem jet_subst_X_mul (F D : ℚ⟦X⟧) (n : ℕ) :
    jet (F.subst (X * D)) n =
      ∑ k ∈ range (n + 1), (n.choose k : ℚ) * jet F k * jet (D ^ k) (n - k) := by
  simp only [jet, coeff_subst_X_mul, mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hf : (n.factorial : ℚ) = n.choose k * (k.factorial : ℚ) * (n - k).factorial := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hkn).symm
  rw [hf]
  ring

/-- Integral EGF substitution by $xD(x)$. -/
def composition (a d : ℕ → R) (n : ℕ) : R :=
  ∑ k ∈ range (n + 1), (n.choose k : R) * a k * power d k (n - k)

lemma jet_subst_qegf (a d : ℕ → ℚ) :
    jet ((qegf a).subst (X * qegf d)) = composition a d := by
  funext n
  rw [jet_subst_X_mul]
  simp only [jet_qegf, jet_pow, composition]

lemma qegf_composition (a d : ℕ → ℚ) :
    qegf (composition a d) = (qegf a).subst (X * qegf d) := by
  apply jet_injective
  rw [jet_qegf, jet_subst_qegf]

lemma map_composition {S : Type*} [CommRing S] (φ : R →+* S) (a d : ℕ → R) :
    φ ∘ composition a d = composition (φ ∘ a) (φ ∘ d) := by
  funext n
  simp only [composition, Function.comp_apply, map_sum, map_mul, map_natCast]
  apply sum_congr rfl
  intro k hk
  rw [← map_power]
  rfl

end Hurwitz

namespace Hurwitz
open PowerSeries
variable {R : Type*} [CommRing R]

/-- The EGF coefficients of the derivative of $xC(x)$. -/
def logDerivative (c : ℕ → R) (n : ℕ) : R := (n + 1) * c n

def expOperator (c a : ℕ → R) : ℕ → R
  | 0 => 1
  | n + 1 => product a (logDerivative c) n

lemma expOperator_causal (c : ℕ → R) : Causal.IsCausal (expOperator c) := by
  intro n a b h
  cases n with
  | zero => rfl
  | succ n =>
    apply product_congr
    · intro k hk; exact h k (Nat.lt_succ_of_le hk)
    · intro k hk; rfl

/-- Integral EGF exponential $\exp(xC(x))$, defined without division. -/
def expSequence (c : ℕ → R) : ℕ → R :=
  Causal.fixedPoint (expOperator c) 0

lemma expSequence_zero (c : ℕ → R) : expSequence c 0 = 1 := by
  exact Causal.fixedPoint_eq _ (expOperator_causal c) 0 0

lemma expSequence_succ (c : ℕ → R) (n : ℕ) :
    expSequence c (n + 1) = product (expSequence c) (logDerivative c) n := by
  exact Causal.fixedPoint_eq _ (expOperator_causal c) 0 (n + 1)

lemma expSequence_congr (a b : ℕ → R) (n : ℕ) (h : ∀ k < n, a k = b k) :
    expSequence a n = expSequence b n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => rw [expSequence_zero, expSequence_zero]
    | succ n =>
      rw [expSequence_succ, expSequence_succ]
      apply product_congr
      · intro k hk
        apply ih k (Nat.lt_succ_of_le hk)
        intro j hj
        exact h j (hj.trans (Nat.lt_succ_of_le hk))
      · intro k hk
        simp only [logDerivative]
        rw [h k (Nat.lt_succ_of_le hk)]

lemma map_expSequence {S : Type*} [CommRing S] (φ : R →+* S) (c : ℕ → R) :
    φ ∘ expSequence c = expSequence (φ ∘ c) := by
  funext n
  change φ (expSequence c n) = expSequence (φ ∘ c) n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [expSequence_zero]
    | succ n =>
      rw [expSequence_succ, expSequence_succ]
      change (φ ∘ product (expSequence c) (logDerivative c)) n = _
      rw [map_product]
      apply product_congr
      · intro k hk; exact ih k (Nat.lt_succ_of_le hk)
      · intro k hk
        simp [logDerivative, Function.comp_apply]

lemma jet_logDerivative (c : ℕ → ℚ) :
    jet (derivative ℚ (X * qegf c)) = logDerivative c := by
  funext n
  rw [jet_derivative]
  change jet (X * qegf c) (n + 1) = _
  rw [jet_X_mul_succ, jet_qegf]
  rfl

/-- Identification of the division-free exponential with the rational exponential series. -/
theorem jet_exp_X_qegf (c : ℕ → ℚ) :
    jet ((exp ℚ).subst (X * qegf c)) = expSequence c := by
  let G : ℚ⟦X⟧ := X * qegf c
  let E : ℚ⟦X⟧ := (exp ℚ).subst G
  have hG0 : G.constantCoeff = 0 := by simp [G]
  have hG : HasSubst G := HasSubst.of_constantCoeff_zero' hG0
  have hd : derivative ℚ E = E * derivative ℚ G := by
    dsimp [E]
    rw [derivative_subst hG, derivative_exp]
  have he0 : jet E 0 = 1 := by
    rw [jet_zero]
    exact (constantCoeff_subst_of_zero (exp ℚ) G hG0).trans (by simp)
  have hr (n : ℕ) : jet E (n + 1) = product (jet E) (logDerivative c) n := by
    change shift (jet E) n = _
    rw [← jet_derivative, hd, jet_product]
    change product (jet E) (jet (derivative ℚ (X * qegf c))) n = _
    rw [jet_logDerivative]
  funext n
  change jet E n = expSequence c n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => rw [he0, expSequence_zero]
    | succ n =>
      rw [hr, expSequence_succ]
      apply product_congr
      · intro k hk; exact ih k (Nat.lt_succ_of_le hk)
      · intro k hk; rfl

lemma qegf_expSequence (c : ℕ → ℚ) :
    qegf (expSequence c) = (exp ℚ).subst (X * qegf c) := by
  apply jet_injective
  rw [jet_qegf, jet_exp_X_qegf]

lemma egf_power (b : ℕ → ℤ) (k : ℕ) : egf (power b k) = egf b ^ k := by
  apply jet_injective
  rw [jet_egf, jet_pow, jet_egf, map_power]

lemma egf_composition (a d : ℕ → ℤ) :
    egf (composition a d) = (egf a).subst (X * egf d) := by
  change qegf (Int.castRingHom ℚ ∘ composition a d) =
    (qegf (Int.castRingHom ℚ ∘ a)).subst (X * qegf (Int.castRingHom ℚ ∘ d))
  rw [map_composition, qegf_composition]

lemma egf_expSequence (c : ℕ → ℤ) :
    egf (expSequence c) = (exp ℚ).subst (X * egf c) := by
  change qegf (Int.castRingHom ℚ ∘ expSequence c) =
    (exp ℚ).subst (X * qegf (Int.castRingHom ℚ ∘ c))
  rw [map_expSequence, qegf_expSequence]
end Hurwitz

namespace Hurwitz
open PowerSeries Finset
variable {R : Type*} [CommRing R]

lemma composition_zero (a d : ℕ → R) : composition a d 0 = a 0 := by
  simp [composition, power, unitSequence]

/-- The auxiliary source operator on integral EGF coefficients. -/
def auxiliaryOperator (r : ℕ) (b : ℕ → R) : ℕ → R :=
  composition (expSequence (power b 3)) (power b r)

lemma map_auxiliaryOperator {S : Type*} [CommRing S] (φ : R →+* S) (r : ℕ)
    (b : ℕ → R) :
    φ ∘ auxiliaryOperator r b = auxiliaryOperator r (φ ∘ b) := by
  simp only [auxiliaryOperator, map_composition, map_expSequence, map_power]

/-- A coefficient of the source operator uses only strictly earlier input coefficients. -/
theorem auxiliaryOperator_causal (r : ℕ) : Causal.IsCausal (auxiliaryOperator r (R := R)) := by
  intro n a b h
  unfold auxiliaryOperator composition
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  cases k with
  | zero => simp [power, expSequence_zero]
  | succ k =>
    have ho : expSequence (power a 3) (k + 1) = expSequence (power b 3) (k + 1) := by
      apply expSequence_congr
      intro i hi
      apply power_congr
      intro j hj
      exact h j (lt_of_le_of_lt hj (lt_of_lt_of_le hi hkn))
    have hi : power (power a r) (k + 1) (n - (k + 1)) =
        power (power b r) (k + 1) (n - (k + 1)) := by
      apply power_congr
      intro i hi
      apply power_congr
      intro j hj
      apply h
      omega
    rw [ho, hi]

lemma jet_subst_X (F D : ℚ⟦X⟧) :
    jet (F.subst (X * D)) = composition (jet F) (jet D) := by
  simpa only [qegf_jet] using jet_subst_qegf (jet F) (jet D)

lemma jet_exp_X_power (B : ℚ⟦X⟧) (k : ℕ) :
    jet ((exp ℚ).subst (X * B ^ k)) = expSequence (power (jet B) k) := by
  have h := jet_exp_X_qegf (jet (B ^ k))
  rw [qegf_jet, jet_pow] at h
  exact h
end Hurwitz

namespace Source
open Hurwitz PowerSeries

/-- The unique integral auxiliary fixed point for the complementary-exponent family. -/
def b (r : ℕ) : ℕ → ℤ := Causal.fixedPoint (auxiliaryOperator r) 0

lemma b_fixed (r : ℕ) : auxiliaryOperator r (b r) = b r := by
  funext n
  exact (Causal.fixedPoint_eq _ (auxiliaryOperator_causal r) 0 n).symm

/-- EGF coefficients of the normalized source solution. -/
def a (r : ℕ) : ℕ → ℤ := expSequence (power (b r) 3)

lemma a_zero (r : ℕ) : a r 0 = 1 := expSequence_zero _

lemma b_zero (r : ℕ) : b r 0 = 1 := by
  rw [← congrFun (b_fixed r) 0]
  exact (composition_zero _ _).trans (expSequence_zero _)

lemma generating_function (r : ℕ) :
    egf (a r) = (exp ℚ).subst (X * egf (b r) ^ 3) := by
  rw [a, egf_expSequence, egf_power]

lemma auxiliary_function (r : ℕ) :
    egf (b r) = (egf (a r)).subst (X * egf (b r) ^ r) := by
  conv_lhs => rw [← b_fixed r]
  change egf (composition (a r) (power (b r) r)) = _
  rw [egf_composition, egf_power]

/-- The constructed integer EGF satisfies the original source equation. -/
theorem original (r s : ℕ) (hrs : r + s = 3) : Original r s (egf (a r)) := by
  apply auxiliary_original (B := egf (b r))
  · simpa [← jet_zero, jet_egf, Function.comp_apply] using
      congrArg (Int.castRingHom ℚ) (b_zero r)
  · exact auxiliary_function r
  · rw [hrs]
    exact generating_function r

/-- Every normalized rational source solution is the constructed integer EGF. -/
theorem eq_egf {r s : ℕ} (hrs : r + s = 3) {F : ℚ⟦X⟧} (hF : Original r s F) :
    F = egf (a r) := by
  obtain ⟨B, _, hB, hA⟩ := original_auxiliary hF
  have hAj : jet F = expSequence (power (jet B) 3) := by
    rw [hA, hrs, jet_exp_X_power]
  have hBj : auxiliaryOperator r (jet B) = jet B := by
    have he := congrArg jet hB
    rw [jet_subst_X, jet_pow, hAj] at he
    exact he.symm
  have hm : auxiliaryOperator r (Int.castRingHom ℚ ∘ b r) = Int.castRingHom ℚ ∘ b r := by
    rw [← map_auxiliaryOperator, b_fixed]
  have heq : jet B = Int.castRingHom ℚ ∘ b r :=
    (Causal.exists_unique_fixed_point (auxiliaryOperator r) (auxiliaryOperator_causal r)
      (0 : ℕ → ℚ)).unique hBj hm
  apply jet_injective
  rw [hAj, jet_egf, heq, ← map_power, ← map_expSequence]
  rfl

/-- Existence and uniqueness for the original normalized equation, with integral EGF coefficients. -/
theorem exists_unique_original (r s : ℕ) (hrs : r + s = 3) :
    ∃! F : ℚ⟦X⟧, Original r s F := by
  exact ⟨egf (a r), original r s hrs, fun _ hF => eq_egf hrs hF⟩

/-- Every coefficient of the original integer EGF is one modulo three. -/
theorem mod_three (r : ℕ) (n : ℕ) : (a r n : ZMod 3) = 1 :=
  exp_cube_mod_three (a r) (b r) (a_zero r) (b_zero r) (generating_function r) n

/-- Unconditional modulo-three result stated directly for every normalized source solution. -/
theorem original_mod_three (r s : ℕ) (hrs : r + s = 3) :
    (∃! F : ℚ⟦X⟧, Original r s F) ∧
      ∀ F : ℚ⟦X⟧, Original r s F →
        ∃ c : ℕ → ℤ, egf c = F ∧ ∀ n, c n % 3 = 1 := by
  refine ⟨exists_unique_original r s hrs, ?_⟩
  intro F hF
  refine ⟨a r, (eq_egf hrs hF).symm, ?_⟩
  intro n
  have he : (a r n : ZMod 3) = ((1 : ℤ) : ZMod 3) := mod_three r n
  simpa using (ZMod.intCast_eq_intCast_iff' (a r n) 1 3).mp he
end Source

/-- The modulo-three conjecture for OEIS A368630, including existence and source identification. -/
theorem a368630_mod_three :
    (∃! F : ℚ⟦X⟧, Original 2 1 F) ∧
      ∀ F : ℚ⟦X⟧, Original 2 1 F →
        ∃ a : ℕ → ℤ, egf a = F ∧ ∀ n, a n % 3 = 1 :=
  Source.original_mod_three 2 1 rfl

namespace Hurwitz
open PowerSeries Finset
variable {R : Type*} [CommRing R]

lemma product_zero_left (a : ℕ → R) : product 0 a = 0 := by
  rw [product_comm, product_zero_right]
lemma power_one (a : ℕ → R) : power a 1 = a := by
  change product unitSequence a = a
  rw [product_comm, product_unit]
lemma power_two (a : ℕ → R) : power a 2 = product a a := by
  change product (power a 1) a = _
  rw [power_one]
lemma power_unit (k : ℕ) : power (unitSequence : ℕ → R) k = unitSequence := by
  induction k with
  | zero => rfl
  | succ k ih => change product (power unitSequence k) unitSequence = _; rw [ih, product_unit]
lemma composition_unit (a : ℕ → R) : composition a unitSequence = a := by
  funext n
  rw [composition, sum_eq_single n]
  · simp [power_unit, unitSequence]
  · intro k hk hkn
    have hn : n - k ≠ 0 := by have := mem_range.mp hk; omega
    simp [power_unit, unitSequence, hn]
  · simp
lemma square_unit_two (a : ℕ → ZMod 2) (h0 : a 0 = 1) :
    product a a = unitSequence := by
  funext n
  cases n with
  | zero => simp [unitSequence, h0]
  | succ n => simpa [unitSequence] using square_succ_two a n
lemma power_two_unit (a : ℕ → ZMod 2) (h0 : a 0 = 1) : power a 2 = unitSequence := by
  rw [power_two, square_unit_two a h0]
lemma power_three_two (a : ℕ → ZMod 2) (h0 : a 0 = 1) : power a 3 = a := by
  change product (power a 2) a = a
  rw [power_two_unit a h0, product_comm, product_unit]

/-- The EGF variable has coefficient one at index one. -/
def xSequence : ℕ → R := fun n => if n = 1 then 1 else 0
lemma shift_x : shift (xSequence : ℕ → R) = unitSequence := by
  funext n
  cases n <;> simp [shift, xSequence, unitSequence]
lemma product_x_succ (a : ℕ → R) (n : ℕ) :
    product xSequence a (n + 1) = (n + 1) * a n := by
  induction n generalizing a with
  | zero => simp [product_succ, shift_x, product_zero, xSequence, unitSequence]
  | succ n ih =>
    rw [product_succ, shift_x, product_comm unitSequence a, product_unit, ih]
    simp only [shift]
    push_cast
    ring
lemma logDerivative_eq (a : ℕ → R) :
    logDerivative a = a + product xSequence (shift a) := by
  funext n
  cases n with
  | zero => simp [logDerivative, product_zero, xSequence]
  | succ n =>
    simp only [logDerivative, Pi.add_apply, product_x_succ, shift]
    push_cast
    ring
lemma product_mul_product (a b c d : ℕ → R) :
    product (product a b) (product c d) = product (product a c) (product b d) := by
  rw [product_assoc a b (product c d), ← product_assoc b c d, product_comm b c,
    product_assoc c b d, ← product_assoc a c (product b d)]
lemma square_x_two : product (xSequence : ℕ → ZMod 2) xSequence = 0 := by
  funext n
  cases n with
  | zero => simp [product_zero, xSequence]
  | succ n => exact square_succ_two xSequence n

/-- Parity forced by the integral EGF equation $A=\exp(xA)$. -/
theorem parity_of_exp_fix (a : ℕ → ZMod 2) (h0 : a 0 = 1)
    (ha : a = expSequence a) :
    (∀ n, a (2 * n) = 1) ∧ (∀ n, 1 ≤ n → a (2 * n + 1) = 0) := by
  have hd : shift a = product a (logDerivative a) := by
    funext n
    change a (n + 1) = _
    rw [congrFun ha (n + 1), expSequence_succ, ← ha]
  let c := product (xSequence : ℕ → ZMod 2) a
  have hc : product c c = 0 := by
    dsimp [c]
    rw [product_mul_product, square_x_two, product_zero_left]
  have hs : shift a = unitSequence + product c (shift a) := by
    rw [logDerivative_eq, product_add_right, square_unit_two a h0] at hd
    rw [← product_assoc a xSequence (shift a), product_comm a xSequence] at hd
    exact hd
  have hcs : product c (shift a) = c := by
    calc
      product c (shift a) = product c (unitSequence + product c (shift a)) := congrArg (product c) hs
      _ = c := by rw [product_add_right, product_unit, ← product_assoc, hc, product_zero_left, add_zero]
  have hf : shift a = unitSequence + product xSequence a := by rw [hs, hcs]
  have hr (n : ℕ) : a (n + 2) = (n + 1) * a n := by
    have he := congrFun hf (n + 1)
    simpa [shift, unitSequence, product_x_succ, Nat.add_assoc] using he
  constructor
  · intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      have he := hr (2 * n)
      have hm : ((2 * n : ℕ) : ZMod 2) + 1 = 1 := by
        have hz : (2 : ZMod 2) = 0 := by decide
        push_cast
        rw [hz, zero_mul, zero_add]
      rw [hm, one_mul, ih] at he
      exact he
  · intro n hn
    cases n with
    | zero => omega
    | succ n =>
      have he := hr (2 * n + 1)
      have hm : ((2 * n + 1 : ℕ) : ZMod 2) + 1 = 0 := by
        have hz : (2 : ZMod 2) = 0 := by decide
        push_cast
        rw [hz, zero_mul, zero_add]
        decide
      rw [hm, zero_mul] at he
      exact he
end Hurwitz

namespace Source
open Hurwitz

/-- The auxiliary substitution of A368630 reduces to the identity modulo two. -/
theorem primary_exp_fix :
    Int.castRingHom (ZMod 2) ∘ a 2 = expSequence (Int.castRingHom (ZMod 2) ∘ a 2) := by
  let φ := Int.castRingHom (ZMod 2)
  let A := φ ∘ a 2
  let B := φ ∘ b 2
  have hb0 : B 0 = 1 := by simp [B, Function.comp_apply, b_zero, φ]
  have hb : B = composition A (power B 2) := by
    have he := congrArg (fun f : ℕ → ℤ => φ ∘ f) (b_fixed 2).symm
    change B = φ ∘ composition (a 2) (power (b 2) 2) at he
    rw [map_composition, map_power] at he
    exact he
  rw [power_two_unit B hb0, composition_unit] at hb
  have he : A = expSequence (power B 3) := by
    change φ ∘ expSequence (power (b 2) 3) = _
    rw [map_expSequence, map_power]
  rw [power_three_two B hb0, hb] at he
  exact he

/-- Both parity clauses for the actual A368630 source sequence. -/
theorem primary_parity :
    (∀ n, a 2 (2 * n) % 2 = 1) ∧
      (∀ n, 1 ≤ n → a 2 (2 * n + 1) % 2 = 0) := by
  have h0 : (Int.castRingHom (ZMod 2) ∘ a 2) 0 = 1 := by simp [Function.comp_apply, a_zero]
  obtain ⟨he, ho⟩ := parity_of_exp_fix _ h0 primary_exp_fix
  constructor
  · intro n
    have h : (a 2 (2 * n) : ZMod 2) = ((1 : ℤ) : ZMod 2) := he n
    simpa using (ZMod.intCast_eq_intCast_iff' (a 2 (2 * n)) 1 2).mp h
  · intro n hn
    have h : (a 2 (2 * n + 1) : ZMod 2) = ((0 : ℤ) : ZMod 2) := ho n hn
    simpa using (ZMod.intCast_eq_intCast_iff' (a 2 (2 * n + 1)) 0 2).mp h
end Source

/-- All three A368630 congruences for the unique normalized solution of the original equation. -/
theorem a368630_congruences : Target 2 1 := by
  refine ⟨Source.exists_unique_original 2 1 rfl, ?_⟩
  intro F hF
  refine ⟨Source.a 2, (Source.eq_egf rfl hF).symm, ?_, Source.primary_parity⟩
  intro n
  have h : (Source.a 2 n : ZMod 3) = ((1 : ℤ) : ZMod 3) := Source.mod_three 2 n
  simpa using (ZMod.intCast_eq_intCast_iff' (Source.a 2 n) 1 3).mp h

/-- The modulo-three conjecture for OEIS A368631, with the original exponent pair $(1,2)$. -/
theorem a368631_mod_three :
    (∃! F : ℚ⟦X⟧, Original 1 2 F) ∧
      ∀ F : ℚ⟦X⟧, Original 1 2 F →
        ∃ a : ℕ → ℤ, egf a = F ∧ ∀ n, a n % 3 = 1 :=
  Source.original_mod_three 1 2 rfl

end OeisA368630

namespace OeisA368630
open PowerSeries

/-- The defining equation for the integer EGF coefficients of OEIS A368630. -/
def IsGeneratingSequence (c : ℕ → ℤ) : Prop :=
  (egf c).constantCoeff = 1 ∧
    (egf c).subst (X * ((egf c)⁻¹) ^ 2) = (exp ℚ).subst (X * egf c)

/-- The integer coefficients of the normalized exponential generating function. -/
noncomputable def a : ℕ → ℤ := Classical.epsilon IsGeneratingSequence

lemma isGeneratingSequence_iff (c : ℕ → ℤ) :
    IsGeneratingSequence c ↔ Original 2 1 (egf c) := by
  simp only [IsGeneratingSequence, Original, pow_one]

lemma egf_injective : Function.Injective egf := by
  intro c d h
  have hj := congrArg Hurwitz.jet h
  rw [Hurwitz.jet_egf, Hurwitz.jet_egf] at hj
  funext n
  have he := congrFun hj n
  change (c n : ℚ) = (d n : ℚ) at he
  exact_mod_cast he

lemma constructed_spec : IsGeneratingSequence (Source.a 2) := by
  rw [isGeneratingSequence_iff]
  exact Source.original 2 1 rfl

/-- The original equation defines a unique integer coefficient sequence. -/
theorem exists_unique_sequence : ∃! c : ℕ → ℤ, IsGeneratingSequence c := by
  refine ⟨Source.a 2, constructed_spec, ?_⟩
  intro c hc
  apply egf_injective
  exact Source.eq_egf (r := 2) (s := 1) rfl ((isGeneratingSequence_iff c).mp hc)

/-- The selected sequence satisfies the source equation. -/
theorem a_spec : IsGeneratingSequence a :=
  Classical.epsilon_spec exists_unique_sequence.exists

lemma a_eq_constructed : a = Source.a 2 :=
  exists_unique_sequence.unique a_spec constructed_spec

/-- Every term is one modulo three. -/
theorem conjecture_mod_three (n : ℕ) : a n % 3 = 1 := by
  rw [a_eq_constructed]
  have h : (Source.a 2 n : ZMod 3) = ((1 : ℤ) : ZMod 3) := Source.mod_three 2 n
  simpa using (ZMod.intCast_eq_intCast_iff' (Source.a 2 n) 1 3).mp h

/-- Every even-indexed term is odd. -/
theorem conjecture_even (n : ℕ) : a (2 * n) % 2 = 1 := by
  rw [a_eq_constructed]
  exact Source.primary_parity.1 n

/-- Every odd-indexed term beyond index one is even. -/
theorem conjecture_odd (n : ℕ) (hn : 1 ≤ n) : a (2 * n + 1) % 2 = 0 := by
  rw [a_eq_constructed]
  exact Source.primary_parity.2 n hn

open OeisA368630 OeisA368630.Hurwitz in
private lemma primary_b_1 : Source.b 2 1 = 1 := by
  have h := congrFun (Source.b_fixed 2) 1
  norm_num [auxiliaryOperator, composition, Finset.sum_range_succ, power, product,
    shift, logDerivative, unitSequence, expSequence_zero, expSequence_succ,
    Source.b_zero] at h
  exact h.symm

open OeisA368630 OeisA368630.Hurwitz in
private lemma primary_b_2 : Source.b 2 2 = 11 := by
  have h := congrFun (Source.b_fixed 2) 2
  norm_num [auxiliaryOperator, composition, Finset.sum_range_succ, power, product,
    shift, logDerivative, unitSequence, expSequence_zero, expSequence_succ,
    Source.b_zero, primary_b_1] at h
  exact h.symm

open OeisA368630 OeisA368630.Hurwitz in
private lemma primary_b_3 : Source.b 2 3 = 292 := by
  have h := congrFun (Source.b_fixed 2) 3
  norm_num [auxiliaryOperator, composition, Finset.sum_range_succ, power, product,
    shift, logDerivative, unitSequence, expSequence_zero, expSequence_succ,
    Source.b_zero, primary_b_1, primary_b_2] at h
  exact h.symm

private theorem constructed_a_0 : OeisA368630.Source.a 2 0 = 1 := OeisA368630.Source.a_zero 2
open OeisA368630 OeisA368630.Hurwitz in
private theorem constructed_a_1 : Source.a 2 1 = 1 := by
  norm_num [Source.a, expSequence_succ, expSequence_zero, logDerivative, power,
    product, shift, unitSequence, Source.b_zero]
open OeisA368630 OeisA368630.Hurwitz in
private theorem constructed_a_2 : Source.a 2 2 = 7 := by
  norm_num [Source.a, expSequence_succ, expSequence_zero, logDerivative, power,
    product, shift, unitSequence, Source.b_zero, primary_b_1]
open OeisA368630 OeisA368630.Hurwitz in
private theorem constructed_a_3 : Source.a 2 3 = 136 := by
  norm_num [Source.a, expSequence_succ, expSequence_zero, logDerivative, power,
    product, shift, unitSequence, Source.b_zero, primary_b_1, primary_b_2]
open OeisA368630 OeisA368630.Hurwitz in
private theorem constructed_a_4 : Source.a 2 4 = 4933 := by
  norm_num [Source.a, expSequence_succ, expSequence_zero, logDerivative, power,
    product, shift, unitSequence, Source.b_zero, primary_b_1, primary_b_2, primary_b_3]

theorem a_0 : a 0 = 1 := by
  rw [a_eq_constructed]
  exact constructed_a_0

theorem a_1 : a 1 = 1 := by
  rw [a_eq_constructed]
  exact constructed_a_1

theorem a_2 : a 2 = 7 := by
  rw [a_eq_constructed]
  exact constructed_a_2

theorem a_3 : a 3 = 136 := by
  rw [a_eq_constructed]
  exact constructed_a_3

theorem a_4 : a 4 = 4933 := by
  rw [a_eq_constructed]
  exact constructed_a_4

end OeisA368630
