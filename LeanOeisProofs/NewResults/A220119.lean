/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
import LeanOeisProofs.NewResults.A098275

/-!
# OEIS A220119

`a220119 n` is the exact OEIS double binomial sum.  This file formalizes
the elementary `n + 1` factor and the Vandermonde, Catalan, binomial,
`U`--`V`, and small-prime Lucas ingredients of the elementary proof,
including the full `(n + 1) * (n + 2)` divisibility theorem.
-/

open Finset Nat

/-- The OEIS A220119 double binomial sum, exactly as published. -/
def a220119 (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1),
    ∑ k ∈ Finset.range (n + 1),
      n.choose j ^ 2 *
      n.choose k ^ 2 *
      (n + j).choose n *
      (n + k).choose n *
      (j + k).choose n

/-- The elementary-proof weight
`U(n,r) = ∑_{j=0}^n C(n,j)^2 C(n+j,n) C(j,r)`. -/
def a220119Weight (n r : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1),
    n.choose j ^ 2 * (n + j).choose n * j.choose r

/-- Vandermonde with the complementary lower index, in the exact finite
range used by `a220119`. -/
lemma choose_add_eq_sum_choose_mul_choose_sub (n j k : ℕ) :
    (j + k).choose n =
      ∑ r ∈ Finset.range (n + 1), j.choose r * k.choose (n - r) := by
  rw [Nat.add_choose_eq,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => j.choose a * k.choose b)]

/-- The exact Vandermonde convolution
`a220119 n = ∑_{r=0}^n U(n,r) U(n,n-r)`. -/
theorem a220119_eq_weight_convolution (n : ℕ) :
    a220119 n =
      ∑ r ∈ Finset.range (n + 1),
        a220119Weight n r * a220119Weight n (n - r) := by
  unfold a220119
  calc
    (∑ j ∈ range (n + 1), ∑ k ∈ range (n + 1),
        n.choose j ^ 2 * n.choose k ^ 2 *
          (n + j).choose n * (n + k).choose n * (j + k).choose n)
        =
      ∑ j ∈ range (n + 1), ∑ k ∈ range (n + 1),
        ∑ r ∈ range (n + 1),
          (n.choose j ^ 2 * (n + j).choose n * j.choose r) *
          (n.choose k ^ 2 * (n + k).choose n * k.choose (n - r)) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [choose_add_eq_sum_choose_mul_choose_sub n j k, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring_nf
    _ =
      ∑ j ∈ range (n + 1), ∑ r ∈ range (n + 1),
        ∑ k ∈ range (n + 1),
          (n.choose j ^ 2 * (n + j).choose n * j.choose r) *
          (n.choose k ^ 2 * (n + k).choose n * k.choose (n - r)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ =
      ∑ r ∈ range (n + 1), ∑ j ∈ range (n + 1),
        ∑ k ∈ range (n + 1),
          (n.choose j ^ 2 * (n + j).choose n * j.choose r) *
          (n.choose k ^ 2 * (n + k).choose n * k.choose (n - r)) :=
      Finset.sum_comm
    _ =
      ∑ r ∈ range (n + 1),
        (∑ j ∈ range (n + 1),
          n.choose j ^ 2 * (n + j).choose n * j.choose r) *
        (∑ k ∈ range (n + 1),
          n.choose k ^ 2 * (n + k).choose n * k.choose (n - r)) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ =
      ∑ r ∈ range (n + 1),
        a220119Weight n r * a220119Weight n (n - r) := by
      rfl

/-- Every weight contains its Catalan factor `r + 1`. -/
theorem add_one_dvd_a220119Weight (n r : ℕ) :
    r + 1 ∣ a220119Weight n r := by
  unfold a220119Weight
  apply Finset.dvd_sum
  intro j _
  rw [choose_sq_mul_choose_mul_choose_eq n j r]
  exact dvd_mul_right (r + 1) _

/-- The binomial coefficient `C(n,r)` divides the weight `U(n,r)`. -/
theorem choose_dvd_a220119Weight (n r : ℕ) :
    n.choose r ∣ a220119Weight n r := by
  unfold a220119Weight
  apply Finset.dvd_sum
  intro j hj
  rw [Finset.mem_range] at hj
  by_cases hrj : r ≤ j
  · have hchoose :
        n.choose j * j.choose r =
          n.choose r * (n - r).choose (j - r) :=
      Nat.choose_mul hrj
    refine ⟨n.choose j * (n + j).choose n * (n - r).choose (j - r), ?_⟩
    calc
      n.choose j ^ 2 * (n + j).choose n * j.choose r
          = (n.choose j * j.choose r) *
              (n.choose j * (n + j).choose n) := by ring
      _ = (n.choose r * (n - r).choose (j - r)) *
              (n.choose j * (n + j).choose n) := by rw [hchoose]
      _ = n.choose r *
            (n.choose j * (n + j).choose n * (n - r).choose (j - r)) := by
            ring
  · rw [Nat.choose_eq_zero_of_lt (by omega : j < r), mul_zero]
    exact dvd_zero _

/-- The auxiliary sum
`V(n,r) = ∑_{j=r}^n C(n,j)^2 C(n+j,j-2) C(j-2,r-2)`. -/
def a220119V (n r : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc r n,
    n.choose j ^ 2 * (n + j).choose (j - 2) * (j - 2).choose (r - 2)

/-- Restrict `U(n,r)` to its natural support `r ≤ j ≤ n`; all omitted
finite-range terms vanish because `C(j,r) = 0`. -/
lemma a220119Weight_eq_sum_Icc (n r : ℕ) :
    a220119Weight n r =
      ∑ j ∈ Finset.Icc r n,
        n.choose j ^ 2 * (n + j).choose n * j.choose r := by
  unfold a220119Weight
  symm
  apply Finset.sum_subset
  · intro j hj
    rw [Finset.mem_Icc] at hj
    rw [Finset.mem_range]
    omega
  · intro j hjrange hjIcc
    rw [Finset.mem_range] at hjrange
    have hjr : j < r := by
      by_contra h
      exact hjIcc (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [Nat.choose_eq_zero_of_lt hjr, mul_zero]

/-- The first exact adjacent-binomial identity used in the `V` argument. -/
lemma mul_pred_mul_choose_eq (j r : ℕ) (hr : 2 ≤ r) (hrj : r ≤ j) :
    r * (r - 1) * j.choose r =
      j * (j - 1) * (j - 2).choose (r - 2) := by
  have h₁ :
      j * (j - 1).choose (r - 1) = j.choose r * r := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j),
      Nat.sub_add_cancel (by omega : 1 ≤ r)] using
      Nat.add_one_mul_choose_eq (j - 1) (r - 1)
  have hjsub : j - 2 + 1 = j - 1 := by omega
  have hrsub : r - 2 + 1 = r - 1 := by omega
  have h₂ :
      (j - 1) * (j - 2).choose (r - 2) =
        (j - 1).choose (r - 1) * (r - 1) := by
    simpa only [hjsub, hrsub] using
      Nat.add_one_mul_choose_eq (j - 2) (r - 2)
  calc
    r * (r - 1) * j.choose r
        = (j.choose r * r) * (r - 1) := by ring
    _ = (j * (j - 1).choose (r - 1)) * (r - 1) := by rw [h₁]
    _ = j * ((j - 1).choose (r - 1) * (r - 1)) := by ring
    _ = j * ((j - 1) * (j - 2).choose (r - 2)) := by rw [h₂]
    _ = j * (j - 1) * (j - 2).choose (r - 2) := by ring

/-- The second exact adjacent-binomial identity used in the `V` argument. -/
lemma mul_pred_mul_add_choose_eq (n j : ℕ) (hj : 2 ≤ j) :
    j * (j - 1) * (n + j).choose n =
      (n + 1) * (n + 2) * (n + j).choose (j - 2) := by
  have h₁ :
      (n + j).choose n * j =
        (n + 1) * (n + j).choose (n + 1) := by
    have h := Nat.choose_succ_right_eq (n + j) n
    rw [show n + j - n = j by omega] at h
    calc
      (n + j).choose n * j
          = (n + j).choose (n + 1) * (n + 1) := h.symm
      _ = (n + 1) * (n + j).choose (n + 1) := by ring
  have h₂ :
      (n + j).choose (n + 1) * (j - 1) =
        (n + 2) * (n + j).choose (n + 2) := by
    have h := Nat.choose_succ_right_eq (n + j) (n + 1)
    rw [show n + j - (n + 1) = j - 1 by omega] at h
    calc
      (n + j).choose (n + 1) * (j - 1)
          = (n + j).choose (n + 2) * (n + 2) := h.symm
      _ = (n + 2) * (n + j).choose (n + 2) := by ring
  have hsymm :
      (n + j).choose (n + 2) = (n + j).choose (j - 2) := by
    apply Nat.choose_symm_of_eq_add
    omega
  calc
    j * (j - 1) * (n + j).choose n
        = ((n + j).choose n * j) * (j - 1) := by ring
    _ = ((n + 1) * (n + j).choose (n + 1)) * (j - 1) := by rw [h₁]
    _ = (n + 1) *
          ((n + j).choose (n + 1) * (j - 1)) := by ring
    _ = (n + 1) * ((n + 2) * (n + j).choose (n + 2)) := by rw [h₂]
    _ = (n + 1) * (n + 2) * (n + j).choose (j - 2) := by
      rw [hsymm]
      ring

/-- For `2 ≤ r ≤ n`, the exact `U`--`V` identity
`r(r-1)U(n,r) = (n+1)(n+2)V(n,r)`. -/
theorem mul_pred_mul_a220119Weight_eq (n r : ℕ) (hr : 2 ≤ r) (_hrn : r ≤ n) :
    r * (r - 1) * a220119Weight n r =
      (n + 1) * (n + 2) * a220119V n r := by
  rw [a220119Weight_eq_sum_Icc n r, a220119V,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_Icc] at hj
  have hchoose := mul_pred_mul_choose_eq j r hr hj.1
  have haddchoose := mul_pred_mul_add_choose_eq n j (by omega)
  calc
    r * (r - 1) *
          (n.choose j ^ 2 * (n + j).choose n * j.choose r)
        = n.choose j ^ 2 * (n + j).choose n *
            (r * (r - 1) * j.choose r) := by ring
    _ = n.choose j ^ 2 * (n + j).choose n *
            (j * (j - 1) * (j - 2).choose (r - 2)) := by rw [hchoose]
    _ = n.choose j ^ 2 *
          (j * (j - 1) * (n + j).choose n) *
          (j - 2).choose (r - 2) := by ring
    _ = n.choose j ^ 2 *
          ((n + 1) * (n + 2) * (n + j).choose (j - 2)) *
          (j - 2).choose (r - 2) := by rw [haddchoose]
    _ = (n + 1) * (n + 2) *
          (n.choose j ^ 2 * (n + j).choose (j - 2) *
            (j - 2).choose (r - 2)) := by ring

/-- The one-binary-digit Lucas consequence used by the parity arguments:
an even upper index and an odd lower index give an even binomial coefficient. -/
lemma two_dvd_choose_two_mul_two_mul_add_one (a b : ℕ) :
    2 ∣ (2 * a).choose (2 * b + 1) := by
  rw [← Nat.modEq_zero_iff_dvd]
  calc
    (2 * a).choose (2 * b + 1) ≡
        ((2 * a) % 2).choose ((2 * b + 1) % 2) *
          ((2 * a) / 2).choose ((2 * b + 1) / 2) [MOD 2] :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat
    _ = 0 := by norm_num

/-- Lucas modulo `2`: if `n` is even and `r` is odd, then `U(n,r)` is even. -/
theorem two_dvd_a220119Weight_of_even_of_odd
    (n r : ℕ) (hn : Even n) (hr : Odd r) :
    2 ∣ a220119Weight n r := by
  obtain ⟨N, rfl⟩ := even_iff_exists_two_mul.mp hn
  obtain ⟨R, rfl⟩ := odd_iff_exists_bit1.mp hr
  unfold a220119Weight
  apply Finset.dvd_sum
  intro j _
  rcases Nat.even_or_odd j with hj | hj
  · obtain ⟨J, rfl⟩ := even_iff_exists_two_mul.mp hj
    exact Dvd.dvd.mul_left (two_dvd_choose_two_mul_two_mul_add_one J R) _
  · obtain ⟨J, rfl⟩ := odd_iff_exists_bit1.mp hj
    rcases two_dvd_choose_two_mul_two_mul_add_one N J with ⟨q, hq⟩
    refine ⟨q * ((2 * N).choose (2 * J + 1) *
      (2 * N + (2 * J + 1)).choose (2 * N) *
      (2 * J + 1).choose (2 * R + 1)), ?_⟩
    rw [hq]
    ring

/-- Lucas modulo `2` for the auxiliary sum: if `n` is even, `r` is odd,
and `3 ≤ r`, then `V(n,r)` is even. -/
theorem two_dvd_a220119V_of_even_of_odd
    (n r : ℕ) (hn : Even n) (hr : Odd r) (hr3 : 3 ≤ r) :
    2 ∣ a220119V n r := by
  obtain ⟨N, rfl⟩ := even_iff_exists_two_mul.mp hn
  obtain ⟨R, hrR⟩ := odd_iff_exists_bit1.mp hr
  subst r
  unfold a220119V
  apply Finset.dvd_sum
  intro j hj
  rw [Finset.mem_Icc] at hj
  rcases Nat.even_or_odd j with hjeven | hjodd
  · obtain ⟨J, rfl⟩ := even_iff_exists_two_mul.mp hjeven
    have htop : 2 * J - 2 = 2 * (J - 1) := by omega
    have hbottom : 2 * R + 1 - 2 = 2 * (R - 1) + 1 := by omega
    rw [htop, hbottom]
    exact Dvd.dvd.mul_left
      (two_dvd_choose_two_mul_two_mul_add_one (J - 1) (R - 1)) _
  · obtain ⟨J, rfl⟩ := odd_iff_exists_bit1.mp hjodd
    rcases two_dvd_choose_two_mul_two_mul_add_one N J with ⟨q, hq⟩
    refine ⟨q * ((2 * N).choose (2 * J + 1) *
      (2 * N + (2 * J + 1)).choose (2 * J + 1 - 2) *
      (2 * J + 1 - 2).choose (2 * R + 1 - 2)), ?_⟩
    rw [hq]
    ring

/-- Split a range of length `3N+2` into complete residue triples and the
final residues `3N, 3N+1`. -/
lemma sum_range_three_mul_add_two (f : ℕ → ℕ) (N : ℕ) :
    ∑ j ∈ range (3 * N + 2), f j =
      (∑ J ∈ range N, ((f (3 * J) + f (3 * J + 1)) + f (3 * J + 2))) +
        (f (3 * N) + f (3 * N + 1)) := by
  induction N with
  | zero => norm_num [Finset.sum_range_succ]
  | succ N ih =>
      rw [show 3 * (N + 1) + 2 = (3 * N + 2) + 1 + 1 + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        ih, Finset.sum_range_succ]
      ring_nf

/-- One-digit Lucas: `C(3a+1,3b) ≡ C(a,b) (mod 3)`. -/
lemma choose_three_mul_add_one_three_mul_modEq (a b : ℕ) :
    (3 * a + 1).choose (3 * b) ≡ a.choose b [MOD 3] := by
  have ha : (3 * a + 1) / 3 = a := by omega
  calc
    (3 * a + 1).choose (3 * b) ≡
        ((3 * a + 1) % 3).choose ((3 * b) % 3) *
          ((3 * a + 1) / 3).choose ((3 * b) / 3) [MOD 3] :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat
    _ = a.choose b := by norm_num [ha]

/-- One-digit Lucas: `C(3a+1,3b+1) ≡ C(a,b) (mod 3)`. -/
lemma choose_three_mul_add_one_three_mul_add_one_modEq (a b : ℕ) :
    (3 * a + 1).choose (3 * b + 1) ≡ a.choose b [MOD 3] := by
  have ha : (3 * a + 1) / 3 = a := by omega
  have hb : (3 * b + 1) / 3 = b := by omega
  calc
    (3 * a + 1).choose (3 * b + 1) ≡
        ((3 * a + 1) % 3).choose ((3 * b + 1) % 3) *
          ((3 * a + 1) / 3).choose ((3 * b + 1) / 3) [MOD 3] :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat
    _ = a.choose b := by norm_num [ha, hb]

/-- One-digit Lucas: `C(3a+1,3b+2)` vanishes modulo `3`. -/
lemma choose_three_mul_add_one_three_mul_add_two_modEq (a b : ℕ) :
    (3 * a + 1).choose (3 * b + 2) ≡ 0 [MOD 3] := by
  calc
    (3 * a + 1).choose (3 * b + 2) ≡
        ((3 * a + 1) % 3).choose ((3 * b + 2) % 3) *
          ((3 * a + 1) / 3).choose ((3 * b + 2) / 3) [MOD 3] :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat
    _ = 0 := by norm_num

/-- One-digit Lucas: `C(3a,3b) ≡ C(a,b) (mod 3)`. -/
lemma choose_three_mul_three_mul_modEq (a b : ℕ) :
    (3 * a).choose (3 * b) ≡ a.choose b [MOD 3] := by
  calc
    (3 * a).choose (3 * b) ≡
        ((3 * a) % 3).choose ((3 * b) % 3) *
          ((3 * a) / 3).choose ((3 * b) / 3) [MOD 3] :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat
    _ = a.choose b := by norm_num

/-- One-digit Lucas: `C(3a+2,3b+1) ≡ 2 C(a,b) (mod 3)`. -/
lemma choose_three_mul_add_two_three_mul_add_one_modEq (a b : ℕ) :
    (3 * a + 2).choose (3 * b + 1) ≡ 2 * a.choose b [MOD 3] := by
  have ha : (3 * a + 2) / 3 = a := by omega
  have hb : (3 * b + 1) / 3 = b := by omega
  calc
    (3 * a + 2).choose (3 * b + 1) ≡
        ((3 * a + 2) % 3).choose ((3 * b + 1) % 3) *
          ((3 * a + 2) / 3).choose ((3 * b + 1) / 3) [MOD 3] :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat
    _ = 2 * a.choose b := by norm_num [ha, hb]

/-- One-digit Lucas: `C(3a+2,3b+2) ≡ C(a,b) (mod 3)`. -/
lemma choose_three_mul_add_two_three_mul_add_two_modEq (a b : ℕ) :
    (3 * a + 2).choose (3 * b + 2) ≡ a.choose b [MOD 3] := by
  have ha : (3 * a + 2) / 3 = a := by omega
  have hb : (3 * b + 2) / 3 = b := by omega
  calc
    (3 * a + 2).choose (3 * b + 2) ≡
        ((3 * a + 2) % 3).choose ((3 * b + 2) % 3) *
          ((3 * a + 2) / 3).choose ((3 * b + 2) / 3) [MOD 3] :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat
    _ = a.choose b := by norm_num [ha, hb]

private def a220119WeightTerm (n r j : ℕ) : ℕ :=
  n.choose j ^ 2 * (n + j).choose n * j.choose r

/-- The `3J` and `3J+1` weight terms cancel modulo `3`. -/
lemma three_dvd_a220119WeightTerm_pair (N R J : ℕ) :
    3 ∣ a220119WeightTerm (3 * N + 1) (3 * R) (3 * J) +
      a220119WeightTerm (3 * N + 1) (3 * R) (3 * J + 1) := by
  rw [← Nat.modEq_zero_iff_dvd]
  let A := N.choose J ^ 2 * (N + J).choose N * J.choose R
  have hn0 :
      (3 * N + 1).choose (3 * J) ≡ N.choose J [MOD 3] :=
    choose_three_mul_add_one_three_mul_modEq N J
  have hn1 :
      (3 * N + 1).choose (3 * J + 1) ≡ N.choose J [MOD 3] :=
    choose_three_mul_add_one_three_mul_add_one_modEq N J
  have hmid0 :
      (3 * N + 1 + 3 * J).choose (3 * N + 1) ≡
        (N + J).choose N [MOD 3] := by
    simpa only [show 3 * N + 1 + 3 * J = 3 * (N + J) + 1 by omega] using
      choose_three_mul_add_one_three_mul_add_one_modEq (N + J) N
  have hmid1 :
      (3 * N + 1 + (3 * J + 1)).choose (3 * N + 1) ≡
        2 * (N + J).choose N [MOD 3] := by
    simpa only [show 3 * N + 1 + (3 * J + 1) = 3 * (N + J) + 2 by omega] using
      choose_three_mul_add_two_three_mul_add_one_modEq (N + J) N
  have hj0 :
      (3 * J).choose (3 * R) ≡ J.choose R [MOD 3] :=
    choose_three_mul_three_mul_modEq J R
  have hj1 :
      (3 * J + 1).choose (3 * R) ≡ J.choose R [MOD 3] :=
    choose_three_mul_add_one_three_mul_modEq J R
  have hterm0 :
      a220119WeightTerm (3 * N + 1) (3 * R) (3 * J) ≡ A [MOD 3] := by
    exact (hn0.pow 2).mul hmid0 |>.mul hj0
  have hterm1 :
      a220119WeightTerm (3 * N + 1) (3 * R) (3 * J + 1) ≡ 2 * A [MOD 3] := by
    unfold a220119WeightTerm A
    convert (hn1.pow 2).mul hmid1 |>.mul hj1 using 1
    all_goals ring_nf
  calc
    a220119WeightTerm (3 * N + 1) (3 * R) (3 * J) +
          a220119WeightTerm (3 * N + 1) (3 * R) (3 * J + 1)
        ≡ A + 2 * A [MOD 3] := hterm0.add hterm1
    _ = 3 * A := by ring
    _ ≡ 0 [MOD 3] := (dvd_mul_right 3 A).modEq_zero_nat

/-- The residue-`2` weight term vanishes modulo `3`. -/
lemma three_dvd_a220119WeightTerm_two (N R J : ℕ) :
    3 ∣ a220119WeightTerm (3 * N + 1) (3 * R) (3 * J + 2) := by
  have hchoose : 3 ∣ (3 * N + 1).choose (3 * J + 2) :=
    Nat.modEq_zero_iff_dvd.mp
      (choose_three_mul_add_one_three_mul_add_two_modEq N J)
  rcases hchoose with ⟨q, hq⟩
  refine ⟨q * ((3 * N + 1).choose (3 * J + 2) *
    (3 * N + 1 + (3 * J + 2)).choose (3 * N + 1) *
    (3 * J + 2).choose (3 * R)), ?_⟩
  unfold a220119WeightTerm
  rw [hq]
  ring

/-- Lucas modulo `3`: if `n ≡ 1` and `r ≡ 0`, then `U(n,r)` is divisible
by `3`.  The proof pairs the exact finite residue ranges. -/
theorem three_dvd_a220119Weight_of_modEq
    (n r : ℕ) (hn : n % 3 = 1) (hr : r % 3 = 0) :
    3 ∣ a220119Weight n r := by
  have hnrepr : n = 3 * (n / 3) + 1 := by
    have h := Nat.mod_add_div n 3
    omega
  have hrrepr : r = 3 * (r / 3) := by
    have h := Nat.mod_add_div r 3
    omega
  rw [hnrepr, hrrepr]
  unfold a220119Weight
  change 3 ∣ ∑ j ∈ range (3 * (n / 3) + 2),
    a220119WeightTerm (3 * (n / 3) + 1) (3 * (r / 3)) j
  rw [sum_range_three_mul_add_two]
  apply Dvd.dvd.add
  · apply Finset.dvd_sum
    intro J _
    exact (three_dvd_a220119WeightTerm_pair (n / 3) (r / 3) J).add
      (three_dvd_a220119WeightTerm_two (n / 3) (r / 3) J)
  · exact three_dvd_a220119WeightTerm_pair (n / 3) (r / 3) (n / 3)

private def a220119VTerm (n r j : ℕ) : ℕ :=
  n.choose j ^ 2 * (n + j).choose (j - 2) * (j - 2).choose (r - 2)

/-- For `r ≥ 3`, extend `V(n,r)` from `j ∈ [r,n]` to `j ∈ [0,n]`;
every added term is zero, including the truncated-subtraction endpoints. -/
lemma a220119V_eq_sum_range (n r : ℕ) (hr3 : 3 ≤ r) :
    a220119V n r =
      ∑ j ∈ range (n + 1), a220119VTerm n r j := by
  unfold a220119V a220119VTerm
  apply Finset.sum_subset
  · intro j hj
    rw [Finset.mem_Icc] at hj
    rw [Finset.mem_range]
    omega
  · intro j hjrange hjIcc
    rw [Finset.mem_range] at hjrange
    have hjr : j < r := by
      by_contra h
      exact hjIcc (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have hsub : j - 2 < r - 2 := by omega
    rw [Nat.choose_eq_zero_of_lt hsub, mul_zero]

/-- The `3J` and `3J+1` auxiliary terms cancel modulo `3` when the
lower-index quotient `R` is positive. -/
lemma three_dvd_a220119VTerm_pair (N R J : ℕ) (hR : 1 ≤ R) :
    3 ∣ a220119VTerm (3 * N + 1) (3 * R) (3 * J) +
      a220119VTerm (3 * N + 1) (3 * R) (3 * J + 1) := by
  cases J with
  | zero =>
      have hsub : 0 < 3 * R - 2 := by omega
      simp [a220119VTerm, Nat.choose_eq_zero_of_lt hsub]
  | succ J =>
      rw [← Nat.modEq_zero_iff_dvd]
      let A :=
        N.choose (J + 1) ^ 2 * (N + (J + 1)).choose J * J.choose (R - 1)
      have hn0 :
          (3 * N + 1).choose (3 * (J + 1)) ≡
            N.choose (J + 1) [MOD 3] :=
        choose_three_mul_add_one_three_mul_modEq N (J + 1)
      have hn1 :
          (3 * N + 1).choose (3 * (J + 1) + 1) ≡
            N.choose (J + 1) [MOD 3] :=
        choose_three_mul_add_one_three_mul_add_one_modEq N (J + 1)
      have hmid0 :
          (3 * N + 1 + 3 * (J + 1)).choose (3 * (J + 1) - 2) ≡
            (N + (J + 1)).choose J [MOD 3] := by
        simpa only [
          show 3 * N + 1 + 3 * (J + 1) = 3 * (N + (J + 1)) + 1 by omega,
          show 3 * (J + 1) - 2 = 3 * J + 1 by omega] using
          choose_three_mul_add_one_three_mul_add_one_modEq
            (N + (J + 1)) J
      have hmid1 :
          (3 * N + 1 + (3 * (J + 1) + 1)).choose
              (3 * (J + 1) + 1 - 2) ≡
            (N + (J + 1)).choose J [MOD 3] := by
        simpa only [
          show 3 * N + 1 + (3 * (J + 1) + 1) =
              3 * (N + (J + 1)) + 2 by omega,
          show 3 * (J + 1) + 1 - 2 = 3 * J + 2 by omega] using
          choose_three_mul_add_two_three_mul_add_two_modEq
            (N + (J + 1)) J
      have hj0 :
          (3 * (J + 1) - 2).choose (3 * R - 2) ≡
            J.choose (R - 1) [MOD 3] := by
        simpa only [
          show 3 * (J + 1) - 2 = 3 * J + 1 by omega,
          show 3 * R - 2 = 3 * (R - 1) + 1 by omega] using
          choose_three_mul_add_one_three_mul_add_one_modEq J (R - 1)
      have hj1 :
          (3 * (J + 1) + 1 - 2).choose (3 * R - 2) ≡
            2 * J.choose (R - 1) [MOD 3] := by
        simpa only [
          show 3 * (J + 1) + 1 - 2 = 3 * J + 2 by omega,
          show 3 * R - 2 = 3 * (R - 1) + 1 by omega] using
          choose_three_mul_add_two_three_mul_add_one_modEq J (R - 1)
      have hterm0 :
          a220119VTerm (3 * N + 1) (3 * R) (3 * (J + 1)) ≡ A [MOD 3] := by
        exact (hn0.pow 2).mul hmid0 |>.mul hj0
      have hterm1 :
          a220119VTerm (3 * N + 1) (3 * R) (3 * (J + 1) + 1) ≡
            2 * A [MOD 3] := by
        unfold a220119VTerm A
        convert (hn1.pow 2).mul hmid1 |>.mul hj1 using 1
        all_goals ring_nf
      calc
        a220119VTerm (3 * N + 1) (3 * R) (3 * (J + 1)) +
              a220119VTerm (3 * N + 1) (3 * R) (3 * (J + 1) + 1)
            ≡ A + 2 * A [MOD 3] := hterm0.add hterm1
        _ = 3 * A := by ring
        _ ≡ 0 [MOD 3] := (dvd_mul_right 3 A).modEq_zero_nat

/-- The residue-`2` auxiliary term vanishes modulo `3`. -/
lemma three_dvd_a220119VTerm_two (N R J : ℕ) :
    3 ∣ a220119VTerm (3 * N + 1) (3 * R) (3 * J + 2) := by
  have hchoose : 3 ∣ (3 * N + 1).choose (3 * J + 2) :=
    Nat.modEq_zero_iff_dvd.mp
      (choose_three_mul_add_one_three_mul_add_two_modEq N J)
  rcases hchoose with ⟨q, hq⟩
  refine ⟨q * ((3 * N + 1).choose (3 * J + 2) *
    (3 * N + 1 + (3 * J + 2)).choose (3 * J + 2 - 2) *
    (3 * J + 2 - 2).choose (3 * R - 2)), ?_⟩
  unfold a220119VTerm
  rw [hq]
  ring

/-- Lucas modulo `3` for the auxiliary sum: if `n ≡ 1`, `r ≡ 0`, and
`r ≥ 3`, then `V(n,r)` is divisible by `3`. -/
theorem three_dvd_a220119V_of_modEq
    (n r : ℕ) (hn : n % 3 = 1) (hr : r % 3 = 0) (hr3 : 3 ≤ r) :
    3 ∣ a220119V n r := by
  have hnrepr : n = 3 * (n / 3) + 1 := by
    have h := Nat.mod_add_div n 3
    omega
  have hrrepr : r = 3 * (r / 3) := by
    have h := Nat.mod_add_div r 3
    omega
  have hR : 1 ≤ r / 3 := by omega
  rw [a220119V_eq_sum_range n r hr3, hnrepr, hrrepr]
  change 3 ∣ ∑ j ∈ range (3 * (n / 3) + 2),
    a220119VTerm (3 * (n / 3) + 1) (3 * (r / 3)) j
  rw [sum_range_three_mul_add_two]
  apply Dvd.dvd.add
  · apply Finset.dvd_sum
    intro J _
    exact (three_dvd_a220119VTerm_pair (n / 3) (r / 3) J hR).add
      (three_dvd_a220119VTerm_two (n / 3) (r / 3) J)
  · exact three_dvd_a220119VTerm_pair (n / 3) (r / 3) (n / 3) hR

/-- The direct gcd-cancellation consequence of the exact `U`--`V` identity:
`(n+2)/gcd(n+2,r(r-1))` divides `U(n,r)`. -/
theorem div_gcd_dvd_a220119Weight
    (n r : ℕ) (hr : 2 ≤ r) (hrn : r ≤ n) :
    (n + 2) / Nat.gcd (n + 2) (r * (r - 1)) ∣ a220119Weight n r := by
  have hprod : n + 2 ∣ r * (r - 1) * a220119Weight n r := by
    rw [mul_pred_mul_a220119Weight_eq n r hr hrn]
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      dvd_mul_left (n + 2) ((n + 1) * a220119V n r)
  have hmod :
      r * (r - 1) * a220119Weight n r ≡ 0 [MOD n + 2] :=
    Nat.modEq_zero_iff_dvd.mpr hprod
  exact Nat.modEq_zero_iff_dvd.mp
    (hmod.cancel_left_div_gcd (by omega : 0 < n + 2))

/-- The strengthened factor `3(n+2)/gcd(...)` follows immediately in the
coprime quotient case from the mod-3 weight theorem and gcd cancellation. -/
theorem three_mul_div_gcd_dvd_a220119Weight_of_coprime
    (n r : ℕ) (hn : n % 3 = 1) (hrmod : r % 3 = 0)
    (hr : 2 ≤ r) (hrn : r ≤ n)
    (hcop : Nat.Coprime 3 ((n + 2) / Nat.gcd (n + 2) (r * (r - 1)))) :
    3 * ((n + 2) / Nat.gcd (n + 2) (r * (r - 1))) ∣
      a220119Weight n r :=
  hcop.mul_dvd_of_dvd_of_dvd
    (three_dvd_a220119Weight_of_modEq n r hn hrmod)
    (div_gcd_dvd_a220119Weight n r hr hrn)

/-- The strengthened `3`-part used in the reflection argument:
`3(n+2)/gcd(n+2,r(r-1))` divides `U(n,r)` whenever both `n+2` and `r`
are divisible by `3`. -/
theorem three_mul_div_gcd_dvd_a220119Weight
    (n r : ℕ) (hn3 : 3 ∣ n + 2) (hr3 : 3 ∣ r) (hrn : r ≤ n) :
    3 * ((n + 2) / Nat.gcd (n + 2) (r * (r - 1))) ∣
      a220119Weight n r := by
  have hnmod : n % 3 = 1 := by
    have h := Nat.dvd_iff_mod_eq_zero.mp hn3
    omega
  have hrmod : r % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hr3
  by_cases hr0 : r = 0
  · subst r
    simpa using three_dvd_a220119Weight_of_modEq n 0 hnmod (by norm_num)
  have hr : 2 ≤ r := by
    rcases hr3 with ⟨R, hR⟩
    have hRpos : 0 < R := by
      by_contra h
      simp_all
    omega
  let M := n + 2
  let A := r * (r - 1)
  let g := Nat.gcd M A
  let m := M / g
  let U := a220119Weight n r
  let V := a220119V n r
  have hM0 : M ≠ 0 := by simp [M]
  have hA0 : A ≠ 0 := by
    dsimp only [A]
    apply mul_ne_zero <;> omega
  have hgM : g ∣ M := by
    exact Nat.gcd_dvd_left M A
  have hg0 : g ≠ 0 := by
    exact (Nat.gcd_pos_of_pos_left A (by omega : 0 < M)).ne'
  have hm0 : m ≠ 0 := by
    exact (Nat.div_pos (Nat.le_of_dvd (by omega : 0 < M) hgM) (by omega : 0 < g)).ne'
  by_cases hU0 : U = 0
  · simp [U, hU0]
  have hVdvd : 3 ∣ V := by
    exact three_dvd_a220119V_of_modEq n r hnmod hrmod (by omega)
  have hEq : A * U = (n + 1) * M * V := by
    exact mul_pred_mul_a220119Weight_eq n r hr hrn
  have hV0 : V ≠ 0 := by
    intro h
    rw [h, mul_zero] at hEq
    exact (mul_ne_zero hA0 hU0) hEq
  have hD0 : 3 * m ≠ 0 := mul_ne_zero (by norm_num) hm0
  apply (Nat.factorization_prime_le_iff_dvd hD0 hU0).mp
  intro p hp
  by_cases hp3 : p = 3
  · subst p
    have hn10 : n + 1 ≠ 0 := by omega
    have hNM0 : (n + 1) * M ≠ 0 := mul_ne_zero hn10 hM0
    have hf := congrArg Nat.factorization hEq
    rw [Nat.factorization_mul hA0 hU0,
      Nat.factorization_mul hNM0 hV0,
      Nat.factorization_mul hn10 hM0] at hf
    have hf3 := DFunLike.congr_fun hf 3
    simp only [Finsupp.add_apply] at hf3
    have hn1not : ¬3 ∣ n + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    have hn1fac : (n + 1).factorization 3 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hn1not
    rw [hn1fac, zero_add] at hf3
    have hUdvd : 3 ∣ U := by
      exact three_dvd_a220119Weight_of_modEq n r hnmod hrmod
    have hUfac : 1 ≤ U.factorization 3 :=
      (Nat.prime_three.dvd_iff_one_le_factorization hU0).mp hUdvd
    have hVfac : 1 ≤ V.factorization 3 :=
      (Nat.prime_three.dvd_iff_one_le_factorization hV0).mp hVdvd
    have hgf : g.factorization 3 =
        min (M.factorization 3) (A.factorization 3) := by
      have h := congrArg (fun f => f 3)
        (Nat.factorization_gcd hM0 hA0)
      simpa using h
    have hmf := congrArg (fun f => f 3) (Nat.factorization_div hgM)
    change m.factorization 3 =
      M.factorization 3 - g.factorization 3 at hmf
    rw [Nat.factorization_mul (by norm_num) hm0]
    simp only [Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_three]
    rw [hmf, hgf]
    by_cases hle : M.factorization 3 ≤ A.factorization 3
    · rw [min_eq_left hle, Nat.sub_self]
      simpa using hUfac
    · rw [min_eq_right (by omega)]
      omega
  · have hmU : m ∣ U := by
      exact div_gcd_dvd_a220119Weight n r hr hrn
    have hmle :=
      (Nat.factorization_prime_le_iff_dvd hm0 hU0).mpr hmU p hp
    calc
      (3 * m).factorization p
          = (3 : ℕ).factorization p + m.factorization p := by
              rw [Nat.factorization_mul (by norm_num) hm0]
              rfl
      _ = m.factorization p := by
        rw [Nat.Prime.factorization Nat.prime_three]
        simp [hp3]
      _ ≤ U.factorization p := hmle

/-- A prime power in `n+2` transfers completely to a weight whenever the
prime does not divide `t(t-1)`. -/
lemma prime_pow_dvd_a220119Weight_of_not_dvd_mul_pred
    (n t p e : ℕ) (ht : 2 ≤ t) (htn : t ≤ n) (hp : p.Prime)
    (hpow : p ^ e ∣ n + 2) (hnot : ¬p ∣ t * (t - 1)) :
    p ^ e ∣ a220119Weight n t := by
  let M := n + 2
  let A := t * (t - 1)
  let g := Nat.gcd M A
  let q := M / g
  let U := a220119Weight n t
  have hM0 : M ≠ 0 := by simp [M]
  have hA0 : A ≠ 0 := by
    dsimp only [A]
    apply mul_ne_zero <;> omega
  have hgM : g ∣ M := Nat.gcd_dvd_left M A
  have hgA : g ∣ A := Nat.gcd_dvd_right M A
  have hg0 : g ≠ 0 :=
    (Nat.gcd_pos_of_pos_left A (by omega : 0 < M)).ne'
  have hq0 : q ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (by omega : 0 < M) hgM) (by omega : 0 < g)).ne'
  have hqU : q ∣ U :=
    div_gcd_dvd_a220119Weight n t ht htn
  change p ^ e ∣ U
  by_cases hU0 : U = 0
  · rw [hU0]
    exact dvd_zero _
  have hqle :=
    (Nat.factorization_prime_le_iff_dvd hq0 hU0).mpr hqU p hp
  have hpe : e ≤ M.factorization p := by
    exact (hp.pow_dvd_iff_le_factorization hM0).mp hpow
  have hpg : ¬p ∣ g := fun h => hnot (h.trans hgA)
  have hgf : g.factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hpg
  have hqf := congrArg (fun f => f p) (Nat.factorization_div hgM)
  change q.factorization p = M.factorization p - g.factorization p at hqf
  rw [hgf, Nat.sub_zero] at hqf
  exact (hp.pow_dvd_iff_le_factorization hU0).mpr (by omega)

/-- The `p ≥ 5` part of every off-middle reflection pair. -/
lemma prime_pow_dvd_a220119Weight_reflection_of_five_le
    (n r p e : ℕ) (hrn : r ≤ n) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpow : p ^ e ∣ n + 2) :
    p ^ e ∣
      2 * a220119Weight n r * a220119Weight n (n - r) := by
  by_cases he0 : e = 0
  · simp [he0]
  have hpM : p ∣ n + 2 := by
    exact (dvd_pow_self p (by omega : e ≠ 0)).trans hpow
  let s := n - r
  have hrs : r + s = n := by
    dsimp only [s]
    omega
  have hsle : s ≤ n := by
    dsimp only [s]
    omega
  have hMmod : n + 2 ≡ 0 [MOD p] :=
    Nat.modEq_zero_iff_dvd.mpr hpM
  have residue_zero_or_one (x : ℕ) (hx : p ∣ x * (x - 1)) :
      x ≡ 0 [MOD p] ∨ x ≡ 1 [MOD p] := by
    rcases hp.dvd_mul.mp hx with hx0 | hx1
    · exact Or.inl (Nat.modEq_zero_iff_dvd.mpr hx0)
    · by_cases hxzero : x = 0
      · subst x
        exact Or.inl Nat.ModEq.rfl
      · right
        have hpred : x - 1 ≡ 0 [MOD p] :=
          Nat.modEq_zero_iff_dvd.mpr hx1
        simpa [Nat.sub_add_cancel (by omega : 1 ≤ x)] using hpred.add_right 1
  have hnot :
      ¬(p ∣ r * (r - 1) ∧ p ∣ s * (s - 1)) := by
    rintro ⟨hrp, hsp⟩
    rcases residue_zero_or_one r hrp with hr0 | hr1
    · rcases residue_zero_or_one s hsp with hs0 | hs1
      · have hsmall : 2 ≡ 0 [MOD p] := by
          calc
            2 ≡ r + s + 2 [MOD p] := (hr0.add hs0 |>.add_right 2).symm
            _ = n + 2 := by omega
            _ ≡ 0 [MOD p] := hMmod
        have hle := Nat.le_of_dvd (by norm_num : 0 < 2)
          (Nat.modEq_zero_iff_dvd.mp hsmall)
        omega
      · have hsmall : 3 ≡ 0 [MOD p] := by
          calc
            3 ≡ r + s + 2 [MOD p] := (hr0.add hs1 |>.add_right 2).symm
            _ = n + 2 := by omega
            _ ≡ 0 [MOD p] := hMmod
        have hle := Nat.le_of_dvd (by norm_num : 0 < 3)
          (Nat.modEq_zero_iff_dvd.mp hsmall)
        omega
    · rcases residue_zero_or_one s hsp with hs0 | hs1
      · have hsmall : 3 ≡ 0 [MOD p] := by
          calc
            3 ≡ r + s + 2 [MOD p] := (hr1.add hs0 |>.add_right 2).symm
            _ = n + 2 := by omega
            _ ≡ 0 [MOD p] := hMmod
        have hle := Nat.le_of_dvd (by norm_num : 0 < 3)
          (Nat.modEq_zero_iff_dvd.mp hsmall)
        omega
      · have hsmall : 4 ≡ 0 [MOD p] := by
          calc
            4 ≡ r + s + 2 [MOD p] := (hr1.add hs1 |>.add_right 2).symm
            _ = n + 2 := by omega
            _ ≡ 0 [MOD p] := hMmod
        have hle := Nat.le_of_dvd (by norm_num : 0 < 4)
          (Nat.modEq_zero_iff_dvd.mp hsmall)
        omega
  rcases not_and_or.mp hnot with hrnot | hsnot
  · have hr2 : 2 ≤ r := by
      by_contra h
      interval_cases r <;> simp_all
    have hd := prime_pow_dvd_a220119Weight_of_not_dvd_mul_pred
      n r p e hr2 hrn hp hpow hrnot
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (hd.mul_right 2).mul_right (a220119Weight n (n - r))
  · have hs2 : 2 ≤ s := by
      by_contra h
      interval_cases s <;> simp_all
    have hd := prime_pow_dvd_a220119Weight_of_not_dvd_mul_pred
      n s p e hs2 hsle hp hpow hsnot
    simpa [s, mul_assoc, mul_comm, mul_left_comm] using
      (hd.mul_left (2 * a220119Weight n r))

private lemma factorization_div_gcd_eq_sub
    (M A p : ℕ) (hM : M ≠ 0) (hA : A ≠ 0) :
    (M / Nat.gcd M A).factorization p =
      M.factorization p - A.factorization p := by
  have hgM : Nat.gcd M A ∣ M := Nat.gcd_dvd_left M A
  have hgf := congrArg (fun f => f p) (Nat.factorization_gcd hM hA)
  have hqf := congrArg (fun f => f p) (Nat.factorization_div hgM)
  change (M / Nat.gcd M A).factorization p =
    M.factorization p - (Nat.gcd M A).factorization p at hqf
  have hgfp :
      (Nat.gcd M A).factorization p =
        min (M.factorization p) (A.factorization p) := by
    simpa using hgf
  rw [hgfp] at hqf
  omega

private lemma factorization_sub_le_a220119Weight
    (n t p : ℕ) (ht : 2 ≤ t) (htn : t ≤ n) (hp : p.Prime)
    (hU : a220119Weight n t ≠ 0) :
    (n + 2).factorization p - (t * (t - 1)).factorization p ≤
      (a220119Weight n t).factorization p := by
  let M := n + 2
  let A := t * (t - 1)
  let q := M / Nat.gcd M A
  let U := a220119Weight n t
  have hM : M ≠ 0 := by simp [M]
  have hA : A ≠ 0 := by
    dsimp only [A]
    apply mul_ne_zero <;> omega
  have hgM : Nat.gcd M A ∣ M := Nat.gcd_dvd_left M A
  have hgpos : 0 < Nat.gcd M A :=
    Nat.gcd_pos_of_pos_left A (by omega : 0 < M)
  have hq : q ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (by omega : 0 < M) hgM) hgpos).ne'
  have hqU : q ∣ U :=
    div_gcd_dvd_a220119Weight n t ht htn
  have hle :=
    (Nat.factorization_prime_le_iff_dvd hq hU).mpr hqU p hp
  rw [factorization_div_gcd_eq_sub M A p hM hA] at hle
  exact hle

private lemma one_add_factorization_sub_le_a220119Weight
    (n t : ℕ) (hn3 : 3 ∣ n + 2) (ht3 : 3 ∣ t)
    (ht : 2 ≤ t) (htn : t ≤ n)
    (hU : a220119Weight n t ≠ 0) :
    1 + ((n + 2).factorization 3 -
      (t * (t - 1)).factorization 3) ≤
      (a220119Weight n t).factorization 3 := by
  let M := n + 2
  let A := t * (t - 1)
  let q := M / Nat.gcd M A
  let U := a220119Weight n t
  have hM : M ≠ 0 := by simp [M]
  have hA : A ≠ 0 := by
    dsimp only [A]
    apply mul_ne_zero <;> omega
  have hgM : Nat.gcd M A ∣ M := Nat.gcd_dvd_left M A
  have hgpos : 0 < Nat.gcd M A :=
    Nat.gcd_pos_of_pos_left A (by omega : 0 < M)
  have hq : q ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (by omega : 0 < M) hgM) hgpos).ne'
  have hdvd : 3 * q ∣ U :=
    three_mul_div_gcd_dvd_a220119Weight n t hn3 ht3 htn
  have hle :=
    (Nat.factorization_prime_le_iff_dvd
      (mul_ne_zero (by norm_num) hq) hU).mpr hdvd 3 Nat.prime_three
  rw [Nat.factorization_mul (by norm_num) hq] at hle
  simp only [Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_three] at hle
  rw [factorization_div_gcd_eq_sub M A 3 hM hA] at hle
  exact hle

private lemma factorization_mul_pred_eq_left
    (t p : ℕ) (ht : 2 ≤ t) (hnot : ¬p ∣ t - 1) :
    (t * (t - 1)).factorization p = t.factorization p := by
  rw [Nat.factorization_mul (by omega) (by omega)]
  simp only [Finsupp.add_apply]
  rw [
    Nat.factorization_eq_zero_of_not_dvd hnot]
  simp

private lemma factorization_mul_pred_eq_right
    (t p : ℕ) (ht : 2 ≤ t) (hnot : ¬p ∣ t) :
    (t * (t - 1)).factorization p = (t - 1).factorization p := by
  rw [Nat.factorization_mul (by omega) (by omega)]
  simp only [Finsupp.add_apply]
  rw [
    Nat.factorization_eq_zero_of_not_dvd hnot]
  simp

/-- The complete `2`-primary part of an off-middle reflection pair. -/
lemma two_pow_dvd_a220119Weight_reflection
    (n r e : ℕ) (hrn : r ≤ n) (hne : r ≠ n - r)
    (hpow : 2 ^ e ∣ n + 2) :
    2 ^ e ∣
      2 * a220119Weight n r * a220119Weight n (n - r) := by
  by_cases he0 : e = 0
  · simp [he0]
  let M := n + 2
  let s := n - r
  let U := a220119Weight n r
  let W := a220119Weight n s
  change 2 ^ e ∣ 2 * U * W
  have hrs : r + s = n := by
    dsimp only [s]
    omega
  have hsle : s ≤ n := by
    dsimp only [s]
    omega
  have hM : M ≠ 0 := by simp [M]
  have hpM : 2 ∣ M := by
    exact (dvd_pow_self 2 he0).trans hpow
  have hnEven : Even n := by
    rw [even_iff_two_dvd]
    rcases hpM with ⟨k, hk⟩
    refine ⟨k - 1, ?_⟩
    dsimp only [M] at hk
    omega
  by_cases hU : U = 0
  · simp [U, hU]
  by_cases hW : W = 0
  · simp [W, hW]
  have hD :
      2 * U * W ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hU) hW
  have hMfac : e ≤ M.factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hM).mp hpow
  apply (Nat.prime_two.pow_dvd_iff_le_factorization hD).mpr
  rw [Nat.factorization_mul (mul_ne_zero (by norm_num) hU) hW,
    Nat.factorization_mul (by norm_num) hU]
  simp only [Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two]
  rcases Nat.even_or_odd r with hrEven | hrOdd
  · have hsEven : Even s := by
      dsimp only [s]
      rw [Nat.even_sub hrn]
      exact iff_of_true hnEven hrEven
    by_cases hr0 : r = 0
    · subst r
      have hsM : s + 2 = M := by omega
      by_cases he1 : e ≤ 1
      · omega
      have h4M : 2 ^ 2 ∣ M :=
        (Nat.prime_two.pow_dvd_iff_le_factorization hM).mpr (by omega)
      have hs2 : 2 ≤ s := by
        have hMge : 2 ^ 2 ≤ M :=
          Nat.le_of_dvd (by omega : 0 < M) h4M
        omega
      have hsnot : ¬2 ∣ s - 1 := by
        rw [← even_iff_two_dvd, not_even_iff_odd]
        exact Nat.Even.sub_odd (by omega) hsEven odd_one
      have hAs :
          (s * (s - 1)).factorization 2 = s.factorization 2 :=
        factorization_mul_pred_eq_left s 2 hs2 hsnot
      have hsfac : s.factorization 2 ≤ 1 := by
        by_contra h
        have h4s : 2 ^ 2 ∣ s :=
          (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mpr (by omega)
        have hsmall : 2 ≡ 0 [MOD 4] := by
          calc
            2 ≡ s + 2 [MOD 4] :=
              (Nat.modEq_zero_iff_dvd.mpr h4s |>.add_right 2).symm
            _ = M := hsM
            _ ≡ 0 [MOD 4] := Nat.modEq_zero_iff_dvd.mpr h4M
        norm_num at hsmall
      have hWs := factorization_sub_le_a220119Weight
        n s 2 hs2 hsle Nat.prime_two hW
      change M.factorization 2 - (s * (s - 1)).factorization 2 ≤
        W.factorization 2 at hWs
      rw [hAs] at hWs
      omega
    · by_cases hs0 : s = 0
      · subst s
        have hrM : r + 2 = M := by omega
        by_cases he1 : e ≤ 1
        · omega
        have h4M : 2 ^ 2 ∣ M :=
          (Nat.prime_two.pow_dvd_iff_le_factorization hM).mpr (by omega)
        have hr2 : 2 ≤ r := by
          have hMge : 2 ^ 2 ≤ M :=
            Nat.le_of_dvd (by omega : 0 < M) h4M
          omega
        have hrnot : ¬2 ∣ r - 1 := by
          rw [← even_iff_two_dvd, not_even_iff_odd]
          exact Nat.Even.sub_odd (by omega) hrEven odd_one
        have hAr :
            (r * (r - 1)).factorization 2 = r.factorization 2 :=
          factorization_mul_pred_eq_left r 2 hr2 hrnot
        have hrfac : r.factorization 2 ≤ 1 := by
          by_contra h
          have h4r : 2 ^ 2 ∣ r :=
            (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mpr (by omega)
          have hsmall : 2 ≡ 0 [MOD 4] := by
            calc
              2 ≡ r + 2 [MOD 4] :=
                (Nat.modEq_zero_iff_dvd.mpr h4r |>.add_right 2).symm
              _ = M := hrM
              _ ≡ 0 [MOD 4] := Nat.modEq_zero_iff_dvd.mpr h4M
          norm_num at hsmall
        have hUr := factorization_sub_le_a220119Weight
          n r 2 hr2 hrn Nat.prime_two hU
        change M.factorization 2 - (r * (r - 1)).factorization 2 ≤
          U.factorization 2 at hUr
        rw [hAr] at hUr
        omega
      · have hr2 : 2 ≤ r := by
          rcases hrEven with ⟨R, hR⟩
          have hRpos : 0 < R := by
            by_contra h
            simp_all
          omega
        have hs2 : 2 ≤ s := by
          rcases hsEven with ⟨S, hS⟩
          have hSpos : 0 < S := by
            by_contra h
            simp_all
          omega
        have hrnot : ¬2 ∣ r - 1 := by
          rw [← even_iff_two_dvd, not_even_iff_odd]
          exact Nat.Even.sub_odd (by omega) hrEven odd_one
        have hsnot : ¬2 ∣ s - 1 := by
          rw [← even_iff_two_dvd, not_even_iff_odd]
          exact Nat.Even.sub_odd (by omega) hsEven odd_one
        have hAr :
            (r * (r - 1)).factorization 2 = r.factorization 2 :=
          factorization_mul_pred_eq_left r 2 hr2 hrnot
        have hAs :
            (s * (s - 1)).factorization 2 = s.factorization 2 :=
          factorization_mul_pred_eq_left s 2 hs2 hsnot
        have hUr := factorization_sub_le_a220119Weight
          n r 2 hr2 hrn Nat.prime_two hU
        have hWs := factorization_sub_le_a220119Weight
          n s 2 hs2 hsle Nat.prime_two hW
        change M.factorization 2 - (r * (r - 1)).factorization 2 ≤
          U.factorization 2 at hUr
        change M.factorization 2 - (s * (s - 1)).factorization 2 ≤
          W.factorization 2 at hWs
        rw [hAr] at hUr
        rw [hAs] at hWs
        by_cases he1 : e ≤ 1
        · omega
        have h4M : 2 ^ 2 ∣ M :=
          (Nat.prime_two.pow_dvd_iff_le_factorization hM).mpr (by omega)
        have hmin :
            min (r.factorization 2) (s.factorization 2) ≤ 1 := by
          by_contra h
          have h4r : 2 ^ 2 ∣ r :=
            (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mpr
              (by omega)
          have h4s : 2 ^ 2 ∣ s :=
            (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mpr
              (by omega)
          have hsmall : 2 ≡ 0 [MOD 4] := by
            calc
              2 ≡ r + s + 2 [MOD 4] :=
                ((Nat.modEq_zero_iff_dvd.mpr h4r).add
                  (Nat.modEq_zero_iff_dvd.mpr h4s) |>.add_right 2).symm
              _ = M := by omega
              _ ≡ 0 [MOD 4] := Nat.modEq_zero_iff_dvd.mpr h4M
          norm_num at hsmall
        omega
  · have hsOdd : Odd s := by
      dsimp only [s]
      exact Nat.Even.sub_odd hrn hnEven hrOdd
    have hUtwo : 2 ∣ U :=
      two_dvd_a220119Weight_of_even_of_odd n r hnEven hrOdd
    have hWtwo : 2 ∣ W :=
      two_dvd_a220119Weight_of_even_of_odd n s hnEven hsOdd
    have hUfac : 1 ≤ U.factorization 2 :=
      (Nat.prime_two.dvd_iff_one_le_factorization hU).mp hUtwo
    have hWfac : 1 ≤ W.factorization 2 :=
      (Nat.prime_two.dvd_iff_one_le_factorization hW).mp hWtwo
    by_cases he3 : e ≤ 3
    · omega
    have h8M : 2 ^ 3 ∣ M :=
      (Nat.prime_two.pow_dvd_iff_le_factorization hM).mpr (by omega)
    by_cases hr1 : r = 1
    · subst r
      have hs1 : s ≠ 1 := by
        intro hs
        apply hne
        dsimp only [s] at hs ⊢
        omega
      have hs2 : 2 ≤ s := by omega
      have hsnot : ¬2 ∣ s := by
        rw [← even_iff_two_dvd, not_even_iff_odd]
        exact hsOdd
      have hAs :
          (s * (s - 1)).factorization 2 = (s - 1).factorization 2 :=
        factorization_mul_pred_eq_right s 2 hs2 hsnot
      have hsfac : (s - 1).factorization 2 ≤ 2 := by
        by_contra h
        have h8s : 2 ^ 3 ∣ s - 1 :=
          (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mpr
            (by omega)
        have hsmall : 4 ≡ 0 [MOD 8] := by
          calc
            4 ≡ (s - 1) + 4 [MOD 8] :=
              (Nat.modEq_zero_iff_dvd.mpr h8s |>.add_right 4).symm
            _ = M := by omega
            _ ≡ 0 [MOD 8] := Nat.modEq_zero_iff_dvd.mpr h8M
        norm_num at hsmall
      have hWs := factorization_sub_le_a220119Weight
        n s 2 hs2 hsle Nat.prime_two hW
      change M.factorization 2 - (s * (s - 1)).factorization 2 ≤
        W.factorization 2 at hWs
      rw [hAs] at hWs
      omega
    · by_cases hs1 : s = 1
      · subst s
        have hr2 : 2 ≤ r := by omega
        have hrnot : ¬2 ∣ r := by
          rw [← even_iff_two_dvd, not_even_iff_odd]
          exact hrOdd
        have hAr :
            (r * (r - 1)).factorization 2 = (r - 1).factorization 2 :=
          factorization_mul_pred_eq_right r 2 hr2 hrnot
        have hrfac : (r - 1).factorization 2 ≤ 2 := by
          by_contra h
          have h8r : 2 ^ 3 ∣ r - 1 :=
            (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mpr
              (by omega)
          have hsmall : 4 ≡ 0 [MOD 8] := by
            calc
              4 ≡ (r - 1) + 4 [MOD 8] :=
                (Nat.modEq_zero_iff_dvd.mpr h8r |>.add_right 4).symm
              _ = M := by omega
              _ ≡ 0 [MOD 8] := Nat.modEq_zero_iff_dvd.mpr h8M
          norm_num at hsmall
        have hUr := factorization_sub_le_a220119Weight
          n r 2 hr2 hrn Nat.prime_two hU
        change M.factorization 2 - (r * (r - 1)).factorization 2 ≤
          U.factorization 2 at hUr
        rw [hAr] at hUr
        omega
      · have hr2 : 2 ≤ r := by
          rcases hrOdd with ⟨R, hR⟩
          omega
        have hs2 : 2 ≤ s := by
          rcases hsOdd with ⟨S, hS⟩
          omega
        have hrnot : ¬2 ∣ r := by
          rw [← even_iff_two_dvd, not_even_iff_odd]
          exact hrOdd
        have hsnot : ¬2 ∣ s := by
          rw [← even_iff_two_dvd, not_even_iff_odd]
          exact hsOdd
        have hAr :
            (r * (r - 1)).factorization 2 = (r - 1).factorization 2 :=
          factorization_mul_pred_eq_right r 2 hr2 hrnot
        have hAs :
            (s * (s - 1)).factorization 2 = (s - 1).factorization 2 :=
          factorization_mul_pred_eq_right s 2 hs2 hsnot
        have hUr := factorization_sub_le_a220119Weight
          n r 2 hr2 hrn Nat.prime_two hU
        have hWs := factorization_sub_le_a220119Weight
          n s 2 hs2 hsle Nat.prime_two hW
        change M.factorization 2 - (r * (r - 1)).factorization 2 ≤
          U.factorization 2 at hUr
        change M.factorization 2 - (s * (s - 1)).factorization 2 ≤
          W.factorization 2 at hWs
        rw [hAr] at hUr
        rw [hAs] at hWs
        have hmin :
            min ((r - 1).factorization 2)
              ((s - 1).factorization 2) ≤ 2 := by
          by_contra h
          have h8r : 2 ^ 3 ∣ r - 1 :=
            (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mpr
              (by omega)
          have h8s : 2 ^ 3 ∣ s - 1 :=
            (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mpr
              (by omega)
          have hsmall : 4 ≡ 0 [MOD 8] := by
            calc
              4 ≡ (r - 1) + (s - 1) + 4 [MOD 8] :=
                ((Nat.modEq_zero_iff_dvd.mpr h8r).add
                  (Nat.modEq_zero_iff_dvd.mpr h8s) |>.add_right 4).symm
              _ = M := by omega
              _ ≡ 0 [MOD 8] := Nat.modEq_zero_iff_dvd.mpr h8M
          norm_num at hsmall
        omega

private lemma three_pow_dvd_a220119Weight_mul_of_mod_zero_one
    (n t u e : ℕ) (htn : t ≤ n) (hun : u ≤ n) (hsum : t + u = n)
    (htmod : t % 3 = 0) (humod : u % 3 = 1)
    (hpow : 3 ^ e ∣ n + 2) :
    3 ^ e ∣ a220119Weight n t * a220119Weight n u := by
  by_cases he0 : e = 0
  · simp [he0]
  let M := n + 2
  let U := a220119Weight n t
  let W := a220119Weight n u
  change 3 ^ e ∣ U * W
  have hM : M ≠ 0 := by simp [M]
  have hM3 : 3 ∣ M := (dvd_pow_self 3 he0).trans hpow
  have ht3 : 3 ∣ t := Nat.dvd_iff_mod_eq_zero.mpr htmod
  have hnmod : n % 3 = 1 := by
    have h := Nat.dvd_iff_mod_eq_zero.mp hM3
    dsimp only [M] at h
    omega
  by_cases hU : U = 0
  · simp [hU]
  by_cases hW : W = 0
  · simp [hW]
  have hMfac : e ≤ M.factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization hM).mp hpow
  have hU3 : 3 ∣ U :=
    three_dvd_a220119Weight_of_modEq n t hnmod htmod
  have hUfac : 1 ≤ U.factorization 3 :=
    (Nat.prime_three.dvd_iff_one_le_factorization hU).mp hU3
  apply (Nat.prime_three.pow_dvd_iff_le_factorization
    (mul_ne_zero hU hW)).mpr
  rw [Nat.factorization_mul hU hW]
  simp only [Finsupp.add_apply]
  by_cases he1 : e ≤ 1
  · omega
  have h9M : 3 ^ 2 ∣ M :=
    (Nat.prime_three.pow_dvd_iff_le_factorization hM).mpr (by omega)
  by_cases ht0 : t = 0
  · subst t
    have hu2 : 2 ≤ u := by
      have hMge : 3 ^ 2 ≤ M :=
        Nat.le_of_dvd (by omega : 0 < M) h9M
      omega
    have hunot : ¬3 ∣ u := by
      intro h
      have hz := Nat.dvd_iff_mod_eq_zero.mp h
      omega
    have hAu :
        (u * (u - 1)).factorization 3 = (u - 1).factorization 3 :=
      factorization_mul_pred_eq_right u 3 hu2 hunot
    have hufac : (u - 1).factorization 3 ≤ 1 := by
      by_contra h
      have h9u : 3 ^ 2 ∣ u - 1 :=
        (Nat.prime_three.pow_dvd_iff_le_factorization (by omega)).mpr
          (by omega)
      have hsmall : 3 ≡ 0 [MOD 9] := by
        calc
          3 ≡ (u - 1) + 3 [MOD 9] :=
            (Nat.modEq_zero_iff_dvd.mpr h9u |>.add_right 3).symm
          _ = M := by omega
          _ ≡ 0 [MOD 9] := Nat.modEq_zero_iff_dvd.mpr h9M
      norm_num at hsmall
    have hWu := factorization_sub_le_a220119Weight
      n u 3 hu2 hun Nat.prime_three hW
    change M.factorization 3 - (u * (u - 1)).factorization 3 ≤
      W.factorization 3 at hWu
    rw [hAu] at hWu
    omega
  · by_cases hu1 : u = 1
    · subst u
      have ht2 : 2 ≤ t := by
        have htpos : 0 < t := by omega
        have hrepr := Nat.mod_add_div t 3
        omega
      have htnot : ¬3 ∣ t - 1 := by
        intro h
        rcases ht3 with ⟨a, ha⟩
        rcases h with ⟨b, hb⟩
        omega
      have hAt :
          (t * (t - 1)).factorization 3 = t.factorization 3 :=
        factorization_mul_pred_eq_left t 3 ht2 htnot
      have htfac : t.factorization 3 ≤ 1 := by
        by_contra h
        have h9t : 3 ^ 2 ∣ t :=
          (Nat.prime_three.pow_dvd_iff_le_factorization (by omega)).mpr
            (by omega)
        have hsmall : 3 ≡ 0 [MOD 9] := by
          calc
            3 ≡ t + 3 [MOD 9] :=
              (Nat.modEq_zero_iff_dvd.mpr h9t |>.add_right 3).symm
            _ = M := by omega
            _ ≡ 0 [MOD 9] := Nat.modEq_zero_iff_dvd.mpr h9M
        norm_num at hsmall
      have hUt := one_add_factorization_sub_le_a220119Weight
        n t hM3 ht3 ht2 htn hU
      change 1 + (M.factorization 3 -
        (t * (t - 1)).factorization 3) ≤ U.factorization 3 at hUt
      rw [hAt] at hUt
      omega
    · have ht2 : 2 ≤ t := by
        have htpos : 0 < t := by omega
        have hrepr := Nat.mod_add_div t 3
        omega
      have hu2 : 2 ≤ u := by
        have hrepr := Nat.mod_add_div u 3
        omega
      have htnot : ¬3 ∣ t - 1 := by
        intro h
        rcases ht3 with ⟨a, ha⟩
        rcases h with ⟨b, hb⟩
        omega
      have hunot : ¬3 ∣ u := by
        intro h
        have hz := Nat.dvd_iff_mod_eq_zero.mp h
        omega
      have hAt :
          (t * (t - 1)).factorization 3 = t.factorization 3 :=
        factorization_mul_pred_eq_left t 3 ht2 htnot
      have hAu :
          (u * (u - 1)).factorization 3 = (u - 1).factorization 3 :=
        factorization_mul_pred_eq_right u 3 hu2 hunot
      have hUt := one_add_factorization_sub_le_a220119Weight
        n t hM3 ht3 ht2 htn hU
      have hWu := factorization_sub_le_a220119Weight
        n u 3 hu2 hun Nat.prime_three hW
      change 1 + (M.factorization 3 -
        (t * (t - 1)).factorization 3) ≤ U.factorization 3 at hUt
      change M.factorization 3 - (u * (u - 1)).factorization 3 ≤
        W.factorization 3 at hWu
      rw [hAt] at hUt
      rw [hAu] at hWu
      have hmin :
          min (t.factorization 3) ((u - 1).factorization 3) ≤ 1 := by
        by_contra h
        have h9t : 3 ^ 2 ∣ t :=
          (Nat.prime_three.pow_dvd_iff_le_factorization (by omega)).mpr
            (by omega)
        have h9u : 3 ^ 2 ∣ u - 1 :=
          (Nat.prime_three.pow_dvd_iff_le_factorization (by omega)).mpr
            (by omega)
        have hsmall : 3 ≡ 0 [MOD 9] := by
          calc
            3 ≡ t + (u - 1) + 3 [MOD 9] :=
              ((Nat.modEq_zero_iff_dvd.mpr h9t).add
                (Nat.modEq_zero_iff_dvd.mpr h9u) |>.add_right 3).symm
            _ = M := by omega
            _ ≡ 0 [MOD 9] := Nat.modEq_zero_iff_dvd.mpr h9M
        norm_num at hsmall
      omega

/-- The complete `3`-primary part of every reflection pair. -/
lemma three_pow_dvd_a220119Weight_reflection
    (n r e : ℕ) (hrn : r ≤ n) (hpow : 3 ^ e ∣ n + 2) :
    3 ^ e ∣
      2 * a220119Weight n r * a220119Weight n (n - r) := by
  by_cases he0 : e = 0
  · simp [he0]
  let s := n - r
  have hrs : r + s = n := by
    dsimp only [s]
    omega
  have hsle : s ≤ n := by
    dsimp only [s]
    omega
  have hM3 : 3 ∣ n + 2 := (dvd_pow_self 3 he0).trans hpow
  have hnmod : n % 3 = 1 := by
    have h := Nat.dvd_iff_mod_eq_zero.mp hM3
    omega
  have hrange : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by
    omega
  rcases hrange with hr0 | hr1 | hr2
  · have hs1 : s % 3 = 1 := by
      have hnrepr := Nat.mod_add_div n 3
      have hrrepr := Nat.mod_add_div r 3
      have hsrepr := Nat.mod_add_div s 3
      omega
    have hd := three_pow_dvd_a220119Weight_mul_of_mod_zero_one
      n r s e hrn hsle hrs hr0 hs1 hpow
    simpa [s, mul_assoc] using hd.mul_left 2
  · have hs0 : s % 3 = 0 := by
      have hnrepr := Nat.mod_add_div n 3
      have hrrepr := Nat.mod_add_div r 3
      have hsrepr := Nat.mod_add_div s 3
      omega
    have hd := three_pow_dvd_a220119Weight_mul_of_mod_zero_one
      n s r e hsle hrn (by omega) hs0 hr1 hpow
    change 3 ^ e ∣ 2 * a220119Weight n r * a220119Weight n s
    rw [show
      2 * a220119Weight n r * a220119Weight n s =
        2 * (a220119Weight n s * a220119Weight n r) by ring]
    exact hd.mul_left 2
  · have hr2le : 2 ≤ r := by
      have hrepr := Nat.mod_add_div r 3
      omega
    have hrnot0 : ¬3 ∣ r := by
      intro h
      have hz := Nat.dvd_iff_mod_eq_zero.mp h
      omega
    have hrnot1 : ¬3 ∣ r - 1 := by
      intro h
      rcases h with ⟨q, hq⟩
      have hrepr := Nat.mod_add_div r 3
      omega
    have hrnot : ¬3 ∣ r * (r - 1) := by
      intro h
      rcases Nat.prime_three.dvd_mul.mp h with h | h
      · exact hrnot0 h
      · exact hrnot1 h
    have hd := prime_pow_dvd_a220119Weight_of_not_dvd_mul_pred
      n r 3 e hr2le hrn Nat.prime_three hpow hrnot
    simpa [mul_assoc] using
      (hd.mul_left 2).mul_right (a220119Weight n (n - r))

/-- Every prime-power part of `n+2` divides an off-middle reflection
pair.  The cases `p=2`, `p=3`, and `p≥5` are supplied by the preceding
three reflection lemmas. -/
theorem n_add_two_dvd_a220119Weight_reflection
    (n r : ℕ) (hrn : r ≤ n) (hne : r ≠ n - r) :
    n + 2 ∣
      2 * a220119Weight n r * a220119Weight n (n - r) := by
  let M := n + 2
  let D := 2 * a220119Weight n r * a220119Weight n (n - r)
  change M ∣ D
  have hM : M ≠ 0 := by simp [M]
  by_cases hD : D = 0
  · simp [hD]
  apply (Nat.factorization_prime_le_iff_dvd hM hD).mp
  intro p hp
  have hpow : p ^ M.factorization p ∣ M :=
    (hp.pow_dvd_iff_le_factorization hM).mpr le_rfl
  by_cases hp2 : p = 2
  · subst p
    have hd := two_pow_dvd_a220119Weight_reflection
      n r (M.factorization 2) hrn hne hpow
    change 2 ^ M.factorization 2 ∣ D at hd
    exact (Nat.prime_two.pow_dvd_iff_le_factorization hD).mp hd
  by_cases hp3 : p = 3
  · subst p
    have hd := three_pow_dvd_a220119Weight_reflection
      n r (M.factorization 3) hrn hpow
    change 3 ^ M.factorization 3 ∣ D at hd
    exact (Nat.prime_three.pow_dvd_iff_le_factorization hD).mp hd
  · have hp5 : 5 ≤ p := by
      rcases hp.odd_of_ne_two hp2 with ⟨k, hk⟩
      have hk0 : k ≠ 0 := by
        intro h
        apply hp.ne_one
        omega
      have hk1 : k ≠ 1 := by
        intro h
        apply hp3
        omega
      omega
    have hd := prime_pow_dvd_a220119Weight_reflection_of_five_le
      n r p (M.factorization p) hrn hp hp5 hpow
    change p ^ M.factorization p ∣ D at hd
    exact (hp.pow_dvd_iff_le_factorization hD).mp hd

/-- The unpaired middle contribution for `n = 2h > 0` is divisible by
`n+2 = 2(h+1)`. -/
theorem two_mul_add_two_dvd_a220119Weight_middle
    (h : ℕ) (hh : 0 < h) :
    2 * h + 2 ∣ a220119Weight (2 * h) h ^ 2 := by
  have hadd : h + 1 ∣ a220119Weight (2 * h) h :=
    add_one_dvd_a220119Weight (2 * h) h
  rcases Nat.even_or_odd h with heven | hodd
  · obtain ⟨q, hq⟩ := even_iff_exists_two_mul.mp heven
    have hchoose :
        (2 * h).choose h ∣ a220119Weight (2 * h) h :=
      choose_dvd_a220119Weight (2 * h) h
    have htwochoose : 2 ∣ (2 * h).choose h := by
      rw [← Nat.centralBinom_eq_two_mul_choose]
      exact Nat.two_dvd_centralBinom_of_one_le hh
    have htwo : 2 ∣ a220119Weight (2 * h) h :=
      htwochoose.trans hchoose
    have hcop : Nat.Coprime 2 (h + 1) := by
      rw [Nat.prime_two.coprime_iff_not_dvd]
      intro hdvd
      rcases hdvd with ⟨d, hd⟩
      omega
    have hwhole : 2 * (h + 1) ∣ a220119Weight (2 * h) h :=
      hcop.mul_dvd_of_dvd_of_dvd htwo hadd
    simpa [pow_two, show 2 * h + 2 = 2 * (h + 1) by ring] using
      hwhole.mul_right (a220119Weight (2 * h) h)
  · obtain ⟨q, hq⟩ := odd_iff_exists_bit1.mp hodd
    rcases hadd with ⟨u, hu⟩
    refine ⟨(q + 1) * u ^ 2, ?_⟩
    rw [hu, hq]
    ring

/-- A reflection-pair assembly lemma for the exact weight convolution.
It reduces `n+2` divisibility to off-diagonal pairs and fixed points. -/
theorem n_add_two_dvd_weight_convolution_of_reflection
    (n : ℕ)
    (hpairs : ∀ r, r ≤ n → r ≠ n - r →
      n + 2 ∣
        a220119Weight n r * a220119Weight n (n - r) +
          a220119Weight n (n - r) * a220119Weight n r)
    (hfixed : ∀ r, r ≤ n → r = n - r →
      n + 2 ∣ a220119Weight n r * a220119Weight n (n - r)) :
    n + 2 ∣ ∑ r ∈ range (n + 1),
      a220119Weight n r * a220119Weight n (n - r) := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  apply Finset.sum_involution
    (s := range (n + 1))
    (f := fun r => (a220119Weight n r : ZMod (n + 2)) *
      a220119Weight n (n - r))
    (g := fun r _ => n - r)
  · intro r hr
    rw [Finset.mem_range] at hr
    have hinv : n - (n - r) = r := by omega
    by_cases heq : r = n - r
    · have hdvd := hfixed r (by omega) heq
      have hz :
          ((a220119Weight n r * a220119Weight n (n - r) : ℕ) :
            ZMod (n + 2)) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
      rw [← heq] at hz
      rw [hinv, ← heq]
      have hzz := congrArg₂ (· + ·) hz hz
      simpa only [Nat.cast_mul, zero_add] using hzz
    · have hdvd := hpairs r (by omega) heq
      rw [hinv]
      have hz :
          ((a220119Weight n r * a220119Weight n (n - r) +
            a220119Weight n (n - r) * a220119Weight n r : ℕ) :
            ZMod (n + 2)) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
      simpa only [Nat.cast_add, Nat.cast_mul] using hz
  · intro r hr hnonzero
    rw [Finset.mem_range] at hr
    intro heq
    have hdvd := hfixed r (by omega) heq.symm
    apply hnonzero
    rw [heq]
    have hz :
        ((a220119Weight n r * a220119Weight n (n - r) : ℕ) :
          ZMod (n + 2)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [heq] at hz
    simpa only [Nat.cast_mul] using hz
  · intro r hr
    rw [Finset.mem_range] at hr ⊢
    omega
  · intro r hr
    rw [Finset.mem_range] at hr
    omega

/-- Once every off-middle reflection pair is divisible by `n+2`, the exact
convolution and the proved middle-term lemma give `n+2 ∣ a220119 n`. -/
theorem n_add_two_dvd_a220119_of_reflection_pairs
    (n : ℕ) (hn : 0 < n)
    (hpairs : ∀ r, r ≤ n → r ≠ n - r →
      n + 2 ∣
        a220119Weight n r * a220119Weight n (n - r) +
          a220119Weight n (n - r) * a220119Weight n r) :
    n + 2 ∣ a220119 n := by
  rw [a220119_eq_weight_convolution]
  apply n_add_two_dvd_weight_convolution_of_reflection n hpairs
  intro r hr heq
  have hnEq : n = 2 * r := by omega
  have hrpos : 0 < r := by omega
  have hmiddle := two_mul_add_two_dvd_a220119Weight_middle r hrpos
  rw [hnEq] at heq ⊢
  have hsub : 2 * r - r = r := by omega
  rw [hsub]
  simpa only [pow_two] using hmiddle

/-- The second consecutive factor in the A220119 conjecture. -/
theorem a220119_divisible_n_add_two (n : ℕ) (hn : 0 < n) :
    n + 2 ∣ a220119 n := by
  apply n_add_two_dvd_a220119_of_reflection_pairs n hn
  intro r hr hne
  rw [show
    a220119Weight n r * a220119Weight n (n - r) +
        a220119Weight n (n - r) * a220119Weight n r =
      2 * a220119Weight n r * a220119Weight n (n - r) by ring]
  exact n_add_two_dvd_a220119Weight_reflection n r hr hne

/-- The product of the three binomial factors that supplies `n + 1`. -/
private def chooseTriple (n j k : ℕ) : ℕ :=
  (n + j).choose n * (n + k).choose n * (j + k).choose n

/-- Every supported triple-binomial factor is divisible by `n + 1`. -/
lemma add_one_dvd_chooseTriple (n j k : ℕ) :
    n + 1 ∣ chooseTriple n j k := by
  by_cases hsupp : j + k < n
  · simp [chooseTriple, Nat.choose_eq_zero_of_lt hsupp]
  · have hnle : n ≤ j + k := by omega
    let z := j + k - n
    have hjchoose :
        (n + j).choose (n + 1) * (n + 1) = (n + j).choose n * j := by
      simpa only [Nat.add_sub_cancel_left] using Nat.choose_succ_right_eq (n + j) n
    have hkchoose :
        (n + k).choose (n + 1) * (n + 1) = (n + k).choose n * k := by
      simpa only [Nat.add_sub_cancel_left] using Nat.choose_succ_right_eq (n + k) n
    have hzchoose :
        (j + k).choose (n + 1) * (n + 1) = (j + k).choose n * z := by
      simpa only [z] using Nat.choose_succ_right_eq (j + k) n
    have hjdvd : n + 1 ∣ j * chooseTriple n j k := by
      refine ⟨(n + j).choose (n + 1) * (n + k).choose n * (j + k).choose n, ?_⟩
      calc
        j * chooseTriple n j k
            = ((n + j).choose n * j) * (n + k).choose n * (j + k).choose n := by
                rw [chooseTriple]
                ring
        _ = ((n + j).choose (n + 1) * (n + 1)) *
              (n + k).choose n * (j + k).choose n := by rw [hjchoose]
        _ = (n + 1) *
              ((n + j).choose (n + 1) * (n + k).choose n * (j + k).choose n) := by ring
    have hkdvd : n + 1 ∣ k * chooseTriple n j k := by
      refine ⟨(n + k).choose (n + 1) * (n + j).choose n * (j + k).choose n, ?_⟩
      calc
        k * chooseTriple n j k
            = ((n + k).choose n * k) * (n + j).choose n * (j + k).choose n := by
                rw [chooseTriple]
                ring
        _ = ((n + k).choose (n + 1) * (n + 1)) *
              (n + j).choose n * (j + k).choose n := by rw [hkchoose]
        _ = (n + 1) *
              ((n + k).choose (n + 1) * (n + j).choose n * (j + k).choose n) := by ring
    have hzdvd : n + 1 ∣ z * chooseTriple n j k := by
      refine ⟨(j + k).choose (n + 1) * (n + j).choose n * (n + k).choose n, ?_⟩
      calc
        z * chooseTriple n j k
            = ((j + k).choose n * z) * (n + j).choose n * (n + k).choose n := by
                rw [chooseTriple]
                ring
        _ = ((j + k).choose (n + 1) * (n + 1)) *
              (n + j).choose n * (n + k).choose n := by rw [hzchoose]
        _ = (n + 1) *
              ((j + k).choose (n + 1) * (n + j).choose n * (n + k).choose n) := by ring
    have hjkdvd : n + 1 ∣ (j + k) * chooseTriple n j k := by
      rw [add_mul]
      exact hjdvd.add hkdvd
    have hsummed :
        n + 1 ∣ z * chooseTriple n j k + n * chooseTriple n j k := by
      have hcoef : z + n = j + k := by
        dsimp only [z]
        exact Nat.sub_add_cancel hnle
      simpa only [← add_mul, hcoef] using hjkdvd
    have hndvd : n + 1 ∣ n * chooseTriple n j k :=
      (Nat.dvd_add_right hzdvd).mp hsummed
    have htotal :
        n + 1 ∣ n * chooseTriple n j k + chooseTriple n j k := by
      simpa only [add_mul, one_mul] using dvd_mul_right (n + 1) (chooseTriple n j k)
    exact (Nat.dvd_add_right hndvd).mp htotal

/-- The first of the two consecutive factors in the A220119 conjecture. -/
theorem a220119_divisible_n_add_one (n : ℕ) :
    n + 1 ∣ a220119 n := by
  apply Finset.dvd_sum
  intro j hj
  apply Finset.dvd_sum
  intro k hk
  rcases add_one_dvd_chooseTriple n j k with ⟨q, hq⟩
  refine ⟨n.choose j ^ 2 * n.choose k ^ 2 * q, ?_⟩
  rw [chooseTriple] at hq
  rw [show
    n.choose j ^ 2 * n.choose k ^ 2 * (n + j).choose n *
        (n + k).choose n * (j + k).choose n
      = n.choose j ^ 2 * n.choose k ^ 2 *
        ((n + j).choose n * (n + k).choose n * (j + k).choose n) by ring,
    hq]
  ring

/-- **OEIS A220119 conjecture:** for every positive `n`, the exact
double binomial sum is divisible by `(n+1)(n+2)`. -/
theorem a220119_divisible (n : ℕ) (hn : 0 < n) :
    (n + 1) * (n + 2) ∣ a220119 n := by
  have hcop : Nat.Coprime (n + 1) (n + 2) := by
    rw [show n + 2 = 1 + (n + 1) by omega,
      Nat.coprime_add_self_right]
    simp
  exact hcop.mul_dvd_of_dvd_of_dvd
    (a220119_divisible_n_add_one n)
    (a220119_divisible_n_add_two n hn)

example : a220119 0 = 1 := by decide
example : a220119 1 = 12 := by decide
example : a220119 2 = 804 := by decide
example : a220119 3 = 88680 := by decide
example : a220119 4 = 12386340 := by decide
example : a220119 5 = 1985320512 := by decide

#print axioms a220119_divisible
