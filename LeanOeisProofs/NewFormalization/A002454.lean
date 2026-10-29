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

Mathematics: Yue-Feng She, Zhi-Wei Sun and Wei Xia;
Xuejun Guo, Xin Li, Zhengyu Tao and Tao Wei.
Lean development: Wentao Li, assisted by OpenAI Codex (GPT-6.1 Sol).
-/

import LeanOeisProofs.NewFormalization.A001818

/-!
# OEIS A002454: the odd-order permanent identity

Formalization by Wentao Li of She–Sun–Xia, Theorem 1.3(ii), using the
Guo–Li–Tao–Wei determinant argument and the existing A001818 development.

*References:*
- https://oeis.org/A002454
- https://arxiv.org/abs/2208.12167v2
- https://arxiv.org/abs/2206.02592
-/

open Complex Equiv Finset Matrix A001818C1
namespace A002454

lemma long_fiber_edge {N : ℕ} (x : Fin N → ℂ) (hx : Function.Injective x)
    (s : Finset (Fin N)) (τ : Perm (Fin N)) :
    (∑ σ : Perm (Fin N),
      if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
        cycleEdgeWeight x σ
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
        have hsum := sum_cycleEdgeWeight_replace_cycle x hx p hcard
          (show τ.support ⊆ sᶜ from hτ.symm ▸ Subset.rfl)
        refine Eq.trans ?_ hsum
        refine (Fintype.sum_of_injective φ hinj
            (fun e => cycleEdgeWeight x (φ e))
            (fun σ =>
              if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
                cycleEdgeWeight x σ
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
          rw [hφ, ite_eq_left hmem]
      · have h0 : ∀ σ : Perm (Fin N),
            (if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
              cycleEdgeWeight x σ
            else 0) = 0 := by
          intro σ
          split_ifs with hfiber
          · exact (hdist (dist_of_longKey hsn hfiber.1 hfiber.2.2)).elim
          · rfl
        exact (Fintype.sum_congr _ _ h0).trans (by simp)
    · have h0 : ∀ σ : Perm (Fin N),
          (if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
            cycleEdgeWeight x σ
          else 0) = 0 := by
        intro σ
        split_ifs with hfiber
        · exact (hτ (remainder_support_of_longKey hfiber.1 hfiber.2.2
            (derangement_support_univ hfiber.2.1))).elim
        · rfl
      exact (Fintype.sum_congr _ _ h0).trans (by simp)
  · have h0 : ∀ σ : Perm (Fin N),
        (if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
          cycleEdgeWeight x σ
        else 0) = 0 := by
      intro σ
      split_ifs with hfiber
      · exact (hs3 (three_le_card_fst_longKey hfiber.1 hfiber.2.2)).elim
      · rfl
    exact (Fintype.sum_congr _ _ h0).trans (by simp)


lemma long_fiber_signed_edge {N : ℕ}
    (x : Fin N → ℂ) (hx : Function.Injective x) (s : Finset (Fin N)) (τ : Perm (Fin N)) :
    (∑ σ : Perm (Fin N),
      if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
        (Perm.sign σ : ℂ) * cycleEdgeWeight x σ
      else 0) = 0 := by
  have hterm : ∀ σ : Perm (Fin N),
      (if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
        (Perm.sign σ : ℂ) * cycleEdgeWeight x σ
      else 0) =
        (-(-1 : ℂ) ^ s.card * (Perm.sign τ : ℂ)) *
          (if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
            cycleEdgeWeight x σ
          else 0) := by
    intro σ
    split_ifs with h
    · rw [sign_eq_of_mem_longKey h.1 h.2.2 (derangement_support_univ h.2.1)]
    · rw [mul_zero]
  simp_rw [hterm, ← mul_sum, long_fiber_edge x hx s τ, mul_zero]

lemma long_cycle_signed_edge_sum {N : ℕ}
    (x : Fin N → ℂ) (hx : Function.Injective x) :
    (∑ σ : Perm (Fin N),
      if (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
        (Perm.sign σ : ℂ) * cycleEdgeWeight x σ
      else 0) = 0 := by
  rw [sum_eq_sum_longKey (fun σ =>
    if (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
      (Perm.sign σ : ℂ) * cycleEdgeWeight x σ
    else 0)]
  refine Eq.trans (Fintype.sum_congr _ _ fun s =>
      Fintype.sum_congr _ _ fun τ =>
        Fintype.sum_congr _ _ fun σ =>
          ite_longKey_and (fun σ =>
            (Perm.sign σ : ℂ) *
              cycleEdgeWeight x σ) σ) ?_
  refine Eq.trans (Fintype.sum_congr _ _ fun s =>
      Fintype.sum_congr _ _ fun τ => long_fiber_signed_edge x hx s τ) (by simp)


lemma signed_derangement_edge_eq_involution {n : ℕ} (hn : 1 ≤ n)
    (x : Fin (2 * n) → ℂ) (hx : Function.Injective x) :
    (∑ σ : Perm (Fin (2 * n)),
      if (∀ i, σ i ≠ i) then
        (Perm.sign σ : ℂ) * cycleEdgeWeight x σ
      else 0) =
      ∑ σ : Perm (Fin (2 * n)),
        if (∀ i, σ i ≠ i) ∧ σ.cycleType = Multiset.replicate n 2 then
          (Perm.sign σ : ℂ) *
            cycleEdgeWeight x σ
        else 0 := by
  have : NeZero (2 * n) := ⟨by omega⟩
  have hterm : ∀ σ : Perm (Fin (2 * n)),
      (if (∀ i, σ i ≠ i) then
        (Perm.sign σ : ℂ) * cycleEdgeWeight x σ
      else 0) =
        (if (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
          (Perm.sign σ : ℂ) * cycleEdgeWeight x σ
        else 0) +
          (if (∀ i, σ i ≠ i) ∧ σ.cycleType = Multiset.replicate n 2 then
            (Perm.sign σ : ℂ) *
              cycleEdgeWeight x σ
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
        rw [ite_eq_left hder, ite_eq_left ⟨hder, hne⟩,
          ite_eq_right (mt And.right hninv), add_zero]
      · have hnlong : ¬ (longPoints σ).Nonempty := by
          intro hne
          obtain ⟨a, ha⟩ := hne
          exact not_mem_longPoints_of_cycleType_eq_two hinv ha
        rw [ite_eq_left hder, ite_eq_right (mt And.right hnlong), ite_eq_left ⟨hder, hinv⟩,
          zero_add]
    · rw [ite_eq_right hder, ite_eq_right (mt And.left hder), ite_eq_right (mt And.left hder),
        add_zero]
  refine Eq.trans (Fintype.sum_congr _ _ hterm) ?_
  rw [sum_add_distrib, long_cycle_signed_edge_sum x hx, zero_add]


/-- The zero-diagonal reciprocal-difference matrix. -/
noncomputable def differenceMatrix {N : ℕ} (x : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => if i = j then 0 else (x i - x j)⁻¹

lemma differenceMatrix_derangement {N : ℕ} (x : Fin N → ℂ)
    (σ : Perm (Fin N)) (hσ : ∀ i, σ i ≠ i) :
    (∏ i, differenceMatrix x (σ i) i) = cycleEdgeWeight x σ := by
  rw [cycleEdgeWeight, derangement_support_univ hσ]
  apply prod_congr rfl
  intro i _
  simp [differenceMatrix, hσ i]

lemma edge_eq_matching_of_involution {N : ℕ} (x : Fin N → ℂ)
    (σ : Perm (Fin N)) (hsup : σ.support = univ) (hsq : σ * σ = 1) :
    cycleEdgeWeight x σ = matchingWeight x σ := by
  rw [cycleEdgeWeight, hsup, matchingWeight_eq_prod _ hsup]
  have he : ∀ i, σ (σ i) = i := fun i => by
    have h := congrArg (fun f : Perm (Fin N) => f i) hsq
    simpa using h
  calc
    (∏ i, (x (σ i) - x i)⁻¹) = ∏ i, (x (σ i) - x (σ (σ i)))⁻¹ := by simp_rw [he]
    _ = ∏ i, (x i - x (σ i))⁻¹ :=
      Equiv.prod_comp σ (fun i => (x i - x (σ i))⁻¹)

/-- Cancellation of long cycles leaves only perfect matchings in the determinant. -/
theorem determinant_differenceMatrix {n : ℕ} (hn : 1 ≤ n)
    (x : Fin (2 * n) → ℂ) (hx : Function.Injective x) :
    (differenceMatrix x).det = (-1 : ℂ) ^ n * matchingSum x := by
  rw [det_of_zero_diag _ (by intro i; simp [differenceMatrix])]
  have ht : ∀ σ : Perm (Fin (2 * n)),
      (if ∀ i, σ i ≠ i then (Perm.sign σ : ℂ) * ∏ i, differenceMatrix x (σ i) i else 0) =
        if ∀ i, σ i ≠ i then (Perm.sign σ : ℂ) * cycleEdgeWeight x σ else 0 := by
    intro σ
    split_ifs with h
    · rw [differenceMatrix_derangement x σ h]
    · rfl
  simp_rw [ht]
  rw [signed_derangement_edge_eq_involution hn x hx]
  unfold matchingSum
  rw [mul_sum]
  apply sum_congr rfl
  intro σ _
  by_cases h : σ.support = univ ∧ σ * σ = 1
  · have hct := (fpfinv_iff_cycleType (n := n)).mp h
    rw [ite_eq_left hct, ite_eq_left h, sign_of_cycleType_replicate_two hct.2,
      edge_eq_matching_of_involution x σ h.1 h.2]
  · have hct : ¬ ((∀ i, σ i ≠ i) ∧ σ.cycleType = Multiset.replicate n 2) := by
      simpa only [← fpfinv_iff_cycleType] using h
    rw [ite_eq_right hct, ite_eq_right h, mul_zero]

/-- The determinant bridge is valid at arbitrary distinct nonzero complex points. -/
theorem permanent_cayley_eq_difference_det {n : ℕ} (hn : 1 ≤ n)
    (x : Fin (2 * n) → ℂ) (hx : Function.Injective x) :
    (cayleyMatrix x).permanent =
      (-1 : ℂ) ^ n * 4 ^ n * (∏ i, x i) * (differenceMatrix x).det := by
  rw [permanent_cayleyMatrix_eq_cayleySum,
    cayleySum_eq_matching x hx (by simp),
    determinant_differenceMatrix hn x hx]
  have hcard : Fintype.card (Fin (2 * n)) / 2 = n := by simp
  rw [hcard]
  have hs : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
    rw [← mul_pow]; norm_num
  calc
    _ = ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) *
        ((4 : ℂ) ^ n * (∏ i, x i) * matchingSum x) := by rw [hs, one_mul]
    _ = _ := by ring

end A002454

open Matrix Finset
open A001818C1

namespace OeisA2454

/-- Central factorial numbers: $a(n) = 4^n (n!)^2$. -/
def a (n : ℕ) : ℕ :=
  4 ^ n * n.factorial ^ 2

end OeisA2454

namespace A002454

/-- The exact matrix in the frozen source statement. -/
noncomputable def rootMatrix (n : ℕ) (ζ : ℂ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ :=
  fun j k => if j = k then 1
    else (1 + ζ ^ ((j : ℤ) - (k : ℤ))) / (1 - ζ ^ ((j : ℤ) - (k : ℤ)))

/-- The empty-matrix endpoint of the assigned identity. -/
theorem conjecture_zero (ζ : ℂ) :
    (rootMatrix 0 ζ).permanent = ((4 ^ 0 * Nat.factorial 0 ^ 2 : ℕ) : ℂ) / (2 * 0 + 1) := by
  simp [Matrix.permanent_isEmpty]

/-- The trace of the adjugate is preserved by an invertible change of basis. -/
theorem trace_adjugate_of_intertwine {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A F D : Matrix ι ι ℂ) (hF : F.det ≠ 0) (h : A * F = F * D) :
    A.adjugate.trace = D.adjugate.trace := by
  have ha := congrArg Matrix.adjugate h
  rw [adjugate_mul_distrib, adjugate_mul_distrib] at ha
  have hb := congrArg (fun M => F * M) ha
  have hc : F.det • A.adjugate = F * D.adjugate * F.adjugate := by
    simpa only [← Matrix.mul_assoc, mul_adjugate, smul_mul, one_mul] using hb
  have ht := congrArg Matrix.trace hc
  rw [trace_smul, trace_mul_cycle, adjugate_mul, smul_mul, one_mul,
    trace_smul] at ht
  exact mul_left_cancel₀ hF ht

/-- A diagonal matrix with exactly one zero eigenvalue has one nonzero adjugate entry. -/
theorem trace_adjugate_diagonal_single_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℂ) (r : ι) (hr : d r = 0) :
    (diagonal d).adjugate.trace = ∏ j ∈ univ.erase r, d j := by
  rw [adjugate_diagonal, trace_diagonal]
  apply sum_eq_single r
  · intro b _ hbr
    exact prod_eq_zero (mem_erase.mpr ⟨Ne.symm hbr, mem_univ r⟩) hr
  · simp

/-- If a transitive family of index permutations preserves a matrix, its diagonal cofactors agree. -/
theorem adjugate_diag_eq_of_reindex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i j : ι) (e : ι ≃ ι)
    (he : A.submatrix e e = A) (hij : e i = j) :
    A.adjugate i i = A.adjugate j j := by
  have h := congrArg (fun M : Matrix ι ι ℂ => M i i)
    (adjugate_submatrix_equiv_self e A)
  simpa only [he, submatrix_apply, hij] using h

/-- A constant diagonal identifies each cofactor from the trace. -/
theorem adjugate_diag_eq_trace_div {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i : ι)
    (h : ∀ j, A.adjugate j j = A.adjugate i i) :
    A.adjugate i i = A.adjugate.trace / Fintype.card ι := by
  have hcard : (Fintype.card ι : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨i⟩))
  have ht : A.adjugate.trace = (Fintype.card ι : ℂ) * A.adjugate i i := by
    simp only [Matrix.trace, Matrix.diag, h, sum_const, card_univ, nsmul_eq_mul]
  rw [ht, mul_div_cancel_left₀ _ hcard]

/-- The principal minor formula needed for the odd-root determinant evaluation. -/
theorem principal_minor_of_spectrum (m : ℕ)
    (A F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (d : Fin (m + 1) → ℂ) (r : Fin (m + 1))
    (hF : F.det ≠ 0) (hAF : A * F = F * diagonal d) (hr : d r = 0)
    (hdiag : ∀ j, A.adjugate j j = A.adjugate (Fin.last m) (Fin.last m)) :
    (A.submatrix Fin.castSucc Fin.castSucc).det =
      (∏ j ∈ univ.erase r, d j) / (m + 1 : ℕ) := by
  have hb : A.adjugate (Fin.last m) (Fin.last m) =
      (A.submatrix Fin.castSucc Fin.castSucc).det := by
    rw [adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
    simp only [Fin.val_last]
    rw [show m + m = 2 * m by omega, pow_mul, neg_one_sq, one_pow, one_mul]
  rw [← hb, adjugate_diag_eq_trace_div A (Fin.last m) hdiag,
    trace_adjugate_of_intertwine A F (diagonal d) hF hAF,
    trace_adjugate_diagonal_single_zero d r hr, Fintype.card_fin]

lemma prod_descending_cast (n : ℕ) :
    (∏ k ∈ range n, ((n : ℂ) - k)) = (n.factorial : ℂ) := by
  have h := prod_range_reflect (fun k => (n : ℂ) - k) n
  have ht : ∀ k ∈ range n,
      (n : ℂ) - ((n - 1 - k : ℕ) : ℂ) = ((k + 1 : ℕ) : ℂ) := by
    intro k hk
    have hk' := mem_range.mp hk
    have he : n - 1 - k = n - (k + 1) := by omega
    rw [he, Nat.cast_sub (by omega : k + 1 ≤ n)]
    ring
  rw [prod_congr rfl ht, ← Nat.cast_prod, prod_range_add_one_eq_factorial] at h
  exact h.symm

/-- The nonzero eigenvalues in odd order occur as positive and negative even pairs. -/
lemma prod_odd_spectrum (n : ℕ) :
    (∏ r ∈ (univ.erase (⟨n, by omega⟩ : Fin (n + n + 1))),
      (2 * (n : ℂ) - 2 * r.val)) =
      (-1 : ℂ) ^ n * (4 : ℂ) ^ n * (n.factorial : ℂ) ^ 2 := by
  let r : Fin (n + n + 1) := ⟨n, by omega⟩
  have hm : (univ : Finset (Fin (n + n + 1))).erase r =
      univ.map (Fin.succAboveEmb r) := by
    rw [Fin.univ_succAbove (n + n) r]
    simp
  change (∏ j ∈ univ.erase r, (2 * (n : ℂ) - 2 * j.val)) = _
  rw [hm, prod_map]
  change (∏ i : Fin (n + n), (2 * (n : ℂ) - 2 * (r.succAbove i).val)) = _
  rw [Fin.prod_univ_add]
  have hlo : ∀ k : Fin n,
      2 * (n : ℂ) - 2 * (r.succAbove (Fin.castAdd n k)).val = 2 * ((n : ℂ) - k.val) := by
    intro k
    rw [Fin.succAbove_of_castSucc_lt _ _ (show (Fin.castAdd n k).castSucc < r from k.isLt)]
    simp only [Fin.val_castSucc, Fin.val_castAdd]
    ring
  have hhi : ∀ k : Fin n,
      2 * (n : ℂ) - 2 * (r.succAbove (Fin.natAdd n k)).val = (-2 : ℂ) * (k.val + 1) := by
    intro k
    rw [Fin.succAbove_of_le_castSucc _ _ (show r ≤ (Fin.natAdd n k).castSucc from by
      change n ≤ n + k.val
      omega)]
    simp only [Fin.val_succ, Fin.val_natAdd, Nat.cast_add, Nat.cast_one]
    ring
  simp_rw [hlo, hhi, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
  rw [Fin.prod_univ_eq_prod_range (fun k => (n : ℂ) - k) n, prod_descending_cast]
  have hf : (∏ k : Fin n, ((k.val : ℂ) + 1)) = (n.factorial : ℂ) := by
    rw [Fin.prod_univ_eq_prod_range (fun k => (k : ℂ) + 1) n]
    exact_mod_cast prod_range_add_one_eq_factorial n
  rw [hf]
  have hp : (-2 : ℂ) ^ n * 2 ^ n = (-1 : ℂ) ^ n * 4 ^ n := by
    rw [← mul_pow, ← mul_pow]
    norm_num
  calc
    _ = ((-2 : ℂ) ^ n * 2 ^ n) * (n.factorial : ℂ) ^ 2 := by ring
    _ = _ := by rw [hp]

lemma calogero_shift {N : ℕ} [NeZero N] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (a : Fin N) :
    (calogero N ζ).submatrix (Equiv.addRight a) (Equiv.addRight a) = calogero N ζ := by
  ext i j
  change calogero N ζ (i + a) (j + a) = calogero N ζ i j
  by_cases hij : i = j
  · simp [hij, calogero]
  · rw [calogero_apply_ne (by simpa using hij), calogero_apply_ne hij,
      zpow_int_val_sub hζ, zpow_int_val_sub hζ, add_sub_add_right_eq_sub]

lemma calogero_adjugate_diag {N : ℕ} [NeZero N] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (i j : Fin N) :
    (calogero N ζ).adjugate i i = (calogero N ζ).adjugate j j := by
  apply adjugate_diag_eq_of_reindex _ i j (Equiv.addRight (j - i))
  · exact calogero_shift hζ _
  · change i + (j - i) = j
    abel

lemma det_calogero_minor_aux {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (n + n + 1)) :
    ((calogero (n + n + 1) ζ).submatrix Fin.castSucc Fin.castSucc).det =
      (-1 : ℂ) ^ n * 4 ^ n * (n.factorial : ℂ) ^ 2 / (n + n + 1 : ℕ) := by
  have : NeZero (n + n + 1) := ⟨by omega⟩
  let d : Fin (n + n + 1) → ℂ := fun r => ((n + n + 1 : ℕ) : ℂ) - 1 - 2 * (r.val : ℂ)
  let r : Fin (n + n + 1) := ⟨n, by omega⟩
  have hr : d r = 0 := by
    simp [d, r]
    ring
  have h := principal_minor_of_spectrum (n + n) (calogero (n + n + 1) ζ)
    (fourierMatrix (n + n + 1) ζ) d r (det_fourierMatrix_ne_zero hζ)
    (calogero_mul_fourier hζ (by omega)) hr
    (fun j => calogero_adjugate_diag hζ j (Fin.last (n + n)))
  rw [h]
  congr 1
  simpa [d, r, Nat.cast_add, two_mul] using prod_odd_spectrum n

/-- The exact odd-order principal minor evaluation, with no Hermitian spectral theorem. -/
theorem det_calogero_minor {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n + 1)) :
    ((calogero (2 * n + 1) ζ).submatrix Fin.castSucc Fin.castSucc).det =
      (-1 : ℂ) ^ n * 4 ^ n * (n.factorial : ℂ) ^ 2 / (2 * n + 1 : ℕ) := by
  rw [two_mul n] at hζ ⊢
  exact det_calogero_minor_aux hn hζ

lemma root_powers_injective {n : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n + 1)) :
    Function.Injective (fun i : Fin (2 * n) => ζ ^ i.val) := by
  intro i j hij
  exact Fin.ext (hζ.pow_inj (by omega) (by omega) hij)

lemma rootMatrix_eq_cayley {n : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n + 1)) :
    rootMatrix n ζ = cayleyMatrix (fun i : Fin (2 * n) => ζ ^ i.val) := by
  have : NeZero (2 * n + 1) := ⟨by omega⟩
  ext i j
  by_cases hij : i = j
  · simp [rootMatrix, cayleyMatrix, hij]
  · rw [cayleyMatrix_apply_ne _ hij]
    change (if i = j then 1 else _) = _
    rw [ite_eq_right hij]
    have hne : j.castSucc ≠ i.castSucc := by simpa using Ne.symm hij
    simpa using (cayley_eq_sunFactor hζ hne).symm

lemma calogero_minor_eq_difference {n : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n + 1)) :
    (calogero (2 * n + 1) ζ).submatrix Fin.castSucc Fin.castSucc =
      Matrix.of (fun i j : Fin (2 * n) =>
        (-2 * ζ ^ j.val) * differenceMatrix (fun k => ζ ^ k.val) i j) := by
  have : NeZero (2 * n + 1) := ⟨by omega⟩
  have hz := zeta_ne_zero hζ
  ext i j
  by_cases hij : i = j
  · simp [hij, calogero, differenceMatrix]
  · have hij' : i.castSucc ≠ j.castSucc := by simpa using hij
    change calogero (2 * n + 1) ζ i.castSucc j.castSucc = _
    rw [calogero_apply_ne hij']
    simp only [Fin.val_castSucc, Matrix.of_apply, differenceMatrix, ite_eq_right hij]
    have hj : ζ ^ j.val ≠ 0 := pow_ne_zero _ hz
    rw [zpow_sub₀ hz, zpow_natCast, zpow_natCast]
    rw [one_sub_div hj, div_div_eq_mul_div,
      show ζ ^ j.val - ζ ^ i.val = -(ζ ^ i.val - ζ ^ j.val) by ring, div_neg]
    simp only [div_eq_mul_inv]
    ring

/-- Permanent-to-determinant reduction specialized to the source matrix. -/
theorem permanent_rootMatrix_eq_minor {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n + 1)) :
    (rootMatrix n ζ).permanent = (-1 : ℂ) ^ n *
      ((calogero (2 * n + 1) ζ).submatrix Fin.castSucc Fin.castSucc).det := by
  rw [rootMatrix_eq_cayley hζ,
    permanent_cayley_eq_difference_det hn _ (root_powers_injective hζ),
    calogero_minor_eq_difference hζ, det_mul_row, prod_mul_distrib, prod_const,
    card_univ, Fintype.card_fin]
  have hp : (-2 : ℂ) ^ (2 * n) = 4 ^ n := by
    rw [pow_mul]; norm_num
  rw [hp]
  ring

/-- The permanent identity for every natural index, including the empty matrix. -/
theorem conjecture (n : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * n + 1)) :
    (rootMatrix n ζ).permanent =
      ((4 ^ n * n.factorial ^ 2 : ℕ) : ℂ) / (2 * n + 1 : ℕ) := by
  by_cases hn : n = 0
  · subst n
    simpa using conjecture_zero ζ
  · have hn' : 1 ≤ n := by omega
    rw [permanent_rootMatrix_eq_minor hn' hζ, det_calogero_minor hn' hζ]
    push_cast
    have hs : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
      rw [← mul_pow]; norm_num
    calc
      _ = ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) *
          ((4 : ℂ) ^ n * (n.factorial : ℂ) ^ 2 / (2 * n + 1 : ℂ)) := by ring
      _ = _ := by rw [hs, one_mul]

/-- Exact wrapper of `OeisA2454.conjecture` at the frozen upstream revision. -/
theorem conjecture_frozen (n : ℕ) :
    let N : ℕ := 2 * n
    let K : ℕ := N + 1
    ∀ (ζ : ℂ), IsPrimitiveRoot ζ K →
      Matrix.permanent (fun (j k : Fin N) =>
        if j = k then (1 : ℂ)
        else
          let pow : ℤ := (j : ℤ) - (k : ℤ)
          (1 + ζ ^ pow) / (1 - ζ ^ pow)) =
      (OeisA2454.a n : ℂ) / (K : ℂ) := by
  exact fun ζ hζ => conjecture n ζ hζ


end A002454
