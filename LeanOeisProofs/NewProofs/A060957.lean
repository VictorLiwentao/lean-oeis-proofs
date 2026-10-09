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
New proof development and write-up: Wentao Li.
Original conjecture: Yan Sheng Ang.
-/

import Mathlib
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.IrreducibleDef


namespace OeisA60957

def productsOfSubsets (n : ℕ) : Set ℕ :=
  {m : ℕ | ∃ s ⊆ Finset.Icc 1 n, m = s.prod id}

end OeisA60957


/-!
# An explicit counterexample to the A060957 interpolation conjecture

Source: https://oeis.org/A060957

Conjecture: Yan Sheng Ang.
Original Lean statement: the Formal Conjectures Authors,
Google DeepMind's formal-conjectures repository.
New proof research and write-up: Wentao Li, with AI tool assistance.

The final declarations `counterexample` and `not_conjecture` give explicit endpoint
subsets and prove that the intermediate product is absent in the original domain.
Earlier local exchange and same-profile interpolation lemmas are preserved.
The exact-statement audit and axiom checks are documented in the accompanying
PROOF.md and SOURCE.md. The original statement's admitted proof is not imported.
-/

set_option maxRecDepth 4096

namespace PilotA060957

/-- The empty subset witnesses membership of 1. -/
theorem one_mem_products (n : ℕ) : 1 ∈ OeisA60957.productsOfSubsets n := by
  exact ⟨∅, by simp, by simp⟩

/-- Every subset product is positive. -/
theorem products_pos {n m : ℕ} (hm : m ∈ OeisA60957.productsOfSubsets n) :
    0 < m := by
  obtain ⟨s, hs, rfl⟩ := hm
  exact Finset.prod_pos fun x hx => (Finset.mem_Icc.mp (hs hx)).1

/-- Replacing a selected factor by an unused multiple gives one upward step. -/
theorem mul_mem_of_exchange {n p x : ℕ} {s : Finset ℕ}
    (hs : s ⊆ Finset.Icc 1 n) (hx : x ∈ s)
    (hpx : p * x ∈ Finset.Icc 1 n) (hfresh : p * x ∉ s) :
    p * s.prod id ∈ OeisA60957.productsOfSubsets n := by
  refine ⟨insert (p * x) (s.erase x), ?_, ?_⟩
  · exact Finset.insert_subset hpx ((Finset.erase_subset x s).trans hs)
  · rw [Finset.prod_insert (fun h => hfresh (Finset.mem_of_mem_erase h))]
    have hprod := Finset.prod_erase_mul s id hx
    rw [← hprod]
    simp only [id]
    ring

/-- Adding the prime itself is valid when it has not already been selected. -/
theorem mul_mem_of_not_mem {n p : ℕ} {s : Finset ℕ}
    (hs : s ⊆ Finset.Icc 1 n) (hp : p ∈ Finset.Icc 1 n) (hfresh : p ∉ s) :
    p * s.prod id ∈ OeisA60957.productsOfSubsets n := by
  exact ⟨insert p s, Finset.insert_subset hp hs, by simp [hfresh]⟩

/-- If all elements of one equicardinal set are no larger, its sum is no larger. -/
theorem sum_le_of_card_eq {s t : Finset ℕ} (hcard : s.card = t.card)
    (hle : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) : s.sum id ≤ t.sum id := by
  let e := Finset.equivOfCardEq hcard
  calc
    s.sum id = ∑ x : s, (x : ℕ) := (Finset.sum_coe_sort s id).symm
    _ ≤ ∑ x : s, (e x : ℕ) := Finset.sum_le_sum fun x _ =>
      hle x x.property (e x) (e x).property
    _ = ∑ y : t, (y : ℕ) := e.sum_comp (fun y : t => (y : ℕ))
    _ = t.sum id := Finset.sum_coe_sort t id

/-- An upward-closed selection in a finite chain maximizes the sum at its size. -/
theorem sum_le_of_upward_closed {L : ℕ} {s t : Finset ℕ}
    (ht : t ⊆ Finset.range (L + 1)) (hcard : s.card = t.card)
    (hclosed : ∀ x ∈ s, ∀ y, x ≤ y → y ≤ L → y ∈ s) :
    t.sum id ≤ s.sum id := by
  have hdiffcard : (t \ s).card = (s \ t).card := by
    have h₁ := Finset.card_sdiff_add_card_inter s t
    have h₂ := Finset.card_sdiff_add_card_inter t s
    rw [Finset.inter_comm t s] at h₂
    omega
  have hdiff : (t \ s).sum id ≤ (s \ t).sum id := by
    apply sum_le_of_card_eq hdiffcard
    intro x hx y hy
    obtain ⟨hxt, hxs⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hys, _⟩ := Finset.mem_sdiff.mp hy
    have hxL : x ≤ L := by simpa using Finset.mem_range.mp (ht hxt)
    by_contra h
    exact hxs (hclosed y hys x (by omega) hxL)
  have hs_sum := Finset.sum_sdiff (f := id) (Finset.inter_subset_left (s₁ := s) (s₂ := t))
  have ht_sum := Finset.sum_sdiff (f := id) (Finset.inter_subset_left (s₁ := t) (s₂ := s))
  simp only [Finset.sdiff_inter_self_left] at hs_sum ht_sum
  rw [Finset.inter_comm t s] at ht_sum
  change (s \ t).sum id + (s ∩ t).sum id = s.sum id at hs_sum
  change (t \ s).sum id + (s ∩ t).sum id = t.sum id at ht_sum
  omega

/-- Below a larger sum with the same number of chain factors, a unit move exists. -/
theorem exists_chain_step {L : ℕ} {s t : Finset ℕ}
    (ht : t ⊆ Finset.range (L + 1)) (hcard : s.card = t.card)
    (hsum : s.sum id < t.sum id) :
    ∃ x ∈ s, x < L ∧ x + 1 ∉ s := by
  by_contra h
  push Not at h
  have hclosed : ∀ x ∈ s, ∀ y, x ≤ y → y ≤ L → y ∈ s := by
    intro x hx y hxy hyL
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hxy
    induction d with
    | zero => simpa using hx
    | succ d ih =>
      have hprev : x + d ∈ s := ih (by omega) (by omega)
      simpa [Nat.add_assoc] using h (x + d) hprev (by omega)
  have := sum_le_of_upward_closed ht hcard hclosed
  omega

/-- One admissible chain move preserves cardinality and increases the sum by one. -/
theorem chain_step {L : ℕ} {s t : Finset ℕ}
    (hs : s ⊆ Finset.range (L + 1)) (ht : t ⊆ Finset.range (L + 1))
    (hcard : s.card = t.card) (hsum : s.sum id < t.sum id) :
    ∃ u ⊆ Finset.range (L + 1), u.card = s.card ∧ u.sum id = s.sum id + 1 := by
  obtain ⟨x, hx, hxL, hfresh⟩ := exists_chain_step ht hcard hsum
  refine ⟨insert (x + 1) (s.erase x), ?_, ?_, ?_⟩
  · exact Finset.insert_subset (Finset.mem_range.mpr (by omega))
      ((Finset.erase_subset x s).trans hs)
  · rw [Finset.card_insert_of_notMem (fun h => hfresh (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem hx]
    have := Finset.card_pos.mpr ⟨x, hx⟩
    omega
  · rw [Finset.sum_insert (fun h => hfresh (Finset.mem_of_mem_erase h))]
    have hsum := Finset.sum_erase_add s id hx
    change (x + 1) + (s.erase x).sum id = s.sum id + 1
    change (s.erase x).sum id + x = s.sum id at hsum
    omega

/-- Sums of equicardinal selections from one finite chain have no integer gaps. -/
theorem chain_interpolation {L : ℕ} {s t : Finset ℕ}
    (hs : s ⊆ Finset.range (L + 1)) (ht : t ⊆ Finset.range (L + 1))
    (hcard : s.card = t.card) {e : ℕ} (hse : s.sum id ≤ e) (het : e ≤ t.sum id) :
    ∃ u ⊆ Finset.range (L + 1), u.card = s.card ∧ u.sum id = e := by
  have aux : ∀ d : ℕ, ∀ v : Finset ℕ, v ⊆ Finset.range (L + 1) →
      v.card = t.card → v.sum id + d ≤ t.sum id →
      ∃ u ⊆ Finset.range (L + 1), u.card = v.card ∧ u.sum id = v.sum id + d := by
    intro d
    induction d with
    | zero =>
      intro v hv _ _
      exact ⟨v, hv, rfl, by omega⟩
    | succ d ih =>
      intro v hv hcard hsum
      obtain ⟨w, hw, hwcard, hwsum⟩ := chain_step hv ht hcard (by omega)
      obtain ⟨u, hu, hucard, husum⟩ := ih w hw (by omega) (by omega)
      exact ⟨u, hu, by omega, by omega⟩
  obtain ⟨u, hu, hucard, husum⟩ := aux (e - s.sum id) s hs hcard (by omega)
  exact ⟨u, hu, hucard, by omega⟩

/-- The original membership definition also admits a finite decision procedure. -/
theorem mem_products_iff {n m : ℕ} :
    m ∈ OeisA60957.productsOfSubsets n ↔
      m ∈ (Finset.Icc 1 n).powerset.image (fun s : Finset ℕ => s.prod id) := by
  simp only [OeisA60957.productsOfSubsets, Set.mem_ofPred_eq,
    Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, h.symm⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, h.symm⟩

/-- Division by a prime does not preserve membership without a lower endpoint. -/
theorem division_closure_fails :
    18 ∈ OeisA60957.productsOfSubsets 6 ∧
      9 ∉ OeisA60957.productsOfSubsets 6 := by
  constructor
  · exact ⟨{3, 6}, by decide, by norm_num⟩
  · rw [mem_products_iff]
    decide

/-- The division-closed upper-witness branch of a public attempt can occur. -/
theorem closed_upper_obstruction :
    ∃ s t : Finset ℕ, s ⊆ Finset.Icc 1 12 ∧ t ⊆ Finset.Icc 1 12 ∧
      s.prod id = 27 ∧ t.prod id = 2 ^ 3 * 27 ∧ 2 ∉ t ∧
      (∀ x ∈ t, 2 ∣ x → x / 2 ∈ t) := by
  refine ⟨{3, 9}, {3, 6, 12}, ?_⟩
  decide

/-- A prime-division-closed factor set can have an internal prime-direction gap. -/
theorem prime_closed_factor_set_gap :
    let D : Finset ℕ := {1, 2, 3, 6, 12, 27}
    (∀ x ∈ D, 2 ∣ x → x / 2 ∈ D) ∧
    54 ∈ D.powerset.image (fun s : Finset ℕ => s.prod id) ∧
    216 ∈ D.powerset.image (fun s : Finset ℕ => s.prod id) ∧
    108 ∉ D.powerset.image (fun s : Finset ℕ => s.prod id) := by
  decide

/-- The sum of exponents in a finite family of chain selections. -/
def exponentSum (R : Finset ℕ) (f : ℕ → Finset ℕ) : ℕ :=
  ∑ r ∈ R, (f r).sum id

/-- A finite family with fixed chain cardinalities admits an upward unit step. -/
theorem family_chain_step {R : Finset ℕ} {L : ℕ → ℕ} {f g : ℕ → Finset ℕ}
    (hf : ∀ r ∈ R, f r ⊆ Finset.range (L r + 1))
    (hg : ∀ r ∈ R, g r ⊆ Finset.range (L r + 1))
    (hcard : ∀ r ∈ R, (f r).card = (g r).card)
    (hsum : exponentSum R f < exponentSum R g) :
    ∃ h : ℕ → Finset ℕ, (∀ r ∈ R, h r ⊆ Finset.range (L r + 1)) ∧
      (∀ r ∈ R, (h r).card = (f r).card) ∧ exponentSum R h = exponentSum R f + 1 := by
  obtain ⟨r, hr, hlt⟩ := Finset.exists_lt_of_sum_lt hsum
  obtain ⟨u, hu, hucard, husum⟩ := chain_step (hf r hr) (hg r hr) (hcard r hr) hlt
  let h := Function.update f r u
  have hsame : ∀ q, q ≠ r → h q = f q := by
    intro q hqr
    simp [h, hqr]
  have hat : h r = u := by simp [h]
  refine ⟨h, ?_, ?_, ?_⟩
  · intro q hq
    by_cases hqr : q = r
    · simpa [hqr, hat] using hu
    · rw [hsame q hqr]
      exact hf q hq
  · intro q hq
    by_cases hqr : q = r
    · simpa [hqr, hat] using hucard
    · rw [hsame q hqr]
  · have hh_sum := Finset.sum_erase_add R (fun q => (h q).sum id) hr
    have hf_sum := Finset.sum_erase_add R (fun q => (f q).sum id) hr
    have heq : ∑ q ∈ R.erase r, (h q).sum id = ∑ q ∈ R.erase r, (f q).sum id := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [hsame q (Finset.mem_erase.mp hq).1]
    rw [heq, hat] at hh_sum
    change (∑ q ∈ R.erase r, (f q).sum id) + u.sum id = exponentSum R h at hh_sum
    change (∑ q ∈ R.erase r, (f q).sum id) + (f r).sum id = exponentSum R f at hf_sum
    omega

/-- Fixed chain-cardinality profiles have no gaps in their total exponents. -/
theorem family_chain_interpolation {R : Finset ℕ} {L : ℕ → ℕ} {f g : ℕ → Finset ℕ}
    (hf : ∀ r ∈ R, f r ⊆ Finset.range (L r + 1))
    (hg : ∀ r ∈ R, g r ⊆ Finset.range (L r + 1))
    (hcard : ∀ r ∈ R, (f r).card = (g r).card)
    {e : ℕ} (hfe : exponentSum R f ≤ e) (heg : e ≤ exponentSum R g) :
    ∃ h : ℕ → Finset ℕ, (∀ r ∈ R, h r ⊆ Finset.range (L r + 1)) ∧
      (∀ r ∈ R, (h r).card = (f r).card) ∧ exponentSum R h = e := by
  have aux : ∀ d : ℕ, ∀ v : ℕ → Finset ℕ,
      (∀ r ∈ R, v r ⊆ Finset.range (L r + 1)) →
      (∀ r ∈ R, (v r).card = (g r).card) →
      exponentSum R v + d ≤ exponentSum R g →
      ∃ h : ℕ → Finset ℕ, (∀ r ∈ R, h r ⊆ Finset.range (L r + 1)) ∧
        (∀ r ∈ R, (h r).card = (v r).card) ∧ exponentSum R h = exponentSum R v + d := by
    intro d
    induction d with
    | zero =>
      intro v hv _ _
      exact ⟨v, hv, fun _ _ => rfl, by omega⟩
    | succ d ih =>
      intro v hv hcard hsum
      obtain ⟨w, hw, hwcard, hwsum⟩ := family_chain_step hv hg hcard (by omega)
      obtain ⟨h, hh, hhcard, hhsum⟩ := ih w hw
        (fun r hr => (hwcard r hr).trans (hcard r hr)) (by omega)
      exact ⟨h, hh, fun r hr => (hhcard r hr).trans (hwcard r hr), by omega⟩
  obtain ⟨h, hh, hhcard, hhsum⟩ := aux (e - exponentSum R f) f hf hcard (by omega)
  exact ⟨h, hh, hhcard, by omega⟩

/-- The subset of natural factors selected from a finite family of prime chains. -/
def chainSet (R : Finset ℕ) (p : ℕ) (f : ℕ → Finset ℕ) : Finset ℕ :=
  R.biUnion fun r => (f r).image fun j => p ^ j * r

/-- The product of the chain roots, with multiplicity given by the profile. -/
def rootProduct (R : Finset ℕ) (f : ℕ → Finset ℕ) : ℕ :=
  ∏ r ∈ R, r ^ (f r).card

/-- Distinct p-free roots define disjoint chains. -/
theorem chain_images_disjoint {p r q : ℕ} (hp : p.Prime)
    (hr : ¬p ∣ r) (hq : ¬p ∣ q) (hrq : r ≠ q) (s t : Finset ℕ) :
    Disjoint (s.image fun j => p ^ j * r) (t.image fun j => p ^ j * q) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, _, heq⟩ := Finset.mem_image.mp hy
  have hcore := congrArg (fun m => ordCompl[p] m) heq
  rw [Nat.ordCompl_pow_mul_of_not_dvd j hp hq,
    Nat.ordCompl_pow_mul_of_not_dvd i hp hr] at hcore
  exact hrq hcore.symm

/-- A selected family of chains stays inside the original factor domain. -/
theorem chainSet_subset {n p : ℕ} (hp : p.Prime) {R : Finset ℕ}
    {L : ℕ → ℕ} {f : ℕ → Finset ℕ}
    (hpos : ∀ r ∈ R, 0 < r) (hbound : ∀ r ∈ R, p ^ L r * r ≤ n)
    (hf : ∀ r ∈ R, f r ⊆ Finset.range (L r + 1)) :
    chainSet R p f ⊆ Finset.Icc 1 n := by
  intro x hx
  obtain ⟨r, hr, hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  have hjL : j ≤ L r := by have := Finset.mem_range.mp (hf r hr hj); omega
  apply Finset.mem_Icc.mpr
  constructor
  · exact Nat.mul_pos (pow_pos hp.pos j) (hpos r hr)
  · exact (Nat.mul_le_mul_right r (pow_le_pow_right' hp.one_lt.le hjL)).trans
      (hbound r hr)

/-- The actual selected subset product splits into its exponent and root product. -/
theorem chainSet_prod {p : ℕ} (hp : p.Prime) {R : Finset ℕ} {f : ℕ → Finset ℕ}
    (hpos : ∀ r ∈ R, 0 < r) (hfree : ∀ r ∈ R, ¬p ∣ r) :
    (chainSet R p f).prod id = p ^ exponentSum R f * rootProduct R f := by
  have hdis : Set.PairwiseDisjoint (↑R) (fun r => (f r).image fun j => p ^ j * r) := by
    intro r hr q hq hrq
    exact chain_images_disjoint hp (hfree r hr) (hfree q hq) hrq (f r) (f q)
  unfold chainSet
  rw [Finset.prod_biUnion hdis]
  have hlocal : ∀ r ∈ R, ((f r).image fun j => p ^ j * r).prod id =
      p ^ (f r).sum id * r ^ (f r).card := by
    intro r hr
    rw [Finset.prod_image]
    · simp only [id, Finset.prod_mul_distrib, Finset.prod_const]
      rw [Finset.prod_pow_eq_pow_sum]
    · intro i _ j _ hij
      exact Nat.pow_right_injective hp.two_le
        (Nat.eq_of_mul_eq_mul_right (hpos r hr) hij)
  calc
    (∏ r ∈ R, ∏ x ∈ (f r).image (fun j => p ^ j * r), id x) =
        ∏ r ∈ R, (p ^ (f r).sum id * r ^ (f r).card) := Finset.prod_congr rfl hlocal
    _ = p ^ exponentSum R f * rootProduct R f := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      rfl

/-- Interpolation in the original product set for endpoints with the same profile. -/
theorem same_profile_interpolation {n p : ℕ} (hp : p.Prime) {R : Finset ℕ}
    {L : ℕ → ℕ} {f g : ℕ → Finset ℕ}
    (hpos : ∀ r ∈ R, 0 < r) (hfree : ∀ r ∈ R, ¬p ∣ r)
    (hbound : ∀ r ∈ R, p ^ L r * r ≤ n)
    (hf : ∀ r ∈ R, f r ⊆ Finset.range (L r + 1))
    (hg : ∀ r ∈ R, g r ⊆ Finset.range (L r + 1))
    (hcard : ∀ r ∈ R, (f r).card = (g r).card)
    {e : ℕ} (hfe : exponentSum R f ≤ e) (heg : e ≤ exponentSum R g) :
    p ^ e * rootProduct R f ∈ OeisA60957.productsOfSubsets n := by
  obtain ⟨h, hh, hhcard, hhsum⟩ := family_chain_interpolation hf hg hcard hfe heg
  refine ⟨chainSet R p h, chainSet_subset hp hpos hbound hh, ?_⟩
  rw [chainSet_prod hp hpos hfree, hhsum]
  congr 1
  exact Finset.prod_congr rfl fun r hr => congrArg (r ^ ·) (hhcard r hr).symm

/-- The exact intermediate-membership conclusion follows from a one-step lemma. -/
theorem interpolation_of_one_step {n p : ℕ}
    (step : ∀ m a : ℕ, 2 ≤ a → m ∈ OeisA60957.productsOfSubsets n →
      p ^ a * m ∈ OeisA60957.productsOfSubsets n →
      p * m ∈ OeisA60957.productsOfSubsets n)
    {m a : ℕ} (hm : m ∈ OeisA60957.productsOfSubsets n)
    (htop : p ^ a * m ∈ OeisA60957.productsOfSubsets n)
    (k : ℕ) (hka : k < a) : p ^ k * m ∈ OeisA60957.productsOfSubsets n := by
  have hall : ∀ j : ℕ, j < a → p ^ j * m ∈ OeisA60957.productsOfSubsets n := by
    intro j
    induction j with
    | zero => intro _; simpa using hm
    | succ j ih =>
      intro hja
      have hcurrent := ih (by omega)
      have heq : p ^ (a - j) * (p ^ j * m) = p ^ a * m := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega)]
      have hupper : p ^ (a - j) * (p ^ j * m) ∈ OeisA60957.productsOfSubsets n := by
        rwa [heq]
      have hnext := step (p ^ j * m) (a - j) (by omega) hcurrent hupper
      simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hnext
  exact hall k hka


/-- A subset attains the maximum total weight exactly by fixing every nonzero sign. -/
theorem weight_max_forces_selection {D s : Finset ℕ} (hs : s ⊆ D) (w : ℕ → ℤ)
    (hsum : ∑ x ∈ s, w x = ∑ x ∈ D.filter (fun x => 0 < w x), w x) :
    D.filter (fun x => 0 < w x) ⊆ s ∧ ∀ x ∈ s, 0 ≤ w x := by
  have hfilter : D.filter (fun x => x ∈ s) = s := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hx => ⟨hs hx, hx⟩⟩
  have hind : (∑ x ∈ D, if x ∈ s then w x else 0) = ∑ x ∈ s, w x := by
    rw [← Finset.sum_filter, hfilter]
  have hmax : (∑ x ∈ D, max (w x) 0) =
      ∑ x ∈ D.filter (fun x => 0 < w x), w x := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs with h
    · exact max_eq_left h.le
    · exact max_eq_right (by omega)
  have hle : ∀ x ∈ D, (if x ∈ s then w x else 0) ≤ max (w x) 0 := by
    intro x _
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
  have heq := (Finset.sum_eq_sum_iff_of_le hle).mp (hind.trans (hsum.trans hmax.symm))
  constructor
  · intro x hx
    obtain ⟨hxD, hpos⟩ := Finset.mem_filter.mp hx
    by_contra hxs
    have := heq x hxD
    simp only [hxs, ↓reduceIte, max_eq_left hpos.le] at this
    omega
  · intro x hx
    have := heq x (hs hx)
    simp only [hx, ↓reduceIte] at this
    exact this ▸ le_max_right (w x) 0

/-- At a maximum additive weight, subset-product membership reduces to zero-weight factors. -/
theorem weight_face_products {D : Finset ℕ} (hD : ∀ x ∈ D, 0 < x)
    (w : ℕ → ℤ) (hw1 : w 1 = 0)
    (hwmul : ∀ a b : ℕ, 0 < a → 0 < b → w (a * b) = w a + w b)
    (z : ℕ) (hz : 0 < z) (hwz : w z = 0) :
    (∃ s ⊆ D, (D.filter (fun x => 0 < w x)).prod id * z = s.prod id) ↔
      ∃ s ⊆ D.filter (fun x => w x = 0), z = s.prod id := by
  have hweight : ∀ t : Finset ℕ, (∀ x ∈ t, 0 < x) →
      w (t.prod id) = ∑ x ∈ t, w x := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _; simpa using hw1
    | @insert a t ha ih =>
      intro ht
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      change w (a * t.prod id) = w a + ∑ x ∈ t, w x
      rw [hwmul a (t.prod id) (ht a (by simp))
        (Finset.prod_pos fun x hx => ht x (Finset.mem_insert_of_mem hx))]
      rw [ih (fun x hx => ht x (Finset.mem_insert_of_mem hx))]
  let P := D.filter (fun x => 0 < w x)
  have hPD : P ⊆ D := Finset.filter_subset _ _
  have hPpos : 0 < P.prod id := Finset.prod_pos fun x hx => hD x (hPD hx)
  constructor
  · rintro ⟨s, hs, hprod⟩
    have hsum : ∑ x ∈ s, w x = ∑ x ∈ P, w x := by
      rw [← hweight s (fun x hx => hD x (hs hx)), ← hprod,
        hwmul (P.prod id) z hPpos hz, hwz, add_zero,
        hweight P (fun x hx => hD x (hPD hx))]
    obtain ⟨hPs, hnonneg⟩ := weight_max_forces_selection hs w hsum
    refine ⟨s \ P, ?_, ?_⟩
    · intro x hx
      obtain ⟨hxs, hxP⟩ := Finset.mem_sdiff.mp hx
      apply Finset.mem_filter.mpr
      refine ⟨hs hxs, ?_⟩
      have hnot : ¬ 0 < w x := fun h => hxP (Finset.mem_filter.mpr ⟨hs hxs, h⟩)
      have := hnonneg x hxs
      omega
    · apply Nat.eq_of_mul_eq_mul_left hPpos
      have hsplit := Finset.prod_sdiff (f := id) hPs
      calc
        P.prod id * z = s.prod id := hprod
        _ = (s \ P).prod id * P.prod id := hsplit.symm
        _ = P.prod id * (s \ P).prod id := Nat.mul_comm _ _
  · rintro ⟨s, hs, hprod⟩
    have hsD : s ⊆ D := hs.trans (Finset.filter_subset _ _)
    have hdis : Disjoint P s := by
      apply Finset.disjoint_left.mpr
      intro x hxP hxs
      have hpos := (Finset.mem_filter.mp hxP).2
      have hzero := (Finset.mem_filter.mp (hs hxs)).2
      omega
    refine ⟨P ∪ s, Finset.union_subset hPD hsD, ?_⟩
    rw [Finset.prod_union hdis, ← hprod]

/-- The nonnegative integer points of the circuit subspace have an integral
normal form in the six X and twelve Y generators. -/
theorem circuit_normal_form {I J : Type*} [Fintype J] [Nonempty J]
    (i₀ : I) (j₀ : J) (d : I → J → ℕ) (c : J → ℕ)
    (hc₀ : c j₀ = d i₀ j₀)
    (hrect : ∀ i j, d i j + d i₀ j₀ = d i j₀ + d i₀ j)
    (hcross : ∀ j, 2 * c j = d i₀ j₀ + d i₀ j) :
    ∃ a : I → ℕ, ∃ b : J → ℕ,
      (∀ i j, d i j = a i + 2 * b j) ∧
      (∀ j, c j = a i₀ + b j₀ + b j) := by
  classical
  obtain ⟨jmin, _, hmin⟩ := Finset.exists_min_image Finset.univ c Finset.univ_nonempty
  have hmin' : ∀ j, c jmin ≤ c j := fun j => hmin j (Finset.mem_univ j)
  refine ⟨fun i => d i jmin, fun j => c j - c jmin, ?_, ?_⟩
  · intro i j
    dsimp only
    have := hrect i j
    have := hrect i jmin
    have := hcross j
    have := hcross jmin
    have := hmin' j
    omega
  · intro j
    dsimp only
    have := hcross jmin
    have := hmin' j
    have := hmin' j₀
    omega

/-- The distinguished prime in the explicit circuit candidate. -/
def circuitPrime : ℕ := 9304595970494411110326649421962412033

/-- Repeated modular squaring, evaluated by ordinary kernel reduction. -/
def iteratedSquareMod (n a : ℕ) : ℕ → ℕ
  | 0 => a % n
  | k + 1 => iteratedSquareMod n ((a * a) % n) k

/-- Correctness of the modular-squaring certificate computation. -/
theorem iteratedSquareMod_spec (n a k : ℕ) :
    (iteratedSquareMod n a k : ZMod n) = (a : ZMod n) ^ (2 ^ k) := by
  induction k generalizing a with
  | zero => simp [iteratedSquareMod, ZMod.natCast_mod]
  | succ k ih =>
    rw [iteratedSquareMod, ih, ZMod.natCast_mod, Nat.cast_mul]
    rw [← pow_two, ← pow_mul]
    congr 1
    rw [Nat.pow_succ]
    omega

set_option maxRecDepth 4096 in
/-- A complete Lucas certificate, using the prime factors 2 and 7 of p-1. -/
theorem circuitPrime_prime : circuitPrime.Prime := by
  apply lucas_primality circuitPrime (3 : ZMod circuitPrime)
  · have he : circuitPrime - 1 = 7 * 2 ^ 120 := by norm_num [circuitPrime]
    rw [he, pow_mul]
    have hseven : (3 : ZMod circuitPrime) ^ 7 = 2187 := by norm_num
    rw [hseven]
    have hs := iteratedSquareMod_spec circuitPrime 2187 120
    norm_num only [Nat.cast_ofNat] at hs ⊢
    rw [← hs]
    have h : iteratedSquareMod circuitPrime 2187 120 = 1 := by decide
    rw [h]
    simp
  · intro q hq hdiv
    have hdiv' : q ∣ 7 * 2 ^ 120 := by simpa [circuitPrime] using hdiv
    rcases hq.dvd_mul.mp hdiv' with h7 | h2
    · have heq : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h7
      subst q
      have he : (circuitPrime - 1) / 7 = 2 ^ 120 := by norm_num [circuitPrime]
      rw [he]
      have hs := iteratedSquareMod_spec circuitPrime 3 120
      norm_num only [Nat.cast_ofNat] at hs ⊢
      rw [← hs]
      have h : iteratedSquareMod circuitPrime 3 120 = 7117895553901548798585914943695356519 := by decide
      rw [h]
      decide
    · have heq : q = 2 :=
        (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2)
      subst q
      have he : (circuitPrime - 1) / 2 = 7 * 2 ^ 119 := by norm_num [circuitPrime]
      rw [he, pow_mul]
      have hseven : (3 : ZMod circuitPrime) ^ 7 = 2187 := by norm_num
      rw [hseven]
      have hs := iteratedSquareMod_spec circuitPrime 2187 119
      norm_num only [Nat.cast_ofNat] at hs ⊢
      rw [← hs]
      have h : iteratedSquareMod circuitPrime 2187 119 = 9304595970494411110326649421962412032 := by decide
      rw [h]
      decide

/-- Auxiliary diagonal primes, arranged in six rows and twelve columns. -/
def circuitDiag : Fin 6 → Fin 12 → ℕ := ![
  ![199, 13381, 10369, 8761, 6991, 6427, 5623, 5323, 4861, 4327, 4177, 3821],
  ![4099, 65537, 65539, 65543, 65551, 65557, 65563, 65579, 65581, 65587, 65599, 65609],
  ![4111, 65617, 65629, 65633, 65647, 65651, 65657, 65677, 65687, 65699, 65701, 65707],
  ![4127, 65713, 65717, 65719, 65729, 65731, 65761, 65777, 65789, 65809, 65827, 65831],
  ![4129, 65837, 65839, 65843, 65851, 65867, 65881, 65899, 65921, 65927, 65929, 65951],
  ![4133, 65957, 65963, 65981, 65983, 65993, 66029, 66037, 66041, 66047, 66067, 66071]]

/-- Auxiliary primes for the eleven cross coordinates. -/
def circuitCross : Fin 11 → ℕ := ![3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

/-- The coordinates of the circuit cone. -/
abbrev CircuitCoord := (Fin 6 × Fin 12) ⊕ Fin 11

/-- The auxiliary prime belonging to a coordinate. -/
def circuitAux : CircuitCoord → ℕ
  | .inl ij => circuitDiag ij.1 ij.2
  | .inr j => circuitCross j

/-- All primes used in the construction, with the distinguished prime at none. -/
def circuitBasis : Option CircuitCoord → ℕ
  | none => circuitPrime
  | some q => circuitAux q

/-- A monomial in an indexed family of primes. -/
def primeMonomial {ι : Type*} [Fintype ι] (q : ι → ℕ) (e : ι → ℕ) : ℕ :=
  ∏ i, q i ^ e i

/-- A monomial in positive bases is positive. -/
theorem primeMonomial_pos {ι : Type*} [Fintype ι] (q : ι → ℕ)
    (hq : ∀ i, 0 < q i) (e : ι → ℕ) : 0 < primeMonomial q e := by
  exact Finset.prod_pos fun i _ => pow_pos (hq i) _

/-- Each indexed prime has its prescribed exponent. -/
theorem primeMonomial_factorization {ι : Type*} [Fintype ι] (q : ι → ℕ)
    (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q) (e : ι → ℕ) (i : ι) :
    (primeMonomial q e).factorization (q i) = e i := by
  classical
  rw [primeMonomial, Nat.factorization_prod (fun j _ => pow_ne_zero _ (hq j).ne_zero)]
  simp [hq, Finsupp.single_apply, hinj.eq_iff]

/-- No unindexed prime appears in a monomial. -/
theorem primeMonomial_factorization_other {ι : Type*} [Fintype ι] (q : ι → ℕ)
    (hq : ∀ i, (q i).Prime) (e : ι → ℕ) (r : ℕ) (hr : ∀ i, q i ≠ r) :
    (primeMonomial q e).factorization r = 0 := by
  classical
  rw [primeMonomial, Nat.factorization_prod (fun j _ => pow_ne_zero _ (hq j).ne_zero)]
  simp [hq, hr]

/-- Divisors of a monomial have bounded exponent vectors in the same basis. -/
theorem dvd_primeMonomial {ι : Type*} [Fintype ι] (q : ι → ℕ)
    (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q) (v : ι → ℕ)
    {x : ℕ} (hx : x ≠ 0) (hdiv : x ∣ primeMonomial q v) :
    ∃ e : ι → ℕ, (∀ i, e i ≤ v i) ∧ x = primeMonomial q e := by
  classical
  let e := fun i => x.factorization (q i)
  have hpos (f : ι → ℕ) := primeMonomial_pos q (fun i => (hq i).pos) f
  have hle := (Nat.factorization_le_iff_dvd hx (hpos v).ne').mpr hdiv
  refine ⟨e, ?_, ?_⟩
  · intro i
    have := hle (q i)
    rwa [primeMonomial_factorization q hq hinj] at this
  · apply Nat.eq_of_factorization_eq hx (hpos e).ne'
    intro r
    by_cases hr : ∃ i, q i = r
    · obtain ⟨i, rfl⟩ := hr
      rw [primeMonomial_factorization q hq hinj]
    · have hr' : ∀ i, q i ≠ r := by simpa using hr
      rw [primeMonomial_factorization_other q hq e r hr']
      have := hle r
      rw [primeMonomial_factorization_other q hq v r hr'] at this
      omega

/-- Addition of exponent vectors corresponds to multiplication. -/
theorem primeMonomial_add {ι : Type*} [Fintype ι] (q : ι → ℕ) (a b : ι → ℕ) :
    primeMonomial q (fun i => a i + b i) = primeMonomial q a * primeMonomial q b := by
  simp [primeMonomial, pow_add, Finset.prod_mul_distrib]

/-- Finite sums of exponent vectors correspond to products. -/
theorem primeMonomial_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (q : ι → ℕ) (e : κ → ι → ℕ) :
    primeMonomial q (fun i => ∑ j, e j i) = ∏ j, primeMonomial q (e j) := by
  simp only [primeMonomial, ← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]

/-- Scaling exponents corresponds to taking powers. -/
theorem primeMonomial_smul {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (e : ι → ℕ) (k : ℕ) :
    primeMonomial q (fun i => e i * k) = primeMonomial q e ^ k := by
  simp [primeMonomial, pow_mul, Finset.prod_pow]

/-- The exponent vector of X_i. -/
def circuitXExp (i : Fin 6) : Option CircuitCoord → ℕ
  | none => 0
  | some (.inl ij) => if ij.1 = i then 1 else 0
  | some (.inr _) => if i = 0 then 1 else 0

/-- The exponent vector of Y_j. -/
def circuitYExp (j : Fin 12) : Option CircuitCoord → ℕ
  | none => 0
  | some (.inl ij) => if ij.2 = j then 2 else 0
  | some (.inr k) => (if j = 0 then 1 else 0) + (if j = k.succ then 1 else 0)

/-- Six repeated atoms of the circuit. -/
def circuitX (i : Fin 6) : ℕ := primeMonomial circuitBasis (circuitXExp i)

/-- Twelve atoms on the other side of the circuit. -/
def circuitY (j : Fin 12) : ℕ := primeMonomial circuitBasis (circuitYExp j)

/-- The original-domain initial-segment endpoint. -/
irreducible_def circuitN : ℕ := circuitPrime * 2 ^ 189

/-- All auxiliary coordinates have multiplicity two in the target core. -/
def circuitCoreExp : Option CircuitCoord → ℕ
  | none => 0
  | some _ => 2

/-- The common p-free core of the two circuit profiles. -/
irreducible_def circuitCore : ℕ := primeMonomial circuitBasis circuitCoreExp

set_option maxRecDepth 16384 in
/-- Small auxiliary primes and all their separation conditions are exact. -/
theorem circuitAux_facts :
    (∀ q, (circuitAux q).Prime) ∧ Function.Injective circuitAux ∧
    (∀ q, circuitAux q < circuitPrime) := by
  constructor
  · intro q
    cases q with
    | inl ij =>
      obtain ⟨i, j⟩ := ij
      fin_cases i <;> fin_cases j <;> norm_num [circuitAux, circuitDiag]
    | inr j => fin_cases j <;> norm_num [circuitAux, circuitCross]
  · decide

/-- The full indexed family consists of distinct primes. -/
theorem circuitBasis_facts :
    (∀ q, (circuitBasis q).Prime) ∧ Function.Injective circuitBasis := by
  obtain ⟨hp, hinj, hlt⟩ := circuitAux_facts
  constructor
  · intro q
    cases q with
    | none => exact circuitPrime_prime
    | some q => exact hp q
  · intro a b h
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b =>
        have hb := hlt b
        change circuitPrime = circuitAux b at h
        omega
    | some a =>
      cases b with
      | none =>
        have ha := hlt a
        change circuitAux a = circuitPrime at h
        omega
      | some b => exact congrArg some (hinj h)

/-- The exact size margins determine all atom capacities and exclude composites. -/
theorem circuit_size_bounds :
    circuitPrime ^ 2 ≤ circuitN ∧ circuitN < circuitPrime ^ 3 ∧
    circuitN < (2 ^ 177) ^ 2 ∧
    (∀ i, 2 ^ 177 ≤ circuitX i ∧ circuitX i * circuitPrime ≤ circuitN ∧
      circuitN < circuitX i * circuitPrime ^ 2) ∧
    (∀ j, 2 ^ 177 ≤ circuitY j ∧ circuitY j ≤ circuitN) ∧
    circuitY 0 * circuitPrime ≤ circuitN ∧
    circuitN < circuitY 0 * circuitPrime ^ 2 ∧
    (∀ j : Fin 11, circuitN < circuitY j.succ * circuitPrime) := by
  rw [circuitN_def]
  decide

/-- Balanced-base combination of finitely many additive weights. -/
def combinedWeight (B : ℤ) : List (ℕ → ℤ) → ℕ → ℤ
  | [], _ => 0
  | w :: ws, x => w x + B * combinedWeight B ws x

/-- Balanced digits of absolute value less than B cannot cancel to zero. -/
theorem combinedWeight_zero {B : ℤ} (hB : 0 < B) (ws : List (ℕ → ℤ)) (x : ℕ)
    (hb : ∀ w ∈ ws, -B < w x ∧ w x < B) :
    combinedWeight B ws x = 0 ↔ ∀ w ∈ ws, w x = 0 := by
  induction ws with
  | nil => simp [combinedWeight]
  | cons w ws ih =>
    have hb₀ := hb w (by simp)
    have hbt : ∀ f ∈ ws, -B < f x ∧ f x < B := fun f hf => hb f (by simp [hf])
    rw [combinedWeight]
    constructor
    · intro hz
      have hd : B ∣ w x := ⟨-combinedWeight B ws x, by nlinarith [hz]⟩
      have hw : w x = 0 := by
        by_cases hnonneg : 0 ≤ w x
        · exact Int.eq_zero_of_dvd_of_nonneg_of_lt hnonneg hb₀.2 hd
        · have hn : -w x = 0 := Int.eq_zero_of_dvd_of_nonneg_of_lt
            (by omega) (by omega) (dvd_neg.mpr hd)
          omega
      have ht : combinedWeight B ws x = 0 := by
        have : B * combinedWeight B ws x = 0 := by omega
        exact (mul_eq_zero.mp this).resolve_left hB.ne'
      simpa [hw] using (ih hbt).mp ht
    · intro hz
      have hw := hz w (by simp)
      have ht := (ih hbt).mpr (fun f hf => hz f (by simp [hf]))
      simp [hw, ht]

/-- Linear combinations preserve additivity of weights on positive products. -/
theorem combinedWeight_additive (B : ℤ) (ws : List (ℕ → ℤ))
    (hws : ∀ w ∈ ws, ∀ a b : ℕ, 0 < a → 0 < b → w (a * b) = w a + w b)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    combinedWeight B ws (a * b) = combinedWeight B ws a + combinedWeight B ws b := by
  induction ws with
  | nil => simp [combinedWeight]
  | cons w ws ih =>
    rw [combinedWeight, hws w (by simp) a b ha hb,
      ih (fun f hf => hws f (by simp [hf]))]
    simp only [combinedWeight]
    ring

/-- The rectangle constraints defining the circuit subspace. -/
def circuitRectWeight (i : Fin 5) (j : Fin 11) (x : ℕ) : ℤ :=
    (x.factorization (circuitDiag i.succ j.succ) : ℤ) -
    x.factorization (circuitDiag i.succ 0) - x.factorization (circuitDiag 0 j.succ) +
    x.factorization (circuitDiag 0 0)

/-- The parity constraints make the circuit normal form integral. -/
def circuitCrossWeight (j : Fin 11) (x : ℕ) : ℤ :=
    2 * (x.factorization (circuitCross j) : ℤ) -
    x.factorization (circuitDiag 0 0) - x.factorization (circuitDiag 0 j.succ)

/-- All sixty-six defining constraints, in a fixed order. -/
def circuitWeights : List (ℕ → ℤ) :=
    ((List.finRange 5).flatMap fun i => (List.finRange 11).map (circuitRectWeight i)) ++
    (List.finRange 11).map circuitCrossWeight

/-- A sufficiently large base prevents cancellation between constraint digits. -/
def circuitWeightBase : ℤ := 4 * (circuitN : ℤ) + 1

/-- The additive weight exposing the circuit face of the original domain. -/
def circuitWeight : ℕ → ℤ := combinedWeight circuitWeightBase circuitWeights

/-- The distinguished prime has no auxiliary coordinate. -/
theorem circuitPrime_factorization_aux (q : CircuitCoord) :
    circuitPrime.factorization (circuitAux q) = 0 := by
  rw [circuitPrime_prime.factorization]
  simp [(circuitAux_facts.2.2 q).ne']

/-- Every individual constraint is additive on positive products. -/
theorem circuitWeights_additive :
    ∀ w ∈ circuitWeights, ∀ a b : ℕ, 0 < a → 0 < b → w (a * b) = w a + w b := by
  intro w hw a b ha hb
  simp only [circuitWeights, List.mem_append, List.mem_flatMap, List.mem_finRange,
    true_and, List.mem_map] at hw
  rcases hw with ⟨i, j, _, rfl⟩ | ⟨j, _, rfl⟩
  · dsimp only [circuitRectWeight]
    simp only [Nat.factorization_mul ha.ne' hb.ne', Finsupp.add_apply, Nat.cast_add]
    ring
  · dsimp only [circuitCrossWeight]
    simp only [Nat.factorization_mul ha.ne' hb.ne', Finsupp.add_apply, Nat.cast_add]
    ring

/-- The face weight is additive on positive products. -/
theorem circuitWeight_additive (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    circuitWeight (a * b) = circuitWeight a + circuitWeight b :=
  combinedWeight_additive _ _ circuitWeights_additive a b ha hb

/-- Prime valuations of a factor do not exceed the factor itself. -/
theorem factorization_le_self_of_prime (x q : ℕ) (hq : q.Prime) :
    x.factorization q ≤ x := by
  rw [Nat.factorization_def x hq]
  exact Nat.padicValNat_le_self x

/-- All constraint digits lie strictly between minus the base and the base. -/
theorem circuitWeights_bounded {x : ℕ} (hx : x ≤ circuitN) :
    ∀ w ∈ circuitWeights, -circuitWeightBase < w x ∧ w x < circuitWeightBase := by
  have hd (i : Fin 6) (j : Fin 12) :
      (x.factorization (circuitDiag i j) : ℤ) ≤ circuitN := by
    exact_mod_cast (factorization_le_self_of_prime x _ (circuitAux_facts.1 (.inl (i,j)))).trans hx
  have hc (j : Fin 11) : (x.factorization (circuitCross j) : ℤ) ≤ circuitN := by
    exact_mod_cast (factorization_le_self_of_prime x _ (circuitAux_facts.1 (.inr j))).trans hx
  intro w hw
  simp only [circuitWeights, List.mem_append, List.mem_flatMap, List.mem_finRange,
    true_and, List.mem_map] at hw
  rcases hw with ⟨i, j, _, rfl⟩ | ⟨j, _, rfl⟩
  · dsimp only [circuitRectWeight, circuitWeightBase]
    have := hd i.succ j.succ
    have := hd i.succ 0
    have := hd 0 j.succ
    have := hd 0 0
    omega
  · dsimp only [circuitCrossWeight, circuitWeightBase]
    have := hc j
    have := hd 0 0
    have := hd 0 j.succ
    omega

set_option maxRecDepth 4096 in
/-- Vanishing of all separate constraints implies vanishing of their combination. -/
theorem circuitWeight_eq_zero {x : ℕ}
    (hr : ∀ i j, circuitRectWeight i j x = 0)
    (hc : ∀ j, circuitCrossWeight j x = 0) : circuitWeight x = 0 := by
  have hall : ∀ w ∈ circuitWeights, w x = 0 := by
    intro w hw
    simp only [circuitWeights, List.mem_append, List.mem_flatMap, List.mem_finRange,
      true_and, List.mem_map] at hw
    rcases hw with ⟨i, j, _, rfl⟩ | ⟨j, _, rfl⟩
    · exact hr i j
    · exact hc j
  have hB : 0 < circuitWeightBase := by
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (by decide) (Int.natCast_nonneg _)) (by decide)
  exact (combinedWeight_zero hB circuitWeights x
    (fun w hw => by rw [hall w hw]; constructor <;> omega)).mpr hall

/-- In the original bounded domain, the single weight detects all constraints. -/
theorem circuitWeight_zero_iff {x : ℕ} (hx : x ≤ circuitN) :
    circuitWeight x = 0 ↔
      (∀ i j, circuitRectWeight i j x = 0) ∧ (∀ j, circuitCrossWeight j x = 0) := by
  constructor
  · intro hw
    unfold circuitWeight at hw
    have hB : 0 < circuitWeightBase := by
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (by decide) (Int.natCast_nonneg _)) (by decide)
    have hall := (combinedWeight_zero hB circuitWeights x (circuitWeights_bounded hx)).mp hw
    constructor
    · intro i j
      apply hall
      simp [circuitWeights]
    · intro j
      apply hall
      simp [circuitWeights]
  · rintro ⟨hr, hc⟩
    exact circuitWeight_eq_zero hr hc

/-- The unit has zero face weight. -/
theorem circuitWeight_one : circuitWeight 1 = 0 := by
  apply circuitWeight_eq_zero
  · intro i j
    dsimp only [circuitRectWeight]
    simp
  · intro j
    dsimp only [circuitCrossWeight]
    simp

/-- Circuit equations for an exponent vector in the full prime basis. -/
def CircuitEquations (e : Option CircuitCoord → ℕ) : Prop :=
    (∀ i j, e (some (.inl (i,j))) + e (some (.inl (0,0))) =
      e (some (.inl (i,0))) + e (some (.inl (0,j)))) ∧
    (∀ j : Fin 11, 2 * e (some (.inr j)) =
      e (some (.inl (0,0))) + e (some (.inl (0,j.succ))))

/-- Valuations in the indexed prime basis. -/
def circuitVal (x : ℕ) (q : Option CircuitCoord) : ℕ :=
  x.factorization (circuitBasis q)

/-- The circuit equations imply zero face weight for a monomial. -/
theorem circuitWeight_monomial {e : Option CircuitCoord → ℕ} (he : CircuitEquations e) :
    circuitWeight (primeMonomial circuitBasis e) = 0 := by
  have hf := primeMonomial_factorization circuitBasis circuitBasis_facts.1 circuitBasis_facts.2 e
  apply circuitWeight_eq_zero
  · intro i j
    have hd := he.1 i.succ j.succ
    change ((primeMonomial circuitBasis e).factorization
      (circuitBasis (some (.inl (i.succ,j.succ)))) : ℤ) -
      (primeMonomial circuitBasis e).factorization (circuitBasis (some (.inl (i.succ,0)))) -
      (primeMonomial circuitBasis e).factorization (circuitBasis (some (.inl (0,j.succ)))) +
      (primeMonomial circuitBasis e).factorization (circuitBasis (some (.inl (0,0)))) = 0
    rw [hf, hf, hf, hf]
    omega
  · intro j
    have hd := he.2 j
    change 2 * ((primeMonomial circuitBasis e).factorization
      (circuitBasis (some (.inr j))) : ℤ) -
      (primeMonomial circuitBasis e).factorization (circuitBasis (some (.inl (0,0)))) -
      (primeMonomial circuitBasis e).factorization (circuitBasis (some (.inl (0,j.succ)))) = 0
    rw [hf, hf, hf]
    omega

/-- Zero weight in the bounded domain gives the defining circuit equations. -/
theorem circuitEquations_of_weight_zero {x : ℕ} (hx : x ≤ circuitN)
    (hw : circuitWeight x = 0) : CircuitEquations (circuitVal x) := by
  obtain ⟨hr, hc⟩ := (circuitWeight_zero_iff hx).mp hw
  constructor
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [circuitVal, circuitBasis, circuitAux]
      omega
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp only [circuitVal, circuitBasis, circuitAux]
      · have h := hr i j
        dsimp only [circuitRectWeight] at h
        dsimp only [circuitVal, circuitBasis, circuitAux]
        omega
  · intro j
    have h := hc j
    dsimp only [circuitCrossWeight] at h
    dsimp only [circuitVal, circuitBasis, circuitAux]
    omega

/-- The unit coordinate isolates a power of the distinguished prime. -/
def circuitPureExp (k : ℕ) : Option CircuitCoord → ℕ
  | none => k
  | some _ => 0

/-- The generators and common core lie in the circuit subspace. -/
theorem circuit_generator_equations :
    (∀ i, CircuitEquations (circuitXExp i)) ∧
    (∀ j, CircuitEquations (circuitYExp j)) ∧
    CircuitEquations circuitCoreExp ∧ (∀ k, CircuitEquations (circuitPureExp k)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold CircuitEquations
    decide
  · unfold CircuitEquations
    decide
  · unfold CircuitEquations
    decide
  · intro k
    constructor <;> intros <;> rfl

/-- Pure monomials are ordinary powers of p. -/
theorem circuitPure_monomial (k : ℕ) :
    primeMonomial circuitBasis (circuitPureExp k) = circuitPrime ^ k := by
  classical
  unfold primeMonomial
  rw [Finset.prod_eq_single none]
  · rfl
  · intro b _ hb
    cases b with
    | none => exact (hb rfl).elim
    | some q => simp [circuitPureExp]
  · simp

/-- Integral normal form gives a decomposition into the eighteen atoms. -/
theorem circuit_monomial_normal_form {e : Option CircuitCoord → ℕ}
    (he : CircuitEquations e) :
    ∃ a : Fin 6 → ℕ, ∃ b : Fin 12 → ℕ,
      primeMonomial circuitBasis e =
        circuitPrime ^ e none * (∏ i, circuitX i ^ a i) * (∏ j, circuitY j ^ b j) := by
  let d := fun (i : Fin 6) (j : Fin 12) => e (some (.inl (i,j)))
  let c : Fin 12 → ℕ := Fin.cases (d 0 0) (fun j => e (some (.inr j)))
  have hc : ∀ j, 2 * c j = d 0 0 + d 0 j := by
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · dsimp [c]
      omega
    · exact he.2 j
  obtain ⟨a, b, hd, hb⟩ := circuit_normal_form (0 : Fin 6) (0 : Fin 12) d c rfl he.1 hc
  have hv : e = fun q => (circuitPureExp (e none) q +
      ∑ i, circuitXExp i q * a i) + ∑ j, circuitYExp j q * b j := by
    funext q
    cases q with
    | none => simp [circuitPureExp, circuitXExp, circuitYExp]
    | some q =>
      cases q with
      | inl ij =>
        obtain ⟨i,j⟩ := ij
        simpa [circuitPureExp, circuitXExp, circuitYExp, d, Nat.mul_comm] using hd i j
      | inr j =>
        have h := hb j.succ
        simpa [circuitPureExp, circuitXExp, circuitYExp, add_mul,
          Finset.sum_add_distrib, c, Nat.add_assoc] using h
  refine ⟨a, b, ?_⟩
  conv_lhs => rw [hv]
  rw [primeMonomial_add, primeMonomial_add, circuitPure_monomial,
    primeMonomial_sum, primeMonomial_sum]
  simp only [primeMonomial_smul, circuitX, circuitY]

/-- A product with total exponent at most one is the unit or one base. -/
theorem prod_pow_of_sum_le_one {ι : Type*} [Fintype ι] (f e : ι → ℕ)
    (he : ∑ i, e i ≤ 1) :
    (∏ i, f i ^ e i) = 1 ∨ ∃ i, (∏ j, f j ^ e j) = f i := by
  classical
  by_cases hz : ∀ i, e i = 0
  · left
    simp [hz]
  · push Not at hz
    obtain ⟨i, hi⟩ := hz
    have hthin := Finset.sum_le_one_iff.mp he
    have hei : e i = 1 := (hthin i i (by simp) (by simp) hi hi).2
    right
    refine ⟨i, ?_⟩
    rw [Finset.prod_eq_single i]
    · simp [hei]
    · intro j _ hji
      have hej : e j = 0 := by
        by_contra hj
        exact hji (hthin j i (by simp) (by simp) hj hi).1
      simp [hej]
    · simp

/-- A relevant zero-weight divisor is a pure power or a power times one atom. -/
theorem circuit_zero_divisor_root {x : ℕ} (hx : 0 < x) (hxn : x ≤ circuitN)
    (hdiv : x ∣ circuitPrime ^ 5 * circuitCore) (hw : circuitWeight x = 0) :
    (∃ k, x = circuitPrime ^ k) ∨
      (∃ i k, x = circuitPrime ^ k * circuitX i) ∨
      (∃ j k, x = circuitPrime ^ k * circuitY j) := by
  classical
  let v := fun q => circuitPureExp 5 q + circuitCoreExp q
  have ht : primeMonomial circuitBasis v = circuitPrime ^ 5 * circuitCore := by
    rw [primeMonomial_add, circuitPure_monomial, circuitCore_def]
  rw [← ht] at hdiv
  obtain ⟨e, _, hxe⟩ := dvd_primeMonomial circuitBasis circuitBasis_facts.1
    circuitBasis_facts.2 v hx.ne' hdiv
  have hval : circuitVal x = e := by
    funext q
    rw [circuitVal, hxe, primeMonomial_factorization circuitBasis
      circuitBasis_facts.1 circuitBasis_facts.2]
  have he := circuitEquations_of_weight_zero hxn hw
  rw [hval] at he
  obtain ⟨a, b, hab⟩ := circuit_monomial_normal_form he
  have hxprod : x = circuitPrime ^ e none * (∏ i, circuitX i ^ a i) *
      (∏ j, circuitY j ^ b j) := hxe.trans hab
  let f : Fin 6 ⊕ Fin 12 → ℕ := Sum.elim circuitX circuitY
  let g : Fin 6 ⊕ Fin 12 → ℕ := Sum.elim a b
  have hgprod : (∏ q, f q ^ g q) = (∏ i, circuitX i ^ a i) *
      (∏ j, circuitY j ^ b j) := by rw [Fintype.prod_sum_type]; rfl
  obtain ⟨_, _, hnK, hX, hY, _, _, _⟩ := circuit_size_bounds
  have hmin : ∀ q, 2 ^ 177 ≤ f q := by
    intro q
    cases q with
    | inl i => exact (hX i).1
    | inr j => exact (hY j).1
  have hlow : (2 ^ 177) ^ (∑ q, g q) ≤ ∏ q, f q ^ g q := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      (fun q _ => Nat.pow_le_pow_left (hmin q) _)
  have hupper : (∏ q, f q ^ g q) ≤ x := by
    rw [hgprod, hxprod]
    have hp : 0 < circuitPrime ^ e none := pow_pos circuitPrime_prime.pos _
    nlinarith
  have hsum : ∑ q, g q ≤ 1 := by
    by_contra h
    have htwo : 2 ≤ ∑ q, g q := by omega
    have hk : (2 ^ 177) ^ 2 ≤ (2 ^ 177) ^ (∑ q, g q) :=
      Nat.pow_le_pow_right (by norm_num) htwo
    have := hk.trans (hlow.trans (hupper.trans hxn))
    omega
  rcases prod_pow_of_sum_le_one f g hsum with hunit | ⟨q, hq⟩
  · left
    refine ⟨e none, ?_⟩
    rw [hxprod, mul_assoc, ← hgprod, hunit, mul_one]
  · cases q with
    | inl i =>
      right; left
      refine ⟨i, e none, ?_⟩
      rw [hxprod, mul_assoc, ← hgprod, hq]
      rfl
    | inr j =>
      right; right
      refine ⟨j, e none, ?_⟩
      rw [hxprod, mul_assoc, ← hgprod, hq]
      rfl

/-- Labels for the twenty-eight possible factors in the reduced problem. -/
abbrev CircuitFactorLabel := Fin 3 ⊕ ((Fin 6 × Fin 2) ⊕ (Fin 2 ⊕ Fin 11))

/-- The exponent vector of a reduced factor. -/
def circuitFactorExp : CircuitFactorLabel → Option CircuitCoord → ℕ
  | .inl k => circuitPureExp k.val
  | .inr (.inl ik) => fun q => circuitPureExp ik.2.val q + circuitXExp ik.1 q
  | .inr (.inr (.inl k)) => fun q => circuitPureExp k.val q + circuitYExp 0 q
  | .inr (.inr (.inr j)) => circuitYExp j.succ

/-- A reduced factor, expressed in the original positive-integer domain. -/
def circuitFactor (l : CircuitFactorLabel) : ℕ :=
  primeMonomial circuitBasis (circuitFactorExp l)

/-- The concrete values of the four groups of reduced factors. -/
theorem circuitFactor_values :
    (∀ k, circuitFactor (.inl k) = circuitPrime ^ k.val) ∧
    (∀ i k, circuitFactor (.inr (.inl (i,k))) = circuitPrime ^ k.val * circuitX i) ∧
    (∀ k, circuitFactor (.inr (.inr (.inl k))) = circuitPrime ^ k.val * circuitY 0) ∧
    (∀ j, circuitFactor (.inr (.inr (.inr j))) = circuitY j.succ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    exact circuitPure_monomial k.val
  · intro i k
    change primeMonomial circuitBasis (fun q => circuitPureExp k.val q + circuitXExp i q) = _
    rw [primeMonomial_add, circuitPure_monomial]
    rfl
  · intro k
    change primeMonomial circuitBasis (fun q => circuitPureExp k.val q + circuitYExp 0 q) = _
    rw [primeMonomial_add, circuitPure_monomial]
    rfl
  · intro j
    rfl

/-- The finite reduced list has no duplicate and lies in the original domain. -/
theorem circuitFactor_facts : Function.Injective circuitFactor ∧
    (∀ l, 0 < circuitFactor l ∧ circuitFactor l ≤ circuitN) := by
  rw [circuitN_def]
  decide

/-- Every relevant zero-weight divisor belongs to the reduced finite list. -/
theorem circuit_zero_divisor_label {x : ℕ} (hx : 0 < x) (hxn : x ≤ circuitN)
    (hdiv : x ∣ circuitPrime ^ 5 * circuitCore) (hw : circuitWeight x = 0) :
    ∃ l, x = circuitFactor l := by
  obtain ⟨_, hp3, _, hX, _, hY0, hY0', hYrest⟩ := circuit_size_bounds
  have hp1 : 1 ≤ circuitPrime := circuitPrime_prime.one_lt.le
  rcases circuit_zero_divisor_root hx hxn hdiv hw with ⟨k, hxk⟩ | ⟨i,k,hxk⟩ | ⟨j,k,hxk⟩
  · have hk : k < 3 := by
      by_contra h
      have hpow := Nat.pow_le_pow_right hp1 (show 3 ≤ k by omega)
      rw [← hxk] at hpow
      omega
    refine ⟨.inl ⟨k,hk⟩, ?_⟩
    rw [circuitFactor_values.1]
    exact hxk
  · have hk : k < 2 := by
      by_contra h
      have hpow := Nat.pow_le_pow_right hp1 (show 2 ≤ k by omega)
      have hmul := Nat.mul_le_mul_right (circuitX i) hpow
      have hbad := (hX i).2.2
      rw [← hxk] at hmul
      nlinarith
    refine ⟨.inr (.inl (i,⟨k,hk⟩)), ?_⟩
    rw [circuitFactor_values.2.1]
    exact hxk
  · revert hxk
    refine Fin.cases (fun hxk => ?_) (fun j hxk => ?_) j
    · have hk : k < 2 := by
        by_contra h
        have hpow := Nat.pow_le_pow_right hp1 (show 2 ≤ k by omega)
        have hmul := Nat.mul_le_mul_right (circuitY 0) hpow
        rw [← hxk] at hmul
        nlinarith
      refine ⟨.inr (.inr (.inl ⟨k,hk⟩)), ?_⟩
      rw [circuitFactor_values.2.2.1]
      exact hxk
    · have hk : k = 0 := by
        by_contra h
        have hpow := Nat.pow_le_pow_right hp1 (show 1 ≤ k by omega)
        have hmul := Nat.mul_le_mul_right (circuitY j.succ) hpow
        simp only [pow_one] at hmul
        rw [← hxk] at hmul
        have hbad := hYrest j
        nlinarith
      refine ⟨.inr (.inr (.inr j)), ?_⟩
      rw [circuitFactor_values.2.2.2]
      simpa [hk] using hxk

/-- Reduced factors have their displayed prime exponents. -/
theorem circuitFactor_factorization (l : CircuitFactorLabel) (q : Option CircuitCoord) :
    (circuitFactor l).factorization (circuitBasis q) = circuitFactorExp l q :=
  primeMonomial_factorization circuitBasis circuitBasis_facts.1 circuitBasis_facts.2 _ q

/-- Summing a single coordinate selector extracts its weight. -/
theorem weighted_delta_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℕ) (i : ι) (k : ℕ) :
    (∑ j, f j * (if j = i then k else 0)) = f i * k := by
  simp [mul_ite]

/-- Exact coefficient descriptions for the diagonal and p coordinates. -/
theorem circuit_selection_coefficients :
    (∀ (i : Fin 6) (l : CircuitFactorLabel),
      circuitFactorExp l (some (.inl (i,1))) =
        (if l = .inr (.inl (i,0)) then 1 else 0) +
        (if l = .inr (.inl (i,1)) then 1 else 0) +
        (if l = .inr (.inr (.inr 0)) then 2 else 0)) ∧
    (∀ l : CircuitFactorLabel, circuitFactorExp l (some (.inl (0,0))) =
        (if l = .inr (.inl (0,0)) then 1 else 0) +
        (if l = .inr (.inl (0,1)) then 1 else 0) +
        (if l = .inr (.inr (.inl 0)) then 2 else 0) +
        (if l = .inr (.inr (.inl 1)) then 2 else 0)) ∧
    (∀ l : CircuitFactorLabel, circuitFactorExp l none =
        (if l = .inl 1 then 1 else 0) + (if l = .inl 2 then 2 else 0) +
        (∑ i : Fin 6, if l = .inr (.inl (i,1)) then 1 else 0) +
        (if l = .inr (.inr (.inl 1)) then 1 else 0)) := by
  decide

/-- No zero-one selection of the reduced factors can have p exponent five
and auxiliary exponents two. -/
theorem circuit_no_selection (f : CircuitFactorLabel → ℕ) (hf : ∀ l, f l ≤ 1)
    (hd : ∀ i j, ∑ l, f l * circuitFactorExp l (some (.inl (i,j))) = 2)
    (hp : ∑ l, f l * circuitFactorExp l none = 5) : False := by
  have hdi (i : Fin 6) : f (.inr (.inl (i,0))) + f (.inr (.inl (i,1))) +
      f (.inr (.inr (.inr 0))) * 2 = 2 := by
    have h := hd i 1
    simp_rw [circuit_selection_coefficients.1, mul_add, Finset.sum_add_distrib,
      weighted_delta_sum, mul_one] at h
    exact h
  have hd00 := hd 0 0
  simp_rw [circuit_selection_coefficients.2.1, mul_add, Finset.sum_add_distrib,
    weighted_delta_sum, mul_one] at hd00
  have hdouble : (∑ l : CircuitFactorLabel, ∑ i : Fin 6,
      f l * (if l = .inr (.inl (i,1)) then 1 else 0)) =
      ∑ i : Fin 6, f (.inr (.inl (i,1))) := by
    rw [Finset.sum_comm]
    simp only [weighted_delta_sum, mul_one]
  simp_rw [circuit_selection_coefficients.2.2, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum] at hp
  rw [hdouble] at hp
  simp only [weighted_delta_sum, mul_one] at hp
  have hb := hf (.inr (.inr (.inr 0)))
  rcases (show f (.inr (.inr (.inr 0))) = 0 ∨ f (.inr (.inr (.inr 0))) = 1 by omega) with hz | ho
  · have hones : ∀ i : Fin 6, f (.inr (.inl (i,1))) = 1 := by
      intro i
      have := hdi i
      have := hf (.inr (.inl (i,0)))
      have := hf (.inr (.inl (i,1)))
      omega
    have hsum : (∑ i : Fin 6, f (.inr (.inl (i,1)))) = 6 := by simp [hones]
    rw [hsum] at hp
    omega
  · have hzeros : ∀ i : Fin 6, f (.inr (.inl (i,1))) = 0 := by
      intro i
      have := hdi i
      omega
    have hsum : (∑ i : Fin 6, f (.inr (.inl (i,1)))) = 0 := by simp [hzeros]
    rw [hsum] at hp
    have := hf (.inl 1)
    have := hf (.inl 2)
    have := hf (.inr (.inr (.inl 1)))
    omega

/-- The missing product is impossible even among all twenty-eight reduced factors. -/
theorem circuit_reduced_nonmembership (s : Finset CircuitFactorLabel) :
    s.prod circuitFactor ≠ circuitPrime ^ 5 * circuitCore := by
  classical
  intro hprod
  let v := fun q => circuitPureExp 5 q + circuitCoreExp q
  have ht : primeMonomial circuitBasis v = circuitPrime ^ 5 * circuitCore := by
    rw [primeMonomial_add, circuitPure_monomial, circuitCore_def]
  rw [← ht] at hprod
  have hval (q : Option CircuitCoord) : ∑ l ∈ s, circuitFactorExp l q = v q := by
    have h := congrArg (fun x : ℕ => x.factorization (circuitBasis q)) hprod
    rw [Nat.factorization_prod (fun l _ => (circuitFactor_facts.2 l).1.ne'),
      primeMonomial_factorization circuitBasis circuitBasis_facts.1 circuitBasis_facts.2] at h
    simpa only [Finsupp.finsetSum_apply, circuitFactor_factorization] using h
  let f := fun l => if l ∈ s then 1 else 0
  have hf : ∀ l, f l ≤ 1 := by intro l; simp [f]; split_ifs <;> omega
  have hsum (q : Option CircuitCoord) : ∑ l, f l * circuitFactorExp l q = v q := by
    rw [← hval q]
    calc
      (∑ l, f l * circuitFactorExp l q) = ∑ l ∈ s, f l * circuitFactorExp l q := by
        symm
        apply Finset.sum_subset (Finset.subset_univ s)
        intro l _ hls
        simp [f, hls]
      _ = ∑ l ∈ s, circuitFactorExp l q := by
        apply Finset.sum_congr rfl
        intro l hl
        simp [f, hl]
  apply circuit_no_selection f hf
  · intro i j
    exact hsum (some (.inl (i,j)))
  · exact hsum none



/-- The positive-weight factors are forced in every endpoint representation. -/
irreducible_def circuitPositive : Finset ℕ :=
  (Finset.Icc 1 circuitN).filter (fun x => 0 < circuitWeight x)

/-- The explicit common multiplier obtained from the supporting face. -/
@[irreducible] def circuitMultiplier : ℕ := circuitPositive.prod id

/-- The lower endpoint parameter in the exact counterexample. -/
@[irreducible] def circuitM : ℕ := circuitMultiplier * circuitCore

/-- The common core is positive. -/
theorem circuitCore_pos : 0 < circuitCore := by
  rw [circuitCore_def]
  exact primeMonomial_pos _ (fun q => (circuitBasis_facts.1 q).pos) _

/-- Every p-power multiple of the common core has zero face weight. -/
theorem circuitWeight_target (k : ℕ) : circuitWeight (circuitPrime ^ k * circuitCore) = 0 := by
  rw [circuitWeight_additive _ _ (pow_pos circuitPrime_prime.pos _) circuitCore_pos]
  have hp : circuitWeight (circuitPrime ^ k) = 0 := by
    rw [← circuitPure_monomial]
    exact circuitWeight_monomial (circuit_generator_equations.2.2.2 k)
  have hr : circuitWeight circuitCore = 0 := by
    rw [circuitCore_def]
    exact circuitWeight_monomial circuit_generator_equations.2.2.1
  rw [hp, hr, add_zero]

/-- Every reduced factor has zero face weight. -/
theorem circuitFactor_weight_zero (l : CircuitFactorLabel) :
    circuitWeight (circuitFactor l) = 0 := by
  apply circuitWeight_monomial
  have he : ∀ l, CircuitEquations (circuitFactorExp l) := by
    unfold CircuitEquations
    decide
  exact he l

/-- A finite classification on a supporting face transfers finite nonmembership
back to the full subset-product domain. -/
theorem nonmembership_of_weight_face {ι : Type*} [Fintype ι]
    (n z : ℕ) (hz : 0 < z) (w : ℕ → ℤ) (hw1 : w 1 = 0)
    (hwmul : ∀ a b : ℕ, 0 < a → 0 < b → w (a * b) = w a + w b)
    (hwz : w z = 0) (f : ι → ℕ) (hinj : Function.Injective f)
    (hclass : ∀ x, 0 < x → x ≤ n → x ∣ z → w x = 0 → ∃ l, x = f l)
    (hred : ∀ s : Finset ι, s.prod f ≠ z) :
    ((Finset.Icc 1 n).filter (fun x => 0 < w x)).prod id * z ∉
      OeisA60957.productsOfSubsets n := by
  classical
  intro hatt
  obtain ⟨s, hs, hsz⟩ := (weight_face_products (D := Finset.Icc 1 n)
    (fun x hx => (Finset.mem_Icc.mp hx).1) w hw1 hwmul z hz hwz).mp hatt
  let t := Finset.univ.filter (fun l => f l ∈ s)
  have himage : t.image f = s := by
    ext x
    constructor
    · intro hx
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hl).2
    · intro hx
      obtain ⟨hxD, hxW⟩ := Finset.mem_filter.mp (hs hx)
      obtain ⟨hxpos, hxn⟩ := Finset.mem_Icc.mp hxD
      have hdiv : x ∣ z := by
        rw [hsz]
        exact Finset.dvd_prod_of_mem id hx
      obtain ⟨l, hl⟩ := hclass x hxpos hxn hdiv hxW
      apply Finset.mem_image.mpr
      refine ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, ?_⟩, hl.symm⟩
      rwa [← hl]
  have htprod : t.prod f = s.prod id := by
    rw [← himage, Finset.prod_image]
    · rfl
    · intro a _ b _ hab
      exact hinj hab
  exact hred t (htprod.trans hsz.symm)

/-- The missing intermediate value is unattainable in the full original domain. -/
theorem circuit_intermediate_not_mem :
    circuitPrime ^ 5 * circuitM ∉ OeisA60957.productsOfSubsets circuitN := by
  have h := nonmembership_of_weight_face circuitN (circuitPrime ^ 5 * circuitCore)
    (mul_pos (pow_pos circuitPrime_prime.pos _) circuitCore_pos)
    circuitWeight circuitWeight_one circuitWeight_additive (circuitWeight_target 5)
    circuitFactor circuitFactor_facts.1
    (fun _ hx hn hd hw => circuit_zero_divisor_label hx hn hd hw)
    circuit_reduced_nonmembership
  rw [← circuitPositive_def] at h
  have he : circuitPrime ^ 5 * circuitM =
      circuitPositive.prod id * (circuitPrime ^ 5 * circuitCore) := by
    delta circuitM circuitMultiplier
    exact Nat.mul_left_comm (circuitPrime ^ 5) (circuitPositive.prod id) circuitCore
  rw [he]
  exact h

/-- The lower endpoint chooses all twelve Y roots. -/
def circuitLowerLabels : Finset CircuitFactorLabel :=
  Finset.univ.image (fun j : Fin 12 =>
    Fin.cases (.inr (.inr (.inl 0))) (fun j => .inr (.inr (.inr j))) j)

/-- The upper endpoint chooses both members of each X chain. -/
def circuitUpperLabels : Finset CircuitFactorLabel :=
  Finset.univ.image (fun ik : Fin 6 × Fin 2 => .inr (.inl ik))

/-- The two small endpoint products satisfy the circuit relation exactly. -/
theorem circuit_endpoint_products :
    circuitLowerLabels.prod circuitFactor = circuitCore ∧
    circuitUpperLabels.prod circuitFactor = circuitPrime ^ 6 * circuitCore := by
  rw [circuitCore_def]
  decide

/-- Adjoin the forced positive-weight factors to a reduced subset. -/
def circuitLift (s : Finset CircuitFactorLabel) : Finset ℕ :=
  circuitPositive ∪ s.image circuitFactor

/-- Every lifted subset lies in the exact original initial segment. -/
theorem circuitLift_subset (s : Finset CircuitFactorLabel) :
    circuitLift s ⊆ Finset.Icc 1 circuitN := by
  apply Finset.union_subset
  · rw [circuitPositive_def]
    exact Finset.filter_subset _ _
  · intro x hx
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Icc.mpr (circuitFactor_facts.2 l)

/-- Lifting multiplies the reduced subset product by the explicit common factor. -/
theorem circuitLift_prod (s : Finset CircuitFactorLabel) :
    (circuitLift s).prod id = circuitMultiplier * s.prod circuitFactor := by
  classical
  have hdis : Disjoint circuitPositive (s.image circuitFactor) := by
    apply Finset.disjoint_left.mpr
    intro x hxP hxs
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hxs
    rw [circuitPositive_def] at hxP
    have hpos := (Finset.mem_filter.mp hxP).2
    rw [circuitFactor_weight_zero] at hpos
    omega
  rw [circuitLift, Finset.prod_union hdis, Finset.prod_image]
  · unfold circuitMultiplier
    rfl
  · intro a _ b _ hab
    exact circuitFactor_facts.1 hab

/-- An explicit subset witnessing the lower endpoint. -/
def circuitLowerWitness : Finset ℕ := circuitLift circuitLowerLabels

/-- An explicit subset witnessing the upper endpoint. -/
def circuitUpperWitness : Finset ℕ := circuitLift circuitUpperLabels

/-- The endpoint subsets have the required products in the original domain. -/
theorem circuit_endpoint_witnesses :
    circuitLowerWitness ⊆ Finset.Icc 1 circuitN ∧
    circuitUpperWitness ⊆ Finset.Icc 1 circuitN ∧
    circuitLowerWitness.prod id = circuitM ∧
    circuitUpperWitness.prod id = circuitPrime ^ 6 * circuitM := by
  refine ⟨circuitLift_subset _, circuitLift_subset _, ?_, ?_⟩
  · rw [circuitLowerWitness, circuitLift_prod, circuit_endpoint_products.1]
    unfold circuitM
    rfl
  · rw [circuitUpperWitness, circuitLift_prod, circuit_endpoint_products.2]
    unfold circuitM
    ring

/-- Explicit parameters disprove the unchanged original interpolation statement. -/
theorem counterexample : circuitPrime.Prime ∧ circuitPrime ≤ circuitN ∧
    circuitM ∈ OeisA60957.productsOfSubsets circuitN ∧
    circuitPrime ^ 6 * circuitM ∈ OeisA60957.productsOfSubsets circuitN ∧
    0 < (5 : ℕ) ∧ 5 < (6 : ℕ) ∧
    circuitPrime ^ 5 * circuitM ∉ OeisA60957.productsOfSubsets circuitN := by
  refine And.intro circuitPrime_prime ?_
  refine And.intro ?_ ?_
  · rw [circuitN_def]
    exact Nat.le_mul_of_pos_right circuitPrime (by decide : 0 < 2 ^ 189)
  refine And.intro ?_ ?_
  · change ∃ s ⊆ Finset.Icc 1 circuitN, circuitM = s.prod id
    exact ⟨circuitLowerWitness, circuit_endpoint_witnesses.1,
      circuit_endpoint_witnesses.2.2.1.symm⟩
  refine And.intro ?_ ?_
  · change ∃ s ⊆ Finset.Icc 1 circuitN, circuitPrime ^ 6 * circuitM = s.prod id
    exact ⟨circuitUpperWitness, circuit_endpoint_witnesses.2.1,
      circuit_endpoint_witnesses.2.2.2.symm⟩
  exact ⟨by decide, by decide, circuit_intermediate_not_mem⟩

/-- Negation of the exact original statement, with every quantifier retained. -/
theorem not_conjecture : ¬ (∀ (n p : ℕ), p.Prime → p ≤ n →
    ∀ (m a_exp : ℕ), m ∈ OeisA60957.productsOfSubsets n →
    p ^ a_exp * m ∈ OeisA60957.productsOfSubsets n →
    ∀ k : ℕ, 0 < k → k < a_exp → p ^ k * m ∈ OeisA60957.productsOfSubsets n) := by
  intro h
  obtain ⟨hp, hpn, hm, hma, hk0, hka, hnot⟩ := counterexample
  exact hnot (h circuitN circuitPrime hp hpn circuitM 6 hm hma 5 hk0 hka)

end PilotA060957

#print axioms PilotA060957.not_conjecture
#print axioms PilotA060957.counterexample
