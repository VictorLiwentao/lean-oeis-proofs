/-
Copyright 2025 The Formal Conjectures Authors.
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
New Lean development and write-up: Wentao Li.
AI assistance: Cursor Grok 4.6 Extra High, as a research worker in batch b01.

Prior informal mathematical proof:
https://github.com/google-deepmind/formal-conjectures/pull/5447
GitHub author: j2d9w5xtjn-png (2026-09-10).
This file is known mathematics with a newly developed Lean proof.
It is not a new mathematical discovery.
-/

import Mathlib


/-- Composite-number predicate from Formal Conjectures (2025). -/
abbrev Nat.Composite (n : ℕ) : Prop := 1 < n ∧ ¬ n.Prime

/-- Carmichael predicate from Formal Conjectures (2026), retained unchanged. -/
def IsCarmichael (n : ℕ) : Prop :=
  ∀ b ≥ 1, n.Coprime b → n.FermatPsp b

namespace OeisA237271

open Nat Finset List

def a (n : ℕ) : ℕ :=
  -- Get the list of divisors of n, sorted ascendingly.
  let divs_list : List ℕ := (n.divisors.sort (· ≤ ·))

  -- Get the list of consecutive pairs of divisors: [(d₁, d₂), (d₂, d₃), ...]
  let consecutive_pairs : List (ℕ × ℕ) := List.zip divs_list divs_list.tail

  -- Count the pairs satisfying the condition
  let count : ℕ := consecutive_pairs.countP fun pair =>
    let d_k := pair.fst
    let d_k_succ := pair.snd
    -- The second divisor d_{k+1} must be odd and at least twice the first divisor d_k.
    Odd d_k_succ ∧ d_k_succ ≥ 2 * d_k

  -- The sequence value is 1 + the count
  1 + count

end OeisA237271


/-!
# Proof of `OeisA237271.observation_carmichael`

Frozen source: `FormalConjectures/OEIS/237271.lean` at
`a2f4a1bb12a28e04a969da78feefac7d1ce49565`.
This file restates and proves that declaration from the definitions.
It does not use `OeisA237271.observation_carmichael`, `conjecture_2`, or any
`sorry`-dependent helper.
-/

open Nat List

namespace OeisA237271.Cursor01

private lemma getElem_eq_of_idx {α : Type*} {l : List α} {i j : ℕ}
    (h : i = j) {hi : i < l.length} {hj : j < l.length} :
    l[i] = l[j] := by
  cases h
  rfl

private lemma a_eq (n : ℕ) :
    a n = 1 + ((n.divisors.sort (· ≤ ·)).zip (n.divisors.sort (· ≤ ·)).tail).countP
      fun pair => Odd pair.snd ∧ pair.snd ≥ 2 * pair.fst :=
  rfl

private lemma countP_ge_two_of_getElem {α : Type*} {p : α → Bool} {l : List α}
    (hlen : 2 ≤ l.length)
    (h0 : p (l[0]'(by omega)) = true)
    (h1 : p (l[l.length - 1]'(by omega)) = true) :
    2 ≤ l.countP p := by
  match l with
  | [] => simp at hlen
  | [_] => simp at hlen
  | x :: y :: rest =>
    have hx : p x = true := by simpa using h0
    rw [countP_cons_of_pos (by simpa using hx)]
    have : 0 < (y :: rest).countP p := by
      rw [countP_pos_iff]
      refine ⟨(y :: rest).getLast (by simp), getLast_mem _, ?_⟩
      have hlast :
          (y :: rest).getLast (by simp) =
            (x :: y :: rest)[(x :: y :: rest).length - 1]'(by omega) := by
        simp [getLast_eq_getElem]
      simpa [hlast] using h1
    omega

private lemma fermatPsp_one_of_isCarmichael {n : ℕ} (hn : IsCarmichael n) :
    n.FermatPsp 1 :=
  hn 1 (by omega) (by simp)

private lemma composite_of_isCarmichael {n : ℕ} (hn : IsCarmichael n) :
    n.Composite := by
  obtain ⟨_, hnp, hn1⟩ := fermatPsp_one_of_isCarmichael hn
  exact ⟨hn1, hnp⟩

/-- Carmichael numbers are odd. An even `n > 1` is Fermat to the coprime base
`n - 1 ≡ -1`, which forces `n ∣ 2`. -/
private lemma odd_of_isCarmichael {n : ℕ} (hn : IsCarmichael n) : Odd n := by
  obtain ⟨_, hnp, hn1⟩ := fermatPsp_one_of_isCarmichael hn
  rw [← Nat.not_even_iff_odd]
  intro heven
  have hcop : n.Coprime (n - 1) := by
    rw [coprime_self_sub_right (by omega)]
    simp
  obtain ⟨hpr, _, _⟩ := hn (n - 1) (by omega) hcop
  have hge : 1 ≤ (n - 1) ^ (n - 1) :=
    Nat.one_le_pow (n - 1) (n - 1) (by omega)
  have : NeZero n := ⟨by omega⟩
  have hpow : ((n - 1 : ℕ) : ZMod n) ^ (n - 1) = 1 := by
    have h0 : ((↑((n - 1) ^ (n - 1) - 1) : ZMod n) = 0) :=
      (ZMod.natCast_eq_zero_iff _ _).2 hpr
    rw [Nat.cast_sub hge, Nat.cast_pow, Nat.cast_one] at h0
    exact sub_eq_zero.mp h0
  have hbase : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one, ZMod.natCast_self, zero_sub]
  have hodd : Odd (n - 1) := by
    rw [← Nat.not_even_iff_odd, even_sub (by omega : 1 ≤ n)]
    simp [heven]
  have hnegpow : (-1 : ZMod n) ^ (n - 1) = 1 := by
    rw [← hbase, hpow]
  have : (2 : ZMod n) = 0 := by
    have hneg1 : (-1 : ZMod n) = 1 := by
      rw [← hodd.neg_one_pow, hnegpow]
    have hsum := congrArg (fun x : ZMod n => x + 1) hneg1
    simpa [one_add_one_eq_two] using hsum.symm
  have hdvd : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).1 this
  rcases (dvd_prime prime_two).1 hdvd with h | h
  · omega
  · exact hnp (h ▸ prime_two)

private lemma three_le_card_divisors_of_composite {n : ℕ} (h : n.Composite) :
    3 ≤ n.divisors.card := by
  obtain ⟨hn1, hnp⟩ := h
  have hn2 : 2 ≤ n := Nat.succ_le_of_lt hn1
  obtain ⟨m, hmd, hm2, hmlt⟩ := exists_dvd_of_not_prime2 hn2 hnp
  have hn0 : n ≠ 0 := by omega
  have h1mem : 1 ∈ n.divisors := one_mem_divisors.mpr hn0
  have hmmem : m ∈ n.divisors := mem_divisors.mpr ⟨hmd, hn0⟩
  have hnmem : n ∈ n.divisors := mem_divisors_self n hn0
  have hsubset : ({1, m, n} : Finset ℕ) ⊆ n.divisors := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact h1mem
    · exact hmmem
    · exact hnmem
  have hcard : Finset.card ({1, m, n} : Finset ℕ) = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      exact hmlt.ne
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨by omega, hn1.ne⟩
  exact hcard ▸ Finset.card_le_card hsubset

private lemma sorted_divisors_zero {n : ℕ} (hn0 : n ≠ 0)
    (hpos : 0 < (n.divisors.sort (· ≤ ·)).length) :
    (n.divisors.sort (· ≤ ·))[0] = 1 := by
  have hne : n.divisors.Nonempty := ⟨1, one_mem_divisors.mpr hn0⟩
  rw [Finset.sorted_zero_eq_min']
  apply le_antisymm
  · exact Finset.min'_le _ 1 (one_mem_divisors.mpr hn0)
  · have : 0 < n.divisors.min' hne := pos_of_mem_divisors (Finset.min'_mem _ _)
    omega

private lemma sorted_divisors_last {n : ℕ} (hn0 : n ≠ 0)
    (hlast : (n.divisors.sort (· ≤ ·)).length - 1 < (n.divisors.sort (· ≤ ·)).length) :
    (n.divisors.sort (· ≤ ·))[(n.divisors.sort (· ≤ ·)).length - 1] = n := by
  rw [Finset.sorted_last_eq_max']
  apply le_antisymm
  · exact divisor_le (Finset.max'_mem _ _)
  · exact Finset.le_max' _ n (mem_divisors_self n hn0)

private lemma two_mul_le_of_proper_dvd {d n : ℕ} (hdvd : d ∣ n) (hlt : d < n) :
    2 * d ≤ n := by
  obtain ⟨k, hk⟩ := hdvd
  have hk2 : 2 ≤ k := by
    have hkpos : 0 < k := by
      have : 0 < n := Nat.zero_lt_of_lt hlt
      exact Nat.pos_of_mul_pos_left (by simpa [hk] using this)
    have : k ≠ 1 := by
      intro hk1
      exact hlt.ne (by simp [hk, hk1])
    omega
  calc
    2 * d ≤ k * d := Nat.mul_le_mul_right d hk2
    _ = n := by rw [mul_comm, hk]

/-- Ordered-divisor structural lemma: every odd composite has at least two
consecutive divisor pairs counted by `a`. -/
theorem a_ge_three_of_odd_composite {n : ℕ} (hcomp : n.Composite) (hodd : Odd n) :
    3 ≤ a n := by
  set d := n.divisors.sort (· ≤ ·)
  set pairs := d.zip d.tail
  have hn0 : n ≠ 0 := by
    obtain ⟨hn1, _⟩ := hcomp
    omega
  have hlen : 3 ≤ d.length := by
    have hcard := three_le_card_divisors_of_composite hcomp
    have hlen_eq : d.length = n.divisors.card := Finset.length_sort _
    omega
  have hsorted : d.SortedLT := Finset.sortedLT_sort n.divisors
  have hlenp : pairs.length = d.length - 1 := by
    change (d.zip d.tail).length = d.length - 1
    rw [length_zip, length_tail, min_eq_right]
    exact Nat.sub_le _ _
  have hplen : 2 ≤ pairs.length := by
    have : 2 ≤ d.length - 1 := Nat.le_sub_of_add_le (by exact hlen)
    simpa [hlenp] using this
  have hd0len : 0 < d.length := Nat.lt_of_lt_of_le (by decide : 0 < 3) hlen
  have hd1len : 1 < d.length := Nat.lt_of_lt_of_le (by decide : 1 < 3) hlen
  have hdlast : d.length - 1 < d.length := Nat.sub_lt hd0len Nat.zero_lt_one
  have hpred : pairs.length - 1 < d.length := by
    rw [hlenp, Nat.sub_sub]
    exact Nat.sub_lt hd0len (by decide : 0 < 2)
  have hpidx : pairs.length - 1 < pairs.length :=
    Nat.sub_lt (Nat.lt_of_lt_of_le (by decide : 0 < 2) hplen) Nat.zero_lt_one
  have hjump0 : Odd (pairs[0]'(Nat.lt_of_lt_of_le (by decide : 0 < 2) hplen)).snd ∧
      (pairs[0]'(Nat.lt_of_lt_of_le (by decide : 0 < 2) hplen)).snd ≥
        2 * (pairs[0]'(Nat.lt_of_lt_of_le (by decide : 0 < 2) hplen)).fst := by
    have hzip0 : 0 < (d.zip d.tail).length := by
      rw [length_zip, length_tail, min_eq_right (Nat.sub_le _ _)]
      exact Nat.sub_pos_of_lt hd1len
    have hz : (d.zip d.tail)[0]'hzip0 = (d[0]'hd0len, d[1]'hd1len) := by
      rw [getElem_zip, getElem_tail]
    have hd0 : d[0]'hd0len = 1 := sorted_divisors_zero hn0 hd0len
    have hlt01 : d[0]'hd0len < d[1]'hd1len := by
      rw [SortedLT.getElem_lt_getElem_iff hsorted]
      decide
    have hmem1 : d[1]'hd1len ∈ n.divisors := (Finset.mem_sort (· ≤ ·)).1 (getElem_mem _)
    have hodd1 : Odd (d[1]'hd1len) := Odd.of_dvd_nat hodd (dvd_of_mem_divisors hmem1)
    have hge : d[1]'hd1len ≥ 2 * (d[0]'hd0len) := by
      have : 2 ≤ d[1]'hd1len := Nat.succ_le_of_lt (by simpa [hd0] using hlt01)
      simpa [hd0] using this
    simpa [pairs, hz] using And.intro hodd1 hge
  have hjumplast : Odd (pairs[pairs.length - 1]'hpidx).snd ∧
      (pairs[pairs.length - 1]'hpidx).snd ≥ 2 * (pairs[pairs.length - 1]'hpidx).fst := by
    have hzi : pairs.length - 1 < (d.zip d.tail).length := by
      simpa [pairs] using hpidx
    have hidx : pairs.length - 1 + 1 = d.length - 1 := by
      rw [Nat.sub_add_cancel (le_trans (by decide : (1 : ℕ) ≤ 2) hplen), hlenp]
    have hz : (d.zip d.tail)[pairs.length - 1]'hzi =
        (d[pairs.length - 1]'hpred, d[d.length - 1]'hdlast) := by
      rw [getElem_zip, getElem_tail]
      exact Prod.ext rfl (getElem_eq_of_idx hidx)
    have hmax : d[d.length - 1]'hdlast = n :=
      sorted_divisors_last hn0 hdlast
    have hlt : d[pairs.length - 1]'hpred < n := by
      have : d[pairs.length - 1]'hpred < d[d.length - 1]'hdlast := by
        rw [SortedLT.getElem_lt_getElem_iff hsorted]
        rw [hlenp]
        exact Nat.sub_lt (Nat.sub_pos_of_lt hd1len) Nat.zero_lt_one
      simpa [hmax] using this
    have hmem : d[pairs.length - 1]'hpred ∈ n.divisors :=
      (Finset.mem_sort (· ≤ ·)).1 (getElem_mem _)
    have hge : n ≥ 2 * (d[pairs.length - 1]'hpred) :=
      two_mul_le_of_proper_dvd (dvd_of_mem_divisors hmem) hlt
    have heq : pairs[pairs.length - 1]'hpidx =
        (d[pairs.length - 1]'hpred, d[d.length - 1]'hdlast) := by
      have : pairs[pairs.length - 1]'hpidx = (d.zip d.tail)[pairs.length - 1]'hzi := by
        simp [pairs]
      rw [this, hz]
    constructor
    · rw [heq, hmax]
      exact hodd
    · rw [heq, hmax]
      exact hge
  have hcount :
      2 ≤ pairs.countP fun pair => Odd pair.snd ∧ pair.snd ≥ 2 * pair.fst := by
    refine countP_ge_two_of_getElem hplen ?_ ?_
    · exact decide_eq_true hjump0
    · exact decide_eq_true hjumplast
  have : 3 ≤ 1 + pairs.countP fun pair => Odd pair.snd ∧ pair.snd ≥ 2 * pair.fst := by
    omega
  simpa [a_eq] using this

/-- Exact frozen type of `OeisA237271.observation_carmichael`. -/
theorem observation_carmichael (k : ℕ) (hk : IsCarmichael k) : 3 ≤ a k :=
  a_ge_three_of_odd_composite (composite_of_isCarmichael hk) (odd_of_isCarmichael hk)

/-- Exact-type audit: this is the frozen declaration's type. -/
example : ∀ (k : ℕ), IsCarmichael k → 3 ≤ OeisA237271.a k :=
  observation_carmichael

#print axioms observation_carmichael
#print axioms a_ge_three_of_odd_composite
#check @observation_carmichael

end OeisA237271.Cursor01
