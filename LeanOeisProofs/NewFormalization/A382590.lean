/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib


namespace OeisA382590

open Int

def abPair : ℕ → ℤ × ℤ
| 0 => (1, 1)
| 1 => (2, 1)
| n + 2 =>
  let (a_n_plus_1, b_n_plus_1) := abPair (n + 1)
  let (a_n, b_n) := abPair n
  (a_n_plus_1 * b_n + a_n * b_n_plus_1, a_n_plus_1 * b_n - a_n * b_n_plus_1)

/--
The sequence defined by the mutual recurrence relations:
$a(n) = a(n-1)b(n-2) + a(n-2)b(n-1)$ and $b(n) = a(n-1)b(n-2) - a(n-2)b(n-1)$
starting with $a(0) = b(0) = b(1) = 1$ and $a(1) = 2$.
The terms are in $\mathbb{Z}$ due to negative values.
-/
def a (n : ℕ) : ℤ := (abPair n).fst

open Nat

/--
The $k$-th smallest distinct prime factor of an integer $n$ (where $k \ge 1$).
This is defined as the $k$-th element (0-indexed $k-1$) of the increasing list of
distinct prime factors of `n.natAbs`.
Returns 1 if n has fewer than k distinct prime factors or if n is 0, 1, or -1,
following the informal convention.
-/
def kthPrimeFactor (k : ℕ) (n : ℤ) : ℕ :=
  if h₀ : k = 0 then 1 else
  let L := (primeFactorsList n.natAbs).dedup
  if h_len : k - 1 ≥ L.length then 1 else
  L[k - 1]

end OeisA382590


/-!
# Eventual period three for distinct prime factors of A382590

The divisibility argument is due to Terence Tao, following Will Jagy's observation:
https://mathoverflow.net/a/490348.

Lean development: Wentao Li, with Codex / GPT-6 Astra assistance.
The original definitions are included unchanged below the imports.
-/

namespace B02R2A382590

open OeisA382590
open scoped List

/-- Each term divides the term three places later. -/
theorem a_dvd_add_three (n : ℕ) : a n ∣ a (n + 3) := by
  cases n with
  | zero => simp [a, abPair]
  | succ m =>
    refine ⟨2 * (abPair (m + 1)).2 *
      ((abPair (m + 2)).1 * (abPair m).2 -
        (abPair m).1 * (abPair (m + 2)).2), ?_⟩
    change a ((m + 2) + 2) = _
    simp only [a, abPair]
    ring

/-- An element of a sublist occurs no earlier in the containing list. -/
theorem sublist_index {α : Type*} {xs ys : List α} (h : xs <+ ys)
    (i : ℕ) (hi : i < xs.length) :
    ∃ j, ∃ hj : j < ys.length, i ≤ j ∧ ys[j] = xs[i] := by
  induction h generalizing i with
  | slnil => simp at hi
  | cons b h ih =>
    obtain ⟨j, hj, hij, heq⟩ := ih i hi
    exact ⟨j + 1, by simpa using hj, by omega, by simpa using heq⟩
  | cons_cons b h ih =>
    cases i with
    | zero => exact ⟨0, by simp, le_refl _, rfl⟩
    | succ i =>
      obtain ⟨j, hj, hij, heq⟩ := ih i (by simpa using hi)
      exact ⟨j + 1, by simpa using hj, by omega, by simpa using heq⟩

/-- Inserting elements in a sorted list cannot increase an existing order statistic. -/
theorem getElem_le_of_sublist {xs ys : List ℕ} (h : xs <+ ys)
    (hs : ys.SortedLE) (i : ℕ) (hi : i < xs.length) :
    ys[i]'(lt_of_lt_of_le hi h.length_le) ≤ xs[i] := by
  obtain ⟨j, hj, hij, heq⟩ := sublist_index h i hi
  rw [← heq]
  exact hs.monotone_get hij

/-- Divisibility gives inclusion of the sorted lists of distinct prime factors. -/
theorem distinctFactors_sublist {x y : ℤ} (hxy : x ∣ y) (hy : y ≠ 0) :
    x.natAbs.primeFactorsList.dedup <+ y.natAbs.primeFactorsList.dedup := by
  apply List.sublist_of_subperm_of_sortedLE
  · apply List.subperm_of_subset (List.nodup_dedup _)
    intro p hp
    simp only [List.mem_dedup] at hp ⊢
    exact Nat.primeFactorsList_subset_of_dvd
      (Int.natAbs_dvd_natAbs.mpr hxy) (Int.natAbs_ne_zero.mpr hy) hp
  · exact ((Nat.primeFactorsList_sorted _).pairwise.sublist (List.dedup_sublist _)).sortedLE
  · exact ((Nat.primeFactorsList_sorted _).pairwise.sublist (List.dedup_sublist _)).sortedLE

/-- An existing distinct-prime order statistic cannot increase under divisibility. -/
theorem kthPrimeFactor_le_of_dvd {x y : ℤ} (hxy : x ∣ y) (hy : y ≠ 0)
    (k : ℕ) (hk : k ≠ 0) (hx : k - 1 < x.natAbs.primeFactorsList.dedup.length) :
    kthPrimeFactor k y ≤ kthPrimeFactor k x := by
  have hs := distinctFactors_sublist hxy hy
  have hlen := lt_of_lt_of_le hx hs.length_le
  simp only [kthPrimeFactor, hk, ↓reduceDIte, Nat.not_le.mpr hx,
    Nat.not_le.mpr hlen]
  exact getElem_le_of_sublist hs
    (((Nat.primeFactorsList_sorted _).pairwise.sublist (List.dedup_sublist _)).sortedLE) _ hx

/-- Divisibility propagates along a divisibility sequence. -/
theorem dvd_of_le (f : ℕ → ℤ) (hf : ∀ n, f n ∣ f (n + 1))
    {n m : ℕ} (hnm : n ≤ m) : f n ∣ f m := by
  induction m, hnm using Nat.le_induction with
  | base => exact dvd_refl _
  | succ m hm ih => exact dvd_trans ih (hf m)

/-- Distinct-prime order statistics stabilize in every integer divisibility sequence. -/
theorem kthPrimeFactor_eventually_constant (f : ℕ → ℤ)
    (hf : ∀ n, f n ∣ f (n + 1)) (k : ℕ) :
    ∃ N, ∀ n ≥ N, kthPrimeFactor k (f n) = kthPrimeFactor k (f N) := by
  classical
  by_cases hk : k = 0
  · exact ⟨0, by simp [kthPrimeFactor, hk]⟩
  by_cases hz : ∃ n, f n = 0
  · obtain ⟨N, hN⟩ := hz
    refine ⟨N, ?_⟩
    intro n hn
    have hd := dvd_of_le f hf hn
    rw [hN] at hd
    rw [zero_dvd_iff.mp hd, hN]
  have hnz : ∀ n, f n ≠ 0 := by simpa using hz
  by_cases he : ∃ n, k - 1 < (f n).natAbs.primeFactorsList.dedup.length
  · let P : ℕ → Prop := fun v => ∃ n,
      k - 1 < (f n).natAbs.primeFactorsList.dedup.length ∧ kthPrimeFactor k (f n) = v
    have hex : ∃ v, P v := by
      obtain ⟨n, hn⟩ := he
      exact ⟨_, n, hn, rfl⟩
    obtain ⟨N, hN, hv⟩ := Nat.find_spec hex
    refine ⟨N, ?_⟩
    intro n hn
    have hd := dvd_of_le f hf hn
    have hlen := lt_of_lt_of_le hN (distinctFactors_sublist hd (hnz n)).length_le
    apply Nat.le_antisymm
    · exact kthPrimeFactor_le_of_dvd hd (hnz n) k hk hN
    · rw [hv]
      exact Nat.find_min' hex ⟨n, hlen, rfl⟩
  · push Not at he
    refine ⟨0, ?_⟩
    intro n hn
    simp [kthPrimeFactor, hk, he]

/-- Every distinct-prime order statistic of A382590 has eventual period three. -/
theorem kthPrimeFactor_period_three (k : ℕ) :
    ∃ N, ∀ n ≥ N, kthPrimeFactor k (a (n + 3)) = kthPrimeFactor k (a n) := by
  classical
  have hr (r : Fin 3) : ∃ N, ∀ n ≥ N,
      kthPrimeFactor k (a (3 * n + r)) = kthPrimeFactor k (a (3 * N + r)) := by
    apply kthPrimeFactor_eventually_constant (fun n => a (3 * n + r))
    intro n
    convert a_dvd_add_three (3 * n + r) using 1
    congr 1
    omega
  choose N hN using hr
  let M := Finset.univ.sup N
  refine ⟨3 * M, ?_⟩
  intro n hn
  let r : Fin 3 := ⟨n % 3, Nat.mod_lt _ (by decide)⟩
  have hrval : (r : ℕ) = n % 3 := rfl
  have hMN : N r ≤ M := Finset.le_sup (f := N) (Finset.mem_univ r)
  have hquot : N r ≤ n / 3 := by omega
  have hfirst := hN r (n / 3) hquot
  have hnext := hN r (n / 3 + 1) (by omega)
  have heq : 3 * (n / 3) + r = n := by omega
  have heq' : 3 * (n / 3 + 1) + r = n + 3 := by omega
  rw [heq] at hfirst
  rw [heq'] at hnext
  exact hnext.trans hfirst.symm

/-- The exact frozen A382590 target, using distinct prime factors. -/
theorem kthPrimeFactor_periodic : ∀ k : ℕ, k ≥ 2 → ∃ N₀ p : ℕ, p > 0 ∧
    ∀ n : ℕ, n ≥ N₀ → kthPrimeFactor k (a (n + p)) = kthPrimeFactor k (a n) := by
  intro k _hk
  obtain ⟨N, hN⟩ := kthPrimeFactor_period_three k
  exact ⟨N, 3, by decide, hN⟩

#print axioms kthPrimeFactor_periodic

end B02R2A382590

#print axioms B02R2A382590.kthPrimeFactor_period_three
