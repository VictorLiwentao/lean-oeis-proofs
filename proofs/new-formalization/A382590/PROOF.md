# A382590: eventual period three

Known mathematics of Terence Tao and Will Jagy; Lean development by Wentao Li.

Write a(n) and b(n) for the two coordinates of the recurrence included in the module. Tao proved
three-step divisibility in his [MathOverflow answer](https://mathoverflow.net/a/490348),
following Will Jagy's observation. The Lean proof uses Jagy's factorization: for n ≥ 1,

a(n+3) = 2 a(n) b(n) [a(n+1)b(n-1) - a(n-1)b(n+1)].

Expanding the three recurrence steps proves the identity by ring algebra. At n = 0,
a(0) = 1 makes divisibility immediate. No sign restriction or nonzero assumption is
needed for this step.

We prove a general stabilization lemma for any integer sequence f with
f(n) dividing f(n+1). Fix a rank k.

1. At k = 0, the included definition always returns 1.
2. If f(N) = 0, divisibility implies f(n) = 0 for every n ≥ N. Hence the kth-factor
   function is constant on this tail.
3. Otherwise every f(n) is nonzero. Divisibility and the Mathlib prime-factor API
   show that the deduplicated factor list of f(n) is a sublist of that of f(m)
   whenever n ≤ m. Deduplication preserves sortedness. Inserting elements into
   a sorted list cannot increase any already existing order statistic.
4. If no term has a kth distinct factor, all values are 1. Otherwise consider the
   nonempty set of values attained at terms having at least k distinct factors.
   Its least natural value is attained at some N. For n ≥ N the kth factor still
   exists and is no greater than the value at N. Minimality gives the reverse
   inequality, so equality holds.

Apply this lemma separately to f_r(t) = a(3t+r), for r = 0, 1, 2. If their
stabilization indices are N_r, let M be their maximum. Every n ≥ 3M has quotient
n/3 ≥ N_(n mod 3). Both n and n+3 therefore have the same stabilized factor value.
This proves eventual period 3 for every natural k, and hence the exact target for
k ≥ 2.

The argument does not assume that the number of distinct factors grows without
bound, nor that the recurrence never vanishes. It covers 0, ±1, negative terms,
insufficient factors, and k = 0 explicitly. The period is not claimed minimal.

The original questioner's missing-factor sentinel was -1; the included Lean
definition uses 1. The stabilization proof works with either fixed sentinel.
The publication includes the definitions, but no admitted upstream proof terms.

Mathematical credit: Terence Tao and Will Jagy. Problem: Bryle Morga.
Lean development and write-up: Wentao Li, with Codex / GPT-6 Astra assistance.

## Lean verification

Source: [the canonical A382590.lean](../../../LeanOeisProofs/NewFormalization/A382590.lean).
Main declarations: `B02R2A382590.kthPrimeFactor_periodic`, `B02R2A382590.kthPrimeFactor_period_three`.

Checked October 9, 2026, using Lean `4.34.0-rc2` and Mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`. The checked declarations use only
`propext`, `Classical.choice`, and `Quot.sound` (or subsets of these).
See the [current verification report](../../../verification/README.md) for
source hashes, compiler output, and the documented direct-compiler fallback.
