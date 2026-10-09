# A237271: Carmichael numbers have at least two divisor jumps

Known mathematical argument recorded by GitHub author `j2d9w5xtjn-png` in
[Formal Conjectures PR 5447](https://github.com/google-deepmind/formal-conjectures/pull/5447).
Lean development and write-up: Wentao Li, with AI assistance.

For the increasing list of positive divisors of n, let a(n) be one plus the
number of adjacent pairs (d,e) for which e is odd and e >= 2d. We prove the
stronger statement a(n) >= 3 for every odd composite n, and deduce the
formalized Carmichael observation.

## Proof

An odd composite n has at least three distinct divisors. The first adjacent
pair is (1,p), where p is its smallest prime divisor. Here p is odd and p >= 3,
so this pair is counted. The last pair is (n/p,n), which is also counted.
These pairs occupy different positions even when n is a prime square.
Consequently the count is at least two and a(n) >= 3.

The imported-style Carmichael predicate is
`forall b >= 1, n.Coprime b -> n.FermatPsp b`; the local publication includes
that definition verbatim. The base b=1 gives compositeness. If n were even,
the coprime base n-1 would give (-1)^(n-1)=1 modulo n. Its odd exponent gives
n dividing 2, contradicting compositeness. Thus Carmichael numbers are odd
composites, and the stronger divisor-list result applies.

The Lean proof counts two distinct positions in the sorted divisor list.
It does not assume Korselt's criterion or an unproved conjecture.
An overlapping external Lean proof is credited in [SOURCE.md](SOURCE.md).

## Lean verification

Source: [the canonical A237271.lean](../../../LeanOeisProofs/NewFormalization/A237271.lean).
Main declarations: `OeisA237271.Cursor01.observation_carmichael`, `OeisA237271.Cursor01.a_ge_three_of_odd_composite`.

Checked October 9, 2026, using Lean `4.34.0-rc2` and Mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`. The checked declarations use only
`propext`, `Classical.choice`, and `Quot.sound` (or subsets of these).
See the [current verification report](../../../verification/README.md) for
source hashes, compiler output, and the documented direct-compiler fallback.
