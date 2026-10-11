# A368628: source and contribution

Author: Wentao Li. Source and prior-work check: October 11, 2026.

## Exact statement

[OEIS A368628](https://oeis.org/A368628), introduced by Paul D. Hanna on
January 10, 2024, is the coefficient sequence of

\[
F(x)=1+\frac{x}{2}\bigl(F(x)^2-F(-x)^2\bigr)
       +\frac{x}{2}\bigl(F(x)^4+F(-x)^4\bigr).
\]

Its parity conjecture reads:

> Conjecture: a(n) is odd when n = (4^k - 1)/3 for k >= 0, and even elsewhere.

Indices start at zero. The [official table](https://oeis.org/A368628/b368628.txt)
starts `1, 1, 2, 14, 32, 345`; all six values are proved in the Lean development.
The power series is over the rationals, so each half is rational multiplication.
Substitution at `-x` is `PowerSeries.rescale (-1)`.

## Contribution and earlier Lean work

[trureturing PR #6718](https://github.com/the-omega-institute/trureturing/pull/6718),
merged September 9, 2026, provides a public Lean proof of parity for the
piecewise-convolution recurrence. Its
[implementation](https://github.com/the-omega-institute/trureturing/blob/423fa7a8cbab01df05a176d48560b70944b53096/D5/S1/Recurrence/PiecewiseConvolutionPowersOfFour.lean)
was inspected; that file does not establish the original rational generating-function
equation or uniqueness among its rational solutions.

This package completes the generating-function bridge: existence and uniqueness,
identification of every coefficient with the natural recurrence, and thus integrality,
nonnegativity and the exact parity statement for the OEIS-defined sequence.
It belongs in **New Formalizations** for that additional Lean coverage. The
supporting recurrence-parity theorem has earlier public Lean coverage. No code from
trureturing is copied or imported.

The dated search found no A368628 statement or matching issue/PR in Google's
Formal Conjectures repository at `cd6912171c5a1de06905795e5533ec7120f34ddc`.
This is a bounded search result, not a claim that no equivalent formalization exists.
Israel's other algebraic formulas and order-68 recurrence are outside this package.

## Formal statements and verification

The canonical file is
[`A368628.lean`](../../../LeanOeisProofs/NewFormalization/A368628.lean).
`OeisA368628.conjecture` proves the exact parity statement for the executable
sequence submitted to Formal Conjectures. `generating_function_iff` proves that
the original equation characterizes this sequence among all natural sequences.
`A368628Proof.exists_unique_oeis_series` and `solution_coefficients` establish
the rational-series existence, uniqueness, integrality and parity results.

The research proof was independently reviewed at source checkpoint
`d8e274c07f6c3e48058fbda954a13804f0eab007` under Lean 4.33.1. Publication uses
the repository's pinned Lean 4.34.0-rc2 and Mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`. The research namespace is renamed,
three deprecated tactic lemma names are updated, diagnostic prints are removed,
and an exact submitted-statement interface is added. The research mathematical
definitions and arguments are preserved.

Fresh compilation, axiom checks and Comparator results are in the
[current verification report](../../../verification/README.md). Comparator checks
the submitted parity theorem and its definitions, together with a separately
written obligation for the original generating function. The allowed axioms are
`propext`, `Classical.choice` and `Quot.sound`.

Copyright and new formalization: Wentao Li, Apache 2.0. Paul D. Hanna retains
the original sequence/conjecture attribution. AI assistance is recorded in
[`PROVENANCE.md`](../../../PROVENANCE.md).
