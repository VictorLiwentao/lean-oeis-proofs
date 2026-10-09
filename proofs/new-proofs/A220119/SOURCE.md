# OEIS A220119 — Source and Statement

Author: Wentao Li

- OEIS entry: A220119
- Canonical URL: <https://oeis.org/A220119>
- Accessed: 9 September 2026
- Conjecture attribution/date: F. Chapoton, 23 April 2026

OEIS offset: \(0\).

## Sequence

For every integer \(n\ge 0\),

\[
a(n)=\sum_{j=0}^{n}\sum_{k=0}^{n}
\binom{n}{j}^{2}\binom{n}{k}^{2}
\binom{n+j}{n}\binom{n+k}{n}\binom{j+k}{n}.
\]

All bounds are inclusive. The binomial coefficient is the ordinary nonnegative-integer binomial coefficient, with value zero when the lower index exceeds the upper index.

The published initial terms for \(n=0,\ldots,14\), accessed 9 September 2026, begin

\[
1,12,804,88680,12386340,1985320512,\ldots
\]

## Conjecture

OEIS comment (F. Chapoton, 23 April 2026):

> Conjecture: For \(n>0\), \(a(n)\) is always divisible by \((n+1)\cdot(n+2)\).

The restriction \(n>0\) is essential: \(a(0)=1\), while \((0+1)(0+2)=2\nmid 1\). Thus the target is

\[
\forall n\in\mathbb{Z}_{>0},\qquad (n+1)(n+2)\mid a(n).
\]

## Formalization

- Lean definition: `a220119`
- Main theorem: `a220119_divisible`
- Lean source: [`LeanOeisProofs/NewProofs/A220119.lean`](../../../LeanOeisProofs/NewProofs/A220119.lean)
- Human-readable proof: [`PROOF.md`](PROOF.md)

The Lean definition is the original double sum. The file imports [`LeanOeisProofs/NewProofs/A098275.lean`](../../../LeanOeisProofs/NewProofs/A098275.lean) for a previously verified Catalan-factor identity used in the inner-sum analysis.

## Status

Proved and formally verified in Lean 4 with Mathlib.

## Contribution and publication

**New proof by Wentao Li, formally verified in Lean.**

The proof is published in this repository and in the immutable
[`v1.0.0` release](https://github.com/VictorLiwentao/lean-oeis-proofs/blob/v1.0.0/LeanOeisProofs/A220119.lean).
The original problem appears on [OEIS A220119](https://oeis.org/A220119).

## Prior-work notes

The October 7, 2026 review found no independent earlier exact Lean proof in the
sources checked. This is a dated, bounded prior-work search, separate from the
completed proof verification. The original conjecture attribution is recorded above.
