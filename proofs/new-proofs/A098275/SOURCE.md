# OEIS A098275 — Source and Statement

Author: Wentao Li

- OEIS entry: A098275
- Canonical URL: <https://oeis.org/A098275>
- Accessed: 8 September 2026
- Conjecture attribution/date: F. Chapoton, 28 January 2026

OEIS name: “Coefficients in a simultaneous approximation to \(\mathrm{Li}(2,-1)\) and \(\mathrm{Li}(3,-1)\).”
Author of the sequence: Ralf Stephan, 3 September 2004. Offset \(0\).

## Sequence

The original OEIS formula is, for every integer \(n\ge 0\),

\[
a(n)=\sum_{i=0}^{n}\sum_{j=0}^{n}
\binom{n}{i}^{2}\binom{n}{j}^{2}\binom{n+i}{n}\binom{i+j}{i}.
\]

Here \(\binom{\,\cdot\,}{\,\cdot\,}\) is the ordinary binomial coefficient. Both indices run through \(\{0,1,\ldots,n\}\). This is the formula implemented by the published Mathematica and PARI programs on the OEIS page.

The published initial terms for \(n=0,\ldots,16\), accessed 8 September 2026, begin

\[
1,8,264,13040,778840,51955008,\ldots
\]

## Conjecture

OEIS comment (F. Chapoton, 28 January 2026):

> Conjecture: \(a(n)\) is divisible by \(n+1\).

The domain is every integer \(n\ge 0\), including \(n=0\) (where \(a(0)=1\) and \(n+1=1\)):

\[
\forall n\ge 0,\qquad (n+1)\mid a(n).
\]

## Formalization

- Lean definition: `a098275`
- Main theorem: `a098275_divisible`
- Lean source: [`LeanOeisProofs/NewProofs/A098275.lean`](../../../LeanOeisProofs/NewProofs/A098275.lean)
- Human-readable proof: [`PROOF.md`](PROOF.md)

The formal theorem is the displayed divisibility for the double sum above, with `Nat.choose` as the binomial coefficient.

## Status

Proved and formally verified in Lean 4 with Mathlib.

## Contribution and publication

**New proof by Wentao Li, formally verified in Lean.**

The proof is published in this repository and in the immutable
[`v1.0.0` release](https://github.com/VictorLiwentao/lean-oeis-proofs/blob/v1.0.0/LeanOeisProofs/A098275.lean).
The original problem appears on [OEIS A098275](https://oeis.org/A098275).

## Prior-work notes

The October 7, 2026 review found no independent earlier exact Lean proof in the
sources checked. This is a dated, bounded prior-work search, separate from the
completed proof verification. The original conjecture attribution is recorded above.
