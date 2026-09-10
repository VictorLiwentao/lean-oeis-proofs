# OEIS A280246 — Source and Statement

Author: Wentao Li

- OEIS entry: A280246
- Canonical URL: <https://oeis.org/A280246>
- Accessed: 8 September 2026
- Conjecture attribution/date: Jaroslav Krizek, 30 December 2016

Related definitional source for \(\psi\): [A023896](https://oeis.org/A023896).

## Sequence

Let \(\psi(m)\) be the sum of totatives of \(m\) (OEIS A023896): for each integer \(m\ge 1\),

\[
\psi(m)=\sum_{\substack{1\le k\le m\\ \gcd(k,m)=1}}k.
\]

In particular \(\psi(1)=1\). For \(n\ge 1\),

\[
a(n)=\prod_{d\mid n}\psi(d),
\]

the product of \(\psi(d)\) over all positive divisors of \(n\). This is OEIS A280246 (offset 1).

The published initial terms for \(n=1,\ldots,43\), accessed 8 September 2026, begin

\[
1,1,3,4,10,18,21,64,81,200,55,1728,\ldots
\]

The OEIS example \(n=6\) records the totative sets of the divisors of \(6\) as \(\{1\}\), \(\{1\}\), \(\{1,2\}\), \(\{1,5\}\), and \(a(6)=1\cdot 1\cdot(1+2)\cdot(1+5)=18\).

## Conjecture

OEIS comment (still labelled a conjecture on the access date):

> Conjecture: \(a(n)\) is odd iff the sum of totatives of \(n\) (A023896) is odd.

The domain is every integer \(n\ge 1\):

\[
a(n)\text{ is odd}\quad\Longleftrightarrow\quad\psi(n)\text{ is odd}.
\]

## Formalization

- Lean definition: `psi`, `a`
- Main theorem: `odd_a_iff_odd_psi`
- Lean source: [`LeanOeisProofs/A280246.lean`](../../LeanOeisProofs/A280246.lean)
- Human-readable proof: [`PROOF.md`](PROOF.md)

The formalization uses the sum-of-totatives definition of \(\psi\), not a closed form as a primitive.

## Status

Proved and formally verified in Lean 4 with Mathlib.
