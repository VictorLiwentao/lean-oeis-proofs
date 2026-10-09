# A001818: the even-order permanent identity

Mathematics: Yue-Feng She, Zhi-Wei Sun, and Wei Xia, with related identities of
Guo–Li–Tao–Wei and Calogero–Perelomov. Lean development: Wentao Li, with AI assistance.

Let N = 2n, n >= 1, and let zeta be any primitive complex Nth root of unity.
Define M on indices 0,...,N-1 by M(i,i)=1 and

$$M(i,j)=\frac{1+\zeta^{i-j}}{1-\zeta^{i-j}}\quad(i\ne j).$$

The exponent difference is an integer. The proved identity is

$$\operatorname{per}(M)=\left(\prod_{k=0}^{n-1}(2k+1)\right)^2.$$

## Proof route implemented in Lean

Distinct indices give distinct powers of zeta, so every off-diagonal denominator
is nonzero. Let J be the all-ones matrix. The matrix M-J has zero diagonal,
so only derangements contribute to its permanent. Factoring its entries and
using the cancellation of the powers of zeta reduces its permanent to

$$2^N\sum_{\sigma\text{ a derangement}}
  \prod_i\frac{1}{1-\zeta^{\sigma(i)-i}}.$$

For distinct complex variables, the sum of reciprocal-difference weights over
cycles of a fixed length at least three vanishes. The Lean proof establishes
this by inserting a distinguished point into a cycle and summing a telescoping
identity. Grouping derangements by a distinguished long cycle cancels their
total contribution, both with and without permutation signs. The remaining
derangements are n disjoint transpositions, all of sign (-1)^n.

The signed sum is a determinant. Fourier diagonalization of the zero-diagonal
matrix with entries 2/(1-zeta^(i-j)) gives eigenvalues
N-1, N-3, ..., 1-N. Their product is (-1)^n times the square of the product of
the first n positive odd integers. Combining this with the common sign of
the surviving involutions evaluates per(M-J).

It remains to prove per(M)=per(M-J). For the Cayley kernel
(x_i+x_j)/(x_i-x_j), with diagonal 1, reversing odd cycles cancels their weights.
The even cycle sums yield a recurrence which removes two indices at a time:
choose the partner q of a fixed index p, multiply by the two-point weight,
and continue on the complement. A matching sum satisfies the same recurrence
and the same empty and two-point initial conditions. This proves the matching
formula and identifies both permanents with it at x_i=zeta^i. Transposition
does not change the permanent, accounting for the choice of kernel orientation.

Thus per(M)=per(M-J)=a(n). The n=1 boundary case is included. The Fourier step
evaluates a determinant; there is no assumption that the eigenvalue product
equals a permanent.

The file proves the cycle identities, matching recurrence, Fourier determinant,
and final wrapper. It does not import an admitted conjecture as a lemma.
The main wrapper `A001818C1.conjecture1_frozen` writes out the original matrix
and the quantifier over all primitive roots explicitly.

## Lean verification

Source: [the canonical A001818.lean](../../../LeanOeisProofs/NewFormalization/A001818.lean).
Main declarations: `A001818C1.conjecture1_frozen`.

Checked October 9, 2026, using Lean `4.34.0-rc2` and Mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`. The checked declarations use only
`propext`, `Classical.choice`, and `Quot.sound` (or subsets of these).
See the [current verification report](../../../verification/README.md) for
source hashes, compiler output, and the documented direct-compiler fallback.
