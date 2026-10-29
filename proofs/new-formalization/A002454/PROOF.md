# OEIS A002454: permanent of an odd-root principal matrix

**Wentao Li** formalized the identity of **Yue-Feng She, Zhi-Wei Sun and Wei Xia**,
using the determinant argument of **Xuejun Guo, Xin Li, Zhengyu Tao and Tao Wei**.
See [sources and earlier work](SOURCE.md). OpenAI Codex assisted development and review.

Put `K = 2n+1` and let `ζ` be any primitive `K`-th root of unity.
Set `x_j = ζ^j` for `0 ≤ j < 2n`. These points are distinct and nonzero.
Let `C` be the matrix in the OEIS statement.

The A001818 development expresses `per C` as `4^n (∏ x_j)` times a
perfect-matching sum. For the zero-diagonal matrix `B` with off-diagonal
entries `1/(x_i-x_j)`, determinant expansion gives the same matching sum
multiplied by `(-1)^n`. Fixed points contribute zero. Contributions with
cycles of length at least three cancel by the reciprocal-difference identity;
the remaining permutations are products of `n` transpositions.

Now take the `K × K` zero-diagonal matrix with entries
`2/(1-ζ^(i-j))`, and denote its leading `2n × 2n` minor by `M`.
Column scaling relates `M` to `B`, giving

`per C = (-1)^n det M`.

The Fourier basis diagonalizes the larger matrix with eigenvalues
`2n - 2r`, for `0 ≤ r ≤ 2n`. The Fourier determinant is nonzero.
Adjugate multiplicativity and invariance of trace under this change of basis
show that the trace of the adjugate is the product of the nonzero eigenvalues.
Cyclic shifts preserve the matrix, so every diagonal cofactor has the same value.
There are `K` such cofactors; the last one is `det M`.

The nonzero eigenvalues are `2, 4, …, 2n` and `-2, -4, …, -2n`. Therefore

`det M = (-1)^n 4^n (n!)² / (2n+1)`.

Multiplying by `(-1)^n` proves the required permanent identity.
For `n = 0`, both sides equal `1`; this endpoint is checked separately.

The canonical file is
[`LeanOeisProofs/NewFormalization/A002454.lean`](../../../LeanOeisProofs/NewFormalization/A002454.lean),
theorem `A002454.conjecture_frozen`. The publication uses pinned Lean
`4.34.0-rc2` and Mathlib; the DeepMind compatibility check uses Lean `4.33.1`.
The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.
Exact checks and source hashes appear in the [verification record](../../../verification/README.md).
