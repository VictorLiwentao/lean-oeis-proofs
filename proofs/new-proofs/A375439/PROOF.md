# A375439: parity of the coefficients

**Proof and Lean formalization: Wentao Li, with AI assistance.**

Let \(A(x)=\sum_{n\geq 1}a_nx^n\) be the series specified in [OEIS A375439](https://oeis.org/A375439):

\[
A(x)=x+x^2+\frac{2A(x)^3+A(x^3)}{3}.
\]

We prove that \(a_n\) is odd exactly when \(n=3^k\) or \(n=2\cdot3^k\), for some integer \(k\geq0\).

## The integral coefficient recurrence

Set \(a_0=0\) and \(a_1=a_2=1\). For \(n\geq3\), extract the coefficient of \(x^n\) and divide the numerator by 3. This is a genuine integral recurrence. For any integral series \(B\), reduction modulo 3 gives

\[
B(x)^3\equiv B(x^3)\pmod 3,
\qquad
2B(x)^3+B(x^3)\equiv0\pmod 3.
\]

Thus the division is exact at every step. The formal proof establishes this coefficientwise using truncated polynomials over \(\mathbb F_3\).

There is no circularity: with constant term zero, every nonzero contribution to \([x^n]A^3\) uses indices strictly below \(n\). A contribution from \(A(x^3)\), for \(n>0\), uses \(a_{n/3}\), also at a smaller index. The recurrence therefore determines the series uniquely. The Lean lemma `three_mul_a` proves the full cleared coefficient equation for every \(n\), including the initial terms; the division is justified by `three_dvd_rhs`.

## Reduction modulo 2

Reducing the cleared equation modulo 2 gives

\[
A(x)\equiv x+x^2+A(x^3)\pmod2.
\]

Consequently, for \(n\geq3\),

\[
a_n\equiv
\begin{cases}
a_{n/3} & 3\mid n,\\
0 & 3\nmid n
\end{cases}
\pmod2.
\]

Repeated division by 3 terminates. The only terminal indices with odd coefficients are 1 and 2. Hence the odd coefficients occur exactly at the indices \(3^k\) and \(2\cdot3^k\). Lean proves both directions by strong induction on \(n\).

## Formal verification

- Module: [`LeanOeisProofs.NewProofs.A375439`](../../../LeanOeisProofs/NewProofs/A375439.lean).
- Main theorem: `A375439.a_odd_iff_A038754` (all natural indices, with the auxiliary value \(a_0=0\)).
- Definition bridge: `A375439.three_mul_a`; integrality: `A375439.three_dvd_rhs`.
- Compiler: `leanprover/lean4:v4.34.0-rc2`; Mathlib commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`.
- Reported axioms for these three declarations: `propext`, `Classical.choice`, `Quot.sound`.

See the [current verification report](../../../verification/README.md) and [source/provenance notes](SOURCE.md).
