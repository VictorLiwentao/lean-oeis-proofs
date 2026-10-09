# A381355: divisibility by the nth prime

**Proof and Lean formalization: Wentao Li, with AI assistance.**

Write \(p_n\) for the nth prime, starting with \(p_1=2\). Let
\(F(x)=\sum_{m\geq0}f_mx^m\) be the [A381353](https://oeis.org/A381353) series, with \(f_0=f_1=1\) and

\[
[x^m]F(x)^{p_m}=0\qquad(m\geq2).
\]

Define \(A(x)=xF'(x)/F(x)=\sum_{n\geq0}a_nx^n\), as in [A381355](https://oeis.org/A381355). We prove \(p_n\mid a_n\) for every \(n>1\).

## A coefficient divisibility lemma

If \(G\in\mathbb Z[[x]]\), \(G(0)=1\), \(p\) is prime and \(0<k<p\), then

\[
p\mid[x^k]G(x)^p.
\]

Write \(G=1+xH\). In the binomial expansion of \((1+xH)^p\), all intermediate binomial coefficients are divisible by \(p\). The constant term contributes nothing in positive degree, and \((xH)^p\) contributes nothing in degrees below \(p\). This proves the lemma.

## Construction and uniqueness of F

The nth prime satisfies \(p_n>n\). Given \(f_0,\ldots,f_{n-1}\), put

\[
F_{<n}(x)=\sum_{j<n}f_jx^j,
\qquad
f_n=-\frac{[x^n]F_{<n}(x)^{p_n}}{p_n}.
\]

The lemma makes this division exact, so the recurrence constructs integral coefficients. Adding \(f_nx^n\) changes the degree-n coefficient of the prime power by exactly \(p_nf_n\), since the constant term is 1. Higher-degree terms cannot contribute. The resulting series therefore satisfies the defining equation at every \(n\geq2\).

The same calculation proves uniqueness: two such series agree in degrees 0 and 1; if they agree below \(n\), subtracting their degree-n equations gives \(p_n(f_n-g_n)=0\). Cancel \(p_n\neq0\) in \(\mathbb Z\) and use induction. The Lean theorem `F_unique` formalizes this statement for integral power series.

## The logarithmic derivative

Fix \(n>1\) and write \(p=p_n\). Since \(F(0)=1\), its inverse exists over \(\mathbb Z[[x]]\), and

\[
x(F^p)'=pAF^p.
\]

The degree-n coefficient on the left is \(n[x^n]F^p=0\). Cancelling the nonzero integer \(p\) gives \([x^n](AF^p)=0\). Since \([x^0]F^p=1\), this yields

\[
a_n=-\sum_{k=0}^{n-1}a_k[x^{n-k}]F^p.
\]

For each summand, \(0<n-k\leq n<p\). The coefficient divisibility lemma therefore makes every summand divisible by \(p\), proving \(p_n\mid a_n\).

## Formal verification

- Module: [`LeanOeisProofs.NewProofs.A381355`](../../../LeanOeisProofs/NewProofs/A381355.lean).
- Main theorem: `A381355.primeN_dvd_a`.
- Definition bridge: `A381355.coeff_F_pow_prime`; integral-series uniqueness: `A381355.F_unique`.
- Compiler: `leanprover/lean4:v4.34.0-rc2`; Mathlib commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`.
- Reported axioms for these declarations: `propext`, `Classical.choice`, `Quot.sound`.

See the [current verification report](../../../verification/README.md) and [source/provenance notes](SOURCE.md).
