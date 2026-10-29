# OEIS A368630: EGF congruences modulo two and three

**Wentao Li**, with OpenAI Codex assistance.
The sequence and conjectures are due to **Paul D. Hanna**; see
[SOURCE.md](SOURCE.md).

Let \(A(0)=1\) and
\(A(x/A(x)^2)=\exp(xA(x))\). We prove that every EGF coefficient is one
modulo three, every even-indexed coefficient is odd, and every odd-indexed
coefficient after index one is even.

## Integral construction and the original equation

The original equation is equivalent to the auxiliary system

\[
B(x)=A(xB(x)^2),\qquad A(x)=\exp(xB(x)^3),\qquad B(0)=1.
\]

To obtain it, take the compositional inverse \(T\) of \(x/A(x)^2\) and set
\(B=A(T)\). The inverse identity gives \(T=xB^2\), and substituting \(T\)
in the original equation gives \(A=\exp(xB^3)\). Conversely, \(xB^2\)
has linear coefficient one, and cancellation of this substitution recovers the
original equation. These arguments take place in rational formal power series.

For integrality, use EGF coefficient sequences with Hurwitz multiplication:

\[
(u*v)_n=\sum_{k=0}^{n}\binom nk u_kv_{n-k}.
\]

Differentiation shifts a sequence. Products, powers, substitution by \(xD(x)\),
and the exponential \(\exp(xC(x))\) all have integral coefficient formulas.
In particular, the exponential is constructed from constant coefficient one
and the differential equation \(E'=(xC)'E\), with no division.

Substitute \(A=\exp(xB^3)\) into the equation for \(B\). Its output
coefficient at index \(n\) depends only on the input coefficients below
\(n\). Coefficient recursion therefore gives a unique integral fixed point.
The same recursion over the rationals proves uniqueness there. The formal
equivalence above identifies the constructed integral EGF with every normalized
rational solution of Hanna's original equation.

## Reduction modulo three

In the Hurwitz algebra over \(\mathbb F_3\), every positive coefficient of
a cube vanishes. Indeed, the product rule gives
\(D(B^3)=3B^2DB=0\), and differentiation is a shift of EGF coefficients.
Since \(B(0)=1\), this means \(B^3=1\).

Differentiate the integral exponential identity and reduce modulo three:

\[
DA=A\,D(xB^3)=A.
\]

Starting with \(a(0)=1\), successive coefficients are all one modulo three.

## Reduction modulo two

Over \(\mathbb F_2\), the same product-rule argument gives \(B^2=1\).
The auxiliary substitution becomes the identity, so \(B=A\), and the
exponential identity reduces to \(A=\exp(xA)\), interpreted through its
integral differential recurrence.

Here \(A^2=1\) and \(x^2=0\) in the Hurwitz algebra. Differentiating gives

\[
DA=A(A+xDA)=1+xA\,DA.
\]

Because \((xA)^2=0\), multiplication by \(1+xA\) yields
\(DA=1+xA\). Thus \(a(1)=1\), and for every \(n\ge0\),

\[
a(n+2)=(n+1)a(n)\quad\text{in }\mathbb F_2.
\]

The even subsequence starts at one and is multiplied only by odd factors.
The odd subsequence reaches zero at index three and remains zero. These are
the exact two parity clauses, with index one excluded from the evenness claim.

## Lean verification

The canonical file is
[LeanOeisProofs/NewProofs/A368630.lean](../../../LeanOeisProofs/NewProofs/A368630.lean).
Its public results are `OeisA368630.exists_unique_sequence`,
`OeisA368630.conjecture_mod_three`, `OeisA368630.conjecture_even` and
`OeisA368630.conjecture_odd`. The source-level theorem
`OeisA368630.a368630_congruences` includes normalized rational uniqueness and
integral identification. The five initial-value certificates agree with OEIS.

Publication uses Lean `4.34.0-rc2` and Mathlib commit
`85e3a25e006c35636f0e53b0e9296caca2685bc0`; the independent DeepMind check uses
Lean `4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.
The same source compiles under both pins. The reported axioms are
`propext`, `Classical.choice` and `Quot.sound`. Exact commands, source hashes,
Comparator results and kernel replay are in the
[verification record](../../../verification/README.md).
