# Generating-function bridge and parity for A368628

Author: Wentao Li. October 11, 2026.

The parity conjecture of Paul D. Hanna is

\[
 a(n)\text{ is odd}\quad\Longleftrightarrow\quad
 n=(4^k-1)/3\text{ for some }k\ge0.
\]

Here `a` denotes the coefficients of the original OEIS generating function.
The [source record](SOURCE.md) credits the earlier public recurrence-parity proof.

## Recovering the exact sequence

Let \(R(F)(x)=F(-x)\). In rational formal power series,
the coefficient of degree \(n\) in \(R(F)^p\) is \((-1)^n\) times that in \(F^p\).
Consequently the original equation

\[
F=1+\frac{x}{2}(F^2-R(F)^2)+\frac{x}{2}(F^4+R(F)^4)
\]

forces constant coefficient one. Its coefficient of degree \(n+1\) is the
degree-\(n\) coefficient of \(F^2\) when \(n\) is odd, and of \(F^4\) when
\(n\) is even. Equivalently, a positive even sequence index uses square
convolution and a positive odd index uses fourth-power convolution.

This gives a recurrence in natural numbers. Its rational generating function
satisfies the equation by the Cauchy product formula. Conversely, strong
induction identifies every coefficient of any rational solution with that
recurrence: the degree-\(n\) coefficient of a fixed power depends only on
coefficients through degree \(n\). Thus the equation has exactly one rational
solution, and all its coefficients are nonnegative integers. No integrality or
recurrence assumption is needed.

## Parity

Reduce the recurrence modulo two. Pairing off unequal-index terms shows that a
square has zero odd-degree coefficients; its degree-\(2j\) coefficient is the
square of the original degree-\(j\) coefficient. Applying this twice handles
fourth powers. Therefore positive even sequence indices have even values,
indices \(4j+3\) have even values, and the parity at \(4j+1\) equals that at \(j\).
The value at zero is one.

Strong induction now gives oddness exactly at
\(0,1,5,21,\ldots\), the indices satisfying \(3n+1=4^k\).
The equivalence with \(n=(4^k-1)/3\), including \(k=0\), is proved in Lean.
The generating-function bridge transfers this conclusion to the original
OEIS-defined sequence and to every rational solution of its equation.

## Lean verification

The full proof is in
[`LeanOeisProofs/NewFormalization/A368628.lean`](../../../LeanOeisProofs/NewFormalization/A368628.lean).
The submitted statement is `OeisA368628.conjecture`; its generating-function
bridge is `OeisA368628.generating_function_iff`.

Lean is pinned to 4.34.0-rc2, with Mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`. The main theorems use only
`propext`, `Classical.choice` and `Quot.sound`. The
[verification report](../../../verification/README.md) records fresh strict
compilation, exact-statement and definition comparison, and fresh Lean kernel replay.
