# A368629: generating function and parity

Author: Wentao Li. Developed with AI assistance.

## Exact result

There exists exactly one $F\in\mathbb Q[[x]]$ satisfying

\[
F(x)=1+x(F(x)^2+F(-x)^2)/2+x(F(x)^4-F(-x)^4)/2.
\]

For every $n\in\mathbb N$, its coefficient is the natural number `a n` from the historical recurrence. Its equation-defined natural coefficient `oeisA n` is odd if and only if $n=2^k-1$ for some $k\in\mathbb N$, and is even elsewhere. Integrality, nonnegativity and uniqueness are conclusions of the proof.

## Coefficient extraction

Write $S_n=[x^n]F^2$ and $T_n=[x^n]F^4$. The rescaling ring homomorphism gives

\[
[x^n]F(-x)^r=(-1)^n[x^n]F(x)^r.
\]

The coefficient of the equation's right side at degree zero is one. At degree $n+1$ it is

\[
\frac{S_n+(-1)^nS_n}{2}+\frac{T_n-(-1)^nT_n}{2}.
\]

For even $n$ this equals $S_n$; for odd $n$ it equals $T_n$. Therefore a positive odd coefficient index uses the square convolution of the earlier coefficients, while a positive even index uses the fourth-power convolution.

`coeff_sq` is the Cauchy-product identity

\[
[x^n]F^2=\sum_{j=0}^n([x^j]F)([x^{n-j}]F).
\]

`fourth_as_sq_sq` identifies $F^4=(F^2)^2$, so `conv4 = conv2 ∘ conv2` has precisely the required fourth-power coefficients. Each summand uses coefficients of degree at most $n$.

## Existence and identification

The historical `a` is constructed by strong recursion with `a 0 = 1`. The finite convolutions at index $n-1$ use only values at smaller indices. `a_of_pos` proves that its zero extension in the recursive definition does not change these convolutions.

`generatingSeries` has coefficient `(a n : ℚ)`. The coefficient extraction lemmas and `a_succ_even` / `a_succ_odd` prove `generatingSeries_isOEISSeries` by extensionality.

For an arbitrary rational solution $F$, strong induction proves $[x^n]F=a(n)$. The base case is the forced constant coefficient. At a successor, equality of all earlier coefficients gives equality of square coefficients by `coeff_sq_congr`, and equality of fourth-power coefficients by applying that lemma twice. The common original right-side formula then gives equality of the next coefficients.

Thus `isOEISSeries_iff_eq` and its literal version `original_equation_iff_eq` identify the entire solution set as the singleton `{generatingSeries}`. `existsUnique_oeisSeries` supplies existence and uniqueness. `existsUnique_nat_coeff` supplies a unique natural representative for each rational coefficient. The choices defining `oeisSeries` and `oeisA` use only these properties, and `oeisA_eq_a` proves the all-index bridge.

## Parity transfer

In $\mathbb F_2$, the involution $j\mapsto n-j$ cancels the square convolution at odd degree. At degree $2m$ all terms cancel except $j=m$, so the coefficient is $a(m)^2=a(m)$ modulo two.

A positive even index of `a` is a square convolution of `conv2 a` at an odd degree, and is consequently even. An odd index $2m+1$ has the same parity as `a m`. Strong induction shows `Odd (a n) ↔ ∃ k, n+1=2^k`. The zero case is odd and corresponds to $k=0$; a positive even index cannot be Mersenne. This is the historical mathematical argument.

`oeisA_eq_a` transfers the result to the coefficient sequence defined by the original equation. `isMersenne_iff_sub` proves that $n+1=2^k$ is equivalent to $n=2^k-1$ without a natural-subtraction boundary error. `oeisA_odd_iff` and `oeisA_even_iff` are the exact OEIS parity conclusions. `oeis_coeff_parity` also states the result directly for every rational series satisfying the equation.

## Published Lean statement

`OeisA368629.conjecture` proves the exact submitted statement for every natural
index, including zero: `Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k - 1`.
The submitted recurrence is identified with the proved recurrence by
`OeisA368629.a_eq_proved`; the rational-series bridge establishes its interpretation
as the unique solution of the original OEIS equation.

The first six coefficients are `1, 1, 4, 9, 88, 210`, matching
[the official b-file](https://oeis.org/A368629/b368629.txt).

## Verification

Canonical file: [A368629.lean](../../../LeanOeisProofs/NewProofs/A368629.lean).
Lean and Mathlib are pinned by the root `lean-toolchain` and `lake-manifest.json`.
The publication compiler is Lean 4.34.0-rc2. The complete file is checked with
warnings as errors. Comparator checks the exact proposed DeepMind theorem and
its definitions, plus an independent original generating-function obligation:
unique rational solution, natural coefficients, and the exact parity pattern.
The permitted axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
Commands, source hashes, actual results and kernel-replay output are in the
[current verification report](../../../verification/README.md).

```sh
lake env lean LeanOeisProofs/NewProofs/A368629.lean
```

The equation is interpreted as an identity of formal power series. These results
do not assert analytic convergence or the other formulas in the OEIS entry.
