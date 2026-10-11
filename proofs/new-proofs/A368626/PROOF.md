# A368626: generating function and parity

Author: Wentao Li. Developed with AI assistance.

## Exact target

There is exactly one rational formal power series satisfying Hanna's original
square/cube equation. Its coefficients are natural numbers. Its degree-n
coefficient is odd if and only if n=2^k-1 for some natural k, and even otherwise.
No recurrence, existence, uniqueness, or integrality assumption may be substituted
for the defining equation in the final statement.

## Bridge argument

Rescaling a series by -1 multiplies its degree-n coefficient by (-1)^n.
Rescaling is a ring homomorphism, so this also computes the coefficient in every
power of the rescaled series. The square difference divided by two therefore
selects odd degrees, and the cube sum divided by two selects even degrees.
The outer x shifts by one. Exact coefficient extraction yields constant term 1,
then the square convolution at even positive sequence indices and the cube
convolution at odd sequence indices.

The historical strong-recursion construction has these coefficients. The
Cauchy-product formula, rewritten as a finite sum on 0..n, identifies the square
and cube coefficients with `conv2 a n` and `conv3 a n`. Extensionality proves
that `recurrenceSeries` satisfies the original equation.

For uniqueness, the degree-n coefficient of a power depends only on input
coefficients at degrees <=n. This is proved by induction on the power using the
Cauchy-product formula. Strong induction then identifies every coefficient of
any solution with the recurrence coefficient: the degree-n+1 output only uses
input coefficients at degrees <=n. This also proves nonnegative integrality.
The equation-defined choice `oeisSeries`, hence `oeisA`, equals the recurrence.

## Preserved parity argument

In characteristic two, the square convolution at odd degree vanishes: pair k
with n-k, with no fixed point. At degree 2m, the paired terms vanish and the
central term is a(m)^2=a(m). Hence every positive even-index sequence term is
even. In the cube convolution at degree 2m, only even square indices contribute.
All terms with remaining positive even sequence index vanish; the terminal term
has remaining index zero and a(0)=1. Thus a(2m+1) has the parity of a(m).
Strong induction gives oddness precisely when n+1 is a power of two.
The n=0 case corresponds to k=0. An arithmetic equivalence translates n+1=2^k
to n=2^k-1, and the natural-number odd/even complement gives the second clause.

## Published Lean statement

`OeisA368626.conjecture` proves the exact submitted statement for every natural
index, including zero: `Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k - 1`.
The submitted recurrence is identified with the proved recurrence by
`OeisA368626.a_eq_proved`; the rational-series bridge establishes its interpretation
as the unique solution of the original OEIS equation.

The first six coefficients are `1, 1, 2, 9, 22, 138`, matching
[the official b-file](https://oeis.org/A368626/b368626.txt).

## Verification

Canonical file: [A368626.lean](../../../LeanOeisProofs/NewProofs/A368626.lean).
Lean and Mathlib are pinned by the root `lean-toolchain` and `lake-manifest.json`.
The publication compiler is Lean 4.34.0-rc2. The complete file is checked with
warnings as errors. Comparator checks the exact proposed DeepMind theorem and
its definitions, plus an independent original generating-function obligation:
unique rational solution, natural coefficients, and the exact parity pattern.
The permitted axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
Commands, source hashes, actual results and kernel-replay output are in the
[current verification report](../../../verification/README.md).

```sh
lake env lean LeanOeisProofs/NewProofs/A368626.lean
```

The equation is interpreted as an identity of formal power series. These results
do not assert analytic convergence or the other formulas in the OEIS entry.
