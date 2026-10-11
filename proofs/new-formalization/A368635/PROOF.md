# A368635: generating function and parity

Author: Wentao Li. Developed with AI assistance.

The intended theorem is for the sequence defined by the original OEIS functional equation, not merely for a recurrence. Work over rational formal power series. Put `F(-x) = evalNegHom F`.

For the right side of `F = 1 + 3 X F² - 2 X F(-x)²`, the constant coefficient is 1. At degree `n+1`, multiplication by `X` lowers coefficient extraction to degree `n`. Since `evalNegHom` is a ring homomorphism, `F(-x)²` is the rescaling of `F²`; its degree `n` coefficient is `(-1)^n` times that of `F²`. The Cauchy product coefficient is the finite sum over `k=0,...,n`. Thus the exact equation is equivalent to

\[
f_0=1,\qquad f_{n+1}=(3-2(-1)^n)\sum_{k=0}^n f_kf_{n-k}.
\]

The multiplier is 1 for even `n`, and 5 for odd `n`. This is precisely the historical recurrence's multiplier at index `n+1`. Casting its natural values into any commutative ring constructs a solution. Strong induction identifies every solution's coefficients with these values: both convolution indices are strictly below `n+1`. This proves uniqueness over ℚ and also proves integrality and nonnegativity of every rational solution. Neither property is assumed.

`a` is defined by choice from the proved unique natural coefficient sequence satisfying the original equation. `a_is_oeis` certifies its generating function, and `a_eq_recurrence` identifies it with the historical sequence. `is_oeis_iff_eq_series_of_a` identifies every rational solution with its generating function.

The retained parity proof reduces the recurrence modulo 2. Its odd convolution degrees vanish by pairing `k` with `n-k`; an even convolution degree leaves only the midpoint square, which equals its base value in `ZMod 2`. Therefore all positive even indices have even values and the parity at `2m+1` equals the parity at `m`. Starting at value 1 for index 0, strong induction gives odd exactly at `n+1=2^k`. Positivity of `2^k` proves this is equivalent to `n=2^k-1`. Transport along `a_eq_recurrence` proves the original OEIS parity clause.

The exact combined declaration is `A368635Proof.oeis_generating_function_and_parity`. It states existence and uniqueness for the literal original rational formal-series equation, and proves that every rational solution's coefficients are natural-number casts, odd exactly when `n=2^k-1`. Its only hypothesis in the universal clause is the original equation itself. `a_odd_iff_power_sub_one` is the same parity statement for the canonical equation-defined sequence; `a_even_iff_not_mersenne` gives the complementary even clause.

## Published Lean statement

`OeisA368635.conjecture` proves the exact submitted statement for every natural
index, including zero: `Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k - 1`.
The submitted recurrence is identified with the proved recurrence by
`OeisA368635.a_eq_proved`; the rational-series bridge establishes its interpretation
as the unique solution of the original OEIS equation.

The first six coefficients are `1, 1, 10, 21, 310, 762`, matching
[the official b-file](https://oeis.org/A368635/b368635.txt).

## Verification

Canonical file: [A368635.lean](../../../LeanOeisProofs/NewFormalization/A368635.lean).
Lean and Mathlib are pinned by the root `lean-toolchain` and `lake-manifest.json`.
The publication compiler is Lean 4.34.0-rc2. The complete file is checked with
warnings as errors. Comparator checks the exact proposed DeepMind theorem and
its definitions, plus an independent original generating-function obligation:
unique rational solution, natural coefficients, and the exact parity pattern.
The permitted axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
Commands, source hashes, actual results and kernel-replay output are in the
[current verification report](../../../verification/README.md).

```sh
lake env lean LeanOeisProofs/NewFormalization/A368635.lean
```

The equation is interpreted as an identity of formal power series. These results
do not assert analytic convergence or the other formulas in the OEIS entry.
