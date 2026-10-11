# A368634: generating function and parity

Author: Wentao Li. Developed with AI assistance.

## Original statement

Let F be the ordinary generating function determined by

F(x) = 1 + x(3F(x)^2 - F(-x)^2)/2.

Its coefficient a(n) is odd exactly when n = 2^k - 1, k ≥ 0, and even elsewhere. All indices start at zero.

## Coefficient equivalence

Work in rational formal power series. Rescaling by -1 is a ring homomorphism, so F(-x)^2 is the rescaling of F(x)^2. Hence its n-th coefficient is (-1)^n times the n-th coefficient of F(x)^2. The square coefficient is the convolution

c(n) = sum_{k=0}^n f(k) f(n-k).

Taking constant coefficients in the equation gives f(0)=1. Taking coefficient n+1 gives

f(n+1) = ((3-(-1)^n)/2)c(n).

The rational multiplier is 1 for even n, and 2 for odd n. This is exactly `(if Even (n+1) then 2 else 1) * c(n)`. Conversely, these coefficient identities at every index imply the formal series equation by extensionality. This is `satisfiesHanna_iff_coeff`.

## Existence, uniqueness and coefficient domain

The recovered natural recurrence a(0)=1 and a(n+1)=(if Even (n+1) then 2 else 1) sum a(k)a(n-k) is well founded: every argument in the convolution is smaller than n+1. Cast its coefficients into ℚ and form `recurrenceSeries`. The complete coefficient equivalence proves this series solves the original equation.

For any rational solution F, prove coeff_n(F) = a(n) by strong induction. The base follows from the forced constant term. The successor convolution uses only previous coefficients, so the induction hypothesis replaces each of its two factors by the cast of the recurrence coefficient. Thus every solution equals recurrenceSeries. This proves uniqueness without assuming integrality or nonnegativity; both follow because a(n) is natural.

`oeisSeries` is chosen using the proved unique existence theorem for the original equation. `oeisCoeff` takes its natural coefficient using the proved integrality. `oeisCoeff_eq_a` identifies it with the recovered recurrence. This is a proved bridge, not a replacement definition asserted to match the OEIS.

## Parity

The recovered proof is preserved mathematically. At a positive even index the recurrence factor is 2, so a(2m+2) is even. At an odd index,

a(2m+1) modulo 2 = sum_{k=0}^{2m} a(k)a(2m-k) modulo 2.

The involution k ↦ 2m-k has unique fixed point m. Every other pair cancels in characteristic two, leaving a(m)^2 = a(m) in ZMod 2. Therefore a(2m+1) is odd iff a(m) is odd. Strong induction gives oddness iff n+1 is a power of two; n=0 uses a(0)=1 and 2^0=1. Positive even n have n+1 odd and at least three, so cannot satisfy that power-of-two condition.

`oeisCoeff_odd_iff_mersenne` transfers this theorem through the proved bridge. `isMersenne_iff_eq_pow_sub_one` formally establishes the literal source wording n=2^k-1, using positivity of 2^k to handle natural subtraction. `oeis_parity` states both oddness at these indices and evenness elsewhere. `hanna_parity` gives the coefficient and oddness for arbitrary rational solutions. `original_equation_parity` states the same natural-coefficient result with both odd/even clauses for the source equation using literal substitution of -X.

## Published Lean statement

`OeisA368634.conjecture` proves the exact submitted statement for every natural
index, including zero: `Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k - 1`.
The submitted recurrence is identified with the proved recurrence by
`OeisA368634.a_eq_proved`; the rational-series bridge establishes its interpretation
as the unique solution of the original OEIS equation.

The first six coefficients are `1, 1, 4, 9, 52, 138`, matching
[the official b-file](https://oeis.org/A368634/b368634.txt).

## Verification

Canonical file: [A368634.lean](../../../LeanOeisProofs/NewProofs/A368634.lean).
Lean and Mathlib are pinned by the root `lean-toolchain` and `lake-manifest.json`.
The publication compiler is Lean 4.34.0-rc2. The complete file is checked with
warnings as errors. Comparator checks the exact proposed DeepMind theorem and
its definitions, plus an independent original generating-function obligation:
unique rational solution, natural coefficients, and the exact parity pattern.
The permitted axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
Commands, source hashes, actual results and kernel-replay output are in the
[current verification report](../../../verification/README.md).

```sh
lake env lean LeanOeisProofs/NewProofs/A368634.lean
```

The equation is interpreted as an identity of formal power series. These results
do not assert analytic convergence or the other formulas in the OEIS entry.
