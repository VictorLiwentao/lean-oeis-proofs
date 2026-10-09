# A397588: parity, divisibility by 3, and the defining series

Sequence and generating function: Paul D. Hanna. Recurrence: Seiichi Manyama,
as recorded in OEIS. Lean development: Wentao Li, with AI assistance.
These are formalizations of known mathematical properties.

Hanna's equation over natural-number formal power series is

$$A(x)=x+\bigl(xA(x)^2\bigr)'.$$

Writing its constant term as c gives c=c^2. The possibility c=1 contradicts
the next coefficient equation over natural numbers. Thus a_0=0, and the
coefficient of x gives a_1=1. For n>1 the equation gives

$$a_n=(n+1)\sum_{k=1}^{n-1}a_k a_{n-k}.$$

Conversely this recurrence defines a series satisfying Hanna's equation.
Strong induction proves uniqueness over natural-number series. The Lean file
also proves equivalence with the product-rule expansion and the weighted
convolution obtained by differentiating the second factor.

## Parity

At odd n>1 the multiplier n+1 is even. At n=2m, pair k with 2m-k in the
convolution. Modulo 2 all pairs cancel, leaving only a_m^2, which has the same
parity as a_m. Thus a_(2m) is odd iff a_m is odd. Iterating, with a_1=1,
proves that the odd terms occur exactly at n=2^t for t >= 0.

## Divisibility by 3

The recurrence gives a_2=3. For n>2, in each product a_k a_(n-k), at least
one index is greater than 1 and both indices are less than n. Strong induction
therefore makes every product divisible by 3, and hence makes a_n divisible
by 3. This proves the property for all n>1.

The main theorems apply these conclusions to every natural-number formal
power series satisfying Hanna's equation, through the proved coefficient
uniqueness theorem. This extends the scope of the previously public
recurrence-parity formalization credited in [SOURCE.md](SOURCE.md).

## Lean verification

Source: [the canonical A397588.lean](../../../LeanOeisProofs/NewFormalization/A397588.lean).
Main declarations: `A397588.hanna_odd_iff_pow_two`, `A397588.hanna_three_dvd`, `A397588.mk_a_satisfiesHanna`, `A397588.hanna_coeff_eq_a`.

Checked October 9, 2026, using Lean `4.34.0-rc2` and Mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`. The checked declarations use only
`propext`, `Classical.choice`, and `Quot.sound` (or subsets of these).
See the [current verification report](../../../verification/README.md) for
source hashes, compiler output, and the documented direct-compiler fallback.
