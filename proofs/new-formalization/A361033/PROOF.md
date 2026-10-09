# A361033: integrality and parity of a factorial ratio

Lean development and write-up: Wentao Li, with AI assistance.
This is classified conservatively as a formalization using classical valuation
methods; no new mathematical priority is claimed.

For n >= 0 define

$$a(n)=\frac{3(4n)!}{n!((n+1)!)^3}.$$

We prove that this is an integer and that it is odd exactly when n+1 is a power
of two (equivalently n=2^k-1 for some k >= 0).

## Integrality

Compare prime valuations of numerator and denominator. For each prime power
q >= 4, write n=qt+r, 0 <= r < q. Then

$$\left\lfloor\frac{4n}{q}\right\rfloor
 -\left\lfloor\frac n q\right\rfloor
 -3\left\lfloor\frac{n+1}{q}\right\rfloor
=\left\lfloor\frac{4r}{q}\right\rfloor
 -3\,\mathbf 1_{r=q-1}\ \geq 0.$$

For q=3 the same difference is at least -1, which is covered by the numerator's
factor 3. Higher powers of 3 are at least 4. Legendre's floor-sum formula
therefore proves nonnegative valuation at every odd prime.

At 2, let s_2(m) be the sum of the binary digits of m. Legendre's formula
v_2(m!)=m-s_2(m), together with s_2(4n)=s_2(n), gives the difference

$$v_2(3(4n)!)-v_2(n!((n+1)!)^3)=3(s_2(n+1)-1)\geq0.$$

Prime factorization now proves the exact denominator divisibility, so natural
number division in the Lean definition is an exact quotient.

## Parity

The positive quotient satisfies v_2(a(n))=3(s_2(n+1)-1). This is zero precisely
when s_2(n+1)=1, which holds precisely when n+1 has a single nonzero binary
digit. Hence n+1=2^k. The case n=0 is included: a(0)=3 is odd.

The Lean file proves the floor comparisons, denominator divisibility, digit-sum
characterization, and the final parity equivalence. The broader multinomial
Catalan literature is credited in [SOURCE.md](SOURCE.md); that citation is not
presented as an explicit prior statement of this exact parity corollary.

## Lean verification

Source: [the canonical A361033.lean](../../../LeanOeisProofs/NewFormalization/A361033.lean).
Main declarations: `A361033.a_odd_iff`, `A361033.denom_dvd_num`, `A361033.v2_a`.

Checked October 9, 2026, using Lean `4.34.0-rc2` and Mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`. The checked declarations use only
`propext`, `Classical.choice`, and `Quot.sound` (or subsets of these).
See the [current verification report](../../../verification/README.md) for
source hashes, compiler output, and the documented direct-compiler fallback.
