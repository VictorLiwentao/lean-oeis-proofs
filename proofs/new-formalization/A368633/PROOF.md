# A368633, Conjecture 1: Catalan parity

Sequence and conjecture: Paul D. Hanna. Lean development: Wentao Li, with AI assistance.
The argument reduces to the classical parity of Catalan numbers.

The defining generating function is

$$A(x)=1+2xA(x)^2-xA(-x)^2.$$

Its constant coefficient is 1. Comparing the coefficient of x^(n+1) gives

$$a_{n+1}=(2-(-1)^n)\sum_{j=0}^n a_j a_{n-j}.$$

The multiplier is 1 for even n and 3 for odd n. This recurrence determines
the coefficients successively and defines a natural-number sequence.
The Lean theorem `mk_a_satisfiesHanna` verifies coefficient by coefficient that
its integral generating function satisfies the displayed equation, including
the alternating signs in A(-x).

Modulo 2 the multiplier is always 1. Hence this is the Catalan convolution
recurrence. Pair each term indexed by j with the term indexed by n-j.
If n is odd, all terms pair off, so a_(n+1) is even. If n=2m, only the middle
term survives and a_(2m+1) is congruent to a_m squared, hence to a_m, modulo 2.
Starting from a_0=1, repeated halving shows that the odd positions are exactly
n=2^k-1, k >= 0. Equivalently, the binary expansion of n consists entirely of
ones (including the empty expansion at zero).

The Lean theorem `a_odd_iff_mersenne` proves this equivalence for every natural
n. The formal generating-function result establishes existence for the
recurrence sequence; the successive coefficient equation explains its unique
identification with the OEIS series. No claim about Conjecture 2 is included.

## Lean verification

Source: [the canonical A368633.lean](../../../LeanOeisProofs/NewFormalization/A368633.lean).
Main declarations: `A368633.a_odd_iff_mersenne`, `A368633.mk_a_satisfiesHanna`.

Checked October 9, 2026, using Lean `4.34.0-rc2` and Mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`. The checked declarations use only
`propext`, `Classical.choice`, and `Quot.sound` (or subsets of these).
See the [current verification report](../../../verification/README.md) for
source hashes, compiler output, and the documented direct-compiler fallback.
