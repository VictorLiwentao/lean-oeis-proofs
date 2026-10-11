# A069004: a certified counterexample to the upper bound

Lean formalization: Wentao Li, building on Epoch Research's certificate attempt.
Original counterexample: j2d9w5xtjn-png, DeepMind PR #5453 (2026).

Let `a(n)` be the number of positive integers `s < n` such that `n^2 + s^2`
is prime. The conjectured upper bound is `a(n) <= pi(n)` for every `n > 1`.

At `N = 512720`, the Lean development establishes

```text
a(N) >= 42494 > 42493 = pi(N).
```

It follows that the upper bound is false. Since the upper bound is one conjunct
of Conjecture 2, that full conjunction is false as well.

## Certificate for the lower bound on a(N)

The certificate supplies 42494 distinct integers `s` with `0 < s < N`.
For each, a Pratt/Lucas certificate proves that `N^2 + s^2` is prime:
factor `p-1`, certify the prime factors, and check a Lucas witness using modular
exponentiation. Mathlib's Lucas primality theorem justifies the checker.
The modular-exponentiation routine is proved correct with fuel 64 for exponents
below `2^64`; every certified number satisfies the corresponding bound.

The data are split into 284 chunks. Lean's kernel checks each chunk's Boolean
certificate with `decide +kernel`. The gluing proof checks the strict ordering
across chunk boundaries, so no witness is counted twice. Summing these witnesses
in the original OEIS definition gives `42494 <= a(N)`.

## Certificate for pi(N)

A trial-division predicate is proved equivalent to `Nat.Prime`. The interval
`[0, N+1)` is partitioned into blocks of 1000 integers, with a final shorter block.
Lean verifies each count and combines the blocks by a proved telescoping identity.
The result is `Nat.primeCounting 512720 = 42493`.

The prime-count blocks and all prime certificates are proved in Lean; numerical
output alone is never used as an assumption. See [SOURCE.md](SOURCE.md) for the
original counterexample, Epoch attribution and exact scope.

## Lean entry points

- `Cursor03R02.A069004.a_512720_ge`: at least 42494 prime witnesses.
- `primeCounting_512720`: exactly 42493 primes at most 512720.
- `Cursor03R02.A069004.upper_bound_false`: negation of the upper bound.
- `Cursor03R02.A069004.conjecture2`: negation of the full conjunction.

The canonical entry point is
[`LeanOeisProofs/NewFormalization/A069004.lean`](../../../LeanOeisProofs/NewFormalization/A069004.lean).
Lean and Mathlib are pinned to `v4.34.0-rc2`; dependency commits are fixed in
`lake-manifest.json`. See the [verification report](../../../verification/README.md)
for compilation, exact-statement comparison, kernel replay and axiom records.

The main theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
