# A003162: source and contribution

Author: Wentao Li

## Exact statement

[OEIS A003162](https://oeis.org/A003162), Peter Bala, March 26, 2023.
Let `b(n) = a(2*n-1)`. For every positive integer `n` and `k` and every prime
`p >= 5`, `b(n*p^k) == b(n*p^(k-1)) (mod p^(3*k))`.
There is no coprimality assumption on `n`.

The original Lean statement is [DeepMind's A003162 file](https://github.com/google-deepmind/formal-conjectures/blob/1646ca16afd6cc7a693d3bdc9f066c4d3cc01a89/FormalConjectures/OEIS/3162.lean).
The original formalization is credited to The Formal Conjectures Authors.
The published OEIS attribution is Peter Bala; the upstream docstring's earlier
Sun attribution is corrected in the accompanying contribution.

The sequence is the rational quotient of that cubic sum by `choose(n,floor(n/2))`. All-index integrality is proved separately; the conjecture uses the reduced numerator exactly as in DeepMind's statement.

## Mathematical sources

- M. J. Coster, [Supercongruences](https://ir.cwi.nl/pub/5804/5804D.pdf), Theorem 4.
- P. J. Miana, H. Ohtsuka and N. Romero, [Sums of powers of Catalan triangle numbers](https://arxiv.org/abs/1602.04347), Theorem 4.1 and Corollary 4.2.
- T. Amdeberhan and S. B. Ekhad, [solution to Monthly Problem 11844](https://www.math.tulane.edu/~tamdeberhan/solutions/11844.PDF), telescoping certificates.
- R. Osburn, B. Sahu and A. Straub, [Supercongruences for sporadic sequences](https://archive.mpim-bonn.mpg.de/id/eprint/4134/1/preprint_2013_62.pdf), Lemmas 2.1 and 2.2.

## Contribution and reused Lean code

**New Formalization:** a complete proof of the exact target using known mathematics.
The development closes the arithmetic premises of the earlier conditional reduction.
The search on October 10, 2026 found no matching accepted public Lean proof or
DeepMind proof PR. Epoch's four published attempts per target all have rejected
verification scores. This dated search records what was located.

The shared `B02R2EpochKazan` namespace is adapted from the `kazan` helper and its
dependencies in [Epoch Research's A141057 solution](https://github.com/epoch-research/LeanOpenProblems-results/blob/fd09021e79869476ef83cda231312f1a2a89c8d7/runs/oeis-full-50usd-ant-j0j0g4uzligm1k41/oeis_a141057_supercongruence_conjecture/Submission/Spec.lean).
Epoch identifies the run as Claude Opus 4.8. Its A141057 proof passed SafeVerify.
`B02R2RefinedKazan` adapts that argument to retain separate valuations.
These shared sections occur once, in `A003161.lean`; `A003162.lean` imports them.
All other target development, compatibility edits, and integration are by Wentao Li
with AI assistance. The source helper and its refinement are credited as reused
formalization.

The Epoch results source has no explicit license notice. Its original licensing
status is retained; this repository's Apache 2.0 grant applies to the original
Formal Conjectures material and Wentao Li's contributions, without asserting a
new license for Epoch-derived portions.

## Verification

Original research proof: `f866d0158ceb5780e3c214eb09937d722b35fcc4`.
Independent exact-type/compilation/axiom audit: September 21, 2026.
Publication rebuild and Comparator comparison: October 10, 2026.
Comparator checks the original DeepMind theorem types and their underlying definitions,
the permitted axiom set, and kernel replay. See the [current verification report](../../../verification/README.md).
