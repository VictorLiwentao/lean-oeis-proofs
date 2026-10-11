# A069004: source and contribution

Author: Wentao Li

## Exact claim

[OEIS A069004](https://oeis.org/A069004) counts positive integers `s < n` for which
`n^2 + s^2` is prime. T. D. Noe's stronger conjecture (February 26, 2007) includes
`pi(n) >= a(n)` for every `n > 1`, as well as a lower bound and three equalities.
The formalization proves the negation of that upper bound and, consequently,
the negation of the complete conjunction called Conjecture 2.

The [original DeepMind statement](https://github.com/google-deepmind/formal-conjectures/blob/4c40439d9be65b242e9196fb7848be02a9a4481d/FormalConjectures/OEIS/69004.lean)
is credited to The Formal Conjectures Authors. Its definition and both disproof
types are preserved. The positivity conjecture and remaining lower-bound variant
are separate targets.

## Original counterexample

GitHub user **j2d9w5xtjn-png** reported the counterexample `n = 512720` in
[DeepMind PR #5453](https://github.com/google-deepmind/formal-conjectures/pull/5453),
merged September 10, 2026. That contribution reports `a(512720) = 42666` and
`pi(512720) = 42493` from two computational methods and records the negative
statements with Lean placeholders.

Our certificate proves `a(512720) >= 42494` and `pi(512720) = 42493`, which
suffice to refute the upper bound. It does not certify the exact value 42666.
This is a formalization of that known counterexample.

## Reused formalization and attribution

The Pratt/Lucas checker, modular-arithmetic routines, certificate data and prime
count data are adapted from [Epoch Research's A069004 submission](https://github.com/epoch-research/LeanOpenProblems-results/blob/fd09021e79869476ef83cda231312f1a2a89c8d7/runs/oeis-full-50usd-ant-j0j0g4uzligm1k41/oeis_a069004_conjecture_2/Submission/Spec.lean).
Epoch identifies this as its Anthropic run
`oeis-full-50usd-ant-j0j0g4uzligm1k41`. The published verification score is `I`,
with exit code 137. The original attempt is credited as substantial reused work.
A check of all 19 published Epoch OEIS runs on October 11, 2026 found four
A069004 C2 attempts, all with rejected verification scores. The other records
report a second resource termination, a timeout, and a Comparator rejection.
That [last attempt](https://github.com/epoch-research/LeanOpenProblems-results/tree/fd09021e79869476ef83cda231312f1a2a89c8d7/runs/oeis-open-full-gemini31pro-7kxsykg62fp9ocz1/oeis_a069004_conjecture_2) compiled, but its proof depended on `Lean.ofReduceBool`, which
the benchmark verifier rejected. The certificate published here uses only
`propext`, `Classical.choice`, and `Quot.sound`.

Wentao Li's development bounds the modular-exponentiation fuel by 64, proves
that bound sufficient, divides verification into independently checked chunks,
and connects the certificates to both exact DeepMind disproof statements.
The publication adapts imports and deprecated lemma aliases to the pinned Lean
version. AI assistance was used in development and verification.

Research source: `17170d58351d9b01d09d7fb0b803e3f978e45ce1`,
`research/batches/b01/workers/cursor-03-r02/targets/A069004/`.

## Earlier Lean coverage

The October 11, 2026 search checked DeepMind PRs (including every changed file
in the open PRs), the 19 published Epoch OEIS runs, and public web searches for
A069004 Lean proofs. PR #5453 records the counterexample without a Lean proof;
the four Epoch attempts did not pass their recorded verification. No earlier
matching, successfully verified public Lean proof was located in these checks.
This is a dated search finding, not a claim that no such proof exists elsewhere.

## License provenance

Checked October 11, 2026. [LeanOpenProblems/LICENSE](https://github.com/epoch-research/LeanOpenProblems/blob/main/LICENSE)
licenses the benchmark harness under MIT and identifies its Formal Conjectures
inputs under Apache 2.0. The separate **LeanOpenProblems-results** repository
and the exact submission above have no explicit license notice in the locations
checked. The harness license is not asserted to cover those generated outputs.

Epoch-derived portions retain their original licensing status; this repository's
Apache 2.0 grant covers Wentao Li's contributions and original Formal Conjectures
material. No new MIT or Apache license is assigned to Epoch-derived code.

## Verification

Fresh publication compilation and Comparator checks are recorded in the
[current verification report](../../../verification/README.md). The main results
are `Cursor03R02.A069004.upper_bound_false` and
`Cursor03R02.A069004.conjecture2`. The entry point is
[`A069004.lean`](../../../LeanOeisProofs/NewFormalization/A069004.lean);
its neighboring `A069004/` directory contains distinct certificate chunks and
supporting proofs, each stored once.
