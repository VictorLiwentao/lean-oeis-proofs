# A237271: Carmichael observation; stronger odd-composite bound

Category: **New Formalizations**. Source/status check: **October 9, 2026**.
Original entry: [OEIS A237271](https://oeis.org/A237271).

For all Carmichael n, a(n)>=3, with the sorted-divisor jump count defined
exactly in the Lean file. A stronger theorem covers every odd composite n.
The OEIS observation concerns the first 10000 Carmichael numbers; the
formalized target is its universal extension.

The informal odd-composite argument was already recorded by GitHub author
**j2d9w5xtjn-png** in [Google PR 5447](https://github.com/google-deepmind/formal-conjectures/pull/5447).
This is known mathematics.

**Overlapping public Lean proof:** [Google PR 6955](https://github.com/google-deepmind/formal-conjectures/pull/6955)
links [Anatolii Horodnyk's proof](https://github.com/anatoliiohorodnyk/lean-fc-proofs/blob/5da9642575b26c2c816a49bcb56b33fed5456619/Proofs/T_OeisA237271_observation_carmichael.lean).
That exact Carmichael target was independently rechecked on October 9 with
standard axioms. This repository publishes Wentao Li's independently developed
formalization and its stronger odd-composite theorem, with no exclusive or
first-public-Lean claim.

## Attribution and frozen source

The original Lean definitions are by **The Formal Conjectures Authors**,
whose Apache 2.0 copyright notices are retained. Proof development and write-up:
**Wentao Li**, with AI assistance. Publication includes the needed definitions
verbatim and omits the admitted upstream theorem terms.

Research commit: `7a2f94d822d3bdef3aceaa1fafc54ed99e828b8c`. Original path: `research/batches/b01/workers/cursor-01/targets/A237271/A237271.lean`.
The current public source is [the canonical Lean module](../../../LeanOeisProofs/NewFormalization/A237271.lean).

Publication adjustments:

- Replace upstream statement import by exact required definitions and Mathlib; omit admitted statements and unused tests.

The mathematical proof bodies are preserved. Lean checking establishes the
stated formal result, not novelty, editorial acceptance, or upstream integration.
See [PROOF.md](PROOF.md) for the argument and [PROVENANCE.md](../../../PROVENANCE.md)
for the collection's attribution policy.
