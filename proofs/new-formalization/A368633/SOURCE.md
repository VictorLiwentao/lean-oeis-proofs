# A368633: Conjecture 1: Catalan parity with generating-function identity

Category: **New Formalizations**. Source/status check: **October 9, 2026**.
Original entry: [OEIS A368633](https://oeis.org/A368633).

Sequence and conjecture: **Paul D. Hanna**. The series satisfying
A(x)=1+2x*A(x)^2-x*A(-x)^2 has a(n) odd exactly when n+1 is a power of two.
The module proves the parity of the recursively defined coefficients and
verifies their integral generating-function identity coefficient by coefficient.
Conjecture 2 is not covered.

Modulo 2 this is the classical Catalan recurrence, so the mathematical parity
result follows from known Catalan parity; see [OEIS A000108](https://oeis.org/A000108).
This publication supplies the sequence-specific Lean reduction and its
generating-function connection. No first mathematical or first-public-Lean
priority is claimed.

## Attribution and frozen source

Lean development and write-up: **Wentao Li**, with AI assistance.
The original AI4Math Lab copyright and Apache 2.0 license are retained. These
standalone Mathlib modules were recovered from the author's private research
history; no admitted DeepMind theorem or external proof implementation is imported.

Research commit: `d57c795e5e00bf6e5888d507b0bb8c33ce22af0b`. Original path: `Ai4mathLab/Research/A368633_C1.lean`.
The current public source is [the canonical Lean module](../../../LeanOeisProofs/NewFormalization/A368633.lean).

Publication adjustments:

- Name the human author while retaining the original AI4Math Lab copyright.
- Remove four unused numerical `native_decide` examples; the general proof is unchanged.

The mathematical proof bodies are preserved. Lean checking establishes the
stated formal result, not novelty, editorial acceptance, or upstream integration.
See [PROOF.md](PROOF.md) for the argument and [PROVENANCE.md](../../../PROVENANCE.md)
for the collection's attribution policy.
