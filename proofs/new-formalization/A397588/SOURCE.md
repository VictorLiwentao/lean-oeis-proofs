# A397588: Parity and divisibility by 3, including the generating-function bridge

Category: **New Formalizations**. Source/status check: **October 9, 2026**.
Original entry: [OEIS A397588](https://oeis.org/A397588).

For every natural-number formal power series F satisfying
F=X+(X*F^2)', its nth coefficient is odd iff n is a power of two, for n>0;
its nth coefficient is divisible by 3 for n>1. The module proves existence,
coefficient uniqueness, equivalence with Manyama's recurrence, and both properties.
Both clauses share one canonical file and one proof/source pair.

The original series is due to **Paul D. Hanna**; the recurrence and related
comments are attributed on OEIS. Both properties are treated as known mathematics.
Prior public recurrence-parity Lean work exists in
[The Omega Institute's trureturing repository](https://github.com/the-omega-institute/trureturing/blob/dev/D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.lean).
Our contribution includes the explicit defining-series bridge and divisibility
by 3. The parity theorem alone is not described as a first Lean formalization.
No code from that external implementation was copied into this module.

## Attribution and frozen source

Lean development and write-up: **Wentao Li**, with AI assistance.
The original AI4Math Lab copyright and Apache 2.0 license are retained. These
standalone Mathlib modules were recovered from the author's private research
history; no admitted DeepMind theorem or external proof implementation is imported.

Research commit: `02fb684ba04306c26d7db882e870485a34fab820`. Original path: `Ai4mathLab/Research/A397588.lean`.
The current public source is [the canonical Lean module](../../../LeanOeisProofs/NewFormalization/A397588.lean).

Publication adjustments:

- Name the human author while retaining the original AI4Math Lab copyright; no mathematical code is changed.

The mathematical proof bodies are preserved. Lean checking establishes the
stated formal result, not novelty, editorial acceptance, or upstream integration.
See [PROOF.md](PROOF.md) for the argument and [PROVENANCE.md](../../../PROVENANCE.md)
for the collection's attribution policy.
