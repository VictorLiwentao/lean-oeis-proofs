# A382590: Eventual period three of kth distinct prime factors

Category: **New Formalizations**. Source/status check: **October 9, 2026**.
Original entry: [OEIS A382590](https://oeis.org/A382590).

For the coupled integer recurrence with initial pairs (1,1),(2,1), the kth
**distinct** prime factor of the absolute first coordinate is eventually
periodic, with period 3, for every natural k (in particular k>=2 as in the target).
The Lean convention returns 1 for k=0 or when the factor is missing, including
zero and units. The original question used -1 for missing factors. The proof
establishes stabilization even on those tails, but this file verifies the
explicit Lean convention. No minimal-period claim is made.

Problem: **Bryle Morga**. Mathematics: **Terence Tao**, following **Will Jagy**,
[MathOverflow answer](https://mathoverflow.net/a/490348), March 31, 2025.
The publication preserves the corrected distinct-factor definition from
Google's [PR 5753](https://github.com/google-deepmind/formal-conjectures/pull/5753).
Earlier accepted Epoch proofs used the old multiplicity convention and were
not accepted as exact coverage of this corrected target in the October 9 audit.

## Attribution and frozen source

The original Lean definitions are by **The Formal Conjectures Authors**,
whose Apache 2.0 copyright notices are retained. Proof development and write-up:
**Wentao Li**, with AI assistance. Publication includes the needed definitions
verbatim and omits the admitted upstream theorem terms.

Research commit: `c748661f1f83630921af1d317a2d535c882212f3`. Original path: `research/batches/b02/workers/R2/targets/A382590/A382590.lean`.
The current public source is [the canonical Lean module](../../../LeanOeisProofs/NewFormalization/A382590.lean).

Publication adjustments:

- Replace upstream statement import by exact required definitions and Mathlib; omit admitted statements and unused tests.

The mathematical proof bodies are preserved. Lean checking establishes the
stated formal result, not novelty, editorial acceptance, or upstream integration.
See [PROOF.md](PROOF.md) for the argument and [PROVENANCE.md](../../../PROVENANCE.md)
for the collection's attribution policy.
