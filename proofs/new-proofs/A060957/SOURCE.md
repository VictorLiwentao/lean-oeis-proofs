# A060957: Prime-exponent interpolation is false

Category: **New Proofs**. Source/status check: **October 9, 2026**.
Original entry: [OEIS A060957](https://oeis.org/A060957).

Original conjecture: **Yan Sheng Ang**, February 13, 2020. For all natural n,p
with p prime and p<=n, and all natural m,a, membership of m and p^a*m in the
set of products of subsets of {1,...,n} was conjectured to imply membership
of p^k*m for every 0<k<a. The proof negates precisely this statement. It gives
explicit finite-set witnesses with a=6 and k=5; it does not address only the
separate parity comment.

The October 9 research audit found no exact earlier public disproof in the
checked OEIS, Google Formal Conjectures/AlphaProof Nexus, Epoch results,
GitHub issues/PRs, and linked literature. Google's statement remained open;
the matching Epoch attempts did not verify. This is a dated search, not proof
that no unindexed or private solution exists. The supporting-face method has
related prior literature credited in PROOF.md.

## Attribution and frozen source

The original Lean definitions are by **The Formal Conjectures Authors**,
whose Apache 2.0 copyright notices are retained. Proof development and write-up:
**Wentao Li**, with AI assistance. Publication includes the needed definitions
verbatim and omits the admitted upstream theorem terms.

Research commit: `e00665575f476811ef241b43e9b45738774165b6`. Original path: `research/targets/A060957/A060957.lean`.
The current public source is [the canonical Lean module](../../../LeanOeisProofs/NewProofs/A060957.lean).

Publication adjustments:

- Replace upstream statement import by exact required definitions and Mathlib; omit admitted statements and unused tests.
- Remove an unavailable Formal Conjectures copyright-linter option; update stale verification comments.

The mathematical proof bodies are preserved. Lean checking establishes the
stated formal result, not novelty, editorial acceptance, or upstream integration.
See [PROOF.md](PROOF.md) for the argument and [PROVENANCE.md](../../../PROVENANCE.md)
for the collection's attribution policy.
