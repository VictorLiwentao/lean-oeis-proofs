# A001818: Conjecture 1: permanent identity

Category: **New Formalizations**. Source/status check: **October 9, 2026**.
Original entry: [OEIS A001818](https://oeis.org/A001818).

Original conjecture: **Zhi-Wei Sun**. For every n>=1 and every primitive complex
2n-th root zeta, the permanent of the matrix with diagonal 1 and off-diagonal
(1+zeta^(i-j))/(1-zeta^(i-j)) equals the square of the product of the first n
positive odd integers. Exponent subtraction is in the integers.

The mathematical result is due to **Yue-Feng She, Zhi-Wei Sun, and Wei Xia**,
[A novel permanent identity with applications](https://arxiv.org/abs/2208.12167v2),
Theorem 1.3(ii), even case. Related steps follow **Guo–Li–Tao–Wei**,
[arXiv:2206.02592](https://arxiv.org/abs/2206.02592), and the
Calogero–Perelomov determinant identity. The code proves these required steps;
it does not take the paper as an axiom.

The October 9 audit found Google's target marked mathematically solved without
an exact Lean proof link, and no successful matching Epoch submission. No
first-public-Lean priority is asserted.

## Attribution and frozen source

The original Lean definitions are by **The Formal Conjectures Authors**,
whose Apache 2.0 copyright notices are retained. Proof development and write-up:
**Wentao Li**, with AI assistance. Publication includes the needed definitions
verbatim and omits the admitted upstream theorem terms.

Research commit: `33fa7621bfa38a41abebd3aedf545dfdce9f94a0`. Original path: `research/batches/b01/workers/cursor-01-r04/targets/A001818-C1/A001818.lean`.
The current public source is [the canonical Lean module](../../../LeanOeisProofs/NewFormalization/A001818.lean).

Publication adjustments:

- Replace upstream statement import by exact required definitions and Mathlib; omit admitted statements and unused tests.
- Remove the diagnostic `#check` of the admitted upstream theorem; retain the explicit proved wrapper and axiom checks.

The mathematical proof bodies are preserved. Lean checking establishes the
stated formal result, not novelty, editorial acceptance, or upstream integration.
See [PROOF.md](PROOF.md) for the argument and [PROVENANCE.md](../../../PROVENANCE.md)
for the collection's attribution policy.
