# A051903: Question 2: no odd universal example

Category: **New Formalizations**. Source/status check: **October 9, 2026**.
Original entry: [OEIS A051903](https://oeis.org/A051903).

Question attributed to **Thomas Ordowski** in OEIS. Let a(n) be the largest
prime-factor exponent of n, using the exact sorted-list definition in the
module. There is no odd natural n with a(n)>1 such that b^n is congruent to
b^a(n) modulo n for every natural b. This proves the negative answer to
question 2; it does not claim question 3, which tests only base 2.

The proof uses the classical odd-prime multiplicative-order/LTE argument.
Related universal-power-congruence classification appears in
[Dutta–Dutta, viXra:2602.0018](https://vixra.org/abs/2602.0018).
No mathematical novelty is claimed.

**Overlapping public Lean proof:** [anshM123/OEIS-A051903](https://github.com/anshM123/OEIS-A051903/tree/c0104e7a9cc2d76d86c3a277c372f91a9553a0f6),
linked from [Google PR 6759](https://github.com/google-deepmind/formal-conjectures/pull/6759).
The earlier audit checked its exact question-2 conclusion and standard axioms.
Our independently developed formalization is retained with this overlap
explicitly credited; it is not advertised as a first public Lean proof.

## Attribution and frozen source

The original Lean definitions are by **The Formal Conjectures Authors**,
whose Apache 2.0 copyright notices are retained. Proof development and write-up:
**Wentao Li**, with AI assistance. Publication includes the needed definitions
verbatim and omits the admitted upstream theorem terms.

Research commit: `e4254e79d1fa492dfae5816e20abd46c469b3f4c`. Original path: `research/batches/b01/workers/cursor-01-r03/targets/A051903-C2/A051903.lean`.
The current public source is [the canonical Lean module](../../../LeanOeisProofs/NewFormalization/A051903.lean).

Publication adjustments:

- Replace upstream statement import by exact required definitions and Mathlib; omit admitted statements and unused tests.
- Replace the identity marker `answer(False)` with `False`; the proposition is unchanged.

The mathematical proof bodies are preserved. Lean checking establishes the
stated formal result, not novelty, editorial acceptance, or upstream integration.
See [PROOF.md](PROOF.md) for the argument and [PROVENANCE.md](../../../PROVENANCE.md)
for the collection's attribution policy.
