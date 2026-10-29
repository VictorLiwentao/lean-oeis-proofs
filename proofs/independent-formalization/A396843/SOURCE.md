# OEIS A396843: integral construction and oddness

Lean formalization and write-up: **Wentao Li**, with OpenAI Codex assistance.

**Paul D. Hanna** introduced [A396843](https://oeis.org/A396843/internal)
on July 1, 2026 and conjectured that all its terms are odd. Its ordinary
generating function satisfies `A(x A(x) − 3x A(x)²) = x²`, with zero constant
coefficient and linear coefficient one. The official offset is one; `a(0)=0`
is an explicit extension outside that domain. The initial terms are
`1, 3, 15, 117, 975`.

**ElonSG / the-omega-institute/trureturing** published an earlier Lean parity
proof in [PR #6773](https://github.com/the-omega-institute/trureturing/pull/6773),
at commit `7062f8c5bbbbee596703ca08a64d26123d4861b0`. Its theorem derives
positive-index oddness from the integral generating-function equation. It uses
characteristic-two uniqueness to prove parity.

Wentao Li's formalization constructs the integral solution, proves normalized
uniqueness over every commutative ring, and proves oddness. It also identifies
every normalized rational solution with the image of the integral construction.
The public interface selects the unique solution by `Classical.epsilon`;
`series_eq_constructed` proves that this choice equals the explicit construction.

The separate modulo-nine conjecture was refuted by **Danial Asaria** on July 26,
2026, as recorded in OEIS: `a(5)=975 ≡ 3 (mod 9)`. It is not part of this submission.

All-state DeepMind PR searches on October 28, 2026 for `A396843`, `396843`,
and the compositional oddness statement found no matching entry or proof PR.
The external parity proof is credited above. The source review used OEIS
revision 12, dated July 30, 2026, and its official b-file.

The canonical module is
[A396843.lean](../../../LeanOeisProofs/IndependentFormalization/A396843.lean).
Its public theorems are `OeisA396843.source_existence`,
`OeisA396843.conjecture`, and `OeisA396843.rational_source_integral`.
See the [verification record](../../../verification/README.md) for the exact
submitted-statement comparison, source audit, and initial-value checks.
