# OEIS A368630: three congruences

Proof and Lean formalization: **Wentao Li**, with OpenAI Codex assistance.

**Paul D. Hanna** introduced [A368630](https://oeis.org/A368630) and its
congruence conjectures on January 2, 2024. Its exponential generating function is

\[
A(x)=\sum_{n\ge0}a(n)\frac{x^n}{n!},\qquad
A(0)=1,\qquad A\bigl(x/A(x)^2\bigr)=\exp(xA(x)).
\]

The offset is zero. The three claims are:

- \(a(n)\equiv1\pmod3\) for every \(n\ge0\).
- \(a(2n)\equiv1\pmod2\) for every \(n\ge0\).
- \(a(2n+1)\equiv0\pmod2\) for every \(n\ge1\).

The excluded term is \(a(1)=1\). The first five terms are
`1, 1, 7, 136, 4933`.

Wentao Li's proof constructs the integral EGF coefficients, proves existence
and uniqueness of the normalized rational solution to the original equation,
and establishes all three congruences. It uses an integral Hurwitz-series
algebra to reduce EGF coefficients modulo two and three without dividing by
factorials in finite characteristic. The public sequence is selected from the
original defining equation and proved equal to the integral construction.

The reviewed research commit is
`e67fdb296cd6a2f718ac8caaf20a0a65aba13fe9`. Publication preserves its mathematical
development and adds an interface matching the proposed DeepMind statements,
with five initial-value certificates. The shared development also proves the
modulo-three clause for A368631; its parity clause is outside this package's
completed A368630 result.

## Source and prior-work review

The October 28, 2026 review checked the official OEIS entry and b-file, the
frozen source used by the research development, and the equation's factorial
normalization, offset and exceptional index. An independent rational-series
calculation from the original equation reproduces terms zero through sixteen.

All-state DeepMind PR searches for `A368630` and `368630`, a global GitHub PR
search for `A368630`, and web searches for the identifier with `proof`, `Lean`
and `Hanna` found no matching earlier mathematical or Lean proof. The current
DeepMind tree at `5a2fb85045c86e4a184b15ce7531ba199a3c4580` has no A368630 entry.
The research search also checked Epoch's main repository. OEIS history and a
complete Epoch results-tree retrieval were unavailable; the search is limited
to the accessible records. This package is classified as **New Proofs** on that
dated evidence.

## Formal entry points

The canonical module is
[A368630.lean](../../../LeanOeisProofs/NewProofs/A368630.lean).
`OeisA368630.exists_unique_sequence` proves unique integral existence;
`a_spec` supplies the original equation for the public sequence. The three
claims are `conjecture_mod_three`, `conjecture_even` and `conjecture_odd`.
`a368630_congruences` additionally quantifies over every normalized rational
solution, identifying its EGF coefficients with an integer sequence.

The complete file compiles with warnings as errors under both pinned Lean
versions. Independent Comparator checks cover the submitted definitions and
theorems and a separately written literal-source obligation. Fresh Lean kernel
replay and axiom checks are recorded in the
[verification report](../../../verification/README.md).
