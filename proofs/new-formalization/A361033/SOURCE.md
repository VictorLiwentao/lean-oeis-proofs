# A361033: Conjecture 1: factorial-ratio parity

Category: **New Formalizations**. Source/status check: **October 9, 2026**.
Original entry: [OEIS A361033](https://oeis.org/A361033).

For every natural n, 3*(4n)!/(n!*((n+1)!)^3) is an integer and is odd iff
n=2^k-1 for some natural k. The Lean proof establishes denominator divisibility
before reasoning about the natural-number quotient. OEIS attributes the parity
conjecture to **Peter Bala**, March 1, 2023.

The method is classical Legendre valuation and binary digit sums. This is
conservatively classified as a formalization, not a new mathematical discovery.
For the broader family, see **Joaquim Cera Da Conceição**,
[Multinomial Catalan Numbers and Lucas Analogues](https://cs.uwaterloo.ca/journals/JIS/VOL26/Cera/cera4.html),
Journal of Integer Sequences 26 (2023), Article 23.9.7. Our sequence is three
times the paper's C_3(n). That paper is a general framework reference; we do not
claim it explicitly states this exact parity corollary. The complete elementary
valuation argument is given in PROOF.md and verified here.

## Attribution and frozen source

Lean development and write-up: **Wentao Li**, with AI assistance.
The copyright and author headers name Wentao Li; the Apache 2.0 license is retained. These
standalone Mathlib modules were recovered from the author's private research
history; no admitted DeepMind theorem or external proof implementation is imported.

Research commit: `3888af2abd61ac930e0a60d2af8ddad169b68dd7`. Original path: `Ai4mathLab/Research/A361033_C1.lean`.
The current public source is [the canonical Lean module](../../../LeanOeisProofs/NewFormalization/A361033.lean).

Publication adjustments:

- Name Wentao Li in the copyright and author headers; retain Apache 2.0 licensing.
- Retain the three diagnostic axiom checks added in the October 2 audit; the proof code matches the frozen research commit.

The mathematical proof bodies are preserved. Lean checking establishes the
stated formal result, not novelty, editorial acceptance, or upstream integration.
See [PROOF.md](PROOF.md) for the argument and [PROVENANCE.md](../../../PROVENANCE.md)
for the collection's attribution policy.
