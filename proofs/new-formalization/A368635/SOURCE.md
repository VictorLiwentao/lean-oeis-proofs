# A368635: source and provenance

Author of the Lean contribution: **Wentao Li**. Source checked October 11, 2026.

## Exact claim

[OEIS A368635](https://oeis.org/A368635), by Paul D. Hanna, January 12, 2024,
defines the coefficients of

`A(x)=1+3xA(x)^2-2xA(-x)^2`.

Its parity conjecture says that `a(n)` is odd exactly when `n = 2^k - 1` for
some natural `k`, and even otherwise. Both `n` and `k` range over all natural
numbers; `k = 0` includes `n = 0`. The offset is zero. The original rational
formal-series equation forces the constant coefficient to be one.

The proof constructs a solution and proves uniqueness among all rational formal
power series. Every coefficient is proved to be a natural-number cast. No
existence, uniqueness, integrality, or recurrence equivalence is assumed.
`OeisA368635.conjecture` is the exact proposed DeepMind statement. The complete
original-equation bridge is in the same canonical file.

## Contribution and earlier work

**New Formalizations.** The original equation reduces modulo two to the classical Catalan equation, so its parity pattern is known mathematics. The contribution is a complete Lean formalization of the original generating-function definition, existence, uniqueness, integrality and parity. No earlier matching public Lean bridge was located in the bounded October 11, 2026 search.

The recurrence parity proof is Wentao Li's earlier local research, recovered at
immutable commit `d57c795e5e00bf6e5888d507b0bb8c33ce22af0b`. The October 2 audit
identified the missing generating-function correspondence. That correspondence
has now been proved and separately reviewed. The bridge research checkpoint is
`9379c1e3c6a61a9189d5a7eb4fa07333ca7d6350`; its original source SHA-256 is
`fd98c87db03ff70efdf6d72d39f0c4405bd3a41196932daceb5f7b2460326753`. Publication preserves its mathematical argument,
updates deprecated tactic names for the pinned compiler, removes diagnostic
prints, and adds the exact submitted interface. The A368635 internal namespace
is renamed to separate that interface from its equation-defined development.

The October 11 screen checked all-state DeepMind issue/PR searches for this
identifier, all open PR changed-file lists, the current upstream tree at
`ca0c9468e77f20afee673d88d3d60ac642655e52`, GitHub's indexed Lean code and exact-ID
web proof searches. No matching DeepMind statement or PR was found before this
submission. Search indexing and alternate names limit coverage. The original
research also checked relevant Epoch and external public repositories; no
external implementation is copied or imported by this publication.

The Catalan connection is also noted in the [public OEIS triage record](https://github.com/the-omega-institute/trureturing/blob/57a811e74db2e1ffe41947d3b0b33f67608d1147/Library/Words/oeis2026triage0910.md). No code from that record is reused.

## Verification and publication

[Lean source](../../../LeanOeisProofs/NewFormalization/A368635.lean) ·
[Readable proof](PROOF.md) · [Verification](../../../verification/README.md).

The official [b-file](https://oeis.org/A368635/b368635.txt) was read through the web tool
on October 11, 2026. Its first six values `1, 1, 10, 21, 310, 762` agree
with the proved term checks. Direct downloads returned HTTP 403, so the recorded
source is the successful web-tool extraction.

Fresh compilation uses Lean 4.34.0-rc2 and pinned Mathlib. Comparator compares the
exact proposed statement and its transitive definitions, and separately checks
the original equation against an independent reference obligation. The recorded
run replays proofs in a fresh built-in Lean kernel; only `propext`,
`Classical.choice`, and `Quot.sound` are permitted. The runner is the documented
macOS adaptation, without an external kernel or Linux sandbox. The comparison
does not replace the mathematical audit of the OEIS translation.

Copyright and license: Wentao Li, Apache 2.0. The statement contributed to DeepMind
uses its required Formal Conjectures Authors header. AI assistance was used for
proof development, source review and verification; see [PROVENANCE](../../../PROVENANCE.md).
