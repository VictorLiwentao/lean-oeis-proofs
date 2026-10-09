# Provenance and AI Assistance

Author: Wentao Li

This repository contains Lean-verified proofs of five OEIS conjectures. AI tools were used throughout the research workflow. They are not authors or coauthors of the results.

## Role of AI tools

AI systems materially assisted:

- screening candidate OEIS statements;
- mathematical exploration and the search for elementary identities;
- proof discovery, including independent alternative arguments;
- counterexample search and numerical checks;
- adversarial critique of candidate proofs and formalizations;
- literature and status searches against OEIS, arXiv, and related sources;
- Lean formalization and debugging.

The extent of that assistance was substantial. Several of the arguments were found, independently re-derived, or stress-tested in AI-assisted trajectories before being synthesized into the proofs recorded here.

Where a specific tool can be identified from the research record, it is named below. Uncertain model names are not guessed.

## Verification records

The archived research and publication checks include:

- comparison of the OEIS statements and formal theorem definitions;
- compilation of the final Lean files;
- a full project build for the original three-proof publication;
- inspection of `#print axioms` for each main theorem;
- scans for `sorry`, `admit`, `sorryAx`, custom axioms, and `native_decide`;
- preservation of the verified source states listed below.

These checks were AI-assisted. The October 9 publication check uses the pinned Lean compiler directly because Lake crashes on the local machine; it is not a successful Lake build. See the [current verification report](verification/README.md) for commands, results and limits. Original research worktrees were not modified during preparation of these public copies.

## Verified source states

The Lean files in this repository were restored from the following independently compiled and checked commits of the research history:

| Result | Verified commit | Main theorem |
| --- | --- | --- |
| A280246 | `d7c8d50` | `odd_a_iff_odd_psi` |
| A098275 | `1c7a20b` | `a098275_divisible` |
| A220119 | `eed144b` | `a220119_divisible` |
| A375439 | `d57c795e5e00bf6e5888d507b0bb8c33ce22af0b` | `A375439.a_odd_iff_A038754` |
| A381355 | `82f7a104fb3f46c6e76f433e9682ad7f65b9402c` | `A381355.primeN_dvd_a` |

The build infrastructure (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`) was restored from `eed144b`. The A098275 and A280246 Lean sources at `eed144b` agree with their earlier verified commits. A220119 imports the A098275 file for a previously proved Catalan-factor identity.

Publication cleanup consisted of authorship and license headers, public documentation, and the removal of internal research scaffolding. Existing mathematical definitions, lemma statements, theorem statements, and proof bodies were not rewritten for style. The two October 9 additions come from the author's private `ai4math-lab` research history. Their original AI4Math Lab copyright notices and Apache 2.0 licensing are retained; the workspace author label is replaced by the human author, Wentao Li. No DeepMind formalization source was copied into these two standalone Mathlib modules.

For A375439, eight optional `native_decide` examples were removed; the general proof never depended on them. For A381355, the new `F_unique` theorem formalizes uniqueness of the integral generating function. Its existing definitions and divisibility proof are unchanged.

## Notes on individual results

**A280246.** The research record describes an elementary classification of those \(n\) for which \(\psi(n)\) is odd, together with divisor-closure of that class, and a separate 2-adic argument not used in the Lean file. Independent proof and skeptic trajectories were run; the compiled formalization follows the classification.

**A098275.** The compiled proof is the Vandermonde–ballot–Catalan argument recorded in [`proofs/new-proofs/A098275/PROOF.md`](proofs/new-proofs/A098275/PROOF.md). The research record names three AI-assisted trajectories used at that stage: a direct prover (Cursor Fable), an alternate prover (Cursor Grok 4.6), and a skeptic (Cursor Grok 4.6). The alternate route is not the Lean proof.

**A220119.** The compiled proof is the elementary Vandermonde convolution and prime-power reflection argument recorded in [`proofs/new-proofs/A220119/PROOF.md`](proofs/new-proofs/A220119/PROOF.md). An earlier constant-term approach is not part of the verified theorem and is not included here. Several independent branches reproduced the elementary route before formalization. Specific model names for those branches are not recorded with enough certainty to list.

**A375439.** The proof uses Frobenius in characteristic 3 to justify the recurrence's division, then reduction modulo 2 and strong induction to classify odd coefficients. The full cleared generating-function coefficient identity is proved in Lean. The original sequence and conjecture are due to Paul D. Hanna. See the [proof](proofs/new-proofs/A375439/PROOF.md) and [source record](proofs/new-proofs/A375439/SOURCE.md).

**A381355.** The proof constructs Hanna's integral prime-power recurrence and uses the logarithmic derivative identity to establish divisibility by the nth prime. A September independent skeptic check and October compiler checks are recorded in the research history. The October 9 addition proves uniqueness of the generating function in Lean. See the [proof](proofs/new-proofs/A381355/PROOF.md) and [source record](proofs/new-proofs/A381355/SOURCE.md). Specific model names for these two research trajectories are not asserted.

## Axiom footprint

For each main theorem, Lean reports the axiom footprint `[propext, Classical.choice, Quot.sound]`. These are the standard Lean axioms, not additional mathematical hypotheses of the theorems. No custom axiom is introduced in the formalizations.

## Repository organization — October 9, 2026

The collection has two categories: **New Proofs** and **Lean Formalizations of
Known Results**. The root README is the main navigation page.

Each published problem has one canonical Lean file in `LeanOeisProofs/NewProofs/`
and one readable proof/source pair in `proofs/new-proofs/`. A220119-C1, A280246,
A098275-C1, A375439 and A381355 are the five completed proofs currently included. The
formalizations folders are reserved for future additions.

The October 9 cleanup removed compatibility modules and redirect documents;
the two subsequent additions follow the same canonical layout. Original published
proof files and their proof/source notes, theorem names, licensing, and pinned
dependencies are unchanged. The `v1.0.0` release is preserved, so
OEIS links pinned to that release remain valid.

See the [current verification report](verification/README.md). Earlier reports
and repository layouts remain available through Git history.
