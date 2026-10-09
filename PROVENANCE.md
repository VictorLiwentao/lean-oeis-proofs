# Provenance and AI Assistance

Author: Wentao Li

This repository contains Lean-verified proofs of three OEIS conjectures. AI tools were used throughout the research workflow. They are not authors or coauthors of the results.

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

## Independent checks by the author

Before this public repository was prepared, Wentao Li independently:

- checked the final OEIS statements and theorem-statement fidelity against the source entries;
- compiled the final Lean files;
- ran the full project build;
- inspected `#print axioms` for each main theorem;
- scanned the formal sources for `sorry`, `admit`, `sorryAx`, custom axioms, and `native_decide`;
- preserved the verified source states listed below, prior to publication cleanup.

The original research worktree was not modified during the preparation of this public copy.

## Verified source states

The Lean files in this repository were restored from the following independently compiled and checked commits of the research history:

| Result | Verified commit | Main theorem |
| --- | --- | --- |
| A280246 | `d7c8d50` | `odd_a_iff_odd_psi` |
| A098275 | `1c7a20b` | `a098275_divisible` |
| A220119 | `eed144b` | `a220119_divisible` |

The build infrastructure (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`) was restored from `eed144b`. The A098275 and A280246 Lean sources at `eed144b` agree with their earlier verified commits. A220119 imports the A098275 file for a previously proved Catalan-factor identity.

Publication cleanup consisted of authorship and license headers, public documentation, and the removal of internal research scaffolding. Mathematical definitions, lemma statements, theorem statements, and proof bodies were not rewritten for style.

## Notes on individual results

**A280246.** The research record describes an elementary classification of those \(n\) for which \(\psi(n)\) is odd, together with divisor-closure of that class, and a separate 2-adic argument not used in the Lean file. Independent proof and skeptic trajectories were run; the compiled formalization follows the classification.

**A098275.** The compiled proof is the Vandermonde–ballot–Catalan argument recorded in [`proofs/new-proofs/A098275/PROOF.md`](proofs/new-proofs/A098275/PROOF.md). The research record names three AI-assisted trajectories used at that stage: a direct prover (Cursor Fable), an alternate prover (Cursor Grok 4.6), and a skeptic (Cursor Grok 4.6). The alternate route is not the Lean proof.

**A220119.** The compiled proof is the elementary Vandermonde convolution and prime-power reflection argument recorded in [`proofs/new-proofs/A220119/PROOF.md`](proofs/new-proofs/A220119/PROOF.md). An earlier constant-term approach is not part of the verified theorem and is not included here. Several independent branches reproduced the elementary route before formalization. Specific model names for those branches are not recorded with enough certainty to list.

## Axiom footprint

For each main theorem, Lean reports the axiom footprint `[propext, Classical.choice, Quot.sound]`. These are the standard Lean axioms, not additional mathematical hypotheses of the theorems. No custom axiom is introduced in the formalizations.

## Repository organization — October 8, 2026

The published collection has two categories: **New Proofs** and **Lean
Formalizations of Known Results**. A220119-C1, A280246, and A098275-C1 are completed
new proofs with Lean verification. Their canonical modules are in
`LeanOeisProofs/NewProofs/`, with readable proofs under `proofs/new-proofs/`.

The formalizations section is ready for future additions and currently contains
no proof modules. Original mathematical authors and reused formalization sources
will be credited with each addition.

Prior-work notes are kept on each source page, separately from the proof's
verification status.

The original module names and the earlier `NewResults` module names remain
compatibility imports. Existing proof-note links and the `v1.0.0` release are
preserved. The reorganization changes only import paths and documentation;
mathematical definitions, statements and proof bodies are unchanged.

See the [verification records](verification/README.md) for the checks of each
published layout. The earlier compiler record is preserved as historical evidence.
