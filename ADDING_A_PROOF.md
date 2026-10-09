# Adding an OEIS result

Author: Wentao Li

## 1. Freeze the verified research state

Record the exact verified commit, the original OEIS definition, the conjecture clause and domain, the Lean compiler result, and the main theorem's axiom footprint. An unfinished proof or a proof of a surrogate sequence is not a completed OEIS result.

## 2. Choose one of the two categories

| Category | Lean folder | Proof-note folder | Contribution |
| --- | --- | --- | --- |
| **New Proofs** | `NewProofs` | `new-proofs` | A new mathematical proof or disproof, with Lean verification. Record the original conjecture and prior-work search. |
| **New Formalizations** | `NewFormalization` | `new-formalization` | A Lean formalization of an existing mathematical proof. Cite the original proof and credit its authors. |

Record the exact contribution and any earlier Lean coverage in `SOURCE.md`. Keep literature-search notes and unresolved publication questions on the individual source page, rather than labeling a completed proof as unverified. An unresolved mathematical argument stays in the research workspace until it is proved. Numerical evidence is not a proof.

Explain the contribution of each conjecture clause when a sequence has multiple targets, but keep one canonical Lean file and proof/source pair per sequence. Clearly mark independent formalizations that overlap other public Lean proofs; inclusion is not a first-public-Lean claim. Do not treat OEIS publication or a successful Lean check alone as evidence of first-ever mathematical priority.

## 3. Add the formal source and proof notes

Use the following layout, substituting the chosen category; keep multiple clauses of a sequence together:

```text
LeanOeisProofs/NewProofs/AXXXXXX.lean
proofs/new-proofs/AXXXXXX/SOURCE.md
proofs/new-proofs/AXXXXXX/PROOF.md
```

`SOURCE.md` must record the statement, quantifiers, original mathematical author, dated source links, main Lean theorem, verification evidence, mathematical novelty assessment, and earlier Lean coverage. Cite the original proof for known mathematics. State the limits and date of any search claiming that no exact earlier proof was found.

`PROOF.md` is a readable mathematical explanation, ending with the Lean version, pinned dependencies, module path, theorem name, and reported axioms. Match its claim to the exact verified statement.

Preserve existing copyright notices, author names, and licenses. For reused Google DeepMind material, retain `Copyright 2026 The Formal Conjectures Authors.` as it appears in the source; credit Wentao Li for the new contribution without replacing the original attribution. Attribute known mathematics to its original authors and document AI assistance in `PROVENANCE.md`.

For an entirely new file, use:

```lean
/-
Copyright (c) 2026 Wentao Li.
Licensed under the Apache License, Version 2.0. See LICENSE.
Authors: Wentao Li
-/
```

Check redistribution licenses before copying external helper code. Preserve mathematical definitions, theorem statements and proof bodies during publication cleanup; only adjust necessary imports and documentation paths. Import verified helpers instead of duplicating them.

## 4. Update the library and index

Add the categorized module to `LeanOeisProofs.lean`, for example:

```lean
import LeanOeisProofs.NewProofs.AXXXXXX
```

Update the root README with the exact target, contribution status, readable proof, and Lean source. Keep **one canonical location per file; no compatibility copies or redirect files**. When moving a module, update imports and current documentation links and remove the old path. Preserve theorem names and existing release tags; release-pinned links remain available through those tags. Do not add duplicate category indexes.

Keep one current verification report under `verification/`; replace it when the checked state changes. Earlier reports remain available through Git history.

## 5. Verify and publish

Run:

```bash
lake build
lake env lean LeanOeisProofs/NewProofs/AXXXXXX.lean
```

Inspect `#print axioms <main theorem>` and check the proof's transitive dependencies. The completed general theorem must not depend on `sorryAx`, custom mathematical axioms, or compiler-trust axioms from `native_decide`. Keep numerical experiments separate from a general proof.

Check local documentation links, attribution, and exact-statement fidelity. Commit and publish only after the relevant modules have been rebuilt and checked. If Lake itself is unavailable, a complete direct rebuild with the pinned Lean compiler and dependencies may be used; document the commands, exit codes and axiom output, and do not describe it as a successful `lake build`.
