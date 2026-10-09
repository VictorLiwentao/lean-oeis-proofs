# Adding an OEIS result

Author: Wentao Li

## 1. Freeze the verified research state

Record the exact verified commit, the original OEIS definition, the conjecture clause and domain, the Lean compiler result, and the main theorem's axiom footprint. An unfinished proof or a proof of a surrogate sequence is not a completed OEIS result.

## 2. Choose a category

| Lean category | Proof-note category | Use when |
| --- | --- | --- |
| `NewResults` | `new-results` | The result is proposed as new mathematics. Record the bounded prior-art search and explicitly state any unresolved priority. |
| `KnownResults` | `known-results` | A prior mathematical proof is known. Cite it and explain what the Lean formalization adds. |
| `UnderReview` | `under-review` | The proof is verified, but classification is unresolved, a prior general theorem may cover it, or there is existing Lean overlap. |

Record mathematical novelty and earlier Lean coverage separately. A new proof of a known theorem is still known mathematics. A disproof is a result, but numerical evidence alone is not a proof. Classify each conjecture clause separately when a sequence has several targets; split files if their categories differ.

## 3. Add the formal source and proof notes

Use the following layout, substituting the chosen category and an exact-target suffix when needed:

```text
LeanOeisProofs/NewResults/AXXXXXX.lean
proofs/new-results/AXXXXXX/SOURCE.md
proofs/new-results/AXXXXXX/PROOF.md
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
import LeanOeisProofs.NewResults.AXXXXXX
```

Update the root README and the relevant category index with the exact target, contribution status, proof note and Lean source. When moving a published module, leave its old path as a compatibility import; preserve theorem names and old documentation links. Never move an existing release tag.

## 5. Verify and publish

Run:

```bash
lake build
lake env lean LeanOeisProofs/NewResults/AXXXXXX.lean
```

Inspect `#print axioms <main theorem>` and check the proof's transitive dependencies. The completed general theorem must not depend on `sorryAx`, custom mathematical axioms, or compiler-trust axioms from `native_decide`. Keep numerical experiments separate from a general proof.

Check local documentation links, attribution, and exact-statement fidelity. Commit and publish only after the relevant modules have been rebuilt and checked. If Lake itself is unavailable, a complete direct rebuild with the pinned Lean compiler and dependencies may be used; document the commands, exit codes and axiom output, and do not describe it as a successful `lake build`.
