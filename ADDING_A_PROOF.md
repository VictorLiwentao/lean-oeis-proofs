# Adding a proof

Author: Wentao Li

This note is the standard process for adding a later OEIS result to the repository. The layout is meant to remain unchanged as the collection grows: a fourth, fifth, or twentieth result should follow the same steps.

## 1. Freeze the verified research state

Independently freeze or tag the verified research result before any publication cleanup. Record the commit (or other exact source state) at which the Lean file compiled, `lake build` succeeded, and `#print axioms` was inspected.

Do not treat an uncompiled or `sorry`-containing file as ready to copy.

## 2. Copy the Lean source

Copy the verified file to

```text
LeanOeisProofs/AXXXXXX.lean
```

Use the header

```lean
/-
Copyright (c) 2026 Wentao Li.
Licensed under the Apache License, Version 2.0. See LICENSE.
Authors: Wentao Li
-/
```

Do not restyle mathematical definitions, lemma statements, theorem statements, or proof bodies. If the new file depends on an already verified helper, import that module rather than duplicating it.

## 3. Record the statement and the proof

Create

```text
proofs/AXXXXXX/SOURCE.md
proofs/AXXXXXX/PROOF.md
```

`SOURCE.md` is a concise factual record of the OEIS problem: the original definition, the exact conjecture and its domain, and pointers to the Lean theorem and the human-readable proof. It is not a derivation.

`PROOF.md` is a short mathematical note, written so that a mathematician can follow the argument without reading Lean. End it with a formal-verification paragraph naming the Lean version, the pinned dependencies, the source path, the main theorem, and the axiom footprint reported by Lean.

## 4. Wire the library and the table

Add

```lean
import LeanOeisProofs.AXXXXXX
```

to `LeanOeisProofs.lean`.

Add one row to the table in `README.md`, with the OEIS number linking to the canonical OEIS entry, “Proof” linking to `proofs/AXXXXXX/PROOF.md`, and “Lean” linking to `LeanOeisProofs/AXXXXXX.lean`.

## 5. Verify

Run

```bash
lake build
lake env lean LeanOeisProofs/AXXXXXX.lean
```

Inspect

```lean
#print axioms <main theorem>
```

Scan the new Lean file (and, if it imports a helper, that helper) for `sorry`, `admit`, `sorryAx`, custom axioms, and `native_decide` in the general theorem. Small `example` checks of published initial terms are separate from the general proof.

## 6. Only then commit and publish

Commit only after the checks above succeed. Do not publish a result whose formal source has not been rebuilt from the files in this repository.
