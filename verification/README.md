# Current verification report

Checked October 10, 2026. The [machine-readable report](current.json) covers
**15 canonical problem modules and the root library**. Every recorded compiler
check passed. The new A003161 and A003162 proofs and the updated root were freshly
compiled; the thirteen unchanged proofs retain their exact-source-hash-matched
October 9 compilation records.

## A003161 and A003162: Comparator

Both supercongruences pass Comparator against the original DeepMind statements
at commit `1646ca16afd6cc7a693d3bdc9f066c4d3cc01a89`.
A003162's all-index integrality statement also passes.

- The challenge preserves the original definitions and theorem types. Imports and
  repository-only module/category metadata are adapted for the pinned Mathlib environment.
- The solution imports the freshly built published files and supplies the exact original
  theorem names through explicit wrappers.
- Comparator checks transitive statement definitions and allowed axioms, then replays the
  solution in a fresh Lean kernel environment.
- Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
- Controls confirm acceptance of a valid proof and rejection of a changed theorem,
  an extra axiom, and a changed definition.

The report includes configurations, challenge text, solution wrappers, source and
export hashes, and complete Comparator logs for reproducible inspection.

## Environment

Lean is `4.34.0-rc2`; dependency commits are pinned by `lake-manifest.json` and
verified against clean dependency checkouts. Existing Mathlib caches are trusted.
Comparator source is `ca04cfc72b550331658ec314bf47685281bfd4bf`; the compatible
lean4export version is `cacf989bd75f608700820f6afc595f32e7a99a4d`.

The macOS runner uses Python and direct Lean compilation to invoke Comparator's
unchanged comparison, axiom-checking, and kernel-replay functions. macOS sandbox-exec
restricts network access and filesystem writes. This is an adapted macOS runner;
the standard Linux Landrun deployment was not used. No external kernel was run.
The local Lake runtime has a previously documented SIGTRAP issue, so the proof
library uses direct compiler checks. In a normal installation, run `lake exe cache get`
and `lake build`.

## Layout and attribution

There are six New Proofs, seven New Formalizations, and two Independent Formalizations.
Each sequence has one canonical Lean file and one proof/source pair. A003162 imports
A003161's shared arithmetic development. The original theorem statements and mathematical arguments were preserved during
consolidation; three deprecated tactic lemma names were updated for Lean 4.34. The Epoch binomial helper and its
refinement are credited in the source notes. The existing `v1.0.0` tag is unchanged.

The earlier reports remain accessible through Git history. A069004 remains outside
this publication batch.
