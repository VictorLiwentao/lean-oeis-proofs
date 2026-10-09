# Verification records

## Current layout: New Proofs — October 8, 2026

The [current compiler record](2026-10-08-new-proofs-layout.json) covers all ten
project modules: three proofs in `NewProofs`, six compatibility imports, and the
root library. Every module compiled successfully. The three main theorems report
only `propext`, `Classical.choice`, and `Quot.sound`.

Definitions, theorem statements, and proof bodies match the previous published
sources after normalizing import and documentation paths. Readable proof notes
also retain their mathematics. The pinned Lean version, dependency manifest,
license, and `v1.0.0` tag are unchanged.

## Earlier layout

The [earlier compiler record](2026-10-08-layout.json) is retained for
[commit 8c41bdf](https://github.com/VictorLiwentao/lean-oeis-proofs/tree/8c41bdfee7449f740a3a2ddf7a9c82369f367eef),
when the canonical folder was `NewResults`. Its seven module hashes describe that
historical layout. Use the current record for the present layout.

## Method and reproduction

The normal build is `lake exe cache get` followed by `lake build`, from the
repository root. The root imports the original module names; their compatibility
imports reach the canonical modules, so every project module belongs to the
library's import graph.

Both recorded checks used the **direct pinned Lean compiler**. Lake's version
command printed its version and then exited 133 (SIGTRAP) on this machine. These
records do not claim a successful `lake build`, and no dependency upgrade was
made to work around that local failure.

Each dependency checkout was checked against its `lake-manifest.json` commit.
`LEAN_PATH` contained a fresh output directory and the pinned dependency library
directories, excluding all previous project builds. The current check ran at most
two compiler processes, scheduling each module only after its local dependencies
had passed. The JSON records the dependency graph, compiler options, source
hashes, exit codes, elapsed times, and axiom output.

Each invocation followed this template:

```text
LEAN_PATH=<fresh-output>:<pinned-dependency-libraries> <pinned-lean> \
  -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true \
  -Dweak.linter.mathlibStandardSet=true -DmaxSynthPendingDepth=3 \
  -o <fresh-output>/<module>.olean <module>.lean
```

Local documentation links were also checked. These records concern proof
compilation and repository organization; prior-work notes are on each result's
`SOURCE.md` page.
