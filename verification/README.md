# Layout verification — October 8, 2026

The [compiler record](2026-10-08-layout.json) records a fresh check of all seven
project modules: the three categorized proofs, all three compatibility modules,
and the root library. Each module exited successfully. Each main theorem reported
only `propext`, `Classical.choice`, and `Quot.sound`.

The three proof files match the previous published source after normalizing one
import path and one documentation link. The proof notes differ only in links.
The pinned Lean version, dependency manifest, license, and `v1.0.0` tag are unchanged.

This was a **direct Lean compiler check**, not a successful `lake build`. On the
verification machine, `lake --version` printed its version and then exited with
status 133 (SIGTRAP), as also observed in the earlier audit. No Lean or dependency
upgrade was made to work around it.

## Reproduction

The normal build remains `lake exe cache get` followed by `lake build`, from the
repository root. The root library imports the compatibility modules, which in
turn import the new module paths, so all seven modules belong to the import graph.

For the direct check, each dependency checkout was first checked against its
commit in `lake-manifest.json`. `LEAN_PATH` contained only a fresh output directory
and the pinned packages' `.lake/build/lib/lean` directories. The previous project
build directory was excluded. The exact compiler options, module order, source
hashes, exit codes, and axiom output are in the linked JSON record. The first two
independent modules ran concurrently; the remaining modules ran in the listed
order. The compiler was the binary from `leanprover/lean4:v4.34.0-rc2`.

Each invocation followed this template:

```text
LEAN_PATH=<fresh-output>:<pinned-dependency-libraries> <pinned-lean> \
  -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true \
  -Dweak.linter.mathlibStandardSet=true -DmaxSynthPendingDepth=3 \
  -o <fresh-output>/<module>.olean <module>.lean
```

Local Markdown links were also checked. These are build and organization checks;
they are not a new mathematical novelty review. The last recorded novelty review
remains October 7, 2026.
