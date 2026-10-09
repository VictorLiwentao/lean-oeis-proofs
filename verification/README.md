# Current verification report

Checked October 9, 2026. The [current report](current.json) covers the three
canonical proof modules and the root library. All four compiled successfully.
Each main theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Layout and source checks

There are exactly three problem `.lean` files and one readable proof/source pair
per problem. No compatibility modules or redirect documents remain. The root
library imports the canonical `NewProofs` modules directly.

The three proof modules and all six proof/source documents match the previous
published commit byte-for-byte. Their hashes and the comparison commit are in the
report. Lean, dependency pins, licensing, and the `v1.0.0` tag are unchanged. The
three original release-pinned Lean files remain available at that tag.

## Compiler method

`lake build` exited with status 133 (SIGTRAP) on this machine. The fallback check
used the pinned `leanprover/lean4:v4.34.0-rc2` compiler. This is a successful direct
Lean compiler check, not a successful Lake build.

Every dependency checkout matched its `lake-manifest.json` commit. `LEAN_PATH`
contained a fresh output directory and the pinned dependency library directories;
previous project build outputs were excluded. At most two compiler processes ran,
and each module was scheduled after its dependencies had passed. The report
records the exact options, dependency graph, file hashes, exit codes and axiom
output.

```text
LEAN_PATH=<fresh-output>:<pinned-dependency-libraries> <pinned-lean> \
  -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true \
  -Dweak.linter.mathlibStandardSet=true -DmaxSynthPendingDepth=3 \
  -o <fresh-output>/<module>.olean <module>.lean
```

For a normal environment, run `lake exe cache get` followed by `lake build`.
Local documentation links were also checked. This report records compilation and
layout checks; prior-work notes remain on each result's `SOURCE.md` page.

Only the current report is stored here. Earlier reports remain available through
[Git history](https://github.com/VictorLiwentao/lean-oeis-proofs/commits/main/verification).
