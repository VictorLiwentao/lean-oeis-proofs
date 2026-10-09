# Current verification report

Checked October 9, 2026. The [current report](current.json) covers all five
canonical proof modules and the root library. All six compiled successfully.
Every main theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
A375439's integrality and coefficient-identity lemmas, and A381355's defining
coefficient equation and new uniqueness theorem, also pass the axiom checks.

## Layout and source checks

There are exactly five problem `.lean` files and one readable proof/source pair
per problem. No compatibility modules or redirect documents remain. The root
library imports the canonical `NewProofs` modules directly.

The original three proof modules and their six proof/source documents match
commit `38d0cd1` byte-for-byte. The two additions were compared with their frozen
research sources. Existing definitions and proof bodies are unchanged; the
report lists the authorship-header changes, removed numerical examples and added
uniqueness lemma. Lean, dependency pins, licensing, and the `v1.0.0` tag are
unchanged. Original release-pinned OEIS links remain valid.

## Compiler method

The earlier October 9 `lake build` attempt exited with status 133 (SIGTRAP).
These checks use the pinned `leanprover/lean4:v4.34.0-rc2` compiler directly;
they do not represent a successful Lake build.

Every dependency checkout matched its `lake-manifest.json` commit. `LEAN_PATH`
contained a fresh output directory and the pinned dependency library directories;
older project build outputs were excluded. At most two compiler processes ran,
with each module scheduled after its dependencies passed. After adding
`F_unique` and cleaning the two new headers, both new modules and the root were
rebuilt. The unchanged three modules retain their successful checks from the
same build. File hashes match every final source.

```text
LEAN_PATH=<fresh-output>:<pinned-dependency-libraries> <pinned-lean> \
  -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true \
  -Dweak.linter.mathlibStandardSet=true -DmaxSynthPendingDepth=3 \
  -o <fresh-output>/<module>.olean <module>.lean
```

A381355 emits three existing tactic-style linter warnings. Compilation and axiom
checks pass. For a normal environment, run `lake exe cache get` and `lake build`.
Local documentation links and canonical file counts were also checked.
Prior-work searches and exact-target explanations are in each `SOURCE.md`.

Only the current report is stored here. Earlier reports remain available through
[Git history](https://github.com/VictorLiwentao/lean-oeis-proofs/commits/main/verification).
