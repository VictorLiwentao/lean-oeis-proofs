# Current verification report

Checked October 9, 2026. The [machine-readable report](current.json) covers
**13 canonical problem modules and the root library: all 14 pass**.
The checked theorem dependencies contain only `propext`, `Classical.choice`,
and `Quot.sound`, or subsets of these. No proof code contains `sorry`, `admit`,
`native_decide`, or a custom axiom.

## Scope

There are six modules in `NewProofs` and seven in `NewFormalization`, with one
readable proof/source pair per sequence. A397588's two clauses share one file.
The root imports all 13 canonical modules. There are no compatibility modules,
redirect documents, or duplicate category indexes.

The previous five proof modules and their proof/source notes are unchanged from
commit `6f54afc`. Eight added modules were compared with their frozen research
sources. Proof bodies are preserved, with the documented identity-marker
replacement in A051903; required upstream definitions were compared verbatim
ignoring comments and whitespace. Unused numerical examples and diagnostic
references to admitted statements were removed where documented. The source
comparison details and all final hashes are in the machine-readable report.
Copyright notices, dependency pins, and the `v1.0.0` release tag are preserved.

## Compiler method

The earlier October 9 `lake build` attempt exited with status 133 (SIGTRAP).
This report uses the pinned Lean `4.34.0-rc2` binary directly; it is not a
successful Lake build.

Each dependency checkout matched its manifest commit. `LEAN_PATH` contained
the publication output directory and those pinned dependency libraries. Eight
new modules were compiled there. The unchanged five modules retained their
successful same-day checks; their hash-matched compiled outputs were copied
into the publication output directory. The combined root was then compiled.
No unrelated or stale project outputs were on the search path. At most two
compiler processes ran concurrently. Copyright-format and tactic-style warnings do
not affect the successful compiler and axiom results; full output is retained.

```text
LEAN_PATH=<publication-output>:<pinned-dependency-libraries> <pinned-lean> \
  -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true \
  -Dweak.linter.mathlibStandardSet=true -DmaxSynthPendingDepth=3 \
  -o <publication-output>/<module>.olean <module>.lean
```

In a normal environment use `lake exe cache get` followed by `lake build`.
Local documentation links, imports, file counts, and release-pinned source
paths were checked. Mathematical attribution and known public Lean overlap
are recorded in each sequence's `SOURCE.md`; compiler success does not prove
novelty or upstream acceptance.

A003161, A003162, and A069004 are not in this build: their reused Epoch results
code has no confirmed redistribution license. Incomplete research attempts are
also excluded. Only this current report is kept in the working tree; earlier
reports remain in [Git history](https://github.com/VictorLiwentao/lean-oeis-proofs/commits/main/verification).
