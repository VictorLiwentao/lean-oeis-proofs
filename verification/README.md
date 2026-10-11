# Current verification report

Updated October 11, 2026. The [machine-readable report](current.json) covers
**17 canonical problem entry points, A069004 certificate support, and the root library**. Every recorded compiler check passed. A069004's entry point, its 314 support
modules, and the combined root library were freshly compiled on October 11.
A368628 and the combined root library were additionally compiled after this addition.
The other proofs retain their source-hash-matched earlier records.

## A368628: original generating-function bridge

The published A368628 module and combined library were freshly compiled with
warnings as errors on October 11. Comparator passed for `OeisA368628.conjecture`,
the exact new statement proposed to Formal Conjectures, checking `a`, `conv2`
and `conv4`. A second, independently written obligation checks the original
rational generating-function equation: unique existence, natural coefficients,
and the complete parity characterization. All checked closures use only the
three standard axioms; fresh built-in Lean kernel replay accepts both results.

The proposed Google statement was new at baseline
`cd6912171c5a1de06905795e5533ec7120f34ddc`. Its metadata and aggregate import
are adapted for the comparison; mathematical definitions and the theorem type
are preserved. The official b-file verifies the first six values.

This run uses the existing Comparator/lean4export kernel driver with the direct
pinned compiler. It does not use the macOS sandbox used for earlier targets or
an external kernel. The machine-readable report retains commands, wrappers,
hashes, axiom output and results. An initial exporter configuration selected the
wrong system Lean path; explicitly pinning `LEAN_SYSROOT` resolved it before the
successful comparison. No mathematical change was needed for that error.

Earlier public recurrence-parity Lean coverage is credited in
[A368628's source record](../proofs/new-formalization/A368628/SOURCE.md).
The added contribution is the original generating-function bridge.

## A069004: fresh certificate and Comparator

Both original DeepMind disproof statements pass: `OeisA69004.conjecture2` and
`OeisA69004.conjecture2.variants.upper_bound_false`. The challenge is pinned to
commit `4c40439d9be65b242e9196fb7848be02a9a4481d`.
The exact sequence definition and theorem types are preserved; repository-only
module metadata and imports are adapted to Lean 4.34.0-rc2.

The certificate proves `42494 <= a(512720)` and
`Nat.primeCounting 512720 = 42493`. It contains 284 prime-certificate chunks and
26 prime-count modules covering 513 counting blocks, all freshly compiled with
warnings treated as errors.
Comparator verifies transitive definitions, permits only the three standard
axioms, and replays the full dependency closure into a fresh Lean kernel.
Controls accepted a correct proof and rejected changed statements, changed
underlying definitions and an extra axiom.

The certificate chunks are prebuilt with the local direct compiler; Comparator
exports and verification run under the macOS sandbox described below.

The machine-readable report includes the complete log, export hashes,
configuration, challenge, solution wrapper, per-file build hashes, source
preservation checks and dependency pins. Compiler and Comparator results are
reported separately from mathematical originality and license provenance.

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

There are six New Proofs, nine New Formalizations, and two Independent Formalizations.
Each sequence has one canonical Lean entry point and one proof/source pair.
A069004 also has distinct checker and certificate support files, each stored once. A003162 imports
A003161's shared arithmetic development. The original theorem statements and mathematical arguments were preserved during
consolidation; three deprecated tactic lemma names were updated for Lean 4.34. The Epoch binomial helper and its
refinement are credited in the source notes. The existing `v1.0.0` tag is unchanged.

The earlier reports remain accessible through Git history. A069004 is included with original counterexample and Epoch attribution.
