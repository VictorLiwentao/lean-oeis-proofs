# Current verification report

Updated October 28, 2026. The [machine-readable report](current.json) covers
**24 canonical problem entry points, A069004 certificate support, and the root library**.
A368630 and the combined root were freshly compiled for this publication. The
other 337 component modules retain source-hash-matched earlier checks and cached
outputs; their original verification dates and compiler output are preserved.

## A368630

The complete canonical file compiles with warnings as errors under both pinned
Lean versions: 4.34.0-rc2 for this repository and 4.33.1 at current DeepMind commit
`5a2fb85045c86e4a184b15ce7531ba199a3c4580`. The same source is used for both checks.
The original research namespace and mathematical proof bodies are preserved;
the public interface and five initial-value certificates are added for submission.

Comparator accepts the three congruences, unique integral existence, the source
equation for the selected sequence, and all five initial-value certificates.
It also compares the EGF, source predicate and selected sequence definitions.
A separately written literal-source obligation verifies unique normalized
rational existence, integer EGF coefficients, and all three congruences for every
solution of the original equation. The proposed DeepMind file is new; its
translation was independently reviewed against Hanna's OEIS entry. Direct
rational-series calculation from the original equation matches b-file terms
zero through sixteen, including the exceptional value at index one.

Fresh built-in Lean kernel replay accepts the full compared closures, with only
`propext`, `Classical.choice` and `Quot.sound`. The checker tools were rebuilt
from pinned source. Controls accept a valid proof and reject a changed theorem,
a changed definition and an extra axiom. The direct macOS adapter uses the
unchanged Comparator comparison and axiom code with the Lean 4.33.1 replay API;
no external kernel or Linux sandbox was used. The report records complete logs,
configurations, source/export hashes, tool provenance and reproduction scripts.

The complete proof library is checked with the direct compiler and previously
verified, source-hash-matched dependencies; this is not reported as a new
`lake build`. Earlier proof sources and the `v1.0.0` release tag are unchanged.

## A002454 and A396843

Both complete publication files compile with the pinned Lean 4.34.0-rc2 compiler
and warnings as errors. A separate review checkout at current Formal Conjectures
commit `5a2fb85045c86e4a184b15ce7531ba199a3c4580` freshly compiles the unchanged
A001818 dependency and both new proofs with Lean 4.33.1. Both proofs use
compatibility copies: `ite_eq_left`, `ite_eq_right` and `ite_false` have the names
`if_pos`, `if_neg` and `if_false` in Lean 4.33. These lemma-name substitutions are
the only source differences; the report records each mapping and both hashes.

Comparator checks A002454 against the existing DeepMind statement, including its
sequence definition. It covers every natural index, every primitive root and the
empty-matrix endpoint. The mathematical identity is She–Sun–Xia, Theorem 1.3(ii).

A396843 is a new DeepMind entry. Comparator checks the proposed parity theorem,
unique integral existence, the defining equation and six initial-value certificates.
It also compares the source predicate, selected generating series and sequence
definitions. The comparison removes repository-only metadata and narrows the
aggregate import; mathematical declarations are unchanged. The public series is proved equal to the explicit integral construction.
The normalized rational solution is separately proved to be the image of that series.
The literal OEIS equation, offset and normalization were reviewed against revision 12;
an independent truncated-series calculation matches the first twenty official b-file
terms. Danial Asaria's separate modulo-nine counterexample is recorded in the source notes.

Both full theorem closures pass fresh built-in Lean kernel replay and use only
`propext`, `Classical.choice` and `Quot.sound`. The checker tools were rebuilt from
pinned source. Controls accepted a valid proof and rejected a changed statement,
a changed underlying definition and an extra axiom. The direct macOS adapter uses
Comparator's comparison and axiom checks with Lean 4.33.1's replay API. No external
kernel or Linux sandbox was used for these checks.

The report includes exact configurations, challenge and solution wrappers, compiler
commands, source/export hashes, axiom output, dependency pins and complete logs.
Older proof sources and the `v1.0.0` release tag are unchanged. Compilation of the
proof library uses the direct compiler; this is not reported as a `lake build`.

## A368626, A368629, A368634 and A368635

All four complete canonical proofs were freshly compiled with the pinned compiler
and warnings as errors on October 11. Comparator accepted each exact proposed
DeepMind parity statement, including the sequence and convolution definitions.
A second independent obligation for each sequence verifies the original rational
generating-function equation: unique existence, natural coefficients and exact
parity at every natural index. All eight compared theorem closures were replayed
in a fresh Lean kernel and use only `propext`, `Classical.choice`, and `Quot.sound`.

These are new DeepMind statements at base
`ca0c9468e77f20afee673d88d3d60ac642655e52`. Comparator tests the declarations
proposed by these submissions; the original OEIS translation was also reviewed
mathematically. The six initial values of each sequence match the official
b-files. All four changed DeepMind modules build with `--wfail`.

The complete original mathematical proof bodies are preserved, with deprecated
`if_*` tactic aliases updated and diagnostic prints removed. A368635 uses an
internal namespace rename to provide the computable submitted interface. Its
first publication compile detected one deprecated `if_true` alias; replacing it
with `ite_true` preceded the successful fresh compile and comparison.

The root library was rebuilt after importing all four. Older proof sources and
the `v1.0.0` release tag are unchanged. The direct macOS Comparator runner is the
same one used for A368628; it does not use an external kernel or Linux sandbox.
The machine-readable report retains full configurations, wrappers, commands,
source/export hashes, axiom output, dependency pins and success logs.

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

The proof-library compiler is `4.34.0-rc2`; dependency commits are pinned by `lake-manifest.json` and
verified against clean dependency checkouts. Existing Mathlib caches are trusted.
Comparator source is `ca04cfc72b550331658ec314bf47685281bfd4bf`; the compatible
lean4export version is `cacf989bd75f608700820f6afc595f32e7a99a4d`.

The earlier sandboxed macOS runner uses Python and direct Lean compilation to invoke Comparator's
unchanged comparison, axiom-checking, and kernel-replay functions. macOS sandbox-exec
restricts network access and filesystem writes. This is an adapted macOS runner;
the standard Linux Landrun deployment was not used. No external kernel was run.
The local Lake runtime has a previously documented SIGTRAP issue, so the proof
library uses direct compiler checks. In a normal installation, run `lake exe cache get`
and `lake build`.

## Layout and attribution

There are ten New Proofs, eleven New Formalizations, and three Independent Formalizations.
Each sequence has one canonical Lean entry point and one proof/source pair.
A069004 also has distinct checker and certificate support files, each stored once. A003162 imports
A003161's shared arithmetic development. The original theorem statements and mathematical arguments were preserved during
consolidation; three deprecated tactic lemma names were updated for Lean 4.34. The Epoch binomial helper and its
refinement are credited in the source notes. The existing `v1.0.0` tag is unchanged.

The earlier reports remain accessible through Git history. A069004 is included with original counterexample and Epoch attribution.
