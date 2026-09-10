# Lean-Verified Proofs of OEIS Conjectures

Author: Wentao Li

This repository collects elementary proofs of selected OEIS conjectures, each accompanied by a Lean 4 formalization in Mathlib. The intended reader is a mathematician who wishes to identify the exact OEIS statement, read a human-readable proof, inspect the Lean source, and reproduce the kernel check.

Each formalization targets the original OEIS definition of the sequence, rather than a recurrence-defined or otherwise surrogate sequence.

| OEIS | Result | Proof | Lean |
| --- | --- | --- | --- |
| [A280246](https://oeis.org/A280246) | \(a(n)\) is odd iff \(\psi(n)\) is odd | [proof](proofs/A280246/PROOF.md) | [Lean](LeanOeisProofs/A280246.lean) |
| [A098275](https://oeis.org/A098275) | \((n+1)\mid a(n)\) for all \(n\ge 0\) | [proof](proofs/A098275/PROOF.md) | [Lean](LeanOeisProofs/A098275.lean) |
| [A220119](https://oeis.org/A220119) | \((n+1)(n+2)\mid a(n)\) for all \(n>0\) | [proof](proofs/A220119/PROOF.md) | [Lean](LeanOeisProofs/A220119.lean) |

Each result has a short source note under `proofs/Axxxxxx/SOURCE.md`, recording the OEIS definition and the exact conjecture.

The Lean library and module root is `LeanOeisProofs`. Adding a later result does not require renaming it.

## Verification

Lean is pinned by `lean-toolchain`. Mathlib and its transitive dependencies are pinned by `lake-manifest.json`.

On a fresh checkout, first run:

```bash
lake exe cache get
lake build
```

This builds the library, including the A220119 dependency on A098275.

After that, individual files may optionally be checked with:

```bash
lake env lean LeanOeisProofs/A280246.lean
lake env lean LeanOeisProofs/A098275.lean
lake env lean LeanOeisProofs/A220119.lean
```

Each main theorem reports the axiom footprint `[propext, Classical.choice, Quot.sound]`. No custom mathematical axioms are introduced. The general theorems contain no `sorry`, `admit`, `sorryAx`, custom axiom, or `native_decide` proof.

## AI assistance

AI systems materially assisted mathematical exploration, proof search, critique, and Lean formalization.

Author: Wentao Li

Details of the research workflow and independently performed checks are recorded in [PROVENANCE.md](PROVENANCE.md).

## License

The contents of this repository are licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE).
