# OEIS Proofs and Lean Formalizations

Author: Wentao Li

This repository collects proposed new results about OEIS sequences and Lean 4 formalizations of known mathematics. Each result includes the exact statement, a readable proof, and a reproducible formalization in Mathlib.

Each formalization targets the original OEIS definition of the sequence, rather than a recurrence-defined or otherwise surrogate sequence.

## Browse by contribution

| Category | What it means | Proof notes | Lean sources |
| --- | --- | --- | --- |
| **NewResults** | Proposed new mathematical proofs or disproofs. Priority remains unestablished unless separately documented. | [new-results](proofs/new-results/) | [NewResults](LeanOeisProofs/NewResults/) |
| **KnownResults** | Lean formalizations of previously proved mathematics, with the original mathematical source credited. | [known-results](proofs/known-results/) | [KnownResults](LeanOeisProofs/KnownResults/) |
| **UnderReview** | Verified results with unresolved novelty, suspected prior-theorem coverage, or existing Lean overlap. | [under-review](proofs/under-review/) | [UnderReview](LeanOeisProofs/UnderReview/) |

Lean verification and mathematical novelty are separate. A `NewResults` folder does not establish first-ever discovery; a `KnownResults` folder does not establish the first Lean formalization. Each result's `SOURCE.md` records those assessments separately, including the date and limits of the prior-art search.

## Published results

The three existing results are proposed new results, with priority unestablished in the October 7, 2026 review. The other categories are ready for future additions and currently contain no proof modules.

| OEIS / exact target | Result | Proof | Lean |
| --- | --- | --- | --- |
| [A280246](https://oeis.org/A280246) | \(a(n)\) is odd iff \(\psi(n)\) is odd, for \(n>0\) | [proof](proofs/new-results/A280246/PROOF.md) | [Lean](LeanOeisProofs/NewResults/A280246.lean) |
| [A098275, C1](https://oeis.org/A098275) | \((n+1)\mid a(n)\) for all \(n\ge 0\) | [proof](proofs/new-results/A098275/PROOF.md) | [Lean](LeanOeisProofs/NewResults/A098275.lean) |
| [A220119, C1](https://oeis.org/A220119) | \((n+1)(n+2)\mid a(n)\) for all \(n>0\) | [proof](proofs/new-results/A220119/PROOF.md) | [Lean](LeanOeisProofs/NewResults/A220119.lean) |

Each result has a neighboring `SOURCE.md` recording the original definition and exact conjecture. A098275 and A220119 cover the divisibility clauses only; their separate second conjectures are not claimed. A280246's OEIS entry credits Li (2026).

The original `LeanOeisProofs/Axxxxxx.lean` paths remain working compatibility imports, and the old proof-note paths point to their new locations. The `v1.0.0` tag and its existing OEIS links are unchanged.

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
lake env lean LeanOeisProofs/NewResults/A280246.lean
lake env lean LeanOeisProofs/NewResults/A098275.lean
lake env lean LeanOeisProofs/NewResults/A220119.lean
```

Each main theorem reports the axiom footprint `[propext, Classical.choice, Quot.sound]`. No custom mathematical axioms are introduced. The general theorems contain no `sorry`, `admit`, `sorryAx`, custom axiom, or `native_decide` proof.

## AI assistance

AI systems materially assisted mathematical exploration, proof search, critique, and Lean formalization.

Author: Wentao Li

Details of the research workflow and independently performed checks are recorded in [PROVENANCE.md](PROVENANCE.md).

For future additions, follow [ADDING_A_PROOF.md](ADDING_A_PROOF.md), including attribution of the original mathematics and any reused formalization.

## License

The contents of this repository are licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE).
