# OEIS: New Proofs and Lean Formalizations

**Wentao Li**

Mathematical proofs about OEIS sequences, with readable explanations and Lean 4 verification. The collection has two categories:

| Category | Contribution | Read the proofs | Lean source |
| --- | --- | --- | --- |
| **New Proofs** | New mathematical proofs and disproofs developed by Wentao Li, with Lean verification. | [New Proofs](proofs/new-proofs/) | [NewProofs](LeanOeisProofs/NewProofs/) |
| **Lean Formalizations of Known Results** | Formalizations of existing mathematical proofs, with attribution to the original authors. | [Formalizations](proofs/formalizations/) | [Formalizations](LeanOeisProofs/Formalizations/) |

## New Proofs

All five proofs below are complete, Lean-verified, and published in this repository.

| OEIS / target | Result | Statement | Readable proof | Lean proof |
| --- | --- | --- | --- | --- |
| [A220119, Conjecture 1](https://oeis.org/A220119) | `a(n)` is divisible by `(n+1)(n+2)` for every `n > 0` | [Source](proofs/new-proofs/A220119/SOURCE.md) | [Proof](proofs/new-proofs/A220119/PROOF.md) | [Lean](LeanOeisProofs/NewProofs/A220119.lean) |
| [A280246](https://oeis.org/A280246) | `a(n)` is odd iff the sum of totatives of `n` is odd, for `n > 0` | [Source](proofs/new-proofs/A280246/SOURCE.md) | [Proof](proofs/new-proofs/A280246/PROOF.md) | [Lean](LeanOeisProofs/NewProofs/A280246.lean) |
| [A098275, Conjecture 1](https://oeis.org/A098275) | `a(n)` is divisible by `n+1` for every `n >= 0` | [Source](proofs/new-proofs/A098275/SOURCE.md) | [Proof](proofs/new-proofs/A098275/PROOF.md) | [Lean](LeanOeisProofs/NewProofs/A098275.lean) |
| [A375439](https://oeis.org/A375439) | `a(n)` is odd exactly at `3^k` and `2*3^k` | [Source](proofs/new-proofs/A375439/SOURCE.md) | [Proof](proofs/new-proofs/A375439/PROOF.md) | [Lean](LeanOeisProofs/NewProofs/A375439.lean) |
| [A381355](https://oeis.org/A381355) | The nth prime divides `a(n)` for every `n > 1` | [Source](proofs/new-proofs/A381355/SOURCE.md) | [Proof](proofs/new-proofs/A381355/PROOF.md) | [Lean](LeanOeisProofs/NewProofs/A381355.lean) |

Each proof has a neighboring `SOURCE.md` with the exact conjecture, its original attribution, publication links, and prior-work notes. The A220119 and A098275 proofs cover their divisibility conjectures. A280246's OEIS entry credits Li (2026).

## Lean Formalizations of Known Results

This section is ready for additions. No proof has been imported into it yet. Each future entry will identify the original mathematical proof and explain the Lean contribution.

## Repository layout

```text
LeanOeisProofs/
  NewProofs/          Lean proofs of the new contributions
  Formalizations/    Lean formalizations of known results
proofs/
  new-proofs/        Readable proofs and exact statements
  formalizations/    Explanations and original references
verification/        Compiler and axiom-check records
```

Each problem has one Lean source and one readable proof/source pair. The root README is the main index. The existing `v1.0.0` release and release-pinned OEIS links are preserved.

## Verify the proofs

Lean is pinned by `lean-toolchain`; Mathlib and its dependencies are pinned by `lake-manifest.json`.

```bash
lake exe cache get
lake build
```

After the build, an individual proof can also be checked with:

```bash
lake env lean LeanOeisProofs/NewProofs/A220119.lean
```

The main theorems use only `propext`, `Classical.choice`, and `Quot.sound`. Their proofs contain no `sorry`, `admit`, custom mathematical axioms, or `native_decide`. See the [current verification report](verification/README.md).

## Attribution and contributions

AI systems materially assisted mathematical exploration, proof search, critique, and Lean formalization. See [PROVENANCE.md](PROVENANCE.md) for attribution and the research record, and [ADDING_A_PROOF.md](ADDING_A_PROOF.md) for the publication workflow.

Licensed under the [Apache License, Version 2.0](LICENSE).
