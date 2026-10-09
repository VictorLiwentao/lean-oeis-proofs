# OEIS: New Proofs and Lean Formalizations

**Wentao Li**

Results for **13 OEIS sequences**, with readable explanations and Lean 4 verification: six new proofs/disproofs and seven formalizations of known mathematics. The collection has two categories:

| Category | Contribution | Read the proofs | Lean source |
| --- | --- | --- | --- |
| **New Proofs** | New mathematical proofs and disproofs developed by Wentao Li, with Lean verification. | [New Proofs](proofs/new-proofs/) | [NewProofs](LeanOeisProofs/NewProofs/) |
| **New Formalizations** | Formalizations of existing mathematical proofs, with attribution to the original authors. | [New Formalizations](proofs/new-formalization/) | [NewFormalization](LeanOeisProofs/NewFormalization/) |

## New Proofs

All six proofs below are complete, Lean-verified, and published in this repository.

| OEIS / target | Result | Statement | Readable proof | Lean proof |
| --- | --- | --- | --- | --- |
| [A220119, Conjecture 1](https://oeis.org/A220119) | `a(n)` is divisible by `(n+1)(n+2)` for every `n > 0` | [Source](proofs/new-proofs/A220119/SOURCE.md) | [Proof](proofs/new-proofs/A220119/PROOF.md) | [Lean](LeanOeisProofs/NewProofs/A220119.lean) |
| [A280246](https://oeis.org/A280246) | `a(n)` is odd iff the sum of totatives of `n` is odd, for `n > 0` | [Source](proofs/new-proofs/A280246/SOURCE.md) | [Proof](proofs/new-proofs/A280246/PROOF.md) | [Lean](LeanOeisProofs/NewProofs/A280246.lean) |
| [A098275, Conjecture 1](https://oeis.org/A098275) | `a(n)` is divisible by `n+1` for every `n >= 0` | [Source](proofs/new-proofs/A098275/SOURCE.md) | [Proof](proofs/new-proofs/A098275/PROOF.md) | [Lean](LeanOeisProofs/NewProofs/A098275.lean) |
| [A375439](https://oeis.org/A375439) | `a(n)` is odd exactly at `3^k` and `2*3^k` | [Source](proofs/new-proofs/A375439/SOURCE.md) | [Proof](proofs/new-proofs/A375439/PROOF.md) | [Lean](LeanOeisProofs/NewProofs/A375439.lean) |
| [A381355](https://oeis.org/A381355) | The nth prime divides `a(n)` for every `n > 1` | [Source](proofs/new-proofs/A381355/SOURCE.md) | [Proof](proofs/new-proofs/A381355/PROOF.md) | [Lean](LeanOeisProofs/NewProofs/A381355.lean) |
| [A060957](https://oeis.org/A060957) | Disproof of prime-exponent interpolation: endpoints with exponents 0 and 6, missing exponent 5 | [Source](proofs/new-proofs/A060957/SOURCE.md) | [Proof](proofs/new-proofs/A060957/PROOF.md) | [Lean](LeanOeisProofs/NewProofs/A060957.lean) |

Each proof has a neighboring `SOURCE.md` with the exact conjecture, its original attribution, publication links, and prior-work notes. The A220119 and A098275 proofs cover their divisibility conjectures. A280246's OEIS entry credits Li (2026).

## New Formalizations

Seven completed formalizations are included. **New Formalizations** means
formalization work contributed here; it does not assert that every target lacks
other public Lean proofs. Known overlap is identified below and in each source page.

| OEIS / target | Formalized result and scope | Statement / prior work | Readable proof | Lean proof |
| --- | --- | --- | --- | --- |
| [A001818](https://oeis.org/A001818) | C1: She–Sun–Xia permanent identity | [Source](proofs/new-formalization/A001818/SOURCE.md) | [Proof](proofs/new-formalization/A001818/PROOF.md) | [Lean](LeanOeisProofs/NewFormalization/A001818.lean) |
| [A051903](https://oeis.org/A051903) | C2: no odd universal example; independent formalization, public Lean overlap | [Source](proofs/new-formalization/A051903/SOURCE.md) | [Proof](proofs/new-formalization/A051903/PROOF.md) | [Lean](LeanOeisProofs/NewFormalization/A051903.lean) |
| [A237271](https://oeis.org/A237271) | Carmichael bound, plus all odd composites; independent formalization, public Lean overlap | [Source](proofs/new-formalization/A237271/SOURCE.md) | [Proof](proofs/new-formalization/A237271/PROOF.md) | [Lean](LeanOeisProofs/NewFormalization/A237271.lean) |
| [A361033](https://oeis.org/A361033) | Factorial-ratio parity via classical valuations; integrality included | [Source](proofs/new-formalization/A361033/SOURCE.md) | [Proof](proofs/new-formalization/A361033/PROOF.md) | [Lean](LeanOeisProofs/NewFormalization/A361033.lean) |
| [A368633](https://oeis.org/A368633) | C1: Catalan parity; defining generating-function identity included | [Source](proofs/new-formalization/A368633/SOURCE.md) | [Proof](proofs/new-formalization/A368633/PROOF.md) | [Lean](LeanOeisProofs/NewFormalization/A368633.lean) |
| [A382590](https://oeis.org/A382590) | Tao–Jagy eventual period three for distinct prime factors | [Source](proofs/new-formalization/A382590/SOURCE.md) | [Proof](proofs/new-formalization/A382590/PROOF.md) | [Lean](LeanOeisProofs/NewFormalization/A382590.lean) |
| [A397588](https://oeis.org/A397588) | Parity and divisibility by 3; defining-series bridge; prior recurrence-parity Lean credited | [Source](proofs/new-formalization/A397588/SOURCE.md) | [Proof](proofs/new-formalization/A397588/PROOF.md) | [Lean](LeanOeisProofs/NewFormalization/A397588.lean) |

## Completed research not included in this release

A003161, A003162, and A069004 have completed research proofs, but reuse helpers
or certificates from `epoch-research/LeanOpenProblems-results`. The October 9
check found no redistribution license in that separate results repository.
They are held back until that permission is established or the reused code is
replaced. The MIT license of Epoch's benchmark repository does not automatically
license its separate results repository. Incomplete attempts and results lacking
a verified connection to the OEIS definition are also excluded.

## Repository layout

```text
LeanOeisProofs/
  NewProofs/          Lean proofs of the new contributions
  NewFormalization/  Lean formalizations of known results
proofs/
  new-proofs/        Readable proofs and exact statements
  new-formalization/ Explanations and original references
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
