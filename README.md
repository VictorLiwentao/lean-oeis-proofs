# OEIS: New Proofs and Lean Formalizations

**Wentao Li**

Results for **15 OEIS sequences**, with readable explanations and Lean 4 verification: six new proofs/disproofs, seven new formalizations of known mathematics, and two independent formalizations with existing public Lean coverage:

| Category | Contribution | Read the proofs | Lean source |
| --- | --- | --- | --- |
| **New Proofs** | New mathematical proofs and disproofs developed by Wentao Li, with Lean verification. | [New Proofs](proofs/new-proofs/) | [NewProofs](LeanOeisProofs/NewProofs/) |
| **New Formalizations** | Known mathematics; no earlier public Lean proof located for the stated new contribution in the dated search. | [New Formalizations](proofs/new-formalization/) | [NewFormalization](LeanOeisProofs/NewFormalization/) |
| **Independent Formalizations** | Our independently developed proofs of statements with existing public Lean proofs. | [Independent Formalizations](proofs/independent-formalization/) | [IndependentFormalization](LeanOeisProofs/IndependentFormalization/) |

## New Proofs

All six results below are complete, Lean-verified, and published in this repository. The outcome records whether the original conjecture was proved or disproved.

| OEIS / target | Outcome | Result | Statement | Readable proof | Lean proof |
| --- | --- | --- | --- | --- | --- |
| [A220119, Conjecture 1](https://oeis.org/A220119) | **Proved** | `a(n)` is divisible by `(n+1)(n+2)` for every `n > 0` | [Source](proofs/new-proofs/A220119/SOURCE.md) | [Proof](proofs/new-proofs/A220119/PROOF.md) | [Lean](LeanOeisProofs/NewProofs/A220119.lean) |
| [A280246](https://oeis.org/A280246) | **Proved** | `a(n)` is odd iff the sum of totatives of `n` is odd, for `n > 0` | [Source](proofs/new-proofs/A280246/SOURCE.md) | [Proof](proofs/new-proofs/A280246/PROOF.md) | [Lean](LeanOeisProofs/NewProofs/A280246.lean) |
| [A098275, Conjecture 1](https://oeis.org/A098275) | **Proved** | `a(n)` is divisible by `n+1` for every `n >= 0` | [Source](proofs/new-proofs/A098275/SOURCE.md) | [Proof](proofs/new-proofs/A098275/PROOF.md) | [Lean](LeanOeisProofs/NewProofs/A098275.lean) |
| [A375439](https://oeis.org/A375439) | **Proved** | `a(n)` is odd exactly at `3^k` and `2*3^k` | [Source](proofs/new-proofs/A375439/SOURCE.md) | [Proof](proofs/new-proofs/A375439/PROOF.md) | [Lean](LeanOeisProofs/NewProofs/A375439.lean) |
| [A381355](https://oeis.org/A381355) | **Proved** | The nth prime divides `a(n)` for every `n > 1` | [Source](proofs/new-proofs/A381355/SOURCE.md) | [Proof](proofs/new-proofs/A381355/PROOF.md) | [Lean](LeanOeisProofs/NewProofs/A381355.lean) |
| [A060957](https://oeis.org/A060957) | **Disproved** | Disproof of prime-exponent interpolation: endpoints with exponents 0 and 6, missing exponent 5 | [Source](proofs/new-proofs/A060957/SOURCE.md) | [Proof](proofs/new-proofs/A060957/PROOF.md) | [Lean](LeanOeisProofs/NewProofs/A060957.lean) |

Each proof has a neighboring `SOURCE.md` with the exact conjecture, its original attribution, publication links, and prior-work notes. The A220119 and A098275 proofs cover their divisibility conjectures. A280246's OEIS entry credits Li (2026).

## New Formalizations

These seven packages formalize known mathematics. This category is reserved for
contributions whose exact Lean coverage was not located elsewhere in the dated
search recorded in `SOURCE.md`; it is not an absolute first-ever claim. A397588
has mixed coverage: the new contribution is the defining-series bridge and
divisibility-by-3 formalization, not its already-formalized recurrence-parity lemma.

| OEIS / target | Outcome | Formalized result and scope | Statement / prior work | Readable proof | Lean proof |
| --- | --- | --- | --- | --- | --- |
| [A001818](https://oeis.org/A001818) | **Proved** | C1: She–Sun–Xia permanent identity | [Source](proofs/new-formalization/A001818/SOURCE.md) | [Proof](proofs/new-formalization/A001818/PROOF.md) | [Lean](LeanOeisProofs/NewFormalization/A001818.lean) |
| [A361033](https://oeis.org/A361033) | **Proved** | Factorial-ratio parity via classical valuations; integrality included | [Source](proofs/new-formalization/A361033/SOURCE.md) | [Proof](proofs/new-formalization/A361033/PROOF.md) | [Lean](LeanOeisProofs/NewFormalization/A361033.lean) |
| [A368633](https://oeis.org/A368633) | **Proved** | C1: Catalan parity; defining generating-function identity included | [Source](proofs/new-formalization/A368633/SOURCE.md) | [Proof](proofs/new-formalization/A368633/PROOF.md) | [Lean](LeanOeisProofs/NewFormalization/A368633.lean) |
| [A382590](https://oeis.org/A382590) | **Proved** | Tao–Jagy eventual period three for distinct prime factors | [Source](proofs/new-formalization/A382590/SOURCE.md) | [Proof](proofs/new-formalization/A382590/PROOF.md) | [Lean](LeanOeisProofs/NewFormalization/A382590.lean) |
| [A397588](https://oeis.org/A397588) | **Proved** | Defining-series bridge and divisibility by 3; supporting parity lemma has prior Lean | [Source](proofs/new-formalization/A397588/SOURCE.md) | [Proof](proofs/new-formalization/A397588/PROOF.md) | [Lean](LeanOeisProofs/NewFormalization/A397588.lean) |
| [A003161](https://oeis.org/A003161) | **Proved** | Cubic ballot-sum supercongruence modulo p^(3k) | [Source](proofs/new-formalization/A003161/SOURCE.md) | [Proof](proofs/new-formalization/A003161/PROOF.md) | [Lean](LeanOeisProofs/NewFormalization/A003161.lean) |
| [A003162](https://oeis.org/A003162) | **Proved** | Normalized ballot-sum supercongruence and all-index integrality | [Source](proofs/new-formalization/A003162/SOURCE.md) | [Proof](proofs/new-formalization/A003162/PROOF.md) | [Lean](LeanOeisProofs/NewFormalization/A003162.lean) |

## Independent Formalizations — existing Lean proofs

These two packages overlap public Lean proofs of the same assigned claims.
They remain available as independently developed work, but are excluded from
**New Formalizations** and from first-public-Lean claims. This classification
records overlap; it does not establish who completed the work first.

| OEIS / target | Outcome | Formalized result and scope | Statement / prior work | Readable proof | Lean proof |
| --- | --- | --- | --- | --- | --- |
| [A051903](https://oeis.org/A051903) | **Negative answer (C2)** | C2: no odd universal example; independent formalization, public Lean overlap | [Source](proofs/independent-formalization/A051903/SOURCE.md) | [Proof](proofs/independent-formalization/A051903/PROOF.md) | [Lean](LeanOeisProofs/IndependentFormalization/A051903.lean) |
| [A237271](https://oeis.org/A237271) | **Proved** | Carmichael bound, plus all odd composites; independent formalization, public Lean overlap | [Source](proofs/independent-formalization/A237271/SOURCE.md) | [Proof](proofs/independent-formalization/A237271/PROOF.md) | [Lean](LeanOeisProofs/IndependentFormalization/A237271.lean) |

## Reading a proof or disproof

The original conjecture and its definitions are recorded in `SOURCE.md` and the
Lean module's documentation. A proved result establishes that exact statement.
A disproof establishes its negation, with all original hypotheses and quantifiers
preserved. A counterexample must satisfy the hypotheses and violate the conclusion;
finding a suspicious numerical case alone is insufficient.
For example, disproving `∀ n, P n` means proving `¬ (∀ n, P n)`; it does not
mean proving `∀ n, ¬ P n`.

For [A060957](LeanOeisProofs/NewProofs/A060957.lean),
`PilotA060957.counterexample` verifies the explicit parameters and missing
intermediate product; `PilotA060957.not_conjecture` then proves the negation of
the complete original conjecture. The original conjecture is not imported or
asserted as an admitted theorem. A statement may also be named with a `def ... : Prop`
without asserting that it is true.

Outcome and contribution category are separate: a new disproof belongs in
**New Proofs**. A known negative answer belongs in **New Formalizations** only
when no earlier matching public Lean proof was located; otherwise it belongs in
**Independent Formalizations**. Each sequence still has one canonical Lean file and one
proof/source pair.

## Completed research not included in this release

A069004 remains a completed research result outside this release. Incomplete
attempts and results lacking a verified connection to the OEIS definition are
also excluded. A003161 and A003162 are included above with their shared Epoch
helper credited in the source notes.

## Repository layout

```text
LeanOeisProofs/
  NewProofs/                 New mathematical proofs and disproofs
  NewFormalization/          Known mathematics with new Lean coverage
  IndependentFormalization/ Known overlapping Lean proofs
proofs/
  new-proofs/                Readable proofs and exact statements
  new-formalization/         Explanations and original references
  independent-formalization/ Explanations and overlapping Lean sources
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

Original Formal Conjectures material and Wentao Li's contributions are licensed
under the [Apache License, Version 2.0](LICENSE). The Epoch-derived helper and
refinement in A003161 retain their source licensing status; see
[the provenance and scope](proofs/new-formalization/A003161/SOURCE.md).
