# A375439: source and contribution

**Category: New Proofs.** Proof and Lean formalization by **Wentao Li**, with AI assistance disclosed in [PROVENANCE.md](../../../PROVENANCE.md).

## Exact target

[OEIS A375439](https://oeis.org/A375439), introduced by **Paul D. Hanna on August 21, 2024**, defines a series with constant term zero by

\[
A(x)=x+x^2+(2A(x)^3+A(x^3))/3.
\]

The target is the parity conjecture: for every \(n\geq1\), its coefficient \(a_n\) is odd if and only if \(n=3^k\) or \(n=2\cdot3^k\) for some \(k\geq0\). This does not address the separate asymptotic formula on OEIS.

The [Lean source](../../../LeanOeisProofs/NewProofs/A375439.lean) constructs the coefficient recurrence, proves the division by 3 exact, and proves the cleared generating-function equation at every index. The [readable proof](PROOF.md) explains why that triangular recurrence uniquely specifies the OEIS series. Main theorem: `A375439.a_odd_iff_A038754`.

## Research provenance and publication changes

The source is the author's research file `Ai4mathLab/Research/A375439.lean` at commit `d57c795e5e00bf6e5888d507b0bb8c33ce22af0b` of the private `ai4math-lab` research history. The public file names Wentao Li in its copyright and author headers and retains Apache 2.0 licensing.

Publication changes use Wentao Li in the copyright and author headers and remove eight optional `native_decide` numerical examples. The mathematical definitions, lemmas and general proof are unchanged. Those examples were not dependencies of the main theorem. The published file contains no `native_decide`.

The source has a saved independent statement-fidelity audit and passed a direct compiler recheck on October 2. The publication copy was rebuilt with the pinned compiler on October 9, 2026; see the [current report](../../../verification/README.md).

## Public-source check — October 9, 2026

The public OEIS page still labels this parity statement a conjecture. Identifier searches for `A375439` with proof/Lean/conjecture terms found no exact independent proof. No matching target path was present in:

- [Google DeepMind Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/tree/a924684979d41f543898ec43b940b74e124315d9), including a search of open and closed issues/PRs;
- [Epoch LeanOpenProblems](https://github.com/epoch-research/LeanOpenProblems/tree/0cc3d23c6f765385efdd221b222296292c330098);
- [Epoch's published results](https://github.com/epoch-research/LeanOpenProblems-results/tree/fd09021e79869476ef83cda231312f1a2a89c8d7) or [AlphaProof Nexus results](https://github.com/google-deepmind/alphaproof-nexus-results/tree/0647711a71183c1ea492ad60860776617ce1ea88).

The Epoch results commit is unchanged from the complete October 2 inspection of its 24 run subtrees; those saved trees were searched again. GitHub code search also returned no indexed match, but misses even some known public work, so that is weak negative evidence. These bounded checks support the repository's contribution classification; they cannot establish exhaustive mathematical priority or exclude unpublished work.

This publication is in Wentao Li's repository. It has not been merged into either upstream collection. Because DeepMind currently has no statement for this target, an upstream contribution would first need to add the statement and an external proof link under its contribution rules.
