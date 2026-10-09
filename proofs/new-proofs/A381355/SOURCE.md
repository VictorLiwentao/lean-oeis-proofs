# A381355: source and contribution

**Category: New Proofs.** Proof and Lean formalization by **Wentao Li**, with AI assistance disclosed in [PROVENANCE.md](../../../PROVENANCE.md).

## Exact target

[OEIS A381355](https://oeis.org/A381355), introduced by **Paul D. Hanna on March 11, 2025**, defines \(A(x)=xF'(x)/F(x)\), where \(F\) is the generating function of [A381353](https://oeis.org/A381353). The latter starts with coefficients 1, 1 and satisfies \([x^n]F^{p_n}=0\) for \(n>1\), where \(p_n\) is the nth prime, with \(p_1=2\).

The target is \(p_n\mid[x^n]A(x)\) for every \(n>1\). The Lean definition `primeN n = Nat.nth Nat.Prime (n - 1)` uses exactly this one-based convention. Coefficients are integers, so negative terms are included.

The [Lean source](../../../LeanOeisProofs/NewProofs/A381355.lean) constructs the integral recurrence used by OEIS's PARI program, proves every defining prime-power coefficient equation, defines the logarithmic derivative using the unit inverse of \(F\), and proves `A381355.primeN_dvd_a`. The added theorem `F_unique` proves uniqueness among integral series with the stated initial coefficients and equations. The [readable proof](PROOF.md) explains all of these steps.

## Research provenance and publication changes

The source is `Ai4mathLab/Research/A381355.lean` at commit `82f7a104fb3f46c6e76f433e9682ad7f65b9402c` of the author's private `ai4math-lab` research history. The public file names Wentao Li in its copyright and author headers and retains Apache 2.0 licensing.

The September 12 research record includes an independent skeptic check. A direct compiler recheck passed on October 2. For publication on October 9, Wentao Li was credited as author, and `F_unique` was added to make the uniqueness argument explicit in Lean. The original sequence definitions and divisibility proof are unchanged. Axiom-print commands also cover the generating-function bridge and uniqueness theorem.

See the [current verification report](../../../verification/README.md) for the publication copy's compiler and axiom checks.

## Public-source check — October 9, 2026

The public OEIS entry still labels the divisibility statement a conjecture. Identifier searches for `A381355` with proof/Lean/conjecture terms found no exact independent proof. No matching target path was present in:

- [Google DeepMind Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/tree/a924684979d41f543898ec43b940b74e124315d9), including a search of open and closed issues/PRs;
- [Epoch LeanOpenProblems](https://github.com/epoch-research/LeanOpenProblems/tree/0cc3d23c6f765385efdd221b222296292c330098);
- [Epoch's published results](https://github.com/epoch-research/LeanOpenProblems-results/tree/fd09021e79869476ef83cda231312f1a2a89c8d7) or [AlphaProof Nexus results](https://github.com/google-deepmind/alphaproof-nexus-results/tree/0647711a71183c1ea492ad60860776617ce1ea88).

The Epoch results commit is unchanged from the complete October 2 inspection of its 24 run subtrees; those saved trees were searched again. GitHub code search also returned no indexed match, but misses even some known public work, so that is weak negative evidence. The binomial divisibility ingredient is classical. No exact earlier assembly for this sequence was located; this is a bounded finding, not an exhaustive priority guarantee.

This publication is in Wentao Li's repository, not an accepted DeepMind or Epoch contribution. An upstream DeepMind contribution would require adding the missing statement and an external proof link under its contribution rules.
