# A003161: binomial-sum supercongruence

Author: Wentao Li

For positive $N$, let
\[
H_N=\binom{2N-1}{N-1},\qquad
S_N=\sum_{j=0}^{N-1}\binom{N-1+j}{j}^2,\qquad
R_N=\mathrm{OeisA3161.b}(N).
\]
The proof has two parts: an exact normalization and two arithmetic congruences.

## Exact normalization

The cubic ballot normalization proves the general cubic ballot identity for every $n\le m$:
\[
\sum_{k=0}^n\left(\binom mk-\binom m{k-1}\right)^3
=4\binom mn^3-3\binom mn\sum_{j=0}^m\binom jn\binom j{m-n}.
\]
The coefficient at $k=-1$ means zero. The proof first verifies the two
Amdeberhan–Ekhad certificates for Monthly Problem 11844. Their weighted sums
satisfy the same recurrence in $m$ and agree at $m=n$. A further telescope gives
the displayed cubic identity. The corrected certificates are checked directly;
no printed typographical error is assumed.

Pascal's identity gives the square telescope. At $m=2N-1$, this yields
\[
2R_N=H_N(3S_N-H_N^2).
\]
`raw_cast` proves nonnegativity of every ballot difference in the source sum.
Thus its natural-number truncation loses nothing, and the identity concerns the
exact frozen definition.

## Arithmetic towers

`CentralCongruence.halfCentral_tower` follows from the credited public Epoch
binomial-scaling helper by applying it to $\binom{2N}{N}=2H_N$ and cancelling two.

For $S_N$, write $B(N,j)=\binom{N+j-1}{j}$. The proof of
`ShiftedCongruence.shiftedSquares_tower` separates indices divisible by $p$ from
indices prime to $p$.

For the unit indices, assume $p^r\mid N$. Use integer representatives of inverses
modulo $p^{3r}$, with inverse-square weight zero at multiples of $p$.
The inverse-square sum over a prefix of length divisible by $p^s$ is divisible
by $p^s$. Put $w(j)=\binom{N+j-1}{j-1}^2$ for $j>0$ and $w(0)=1$.
The adjacent-binomial identity shows that each weight jump is divisible by
$p^{\max(0,r-v_p(j))}$. Summation by parts gives
$p^r\mid\sum_{j<N}w(j)j^{-2}$, where multiples of $p$ have zero weight.
Since $B(N,j)^2=N^2w(j)j^{-2}$ modulo $p^{3r}$ at unit indices, their complete sum
vanishes modulo $p^{3r}$. This is `ShiftedUnits.shifted_units_dvd`.

For divisible indices, `RefinedKazan.kazan_refined` retains separate valuations
in the public product-expansion proof. It gives exponent
$3+\max(v_pB,v_pL)+2\min(v_pB,v_pL)$, plus the binomial coefficient's valuation.
The relation $(N+j)B(N,j)=N\binom{N+j}{N}$ transfers this to the shifted
coefficients. After squaring, `ShiftedScaling.shifted_square_scale_dvd` proves
\[
B(Np,jp)^2\equiv B(N,j)^2\pmod{p^{3(r+1)}}\quad\text{if }p^r\mid N.
\]
Valuation identities account for cancellation of $N+j$; it is not assumed to be
a unit. Reindex the divisible indices and add the unit-index cancellation.
This proves $S_{np^k}\equiv S_{np^{k-1}}\pmod{p^{3k}}$ for all positive $n,k$
and primes $p\ge5$, with no coprimality condition on $n$.

## Transfer and checks

Substitute the two proved towers into the exact normalization and cancel two.
`conjecture_of_coster` remains as an algebraic transfer lemma, but the final
`conjecture` supplies both of its hypotheses with proved theorems.


## Attribution and verification

The argument uses classical binomial congruences of Jacobsthal and Kazandzidis,
Coster's supercongruences, and cubic ballot identities of Miana, Ohtsuka and
Romero and Amdeberhan and Ekhad. The shared Lean binomial helper is adapted
from Epoch Research's published A141057 solution. Wentao Li developed the
normalization, refinements, target proofs, and integration with AI assistance.
See [SOURCE.md](SOURCE.md) for the exact sources.

Lean: `4.34.0-rc2`; Mathlib and dependencies are pinned in the repository manifest.
The complete source target is checked by Comparator, including dependent
definitions, permitted axioms, and replay in Lean's kernel.

Canonical module: `LeanOeisProofs.NewFormalization.A003161`.
Main theorem: `B02R2A003161.conjecture`.
Axioms: `propext`, `Classical.choice`, `Quot.sound`.

Verification records: [current report](../../../verification/README.md).
