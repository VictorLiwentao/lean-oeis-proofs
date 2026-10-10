# A003162: binomial-sum supercongruence

Author: Wentao Li

The shared general cubic identity gives the explicit integer quotient
\[
\mathrm{OeisA3162.a}(m)=4\binom m{\lfloor m/2\rfloor}^{2}
-3\sum_{j=0}^{m}\binom j{\lfloor m/2\rfloor}
\binom j{m-\lfloor m/2\rfloor}.
\]
The central binomial denominator is positive. Hence the rational source equals
the cast of this integer, and its reduced denominator is one. This includes
$m=0$ and uses no upstream admitted integrality theorem.

Write $H_N=\binom{2N-1}{N-1}$ and $S_N=\sum_{j=0}^{N-1}\binom{N-1+j}{j}^2$. At $m=2N-1$, the reduced numerator is the integer quotient itself. The square
sum telescope therefore proves
\[
2\,\mathrm{OeisA3162.b}(N).\mathrm{num}=3S_N-H_N^2.
\]
Insert the two proved arithmetic towers from the sibling A003161 development,
then cancel two modulo $p^{3k}$. This gives the exact frozen reduced-numerator
conclusion for all positive $n,k$ and primes $p\ge5$.


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

Canonical module: `LeanOeisProofs.NewFormalization.A003162`.
Main theorem: `B02R2A003162.conjecture`.
Axioms: `propext`, `Classical.choice`, `Quot.sound`.
The module also proves `B02R2A003162.a_is_integer` for every natural index.

Verification records: [current report](../../../verification/README.md).
