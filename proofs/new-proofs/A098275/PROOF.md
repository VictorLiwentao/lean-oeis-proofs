# A proof of the OEIS A098275 conjecture

**Author:** Wentao Li

Let \(C(x,y)\) denote the ordinary binomial coefficient, with the convention \(C(x,y)=0\) for \(y>x\). For each integer \(n\ge 0\), define

\[
a(n)=\sum_{i=0}^{n}\sum_{j=0}^{n}
C(n,i)^{2}\,C(n,j)^{2}\,C(n+i,n)\,C(i+j,i).
\]

**Theorem.** For every integer \(n\ge 0\), one has \((n+1)\mid a(n)\).

Write \(\mathrm{Cat}(i)=C(2i,i)/(i+1)\) for the \(i\)-th Catalan number. The identity \((i+1)\,\mathrm{Cat}(i)=C(2i,i)\) exhibits \(\mathrm{Cat}(i)\) as an integer.

## Vandermonde and the contracted inner sum

Chu–Vandermonde gives \(C(i+j,j)=\sum_{a}C(i,a)\,C(j,j-a)\). Since \(C(j,j-a)=C(j,a)\) for \(a\le j\), and both \(C(j,j-a)\) and \(C(j,a)\) vanish for \(a>j\), one obtains the symmetric form

\[
C(i+j,i)=\sum_{k}C(i,k)\,C(j,k).
\]

Terms with \(k>\min(i,j)\) vanish, so the sum may be taken over \(0\le k\le n\) whenever \(0\le i,j\le n\).

Next, for \(0\le k\le n\),

\[
\sum_{j=0}^{n}C(n,j)^{2}\,C(j,k)=C(n,k)\,C(2n-k,n).
\]

Indeed, the summand vanishes for \(j<k\). For \(k\le j\le n\) the identity \(C(n,j)\,C(j,k)=C(n,k)\,C(n-k,j-k)\) holds, both sides being \(n!/(k!\,(j-k)!\,(n-j)!)\). Thus the left-hand side is

\[
C(n,k)\sum_{j=k}^{n}C(n,j)\,C(n-k,j-k)
=C(n,k)\sum_{j=k}^{n}C(n,n-j)\,C(n-k,j-k).
\]

The change of index \(a=n-j\) converts the remaining sum into a Chu–Vandermonde convolution with \(a+b=n-k\), hence into \(C(n+(n-k),n-k)=C(2n-k,n-k)=C(2n-k,n)\).

Substituting the Vandermonde expansion into the definition of \(a(n)\) and exchanging the three finite sums therefore yields

\[
a(n)=\sum_{i=0}^{n}\sum_{k=0}^{n}
\Bigl(C(n,i)^{2}\,C(n+i,n)\,C(i,k)\Bigr)
\cdot\Bigl(C(n,k)\,C(2n-k,n)\Bigr).
\]

## Ballot divisibility and the Catalan factor

The adjacent-binomial identity \(C(m,r+1)\,(r+1)=C(m,r)\,(m-r)\), applied with \(m=2n-k\) and \(r=n\), gives

\[
(n+1)\,C(2n-k,n+1)=(n-k)\,C(2n-k,n),
\]

where \(m-r=n-k\ge 0\). Rearranging,

\[
(k+1)\,C(2n-k,n)=(n+1)\bigl(C(2n-k,n)-C(2n-k,n+1)\bigr).
\]

Since \(n-k\le n+1\), the difference on the right is a nonnegative integer (a classical ballot number). In particular,

\[
n+1\mid (k+1)\,C(2n-k,n)\qquad\text{for }0\le k\le n.
\]

This is the source of the factor \(n+1\). It does not by itself divide the summand, because the complementary factor \(C(n,i)^{2}\,C(n+i,n)\,C(i,k)\) need not be divisible by \(k+1\) in any naive way that would cancel the remaining obstruction. The cancellation is supplied termwise by a Catalan factorization.

**Lemma.** For all \(n,i,k\ge 0\),

\[
C(n,i)^{2}\,C(n+i,n)\,C(i,k)
=(k+1)\,C(n,i)\,C(n+i,2i)\,\mathrm{Cat}(i)\,C(i+1,k+1).
\]

To see this, use three standard identities: \(C(n+i,n)=C(n+i,i)\); the chain \(C(n+i,2i)\,C(2i,i)=C(n+i,i)\,C(n,i)\); and \((k+1)\,C(i+1,k+1)=(i+1)\,C(i,k)\), which continues to hold when \(k>i\) because both sides vanish. Starting from the right-hand side,

\begin{align*}
(k+1)\,C(n,i)\,C(n+i,2i)\,\mathrm{Cat}(i)\,C(i+1,k+1)
&=C(n,i)\,C(n+i,2i)\,\mathrm{Cat}(i)\cdot(i+1)\,C(i,k)\\
&=C(n,i)\,C(n+i,2i)\,C(2i,i)\,C(i,k)\\
&=C(n,i)\cdot C(n+i,i)\,C(n,i)\cdot C(i,k)\\
&=C(n,i)^{2}\,C(n+i,n)\,C(i,k).
\end{align*}

No division is performed: \(\mathrm{Cat}(i)\) enters only through \((i+1)\,\mathrm{Cat}(i)=C(2i,i)\).

## Assembly

Inserting the lemma into the reorganized double sum produces, for each pair \((i,k)\), a factor of \(k+1\) on the \(i\)-side. Grouping that factor with \(C(2n-k,n)\) gives a product \((k+1)\,C(2n-k,n)\), which is divisible by \(n+1\) by the ballot identity. Every remaining factor is an integer. Hence each summand of the reorganized expression is divisible by \(n+1\), and so is \(a(n)\).

The argument applies for every \(n\ge 0\), including \(n=0\). All sums run over \(\{0,\ldots,n\}\), matching the original OEIS formula; binomial coefficients with lower index exceeding the upper index vanish, so there is no endpoint adjustment. The original double sum is never replaced by a recurrence or by an equivalent generating function.

## Formal verification

Lean version: `leanprover/lean4:v4.34.0-rc2`, as recorded in `lean-toolchain`.

Dependencies: Mathlib and its transitive dependencies, pinned by `lake-manifest.json`.

Formal source: [`LeanOeisProofs/NewProofs/A098275.lean`](../../../LeanOeisProofs/NewProofs/A098275.lean)

Main theorem: `a098275_divisible`

Axiom footprint reported by Lean: `[propext, Classical.choice, Quot.sound]`

No custom mathematical axioms are introduced. The general theorem contains no `sorry`, `admit`, `sorryAx`, custom axiom, or `native_decide` proof.
