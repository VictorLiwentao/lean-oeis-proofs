# A proof of the OEIS A280246 conjecture

**Author:** Wentao Li

Let \(\psi(m)\) denote the sum of totatives of \(m\): for \(m\ge 1\),

\[
\psi(m)=\sum_{\substack{1\le k\le m\\ \gcd(k,m)=1}}k.
\]

Write \(\varphi\) for Euler’s totient function, and for \(n\ge 1\) put

\[
a(n)=\prod_{d\mid n}\psi(d).
\]

**Theorem.** For every integer \(n\ge 1\), \(a(n)\) is odd if and only if \(\psi(n)\) is odd.

## Pairing of totatives

The value \(\psi(1)\) is \(1\). For \(n>1\), the map \(k\mapsto n-k\) is an involution of the set \(T\) of totatives of \(n\) in \(\{1,\ldots,n\}\): a common divisor of \(k\) and \(n\) divides \(n-k\), and conversely. Neither \(0\) nor \(n\) is coprime to \(n\), so \(T\) may equally be taken as the set of residues counted by \(\varphi(n)\). In particular \(\#T=\varphi(n)\). Summing \(k\) and \(n-k\) over \(T\) therefore yields

\[
2\psi(n)=\sum_{k\in T}n=n\,\varphi(n).
\]

(The involution has a fixed point only for \(n=2\), where \(k=1\); both sides of the identity equal \(2\).) Thus \(\psi(n)\) is even if and only if \(4\mid n\,\varphi(n)\).

If \(n>2\), then \(\varphi(n)\) is even: the same involution on totatives has no fixed point, since \(n/2\) is never coprime to \(n\). Consequently, if \(n\) is even and \(n>2\), then \(4\mid n\,\varphi(n)\). Indeed, either \(4\mid n\), or else \(n=2m\) with \(m\) odd and \(m>1\), hence \(m\ge 3\). In the latter case \(\varphi(2m)=\varphi(m)\) and \(\varphi(m)\) is even, so \(n\,\varphi(n)=2m\,\varphi(m)\) is a product of two even integers. The only even \(n\) with \(\psi(n)\) odd is therefore \(n=2\), where \(\psi(2)=1\).

## Classification of odd \(\psi\)

The remaining analysis uses the standard formulae \(\varphi(p^k)=p^{k-1}(p-1)\) for a prime \(p\) and \(k\ge 1\), multiplicativity of \(\varphi\) on coprime arguments, and the fact that \(a\mid b\) implies \(\varphi(a)\mid\varphi(b)\).

If distinct odd primes \(p\) and \(q\) both divide \(n\), then \(pq\mid n\), so \(\varphi(pq)=(p-1)(q-1)\) divides \(\varphi(n)\). Each of \(p-1\) and \(q-1\) is even, hence \(4\mid\varphi(n)\).

If \(p\) is an odd prime and \(k\ge 1\), then \(\varphi(p^k)=p^{k-1}(p-1)\) with \(p^{k-1}\) odd, so \(4\mid\varphi(p^k)\) if and only if \(4\mid(p-1)\). An odd prime is congruent to \(1\) or \(3\) modulo \(4\), and \(4\mid(p-1)\) if and only if \(p\equiv 1\pmod{4}\).

Now let \(n>1\) be odd. Then \(n\) is coprime to \(4\), so \(4\mid n\,\varphi(n)\) if and only if \(4\mid\varphi(n)\). If \(n\) is not a prime power, then \(n\) has at least two distinct odd prime factors, and the preceding paragraph gives \(4\mid\varphi(n)\). If \(n=p^k\) with \(p\) an odd prime, then \(4\nmid\varphi(n)\) if and only if \(p\equiv 3\pmod{4}\). Combining this with the even case:

**Proposition.** For \(n\ge 1\), \(\psi(n)\) is odd if and only if \(n=1\), or \(n=2\), or \(n=p^k\) for a prime \(p\equiv 3\pmod{4}\) and an integer \(k\ge 1\).

The boundary cases are as follows. For \(n=1\) one has \(\psi(1)=1\). For \(n=2^a\) with \(a\ge 2\), or more generally any even \(n>2\), the pairing argument shows that \(\psi(n)\) is even. A prime \(p\equiv 1\pmod{4}\) and its powers have even \(\psi\). If two distinct odd primes divide \(n\), then \(\psi(n)\) is even.

## Divisor-closure and the product

A finite product of natural numbers is odd if and only if every factor is odd. Since \(a(n)=\prod_{d\mid n}\psi(d)\), it follows that \(a(n)\) is odd if and only if \(\psi(d)\) is odd for every positive divisor \(d\) of \(n\). In particular, if \(a(n)\) is odd then \(\psi(n)\) is odd.

For the converse, it is enough to show that the set of \(n\ge 1\) with \(\psi(n)\) odd is closed under taking positive divisors. By the classification, such an \(n\) is \(1\), or \(2\), or \(p^k\) with \(p\equiv 3\pmod{4}\). The only positive divisor of \(1\) is \(1\). The positive divisors of \(2\) are \(1\) and \(2\), both of which have odd \(\psi\). The positive divisors of \(p^k\) are \(1,p,\ldots,p^k\); here \(\psi(1)\) is odd, and each \(p^j\) with \(j\ge 1\) is a power of the same prime \(p\equiv 3\pmod{4}\), hence has odd \(\psi\) by the classification.

Thus if \(\psi(n)\) is odd, then \(\psi(d)\) is odd for every \(d\mid n\), so \(a(n)\) is odd. This proves both directions of the theorem. The domain is exactly \(n\ge 1\), as in the OEIS statement.

The identity \(2\psi(n)=n\,\varphi(n)\) for \(n>1\) is proved from the sum-of-totatives definition; it is not taken as a replacement for that definition. In particular the case \(n=1\) cannot be absorbed into the same closed form, since \(\frac12\cdot 1\cdot\varphi(1)\) is not an integer.

## Formal verification

Lean version: `leanprover/lean4:v4.34.0-rc2`, as recorded in `lean-toolchain`.

Dependencies: Mathlib and its transitive dependencies, pinned by `lake-manifest.json`.

Formal source: [`LeanOeisProofs/NewProofs/A280246.lean`](../../../LeanOeisProofs/NewProofs/A280246.lean)

Main theorem: `odd_a_iff_odd_psi`

Axiom footprint reported by Lean: `[propext, Classical.choice, Quot.sound]`

No custom mathematical axioms are introduced. The general theorem contains no `sorry`, `admit`, `sorryAx`, custom axiom, or `native_decide` proof.
