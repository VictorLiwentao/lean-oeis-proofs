# A proof of the OEIS A220119 conjecture

**Author:** Wentao Li

Let \(C(x,y)\) denote the ordinary binomial coefficient, vanishing when the lower index exceeds the upper index. For each integer \(n\ge 0\), define

\[
a(n)=\sum_{j=0}^{n}\sum_{k=0}^{n}
C(n,j)^{2}\,C(n,k)^{2}\,C(n+j,n)\,C(n+k,n)\,C(j+k,n).
\]

**Theorem.** For every integer \(n>0\), one has \((n+1)(n+2)\mid a(n)\).

The restriction \(n>0\) is essential: \(a(0)=1\), while \(2\nmid 1\). The two consecutive factors are established separately. The factor \(n+1\) divides every original summand. The factor \(n+2\) is obtained from a Vandermonde convolution, an exact relation between two inner sums, and a prime-power analysis of reflection pairs; direct cancellation of \(r(r-1)\) against \(n+2\) is not always available, and the primes \(2\) and \(3\) require additional congruences.

Throughout, write \(v_p\) for the \(p\)-adic valuation.

## The weight \(U(n,r)\) and the convolution

For \(0\le r\le n\), define

\[
U(n,r)=\sum_{j=0}^{n}C(n,j)^{2}\,C(n+j,n)\,C(j,r).
\]

Chu–Vandermonde, with complementary lower index, gives

\[
C(j+k,n)=\sum_{r=0}^{n}C(j,r)\,C(k,n-r).
\]

Terms outside the natural binomial ranges vanish, so the displayed range is exact for the finite sums at hand. Substituting into \(a(n)\) and exchanging the three finite sums produces the convolution

\[
a(n)=\sum_{r=0}^{n}U(n,r)\,U(n,n-r).
\]

The Catalan factorization already used for OEIS A098275 applies termwise inside \(U(n,r)\):

\[
C(n,j)^{2}\,C(n+j,n)\,C(j,r)
=(r+1)\,C(n,j)\,C(n+j,2j)\,\mathrm{Cat}(j)\,C(j+1,r+1).
\]

Hence \((r+1)\mid U(n,r)\). Independently, \(C(n,j)\,C(j,r)=C(n,r)\,C(n-r,j-r)\) for \(r\le j\), and the summand vanishes for \(j<r\), so \(C(n,r)\mid U(n,r)\).

## The auxiliary sum \(V(n,r)\)

For \(r\ge 2\), put

\[
V(n,r)=\sum_{j=r}^{n}C(n,j)^{2}\,C(n+j,j-2)\,C(j-2,r-2).
\]

Two adjacent-binomial identities relate \(U\) to \(V\). First, for \(2\le r\le j\),

\[
r(r-1)\,C(j,r)=j(j-1)\,C(j-2,r-2).
\]

Second, for \(j\ge 2\),

\[
j(j-1)\,C(n+j,n)=(n+1)(n+2)\,C(n+j,j-2).
\]

(The second identity is the composition of \(j\,C(n+j,n)=(n+1)\,C(n+j,n+1)\) with \((j-1)\,C(n+j,n+1)=(n+2)\,C(n+j,n+2)\), followed by the symmetry \(C(n+j,n+2)=C(n+j,j-2)\).) Substituting these into the sum for \(U(n,r)\) (whose support is \(r\le j\le n\)) yields the exact relation

\[
r(r-1)\,U(n,r)=(n+1)(n+2)\,V(n,r)\qquad(2\le r\le n).
\]

In particular,

\[
\frac{n+2}{\gcd\bigl(n+2,\,r(r-1)\bigr)}\Bigm|\,U(n,r).
\]

For \(r=0\) or \(r=1\) the displayed divisor is \(1\). Thus if a prime power \(p^e\) divides \(n+2\) and \(p\) does not divide \(r(r-1)\), the full power \(p^e\) divides \(U(n,r)\). If \(p\) does divide \(r(r-1)\), this cancellation loses some or all of the \(p\)-part of \(n+2\).

That loss is not merely formal. The three divisibilities \((r+1)\mid U(n,r)\), \(C(n,r)\mid U(n,r)\), and \(\frac{n+2}{\gcd(n+2,r(r-1))}\mid U(n,r)\) do not by themselves imply \((n+1)(n+2)\mid U(n,r)U(n,n-r)\). Abstract values \(X_0=1\), \(X_4=5\) at \(n=4\) satisfy all three constraints, yet \(30\nmid 2X_0X_4\). The missing factors of \(2\) and \(3\) must come from genuine properties of the actual weights \(U(n,r)\).

## Lucas congruences

Lucas’s theorem for \(p=2\) asserts that \(C(2a,2b+1)\) is even. Consequently, if \(n\) is even and \(r\) is odd, then \(2\mid U(n,r)\). Indeed, in each summand, either \(j\) is odd, in which case \(C(n,j)\) is even, or \(j\) is even, in which case \(C(j,r)\) is even. The same argument, applied to \(C(j-2,r-2)\) after writing \(j-2\) even and \(r-2\) odd, shows that if additionally \(r\ge 3\), then \(2\mid V(n,r)\).

For \(p=3\), the one-digit Lucas congruences are

\begin{align*}
C(3a+1,3b)&\equiv C(a,b),&
C(3a+1,3b+1)&\equiv C(a,b),&
C(3a+1,3b+2)&\equiv 0\pmod{3},
\end{align*}

together with \(C(3a,3b)\equiv C(a,b)\), \(C(3a+2,3b+1)\equiv 2C(a,b)\), and \(C(3a+2,3b+2)\equiv C(a,b)\pmod{3}\). If \(n\equiv 1\pmod{3}\) and \(r\equiv 0\pmod{3}\), write \(n=3N+1\) and \(r=3R\), and split the sum for \(U(n,r)\) into residue classes of \(j\) modulo \(3\). The class \(j\equiv 2\pmod{3}\) vanishes. The classes \(j=3J\) and \(j=3J+1\) have the same higher-digit factor \(C(N,J)^{2}\,C(N+J,N)\,C(J,R)\) and unit-digit factors \(1\) and \(2\) respectively, so they cancel modulo \(3\). The finite range \(0\le j\le n\) is a complete collection of such pairs, including the final pair \(j=3N,\,3N+1\). Hence \(3\mid U(n,r)\). The same pairing, with lower indices shifted by \(2\), gives \(3\mid V(n,r)\) when additionally \(r\ge 3\) (so that \(R\ge 1\) and the truncated endpoints remain well-defined).

Combined with \(r(r-1)U(n,r)=(n+1)(n+2)V(n,r)\), this yields a strengthened \(3\)-adic statement: if \(3\mid n+2\) and \(3\mid r\), then

\[
\frac{3(n+2)}{\gcd\bigl(n+2,\,r(r-1)\bigr)}\Bigm|\,U(n,r).
\]

For \(r=0\) this is the Lucas conclusion \(3\mid U(n,0)\). For \(r>0\) one compares \(3\)-adic valuations in the \(U\)--\(V\) identity: \(3\nmid n+1\) (since \(n+2\equiv 0\pmod{3}\)), while \(3\mid V(n,r)\), so the extra factor of \(3\) on the left after cancelling \(\gcd(n+2,r(r-1))\) is accounted for on the right.

## Reflection pairs and the factor \(n+2\)

Write \(M=n+2\) and pair the convolution as \(r\leftrightarrow s\) with \(s=n-r\). For \(r\neq s\) the paired contribution is \(2U(n,r)U(n,s)\). We show that \(M\) divides this product, prime power by prime power. Let \(p^e\) be the exact \(p\)-part of \(M\).

### Primes \(p\ge 5\)

The residues \(r\) and \(s\) cannot both lie in \(\{0,1\}\pmod{p}\). Indeed \(r+s=n\equiv -2\pmod{p}\), so the four combinations in \(\{0,1\}^{2}\) would force \(2\equiv 0\), \(3\equiv 0\), or \(4\equiv 0\pmod{p}\), all incompatible with \(p\ge 5\). Therefore \(p\) fails to divide at least one of \(r(r-1)\) and \(s(s-1)\). The corresponding index is then at least \(2\) (the residues \(0\) and \(1\) being precisely the cases in which \(p\) divides \(t(t-1)\)), and the gcd-cancellation supplies the full power \(p^e\) in that weight.

### The prime \(p=3\)

Here \(n\equiv 1\pmod{3}\). The possible residue pairs \((r,s)\) modulo \(3\) with \(r+s\equiv 1\pmod{3}\) are \((2,2)\) and \(\{0,1\}\) in either order.

If \(r\equiv 2\pmod{3}\), then \(3\nmid r(r-1)\), so gcd-cancellation supplies the full power \(3^e\) in \(U(n,r)\).

If \(\{r,s\}\equiv\{0,1\}\pmod{3}\), write \(x\equiv 0\) and \(y\equiv 1\pmod{3}\). Lucas gives \(3\mid U(n,x)\). If \(e=1\), this is the required power. If \(e\ge 2\), then \(x+(y-1)=M-3\), and \(v_3(M-3)=1\). In particular the two valuations \(v_3(x)\) and \(v_3(y-1)\) cannot both be at least \(2\).

- If \(v_3(x)=1\), then \(v_3\bigl(\gcd(M,x(x-1))\bigr)=1\) (since \(x\equiv 0\) implies \(3\nmid x-1\)), and the strengthened factor supplies \(3\cdot 3^{e-1}=3^e\) in \(U(n,x)\).
- If \(v_3(x)\ge 2\), then \(v_3(y-1)=1\). Gcd-cancellation on \(U(n,y)\) supplies \(3^{e-1}\), while Lucas on \(U(n,x)\) supplies the remaining factor \(3\).
- If \(x=0\), then \(y-1=M-3\) has valuation \(1\). Gcd-cancellation on \(U(n,y)\) again supplies \(3^{e-1}\), and Lucas on \(U(n,0)\) supplies the remaining \(3\).

### The prime \(p=2\)

If \(e\ge 1\), then \(M\) is even, so \(n\) is even, and the explicit factor \(2\) in the paired product \(2U(n,r)U(n,s)\) accounts for one power of \(2\). If \(e=1\) there is nothing further to prove. Assume \(e\ge 2\), so \(4\mid M\).

If \(r\) is even, then \(s\) is even. For \(r=0\) one has \(s=M-2\equiv 2\pmod{4}\), hence \(v_2(s)=1\) and \(s\ge 2\); gcd-cancellation supplies \(2^{e-1}\) in \(U(n,s)\). The case \(s=0\) is symmetric. If \(r,s\ge 2\) are both even, then \(\min\bigl(v_2(r),v_2(s)\bigr)\le 1\): otherwise \(r\equiv s\equiv 0\pmod{4}\) would give \(M=r+s+2\equiv 2\pmod{4}\), contradicting \(4\mid M\). Gcd-cancellation on the factor of smaller valuation therefore supplies at least \(2^{e-1}\).

If \(r\) is odd, then \(s\) is odd. Lucas gives that both \(U(n,r)\) and \(U(n,s)\) are even, so the product \(2U(n,r)U(n,s)\) is already divisible by \(8\). This finishes the case \(e\le 3\). Assume \(e\ge 4\), so \(8\mid M\).

- If \(r=1\), then \(s=M-3\) and \(v_2(s-1)=v_2(M-4)=2\). Gcd-cancellation supplies \(2^{e-2}\) in \(U(n,s)\). Combined with the outer factor \(2\) and the evenness of \(U(n,1)\), this yields \(2^e\). The case \(s=1\) is symmetric.
- If \(r\equiv 3\pmod{4}\) and \(r\ge 3\), then \(v_2(r-1)=1\). Gcd-cancellation supplies \(2^{e-1}\) in \(U(n,r)\).
- If \(r\equiv 1\pmod{4}\) and \(r\neq 1\), then both weights are even by Lucas, and \(\min\bigl(v_2(r-1),v_2(s-1)\bigr)\le 2\): otherwise \(r-1\equiv s-1\equiv 0\pmod{8}\) would give \(M=(r-1)+(s-1)+4\equiv 4\pmod{8}\), contradicting \(8\mid M\). Gcd-cancellation therefore supplies at least \(2^{e-2}\) in one weight, which together with the outer \(2\) and the remaining even weight yields \(2^e\).

In every case, \(M\mid 2U(n,r)U(n,s)\).

## The middle term

If \(n=2h\) with \(h>0\), the unpaired term is \(U(n,h)^{2}\). Here \(M=2(h+1)\) and \((h+1)\mid U(n,h)\). If \(h\) is odd, then \(h+1\) is even. More precisely \(v_2(M)=1+v_2(h+1)\) and \(v_2\bigl((h+1)^{2}\bigr)=2v_2(h+1)\), so \(v_2\bigl((h+1)^{2}\bigr)\ge v_2(M)\) because \(v_2(h+1)\ge 1\). The odd part of \(M\) already divides \(h+1\). Thus \(M\mid(h+1)^{2}\mid U(n,h)^{2}\).

If \(h\) is even, then \(h+1\) is odd, hence coprime to \(2\). The central binomial coefficient \(C(2h,h)\) is even for \(h>0\), and \(C(2h,h)\mid U(n,h)\), so \(2\mid U(n,h)\). Combined with \((h+1)\mid U(n,h)\), this gives \(M\mid U(n,h)\), and therefore \(M\mid U(n,h)^{2}\).

The convolution, the reflection pairs, and the middle term together prove \(n+2\mid a(n)\).

## The factor \(n+1\)

The factor \(n+1\) is most directly visible in the original summands. Write

\[
T_{n,j,k}=C(n,j)^{2}\,C(n,k)^{2}\,C(n+j,n)\,C(n+k,n)\,C(j+k,n)
\]

and \(D=C(n+j,n)\,C(n+k,n)\,C(j+k,n)\). If \(j+k<n\), then \(T_{n,j,k}=0\). Otherwise set \(z=j+k-n\), so \(z\ge 0\) and \(j+k-z=n\). The adjacent-binomial identities

\[
j\,C(n+j,n)=(n+1)\,C(n+j,n+1),\qquad
k\,C(n+k,n)=(n+1)\,C(n+k,n+1),\qquad
z\,C(j+k,n)=(n+1)\,C(j+k,n+1)
\]

show that \(n+1\) divides \(jD\), \(kD\), and \(zD\). Hence \(n+1\) divides \((j+k)D\) and therefore divides \((j+k-z)D=nD\). Subtracting this from the trivial divisibility \(n+1\mid(n+1)D\) gives \(n+1\mid D\), and thus \(n+1\mid T_{n,j,k}\). Summing over \(j\) and \(k\) yields \(n+1\mid a(n)\). This argument does not require \(n>0\).

## Conclusion

Since \(\gcd(n+1,n+2)=1\), the two divisibilities combine to give \((n+1)(n+2)\mid a(n)\) for every \(n>0\).

The argument manipulates the original double sum (and finite reorganizations thereof). It does not replace \(a(n)\) by a recurrence-defined sequence.

## Formal verification

Lean version: `leanprover/lean4:v4.34.0-rc2`, as recorded in `lean-toolchain`.

Dependencies: Mathlib and its transitive dependencies, pinned by `lake-manifest.json`.

Formal source: [`LeanOeisProofs/A220119.lean`](../../LeanOeisProofs/A220119.lean)

Main theorem: `a220119_divisible`

The file imports [`LeanOeisProofs/A098275.lean`](../../LeanOeisProofs/A098275.lean) for the Catalan-factor identity used to prove \((r+1)\mid U(n,r)\).

Axiom footprint reported by Lean: `[propext, Classical.choice, Quot.sound]`

No custom mathematical axioms are introduced. The general theorem contains no `sorry`, `admit`, `sorryAx`, custom axiom, or `native_decide` proof.
