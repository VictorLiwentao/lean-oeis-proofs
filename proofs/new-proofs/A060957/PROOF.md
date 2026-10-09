# A counterexample to the A060957 interpolation conjecture

Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Wentao Li.
Licensed under Apache 2.0; see the repository LICENSE.

Original conjecture: Yan Sheng Ang.
Original Lean formalization: The Formal Conjectures Authors.
New proof development and write-up: Wentao Li.

**Status: proved disproof, with a Lean-checked counterexample.** The research
record includes a successful exact-statement audit and a separate September 12
review; the publication module is checked again on October 9, 2026. The final
declarations are `PilotA060957.counterexample` and `PilotA060957.not_conjecture`.

The construction and the new proof development are by Wentao Li. AI assistance
was used for mathematical exploration, deterministic programs, and Lean code.
The supporting-face idea is related to Bach, Eisenbrand, and Pinchasi (2023),
cited below; their prior results are not attributed to the new author.

## The exact statement and notation

For a natural number n, let

$$\mathcal P(n)=\left\{\prod_{x\in S}x:S\subseteq\{1,\ldots,n\}\right\}.$$

The subsets are finite sets: a factor can occur at most once. The empty product
is 1. This is precisely `OeisA60957.productsOfSubsets n`, included unchanged in the publication module.
Yan Sheng Ang's conjecture of 13 February 2020 says: for all natural numbers
n and p, if p is prime and p≤n, then for all natural numbers m and a, if
m and p^a m belong to P(n), every p^k m with natural 0<k<a belongs to P(n).
There is no hypothesis that m is coprime to p. The target is exactly
`OeisA60957.conjecture`, not a parity or counting identity associated with the
same OEIS entry.

We construct n,p,m with a=6 and k=5. The lower and upper endpoint subsets
will be given explicitly by finite-set formulas. Unique prime factorization
and a supporting face reduce nonmembership of the intermediate value to a
28-element subset-product problem.

For a prime q and positive x, write v_q(x) for the exponent of q in x.
It is additive on products. Every sum and product below has the displayed
finite index range. In Lean, these valuations are `Nat.factorization`, and
`primeMonomial` denotes a product of indexed prime powers. All Lean declaration
names in this document are in namespace `PilotA060957` unless stated otherwise.

## Exact parameters and atoms

Put

 p = 9304595970494411110326649421962412033 = 7*2^120+1,
 H = 2^189,
 n = p*H
   = 7300736939182798133186109347259211329993100439822050617759401048387060880364593185519300509696.

Primality of p has a Lucas certificate with base 3: 3^(p-1)=1 modulo p,
whereas 3^((p-1)/2) and 3^((p-1)/7) are not 1 modulo p. The only prime
factors of p-1 are 2 and 7. Explicitly, the three residues are

```
3^(p-1) mod p       = 1
3^((p-1)/2) mod p   = 9304595970494411110326649421962412032
3^((p-1)/7) mod p   = 7117895553901548798585914943695356519
```

Here is why this certificate proves primality, rather than probable primality.
The first equality makes 3 a unit modulo p. Its multiplicative order d divides
p−1. If d were a proper divisor of p−1, then d would divide (p−1)/q for some
prime divisor q of p−1. The other two residues exclude this, so d=p−1.
The first p−1 powers of 3 are therefore distinct nonzero unit residues, and
exhaust all nonzero residues modulo p. Every integer from 1 to p−1 is a unit,
which excludes any proper prime divisor of p. Thus p is prime.

The residues can be reproduced by repeated squaring: start with u_0=a mod p
and set u_(t+1)=u_t^2 mod p. Induction gives u_t=a^(2^t) mod p. Use
(a,t)=(2187,120), (2187,119), and (3,120), respectively, for the three tests
above, since 2187=3^7.
`iteratedSquareMod_spec` proves this repeated modular squaring calculation correct by induction;
`circuitPrime_prime` combines its kernel-reduced residues with Mathlib's Lucas
criterion. All small auxiliary primes below can be checked by trial division
through 257. `circuitAux_facts` proves their primality, distinctness, and
separation from p; `circuitBasis_facts` includes p in this indexed prime basis.

Choose 72 distinct primes D_ij (0<=i<6, 0<=j<12), given row by row:

```
199 13381 10369 8761 6991 6427 5623 5323 4861 4327 4177 3821
4099 65537 65539 65543 65551 65557 65563 65579 65581 65587 65599 65609
4111 65617 65629 65633 65647 65651 65657 65677 65687 65699 65701 65707
4127 65713 65717 65719 65729 65731 65761 65777 65789 65809 65827 65831
4129 65837 65839 65843 65851 65867 65881 65899 65921 65927 65929 65951
4133 65957 65963 65981 65983 65993 66029 66037 66041 66047 66067 66071
```

Choose eleven further primes C_j (1<=j<12), in order:

 3,5,7,11,13,17,19,23,29,31,37.

All 83 primes are distinct and different from p. Set C=prod_j C_j. Define

 X_0 = C * prod_j D_0j,
 X_i = prod_j D_ij  (1<=i<6),
 Y_0 = C * prod_i D_i0^2,
 Y_j = C_j * prod_i D_ij^2  (1<=j<12).

Write Q for the product of all 83 auxiliary primes. Then

 R = Q^2 = prod_i X_i^2 = prod_j Y_j.

The following are exact integer inequalities, proved by kernel-checked integer
arithmetic in `circuit_size_bounds`. For convenient arithmetic margins, every X_i is in
[2^188,2^189), Y_0 is in [2^177,2^178), and each remaining Y_j is in
[2^189,2^190). Also 2^122<p<2^123. These inequalities follow directly by
multiplying the displayed primes. Each Y_j is odd, so a Y_j in [2^189,2^190)
is strictly greater than the even number H=2^189. Also 2^311<n<2^312,
whereas p^2<2^246 and p^3>2^366. The X_i and Y_0 lie below H; the remaining
Y_j lie above H but below n. Multiplication of any atom by p^2 exceeds n,
and multiplication of any two atoms exceeds n because 2^354>n. These
observations give all bounds in the following list:

* p^2 <= n < p^3.
* X_i <= H and p^2*X_i > n, for every i.
* Y_0 <= H and p^2*Y_0 > n.
* H < Y_j <= n for j>0.
* Every X_i and Y_j is at least 2^177, and n < 2^354.

Thus the available p chains of these roots have capacities 2 for each X_i
and for Y_0, and 1 for the remaining Y_j. No product of two atoms is <=n.
The six X and twelve Y are pairwise distinct, as is immediate from their
auxiliary prime exponents. In particular, an X has exponent 1 on an entire
row, whereas a Y has exponent 2 on an entire column. Distinct rows or columns
have different supports. The definitions are `circuitX`, `circuitY`,
`circuitCore`, `circuitPrime`, and `circuitN`.

The product relation follows coordinate by coordinate: each D_ij occurs twice
on both sides; each C_j occurs twice in X_0^2, and once in each of Y_0 and Y_j.
Thus both products equal Q^2. It is also checked explicitly in
`circuit_endpoint_products`.

## A supporting face isolates the atoms

For a positive integer x, let d_ij(x)=v_(D_ij)(x) and c_j(x)=v_(C_j)(x).
Consider the following 66 integer additive functions:

 d_ij - d_i0 - d_0j + d_00  (i=1..5, j=1..11),
 2*c_j - d_00 - d_0j       (j=1..11).

List the first 55 in lexicographic order (i,j), followed by the last 11 in
increasing j. Write them as ell_0,...,ell_65. Put B=4*n+1 and define

 W(x) = sum_(t=0)^65 B^t * ell_t(x).

For x<=n each valuation lies between 0 and n. Hence each ell_t(x) lies
between -2*n and 2*n. Balanced base-B uniqueness proves that W(x)=0 if and
only if every ell_t(x)=0: reduce modulo B to force ell_0=0, divide by B,
and repeat. Indeed an integer of absolute value <=2*n cannot be a nonzero
multiple of B. W is additive on products of positive integers. All X_i,
Y_j, and p have weight zero: substitution into each rectangle and cross
constraint gives zero. Consequently W(p^k R)=0 for every natural k.

The definitions are `circuitWeights`, `circuitWeightBase`, and `circuitWeight`.
The balanced-digit argument is `combinedWeight_zero`; valuation bounds and
the application to this list are `factorization_le_self_of_prime`,
`circuitWeights_bounded`, and `circuitWeight_zero_iff`.
`circuitWeight_additive`, `circuit_generator_equations`, and
`circuitWeight_target` give the remaining assertions.

Let P be the explicitly defined finite subset

 P = {x in {1,...,n} : W(x)>0},   F = prod_(x in P) x.

For any positive z of weight zero, the supporting-face argument gives

 F*z in P(n) iff z is a product of distinct weight-zero factors <=n.

Proof: a subset attaining F*z has the largest possible sum of W weights.
To see this without an assumption about signs cancelling, for any subset S
of {1,...,n} subtract its total weight from the total weight of P. The difference is

$$\sum_{x\in P\setminus S} W(x)+
  \sum_{x\in S,\ W(x)<0}(-W(x)).$$

Both sums have nonnegative terms; every term present is strictly positive.
If prod(S)=Fz, additivity and W(z)=0 make this difference zero. Therefore every
positive-weight factor is selected and every negative-weight factor is absent.
S\P consists of weight-zero factors. Since F>0, cancelling F gives
z=prod(S\P). Conversely, a zero-weight subset is disjoint from P; adjoining
P gives the required subset product.
This is the already verified Lean lemma `PilotA060957.weight_face_products`.

## Classification of the relevant weight-zero factors

Suppose x divides p^5*R, x<=n, and W(x)=0. Unique prime factorization implies
that x has no prime divisors outside p and the 83 auxiliary primes. Set
c_0=d_00. The vanishing equations are equivalent to

 d_ij + d_00 = d_i0 + d_0j,
 2*c_j = d_00 + d_0j  (also valid at j=0).

The rectangle identities on row zero or column zero are tautologies; the
cross identity at j=0 follows from c_0=d_00. Thus these identities hold for
all the displayed row and column indices, including the boundary indices.

Choose j* minimizing c_j. Define

 a_i = d_i,j*,   b_j = c_j - c_j*.

These are nonnegative integers. Subtracting the displayed equations gives

 d_ij = a_i + 2*b_j,
 c_j = a_0 + b_0 + b_j.

The second identity follows from d_0,j*=2*c_j*-d_00 and c_0=d_00.
More explicitly, 2b_j=d_0j−d_0,j* follows from the cross equations;
subtracting the two rectangle equations yields d_ij−d_i,j*=2b_j.
Also a_0=2c_j*−c_0, whence a_0+b_0+b_j=c_j. Minimality guarantees that
all subtractions defining b are nonnegative. No division closure is assumed.
This integral normal-form argument is `circuit_normal_form`.
`dvd_primeMonomial` shows that x uses only the indexed primes;
`circuitEquations_of_weight_zero` obtains the displayed equations. Comparing
prime exponents, `circuit_monomial_normal_form` gives

 x = p^e * prod_i X_i^(a_i) * prod_j Y_j^(b_j).

Since every atom is >=2^177 and x<=n<2^354, the total atom multiplicity
sum_i a_i + sum_j b_j is at most one. The size inequalities above therefore
leave exactly the following possible factors:

 Z = {1,p,p^2}
     union {X_i,p*X_i : 0<=i<6}
     union {Y_0,p*Y_0}
     union {Y_j : 1<=j<12}.

Every member of this list is weight zero and <=n. All are distinct: different
atoms have different auxiliary exponents, and different members of one p chain
have different p exponents. The pure powers have no auxiliary prime divisor.

For completeness, if two or more atoms occurred, their product alone would
be at least (2^177)^2>n, and multiplication by p^e cannot reduce it. If no atom
occurs, n<p^3 forces e≤2. If an X_i or Y_0 occurs, p^2 times that atom exceeds
n, forcing e≤1. For every other Y_j, already pY_j>n, forcing e=0.
These are `circuit_zero_divisor_root` and `circuit_zero_divisor_label`.
`CircuitFactorLabel` indexes the list Z; `circuitFactor_values`,
`circuitFactor_facts`, and `circuitFactor_weight_zero` verify its values,
distinctness, bounds, and weights. This is a classification of relevant
zero-weight **divisors of p^5R**, which is all the proof requires; it does not
assert that arbitrary zero-weight integers use this prime basis.

## The exponent gap

Assume a subset of Z has product p^5*R. Let a_i count the selected factors
with root X_i, and b_j the selected factors with root Y_j. Then 0<=a_i<=2,
0<=b_0<=2, and 0<=b_j<=1 for j>0. Comparing exponents at D_ij gives

 a_i + 2*b_j = 2   for all i,j.

It follows that all b_j are equal, and their common value is 0 or 1.

* If all b_j=0, every a_i=2. Both X_i and p*X_i must be selected for each
  of the six roots. The product has p exponent at least 6, a contradiction.
* If all b_j=1, every a_i=0. Each Y root is selected once. Only Y_0 can
  contribute a p, and the independent factors p and p^2 contribute at most
  three more. The product has p exponent at most 4, a contradiction.

In Lean, the zero-one indicator of a subset of Z is used instead of root
counts. `circuit_selection_coefficients` records its prime exponents,
`circuit_no_selection` derives the two contradictory bounds on the p exponent,
and `circuit_reduced_nonmembership` proves the finite impossibility.

Now suppose F*p^5*R were in P(n). The supporting-face lemma leaves a subset
of zero-weight factors with product p^5R. Every selected factor is a positive
divisor of that product, so the classification applies to each one. Because
the 28 labels have distinct values, this subset pulls back to a subset of Z,
contradicting finite nonmembership. This proves the assertion in the full
original domain (`nonmembership_of_weight_face` and `circuit_intermediate_not_mem`), not only in a restricted
factor set.

On the other hand, define m=F*R and the two explicit endpoint subsets

 S = P union {Y_j : 0<=j<12},
 T = P union {X_i,p*X_i : 0<=i<6}.

They are subsets of {1,...,n}. Their displayed parts are disjoint from P
because their weights are zero. Their products are m and p^6*m. Since p is
prime, p<=n, and 0<5<6, these endpoints and the missing intermediate value
disprove the **unchanged** original statement, with a_exp=6 and k=5.

The multiplier and lower endpoint are `circuitPositive`, `circuitMultiplier`,
and `circuitM`. The explicit subsets are `circuitLowerWitness` and
`circuitUpperWitness`. `circuitLift_subset` and `circuitLift_prod` justify
adjoining P, and `circuit_endpoint_witnesses` verifies their bounds and exact
products. `counterexample` collects all original-domain hypotheses and the
missing intermediate product. `not_conjecture` states the negation of the
original universally quantified proposition. There is no affirmative
`PilotA060957.conjecture`, since the result is negative.


## Construction and credit

The supporting-face idea is related to Eleonore Bach, Friedrich Eisenbrand,
and Rom Pinchasi, [Integer points in the degree-sequence polytope](https://arxiv.org/html/2305.06732v1)
(2023), Section 3. Their result is not a disproof of this OEIS conjecture.
The explicit construction and its Lean development are by Wentao Li, with
AI assistance. The original conjecture is due to Yan Sheng Ang; the original
Lean statement is by The Formal Conjectures Authors.

The enormous finite sets are specified exactly, without enumerating them.
Mathlib's `irreducible_def` supplies kernel-checked defining equations;
`decide` and `norm_num` check finite arithmetic certificates. No experiment,
probable-prime test, or `native_decide` result substitutes for the proof.

## Lean verification

Source: [the canonical A060957.lean](../../../LeanOeisProofs/NewProofs/A060957.lean).
Main declarations: `PilotA060957.not_conjecture`, `PilotA060957.counterexample`.

Checked October 9, 2026, using Lean `4.34.0-rc2` and Mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`. The checked declarations use only
`propext`, `Classical.choice`, and `Quot.sound` (or subsets of these).
See the [current verification report](../../../verification/README.md) for
source hashes, compiler output, and the documented direct-compiler fallback.
