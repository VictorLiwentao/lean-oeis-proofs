# OEIS A396843: integral existence, uniqueness and oddness

**Wentao Li**, with OpenAI Codex assistance.
The sequence and conjecture are due to **Paul D. Hanna**. The earlier
characteristic-two parity proof by **ElonSG / the-omega-institute/trureturing**
is credited in [SOURCE.md](SOURCE.md).

For a formal series `F`, write `H(F)=xF−3xF²` and `E(F)=F(H(F))`.
Suppose normalized series `F` and `G` agree below degree `d ≥ 2`.
Both inner series have order at least two. Expanding their difference gives

`E(F)−E(G) ≡ x(F−G) mod x^(d+2)`.

The outer-series difference has order at least `2d`. In the inner-series
difference, the linear coefficient of `F` contributes `H(F)−H(G)`;
every higher power contributes only in later degrees. Thus changing input
coefficient `d` changes output coefficient `d+1` by exactly the same amount.
This argument uses no division and works over every commutative ring.

Start with `F₀=x`. At step `n`, subtract from `Fₙ` the monomial of degree
`n+2` whose coefficient is `[x^(n+3)] E(Fₙ)`. The congruence cancels that
output coefficient and preserves all earlier ones. The coefficients stabilize,
and their limit satisfies `E(F)=x²`. Over the integers all corrections are
integral. Applying the same congruence to two normalized solutions proves
coefficientwise uniqueness. The construction commutes with coefficient maps,
which also proves integrality of the normalized rational solution.

Reduce the integral solution modulo two. The geometric series
`S=x/(1−x)` has coefficient one at every positive index. Let `T=H(S)`.
Using `S(1−x)=x` and characteristic two gives

`T(1−x)²=x²` and `(1−T)(1−x)²=1`.

Substituting `T` into the geometric-series relation gives
`S(T)(1−T)=T`, hence `S(T)=x²`. Uniqueness identifies the reduced integral
solution with `S`. Every positive-index coefficient is therefore odd.

The public sequence definition selects the normalized solution. The theorem
`series_eq_constructed` identifies it with the correction construction, so the
source equation, oddness and term certificates all apply to the same sequence.
The first five positive terms are checked as `1, 3, 15, 117, 975`.

The canonical file is
[`LeanOeisProofs/IndependentFormalization/A396843.lean`](../../../LeanOeisProofs/IndependentFormalization/A396843.lean).
The final parity theorem is `OeisA396843.conjecture`. The publication uses
pinned Lean `4.34.0-rc2` and Mathlib; the DeepMind check uses Lean `4.33.1`.
The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.
Exact checks and hashes appear in the [verification record](../../../verification/README.md).
