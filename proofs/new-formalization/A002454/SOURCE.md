# OEIS A002454: the odd-order permanent identity

Lean formalization and write-up: **Wentao Li**, with OpenAI Codex assistance.

For every natural number `n` and every primitive complex `(2n+1)`-th root
`ζ`, form the `2n × 2n` matrix with diagonal entries `1` and off-diagonal
entries `(1 + ζ^(j-k))/(1 - ζ^(j-k))`, using integer subtraction. Its
permanent is `4^n (n!)²/(2n+1)`. The empty matrix at `n = 0` has permanent `1`.
The indices may start at zero because translating both indices preserves their difference.

Zhi-Wei Sun posed this identity in [OEIS A002454](https://oeis.org/A002454/internal)
on June 26, 2022. **Yue-Feng She, Zhi-Wei Sun and Wei Xia** proved it in
[Theorem 1.3(ii)](https://arxiv.org/html/2208.12167v2).
The determinant calculation follows **Xuejun Guo, Xin Li, Zhengyu Tao and Tao Wei**,
[equation (1.3)](https://arxiv.org/html/2206.02592). The Fourier eigenvalue
identity is due to **F. Calogero and A. M. Perelomov**.

The Lean development imports Wentao Li's existing
[A001818 formalization](../../../LeanOeisProofs/NewFormalization/A001818.lean)
and adds a general reciprocal-difference determinant identity and an odd-order
principal-minor calculation. The original statement and sequence definition
are credited to **The Formal Conjectures Authors**.

[Epoch Research's earlier partial development](https://github.com/epoch-research/LeanOpenProblems-results/blob/fd09021e79869476ef83cda231312f1a2a89c8d7/runs/oeis-full-50usd-ant-j0j0g4uzligm1k41/oeis_2454_conjecture_0/Submission/Spec.lean)
also describes the cofactor approach. Its submitted target remains incomplete.

All-state DeepMind PR searches on October 28, 2026 covered `A002454`,
`OeisA2454` and `OEIS/2454`. [PR #5447](https://github.com/google-deepmind/formal-conjectures/pull/5447)
records the published mathematical result and retains the proof placeholder.
The related A001818 submissions concern a different identity. No matching
DeepMind proof PR was found in these searches. Additional public PR searches for
`A002454` and `oeis_2454`, including trureturing, found no complete matching Lean
proof. This package is classified as a new formalization of the cited theorem.

The canonical theorem is `A002454.conjecture_frozen` in
[A002454.lean](../../../LeanOeisProofs/NewFormalization/A002454.lean).
The exact target is frozen at Formal Conjectures commit
`5a2fb85045c86e4a184b15ce7531ba199a3c4580`.
See the [verification record](../../../verification/README.md) for compiler,
Comparator, axiom and kernel-replay checks.
