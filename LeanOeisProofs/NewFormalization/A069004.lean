/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Wentao Li.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Original Lean formalization: The Formal Conjectures Authors.
New Lean proof development and write-up: Wentao Li.
Mathematical counterexample: j2d9w5xtjn-png, GitHub PR #5453 (2026-09-10),
reporting a(512720)=42666 and π(512720)=42493 against T. D. Noe's 2007 upper bound.
Certificate data and Pratt/Lucas checker architecture adapted from the public
Epoch Anthropic run oeis-full-50usd-ant-j0j0g4uzligm1k41 (resource-limited, score I).
-/

import LeanOeisProofs.NewFormalization.A069004.Statement
import LeanOeisProofs.NewFormalization.A069004.GlueCert
import LeanOeisProofs.NewFormalization.A069004.GlueCount

/-!
Exact frozen-target certificate for `OeisA69004.conjecture2.variants.upper_bound_false`
and the same-group corollary `OeisA69004.conjecture2`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

namespace Cursor03R02.A069004

theorem a_eq_aCount (n : ℕ) : OeisA69004.a n = aCount n := rfl

theorem a_512720_ge : 42494 ≤ OeisA69004.a 512720 := by
  have h := aCount_ge 512720 chunks.flatten hflat
  rw [hlen] at h
  simpa [a_eq_aCount] using h

/-- Exact frozen type of `OeisA69004.conjecture2.variants.upper_bound_false`. -/
theorem upper_bound_false :
    ¬ ∀ n : ℕ, 1 < n → Nat.primeCounting n ≥ OeisA69004.a n := by
  intro h
  have hpi := h 512720 (by decide)
  have ha := a_512720_ge
  have hpc : Nat.primeCounting 512720 = 42493 := primeCounting_512720
  omega

/-- Exact frozen type of `OeisA69004.conjecture2`. -/
theorem conjecture2 :
    ¬ ((∀ n : ℕ, 1 < n → Nat.primeCounting n ≥ OeisA69004.a n) ∧
      (∀ n : ℕ, 1 < n → 5 * OeisA69004.a n ≥ Nat.primeCounting n) ∧
      Nat.primeCounting 2 = OeisA69004.a 2 ∧
      Nat.primeCounting 10 = OeisA69004.a 10 ∧
      5 * OeisA69004.a 12 = Nat.primeCounting 12) := by
  intro h
  exact upper_bound_false h.1

end Cursor03R02.A069004

