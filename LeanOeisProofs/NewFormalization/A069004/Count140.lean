/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Wentao Li.
Wentao Li modifications are licensed under Apache 2.0.
Epoch-derived portions retain their original licensing status.
Original Lean formalization: The Formal Conjectures Authors.
New Lean proof development: Wentao Li.
Prime-count block data from Epoch Anthropic oeis-full-50usd-ant-j0j0g4uzligm1k41.
-/
import LeanOeisProofs.NewFormalization.A069004.Core

/-! Independent trial-division prime-count block Count140. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

theorem hc140 : countRange 140000 1000 = 87 := by decide +kernel
theorem hc141 : countRange 141000 1000 = 87 := by decide +kernel
theorem hc142 : countRange 142000 1000 = 82 := by decide +kernel
theorem hc143 : countRange 143000 1000 = 77 := by decide +kernel
theorem hc144 : countRange 144000 1000 = 79 := by decide +kernel
theorem hc145 : countRange 145000 1000 = 85 := by decide +kernel
theorem hc146 : countRange 146000 1000 = 84 := by decide +kernel
theorem hc147 : countRange 147000 1000 = 83 := by decide +kernel
theorem hc148 : countRange 148000 1000 = 83 := by decide +kernel
theorem hc149 : countRange 149000 1000 = 91 := by decide +kernel
theorem hc150 : countRange 150000 1000 = 85 := by decide +kernel
theorem hc151 : countRange 151000 1000 = 90 := by decide +kernel
theorem hc152 : countRange 152000 1000 = 88 := by decide +kernel
theorem hc153 : countRange 153000 1000 = 77 := by decide +kernel
theorem hc154 : countRange 154000 1000 = 84 := by decide +kernel
theorem hc155 : countRange 155000 1000 = 85 := by decide +kernel
theorem hc156 : countRange 156000 1000 = 76 := by decide +kernel
theorem hc157 : countRange 157000 1000 = 88 := by decide +kernel
theorem hc158 : countRange 158000 1000 = 77 := by decide +kernel
theorem hc159 : countRange 159000 1000 = 85 := by decide +kernel
