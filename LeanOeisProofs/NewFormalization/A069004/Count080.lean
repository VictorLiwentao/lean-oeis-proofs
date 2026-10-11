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

/-! Independent trial-division prime-count block Count080. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

theorem hc80 : countRange 80000 1000 = 88 := by decide +kernel
theorem hc81 : countRange 81000 1000 = 92 := by decide +kernel
theorem hc82 : countRange 82000 1000 = 89 := by decide +kernel
theorem hc83 : countRange 83000 1000 = 84 := by decide +kernel
theorem hc84 : countRange 84000 1000 = 87 := by decide +kernel
theorem hc85 : countRange 85000 1000 = 85 := by decide +kernel
theorem hc86 : countRange 86000 1000 = 88 := by decide +kernel
theorem hc87 : countRange 87000 1000 = 93 := by decide +kernel
theorem hc88 : countRange 88000 1000 = 76 := by decide +kernel
theorem hc89 : countRange 89000 1000 = 94 := by decide +kernel
theorem hc90 : countRange 90000 1000 = 89 := by decide +kernel
theorem hc91 : countRange 91000 1000 = 85 := by decide +kernel
theorem hc92 : countRange 92000 1000 = 97 := by decide +kernel
theorem hc93 : countRange 93000 1000 = 86 := by decide +kernel
theorem hc94 : countRange 94000 1000 = 87 := by decide +kernel
theorem hc95 : countRange 95000 1000 = 95 := by decide +kernel
theorem hc96 : countRange 96000 1000 = 84 := by decide +kernel
theorem hc97 : countRange 97000 1000 = 82 := by decide +kernel
theorem hc98 : countRange 98000 1000 = 87 := by decide +kernel
theorem hc99 : countRange 99000 1000 = 87 := by decide +kernel
