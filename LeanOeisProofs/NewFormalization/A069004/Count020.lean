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

/-! Independent trial-division prime-count block Count020. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

theorem hc20 : countRange 20000 1000 = 98 := by decide +kernel
theorem hc21 : countRange 21000 1000 = 104 := by decide +kernel
theorem hc22 : countRange 22000 1000 = 100 := by decide +kernel
theorem hc23 : countRange 23000 1000 = 104 := by decide +kernel
theorem hc24 : countRange 24000 1000 = 94 := by decide +kernel
theorem hc25 : countRange 25000 1000 = 98 := by decide +kernel
theorem hc26 : countRange 26000 1000 = 101 := by decide +kernel
theorem hc27 : countRange 27000 1000 = 94 := by decide +kernel
theorem hc28 : countRange 28000 1000 = 98 := by decide +kernel
theorem hc29 : countRange 29000 1000 = 92 := by decide +kernel
theorem hc30 : countRange 30000 1000 = 95 := by decide +kernel
theorem hc31 : countRange 31000 1000 = 92 := by decide +kernel
theorem hc32 : countRange 32000 1000 = 106 := by decide +kernel
theorem hc33 : countRange 33000 1000 = 100 := by decide +kernel
theorem hc34 : countRange 34000 1000 = 94 := by decide +kernel
theorem hc35 : countRange 35000 1000 = 92 := by decide +kernel
theorem hc36 : countRange 36000 1000 = 99 := by decide +kernel
theorem hc37 : countRange 37000 1000 = 94 := by decide +kernel
theorem hc38 : countRange 38000 1000 = 90 := by decide +kernel
theorem hc39 : countRange 39000 1000 = 96 := by decide +kernel
