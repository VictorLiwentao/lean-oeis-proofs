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

/-! Independent trial-division prime-count block Count000. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

theorem hc0 : countRange 0 1000 = 168 := by decide +kernel
theorem hc1 : countRange 1000 1000 = 135 := by decide +kernel
theorem hc2 : countRange 2000 1000 = 127 := by decide +kernel
theorem hc3 : countRange 3000 1000 = 120 := by decide +kernel
theorem hc4 : countRange 4000 1000 = 119 := by decide +kernel
theorem hc5 : countRange 5000 1000 = 114 := by decide +kernel
theorem hc6 : countRange 6000 1000 = 117 := by decide +kernel
theorem hc7 : countRange 7000 1000 = 107 := by decide +kernel
theorem hc8 : countRange 8000 1000 = 110 := by decide +kernel
theorem hc9 : countRange 9000 1000 = 112 := by decide +kernel
theorem hc10 : countRange 10000 1000 = 106 := by decide +kernel
theorem hc11 : countRange 11000 1000 = 103 := by decide +kernel
theorem hc12 : countRange 12000 1000 = 109 := by decide +kernel
theorem hc13 : countRange 13000 1000 = 105 := by decide +kernel
theorem hc14 : countRange 14000 1000 = 102 := by decide +kernel
theorem hc15 : countRange 15000 1000 = 108 := by decide +kernel
theorem hc16 : countRange 16000 1000 = 98 := by decide +kernel
theorem hc17 : countRange 17000 1000 = 104 := by decide +kernel
theorem hc18 : countRange 18000 1000 = 94 := by decide +kernel
theorem hc19 : countRange 19000 1000 = 104 := by decide +kernel
