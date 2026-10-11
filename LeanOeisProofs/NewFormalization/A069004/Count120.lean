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

/-! Independent trial-division prime-count block Count120. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

theorem hc120 : countRange 120000 1000 = 88 := by decide +kernel
theorem hc121 : countRange 121000 1000 = 86 := by decide +kernel
theorem hc122 : countRange 122000 1000 = 88 := by decide +kernel
theorem hc123 : countRange 123000 1000 = 88 := by decide +kernel
theorem hc124 : countRange 124000 1000 = 83 := by decide +kernel
theorem hc125 : countRange 125000 1000 = 84 := by decide +kernel
theorem hc126 : countRange 126000 1000 = 83 := by decide +kernel
theorem hc127 : countRange 127000 1000 = 86 := by decide +kernel
theorem hc128 : countRange 128000 1000 = 89 := by decide +kernel
theorem hc129 : countRange 129000 1000 = 83 := by decide +kernel
theorem hc130 : countRange 130000 1000 = 85 := by decide +kernel
theorem hc131 : countRange 131000 1000 = 83 := by decide +kernel
theorem hc132 : countRange 132000 1000 = 87 := by decide +kernel
theorem hc133 : countRange 133000 1000 = 82 := by decide +kernel
theorem hc134 : countRange 134000 1000 = 80 := by decide +kernel
theorem hc135 : countRange 135000 1000 = 89 := by decide +kernel
theorem hc136 : countRange 136000 1000 = 96 := by decide +kernel
theorem hc137 : countRange 137000 1000 = 80 := by decide +kernel
theorem hc138 : countRange 138000 1000 = 85 := by decide +kernel
theorem hc139 : countRange 139000 1000 = 84 := by decide +kernel
