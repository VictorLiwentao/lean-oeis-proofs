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

/-! Independent trial-division prime-count block Count500. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

theorem hc500 : countRange 500000 1000 = 79 := by decide +kernel
theorem hc501 : countRange 501000 1000 = 74 := by decide +kernel
theorem hc502 : countRange 502000 1000 = 67 := by decide +kernel
theorem hc503 : countRange 503000 1000 = 76 := by decide +kernel
theorem hc504 : countRange 504000 1000 = 76 := by decide +kernel
theorem hc505 : countRange 505000 1000 = 83 := by decide +kernel
theorem hc506 : countRange 506000 1000 = 76 := by decide +kernel
theorem hc507 : countRange 507000 1000 = 71 := by decide +kernel
theorem hc508 : countRange 508000 1000 = 76 := by decide +kernel
theorem hc509 : countRange 509000 1000 = 75 := by decide +kernel
theorem hc510 : countRange 510000 1000 = 72 := by decide +kernel
theorem hc511 : countRange 511000 1000 = 82 := by decide +kernel
theorem hc512 : countRange 512000 721 = 48 := by decide +kernel
