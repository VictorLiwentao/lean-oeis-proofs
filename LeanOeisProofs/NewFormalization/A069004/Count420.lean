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

/-! Independent trial-division prime-count block Count420. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

theorem hc420 : countRange 420000 1000 = 75 := by decide +kernel
theorem hc421 : countRange 421000 1000 = 73 := by decide +kernel
theorem hc422 : countRange 422000 1000 = 77 := by decide +kernel
theorem hc423 : countRange 423000 1000 = 83 := by decide +kernel
theorem hc424 : countRange 424000 1000 = 81 := by decide +kernel
theorem hc425 : countRange 425000 1000 = 74 := by decide +kernel
theorem hc426 : countRange 426000 1000 = 71 := by decide +kernel
theorem hc427 : countRange 427000 1000 = 78 := by decide +kernel
theorem hc428 : countRange 428000 1000 = 71 := by decide +kernel
theorem hc429 : countRange 429000 1000 = 89 := by decide +kernel
theorem hc430 : countRange 430000 1000 = 76 := by decide +kernel
theorem hc431 : countRange 431000 1000 = 79 := by decide +kernel
theorem hc432 : countRange 432000 1000 = 84 := by decide +kernel
theorem hc433 : countRange 433000 1000 = 80 := by decide +kernel
theorem hc434 : countRange 434000 1000 = 85 := by decide +kernel
theorem hc435 : countRange 435000 1000 = 82 := by decide +kernel
theorem hc436 : countRange 436000 1000 = 73 := by decide +kernel
theorem hc437 : countRange 437000 1000 = 70 := by decide +kernel
theorem hc438 : countRange 438000 1000 = 75 := by decide +kernel
theorem hc439 : countRange 439000 1000 = 75 := by decide +kernel
