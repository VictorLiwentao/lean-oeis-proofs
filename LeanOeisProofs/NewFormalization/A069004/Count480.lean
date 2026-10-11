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

/-! Independent trial-division prime-count block Count480. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

theorem hc480 : countRange 480000 1000 = 77 := by decide +kernel
theorem hc481 : countRange 481000 1000 = 78 := by decide +kernel
theorem hc482 : countRange 482000 1000 = 82 := by decide +kernel
theorem hc483 : countRange 483000 1000 = 75 := by decide +kernel
theorem hc484 : countRange 484000 1000 = 65 := by decide +kernel
theorem hc485 : countRange 485000 1000 = 63 := by decide +kernel
theorem hc486 : countRange 486000 1000 = 82 := by decide +kernel
theorem hc487 : countRange 487000 1000 = 78 := by decide +kernel
theorem hc488 : countRange 488000 1000 = 83 := by decide +kernel
theorem hc489 : countRange 489000 1000 = 78 := by decide +kernel
theorem hc490 : countRange 490000 1000 = 78 := by decide +kernel
theorem hc491 : countRange 491000 1000 = 76 := by decide +kernel
theorem hc492 : countRange 492000 1000 = 67 := by decide +kernel
theorem hc493 : countRange 493000 1000 = 82 := by decide +kernel
theorem hc494 : countRange 494000 1000 = 80 := by decide +kernel
theorem hc495 : countRange 495000 1000 = 87 := by decide +kernel
theorem hc496 : countRange 496000 1000 = 68 := by decide +kernel
theorem hc497 : countRange 497000 1000 = 81 := by decide +kernel
theorem hc498 : countRange 498000 1000 = 72 := by decide +kernel
theorem hc499 : countRange 499000 1000 = 81 := by decide +kernel
