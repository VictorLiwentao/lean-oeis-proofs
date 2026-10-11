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

/-! Independent trial-division prime-count block Count360. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

theorem hc360 : countRange 360000 1000 = 68 := by decide +kernel
theorem hc361 : countRange 361000 1000 = 79 := by decide +kernel
theorem hc362 : countRange 362000 1000 = 76 := by decide +kernel
theorem hc363 : countRange 363000 1000 = 84 := by decide +kernel
theorem hc364 : countRange 364000 1000 = 77 := by decide +kernel
theorem hc365 : countRange 365000 1000 = 77 := by decide +kernel
theorem hc366 : countRange 366000 1000 = 85 := by decide +kernel
theorem hc367 : countRange 367000 1000 = 79 := by decide +kernel
theorem hc368 : countRange 368000 1000 = 72 := by decide +kernel
theorem hc369 : countRange 369000 1000 = 68 := by decide +kernel
theorem hc370 : countRange 370000 1000 = 70 := by decide +kernel
theorem hc371 : countRange 371000 1000 = 76 := by decide +kernel
theorem hc372 : countRange 372000 1000 = 81 := by decide +kernel
theorem hc373 : countRange 373000 1000 = 73 := by decide +kernel
theorem hc374 : countRange 374000 1000 = 82 := by decide +kernel
theorem hc375 : countRange 375000 1000 = 85 := by decide +kernel
theorem hc376 : countRange 376000 1000 = 80 := by decide +kernel
theorem hc377 : countRange 377000 1000 = 71 := by decide +kernel
theorem hc378 : countRange 378000 1000 = 77 := by decide +kernel
theorem hc379 : countRange 379000 1000 = 83 := by decide +kernel
