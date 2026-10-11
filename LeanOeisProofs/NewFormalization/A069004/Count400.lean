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

/-! Independent trial-division prime-count block Count400. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

theorem hc400 : countRange 400000 1000 = 70 := by decide +kernel
theorem hc401 : countRange 401000 1000 = 71 := by decide +kernel
theorem hc402 : countRange 402000 1000 = 76 := by decide +kernel
theorem hc403 : countRange 403000 1000 = 75 := by decide +kernel
theorem hc404 : countRange 404000 1000 = 70 := by decide +kernel
theorem hc405 : countRange 405000 1000 = 83 := by decide +kernel
theorem hc406 : countRange 406000 1000 = 67 := by decide +kernel
theorem hc407 : countRange 407000 1000 = 81 := by decide +kernel
theorem hc408 : countRange 408000 1000 = 79 := by decide +kernel
theorem hc409 : countRange 409000 1000 = 82 := by decide +kernel
theorem hc410 : countRange 410000 1000 = 73 := by decide +kernel
theorem hc411 : countRange 411000 1000 = 81 := by decide +kernel
theorem hc412 : countRange 412000 1000 = 74 := by decide +kernel
theorem hc413 : countRange 413000 1000 = 69 := by decide +kernel
theorem hc414 : countRange 414000 1000 = 90 := by decide +kernel
theorem hc415 : countRange 415000 1000 = 80 := by decide +kernel
theorem hc416 : countRange 416000 1000 = 67 := by decide +kernel
theorem hc417 : countRange 417000 1000 = 82 := by decide +kernel
theorem hc418 : countRange 418000 1000 = 85 := by decide +kernel
theorem hc419 : countRange 419000 1000 = 75 := by decide +kernel
