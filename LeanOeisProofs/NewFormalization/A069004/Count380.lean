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

/-! Independent trial-division prime-count block Count380. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

theorem hc380 : countRange 380000 1000 = 72 := by decide +kernel
theorem hc381 : countRange 381000 1000 = 76 := by decide +kernel
theorem hc382 : countRange 382000 1000 = 74 := by decide +kernel
theorem hc383 : countRange 383000 1000 = 81 := by decide +kernel
theorem hc384 : countRange 384000 1000 = 78 := by decide +kernel
theorem hc385 : countRange 385000 1000 = 80 := by decide +kernel
theorem hc386 : countRange 386000 1000 = 78 := by decide +kernel
theorem hc387 : countRange 387000 1000 = 69 := by decide +kernel
theorem hc388 : countRange 388000 1000 = 75 := by decide +kernel
theorem hc389 : countRange 389000 1000 = 84 := by decide +kernel
theorem hc390 : countRange 390000 1000 = 81 := by decide +kernel
theorem hc391 : countRange 391000 1000 = 79 := by decide +kernel
theorem hc392 : countRange 392000 1000 = 86 := by decide +kernel
theorem hc393 : countRange 393000 1000 = 87 := by decide +kernel
theorem hc394 : countRange 394000 1000 = 75 := by decide +kernel
theorem hc395 : countRange 395000 1000 = 72 := by decide +kernel
theorem hc396 : countRange 396000 1000 = 75 := by decide +kernel
theorem hc397 : countRange 397000 1000 = 75 := by decide +kernel
theorem hc398 : countRange 398000 1000 = 82 := by decide +kernel
theorem hc399 : countRange 399000 1000 = 81 := by decide +kernel
