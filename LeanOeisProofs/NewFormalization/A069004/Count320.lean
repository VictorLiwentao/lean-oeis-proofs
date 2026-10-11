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

/-! Independent trial-division prime-count block Count320. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

theorem hc320 : countRange 320000 1000 = 79 := by decide +kernel
theorem hc321 : countRange 321000 1000 = 80 := by decide +kernel
theorem hc322 : countRange 322000 1000 = 81 := by decide +kernel
theorem hc323 : countRange 323000 1000 = 71 := by decide +kernel
theorem hc324 : countRange 324000 1000 = 87 := by decide +kernel
theorem hc325 : countRange 325000 1000 = 85 := by decide +kernel
theorem hc326 : countRange 326000 1000 = 73 := by decide +kernel
theorem hc327 : countRange 327000 1000 = 86 := by decide +kernel
theorem hc328 : countRange 328000 1000 = 73 := by decide +kernel
theorem hc329 : countRange 329000 1000 = 81 := by decide +kernel
theorem hc330 : countRange 330000 1000 = 80 := by decide +kernel
theorem hc331 : countRange 331000 1000 = 82 := by decide +kernel
theorem hc332 : countRange 332000 1000 = 72 := by decide +kernel
theorem hc333 : countRange 333000 1000 = 81 := by decide +kernel
theorem hc334 : countRange 334000 1000 = 77 := by decide +kernel
theorem hc335 : countRange 335000 1000 = 77 := by decide +kernel
theorem hc336 : countRange 336000 1000 = 84 := by decide +kernel
theorem hc337 : countRange 337000 1000 = 80 := by decide +kernel
theorem hc338 : countRange 338000 1000 = 77 := by decide +kernel
theorem hc339 : countRange 339000 1000 = 68 := by decide +kernel
