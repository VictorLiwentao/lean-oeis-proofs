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

/-! Independent trial-division prime-count block Count280. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

theorem hc280 : countRange 280000 1000 = 87 := by decide +kernel
theorem hc281 : countRange 281000 1000 = 85 := by decide +kernel
theorem hc282 : countRange 282000 1000 = 77 := by decide +kernel
theorem hc283 : countRange 283000 1000 = 72 := by decide +kernel
theorem hc284 : countRange 284000 1000 = 90 := by decide +kernel
theorem hc285 : countRange 285000 1000 = 77 := by decide +kernel
theorem hc286 : countRange 286000 1000 = 71 := by decide +kernel
theorem hc287 : countRange 287000 1000 = 71 := by decide +kernel
theorem hc288 : countRange 288000 1000 = 77 := by decide +kernel
theorem hc289 : countRange 289000 1000 = 85 := by decide +kernel
theorem hc290 : countRange 290000 1000 = 84 := by decide +kernel
theorem hc291 : countRange 291000 1000 = 77 := by decide +kernel
theorem hc292 : countRange 292000 1000 = 78 := by decide +kernel
theorem hc293 : countRange 293000 1000 = 68 := by decide +kernel
theorem hc294 : countRange 294000 1000 = 85 := by decide +kernel
theorem hc295 : countRange 295000 1000 = 75 := by decide +kernel
theorem hc296 : countRange 296000 1000 = 82 := by decide +kernel
theorem hc297 : countRange 297000 1000 = 73 := by decide +kernel
theorem hc298 : countRange 298000 1000 = 73 := by decide +kernel
theorem hc299 : countRange 299000 1000 = 78 := by decide +kernel
