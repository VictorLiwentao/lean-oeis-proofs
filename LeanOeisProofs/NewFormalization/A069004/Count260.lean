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

/-! Independent trial-division prime-count block Count260. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

theorem hc260 : countRange 260000 1000 = 77 := by decide +kernel
theorem hc261 : countRange 261000 1000 = 73 := by decide +kernel
theorem hc262 : countRange 262000 1000 = 79 := by decide +kernel
theorem hc263 : countRange 263000 1000 = 84 := by decide +kernel
theorem hc264 : countRange 264000 1000 = 80 := by decide +kernel
theorem hc265 : countRange 265000 1000 = 78 := by decide +kernel
theorem hc266 : countRange 266000 1000 = 87 := by decide +kernel
theorem hc267 : countRange 267000 1000 = 94 := by decide +kernel
theorem hc268 : countRange 268000 1000 = 75 := by decide +kernel
theorem hc269 : countRange 269000 1000 = 78 := by decide +kernel
theorem hc270 : countRange 270000 1000 = 84 := by decide +kernel
theorem hc271 : countRange 271000 1000 = 78 := by decide +kernel
theorem hc272 : countRange 272000 1000 = 83 := by decide +kernel
theorem hc273 : countRange 273000 1000 = 71 := by decide +kernel
theorem hc274 : countRange 274000 1000 = 80 := by decide +kernel
theorem hc275 : countRange 275000 1000 = 83 := by decide +kernel
theorem hc276 : countRange 276000 1000 = 83 := by decide +kernel
theorem hc277 : countRange 277000 1000 = 74 := by decide +kernel
theorem hc278 : countRange 278000 1000 = 81 := by decide +kernel
theorem hc279 : countRange 279000 1000 = 73 := by decide +kernel
