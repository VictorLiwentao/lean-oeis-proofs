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

/-! Independent trial-division prime-count block Count240. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

theorem hc240 : countRange 240000 1000 = 80 := by decide +kernel
theorem hc241 : countRange 241000 1000 = 91 := by decide +kernel
theorem hc242 : countRange 242000 1000 = 76 := by decide +kernel
theorem hc243 : countRange 243000 1000 = 77 := by decide +kernel
theorem hc244 : countRange 244000 1000 = 88 := by decide +kernel
theorem hc245 : countRange 245000 1000 = 80 := by decide +kernel
theorem hc246 : countRange 246000 1000 = 84 := by decide +kernel
theorem hc247 : countRange 247000 1000 = 79 := by decide +kernel
theorem hc248 : countRange 248000 1000 = 88 := by decide +kernel
theorem hc249 : countRange 249000 1000 = 80 := by decide +kernel
theorem hc250 : countRange 250000 1000 = 71 := by decide +kernel
theorem hc251 : countRange 251000 1000 = 88 := by decide +kernel
theorem hc252 : countRange 252000 1000 = 78 := by decide +kernel
theorem hc253 : countRange 253000 1000 = 81 := by decide +kernel
theorem hc254 : countRange 254000 1000 = 76 := by decide +kernel
theorem hc255 : countRange 255000 1000 = 87 := by decide +kernel
theorem hc256 : countRange 256000 1000 = 72 := by decide +kernel
theorem hc257 : countRange 257000 1000 = 78 := by decide +kernel
theorem hc258 : countRange 258000 1000 = 86 := by decide +kernel
theorem hc259 : countRange 259000 1000 = 76 := by decide +kernel
