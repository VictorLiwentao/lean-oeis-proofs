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

/-! Independent trial-division prime-count block Count300. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

theorem hc300 : countRange 300000 1000 = 85 := by decide +kernel
theorem hc301 : countRange 301000 1000 = 83 := by decide +kernel
theorem hc302 : countRange 302000 1000 = 72 := by decide +kernel
theorem hc303 : countRange 303000 1000 = 84 := by decide +kernel
theorem hc304 : countRange 304000 1000 = 88 := by decide +kernel
theorem hc305 : countRange 305000 1000 = 80 := by decide +kernel
theorem hc306 : countRange 306000 1000 = 82 := by decide +kernel
theorem hc307 : countRange 307000 1000 = 73 := by decide +kernel
theorem hc308 : countRange 308000 1000 = 76 := by decide +kernel
theorem hc309 : countRange 309000 1000 = 80 := by decide +kernel
theorem hc310 : countRange 310000 1000 = 79 := by decide +kernel
theorem hc311 : countRange 311000 1000 = 69 := by decide +kernel
theorem hc312 : countRange 312000 1000 = 86 := by decide +kernel
theorem hc313 : countRange 313000 1000 = 86 := by decide +kernel
theorem hc314 : countRange 314000 1000 = 76 := by decide +kernel
theorem hc315 : countRange 315000 1000 = 77 := by decide +kernel
theorem hc316 : countRange 316000 1000 = 84 := by decide +kernel
theorem hc317 : countRange 317000 1000 = 84 := by decide +kernel
theorem hc318 : countRange 318000 1000 = 81 := by decide +kernel
theorem hc319 : countRange 319000 1000 = 86 := by decide +kernel
