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

/-! Independent trial-division prime-count block Count440. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

theorem hc440 : countRange 440000 1000 = 79 := by decide +kernel
theorem hc441 : countRange 441000 1000 = 72 := by decide +kernel
theorem hc442 : countRange 442000 1000 = 85 := by decide +kernel
theorem hc443 : countRange 443000 1000 = 88 := by decide +kernel
theorem hc444 : countRange 444000 1000 = 82 := by decide +kernel
theorem hc445 : countRange 445000 1000 = 68 := by decide +kernel
theorem hc446 : countRange 446000 1000 = 68 := by decide +kernel
theorem hc447 : countRange 447000 1000 = 73 := by decide +kernel
theorem hc448 : countRange 448000 1000 = 70 := by decide +kernel
theorem hc449 : countRange 449000 1000 = 80 := by decide +kernel
theorem hc450 : countRange 450000 1000 = 92 := by decide +kernel
theorem hc451 : countRange 451000 1000 = 76 := by decide +kernel
theorem hc452 : countRange 452000 1000 = 63 := by decide +kernel
theorem hc453 : countRange 453000 1000 = 72 := by decide +kernel
theorem hc454 : countRange 454000 1000 = 74 := by decide +kernel
theorem hc455 : countRange 455000 1000 = 82 := by decide +kernel
theorem hc456 : countRange 456000 1000 = 73 := by decide +kernel
theorem hc457 : countRange 457000 1000 = 77 := by decide +kernel
theorem hc458 : countRange 458000 1000 = 75 := by decide +kernel
theorem hc459 : countRange 459000 1000 = 68 := by decide +kernel
