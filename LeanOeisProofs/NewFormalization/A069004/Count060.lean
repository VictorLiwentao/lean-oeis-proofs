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

/-! Independent trial-division prime-count block Count060. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

theorem hc60 : countRange 60000 1000 = 88 := by decide +kernel
theorem hc61 : countRange 61000 1000 = 87 := by decide +kernel
theorem hc62 : countRange 62000 1000 = 88 := by decide +kernel
theorem hc63 : countRange 63000 1000 = 93 := by decide +kernel
theorem hc64 : countRange 64000 1000 = 80 := by decide +kernel
theorem hc65 : countRange 65000 1000 = 98 := by decide +kernel
theorem hc66 : countRange 66000 1000 = 84 := by decide +kernel
theorem hc67 : countRange 67000 1000 = 99 := by decide +kernel
theorem hc68 : countRange 68000 1000 = 80 := by decide +kernel
theorem hc69 : countRange 69000 1000 = 81 := by decide +kernel
theorem hc70 : countRange 70000 1000 = 98 := by decide +kernel
theorem hc71 : countRange 71000 1000 = 95 := by decide +kernel
theorem hc72 : countRange 72000 1000 = 90 := by decide +kernel
theorem hc73 : countRange 73000 1000 = 83 := by decide +kernel
theorem hc74 : countRange 74000 1000 = 92 := by decide +kernel
theorem hc75 : countRange 75000 1000 = 91 := by decide +kernel
theorem hc76 : countRange 76000 1000 = 83 := by decide +kernel
theorem hc77 : countRange 77000 1000 = 95 := by decide +kernel
theorem hc78 : countRange 78000 1000 = 84 := by decide +kernel
theorem hc79 : countRange 79000 1000 = 91 := by decide +kernel
