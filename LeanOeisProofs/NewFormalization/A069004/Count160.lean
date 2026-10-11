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

/-! Independent trial-division prime-count block Count160. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

theorem hc160 : countRange 160000 1000 = 85 := by decide +kernel
theorem hc161 : countRange 161000 1000 = 84 := by decide +kernel
theorem hc162 : countRange 162000 1000 = 81 := by decide +kernel
theorem hc163 : countRange 163000 1000 = 83 := by decide +kernel
theorem hc164 : countRange 164000 1000 = 77 := by decide +kernel
theorem hc165 : countRange 165000 1000 = 80 := by decide +kernel
theorem hc166 : countRange 166000 1000 = 81 := by decide +kernel
theorem hc167 : countRange 167000 1000 = 83 := by decide +kernel
theorem hc168 : countRange 168000 1000 = 73 := by decide +kernel
theorem hc169 : countRange 169000 1000 = 87 := by decide +kernel
theorem hc170 : countRange 170000 1000 = 87 := by decide +kernel
theorem hc171 : countRange 171000 1000 = 81 := by decide +kernel
theorem hc172 : countRange 172000 1000 = 89 := by decide +kernel
theorem hc173 : countRange 173000 1000 = 79 := by decide +kernel
theorem hc174 : countRange 174000 1000 = 83 := by decide +kernel
theorem hc175 : countRange 175000 1000 = 75 := by decide +kernel
theorem hc176 : countRange 176000 1000 = 95 := by decide +kernel
theorem hc177 : countRange 177000 1000 = 73 := by decide +kernel
theorem hc178 : countRange 178000 1000 = 89 := by decide +kernel
theorem hc179 : countRange 179000 1000 = 94 := by decide +kernel
