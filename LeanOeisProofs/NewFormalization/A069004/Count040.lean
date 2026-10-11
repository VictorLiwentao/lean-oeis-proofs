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

/-! Independent trial-division prime-count block Count040. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

theorem hc40 : countRange 40000 1000 = 88 := by decide +kernel
theorem hc41 : countRange 41000 1000 = 101 := by decide +kernel
theorem hc42 : countRange 42000 1000 = 102 := by decide +kernel
theorem hc43 : countRange 43000 1000 = 85 := by decide +kernel
theorem hc44 : countRange 44000 1000 = 96 := by decide +kernel
theorem hc45 : countRange 45000 1000 = 86 := by decide +kernel
theorem hc46 : countRange 46000 1000 = 90 := by decide +kernel
theorem hc47 : countRange 47000 1000 = 95 := by decide +kernel
theorem hc48 : countRange 48000 1000 = 89 := by decide +kernel
theorem hc49 : countRange 49000 1000 = 98 := by decide +kernel
theorem hc50 : countRange 50000 1000 = 89 := by decide +kernel
theorem hc51 : countRange 51000 1000 = 97 := by decide +kernel
theorem hc52 : countRange 52000 1000 = 89 := by decide +kernel
theorem hc53 : countRange 53000 1000 = 92 := by decide +kernel
theorem hc54 : countRange 54000 1000 = 90 := by decide +kernel
theorem hc55 : countRange 55000 1000 = 93 := by decide +kernel
theorem hc56 : countRange 56000 1000 = 99 := by decide +kernel
theorem hc57 : countRange 57000 1000 = 91 := by decide +kernel
theorem hc58 : countRange 58000 1000 = 90 := by decide +kernel
theorem hc59 : countRange 59000 1000 = 94 := by decide +kernel
