/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Wentao Li.
Licensed under the Apache License, Version 2.0.
Original Lean formalization: The Formal Conjectures Authors.
New Lean proof development: Wentao Li.
-/
import LeanOeisProofs.NewFormalization.A069004.Count000
import LeanOeisProofs.NewFormalization.A069004.Count020
import LeanOeisProofs.NewFormalization.A069004.Count040
import LeanOeisProofs.NewFormalization.A069004.Count060
import LeanOeisProofs.NewFormalization.A069004.Count080
import LeanOeisProofs.NewFormalization.A069004.Count100
import LeanOeisProofs.NewFormalization.A069004.Count120
import LeanOeisProofs.NewFormalization.A069004.Count140
import LeanOeisProofs.NewFormalization.A069004.Count160
import LeanOeisProofs.NewFormalization.A069004.Count180
import LeanOeisProofs.NewFormalization.A069004.Count200
import LeanOeisProofs.NewFormalization.A069004.Count220
import LeanOeisProofs.NewFormalization.A069004.Count240
import LeanOeisProofs.NewFormalization.A069004.Count260
import LeanOeisProofs.NewFormalization.A069004.Count280
import LeanOeisProofs.NewFormalization.A069004.Count300
import LeanOeisProofs.NewFormalization.A069004.Count320
import LeanOeisProofs.NewFormalization.A069004.Count340
import LeanOeisProofs.NewFormalization.A069004.Count360
import LeanOeisProofs.NewFormalization.A069004.Count380
import LeanOeisProofs.NewFormalization.A069004.Count400
import LeanOeisProofs.NewFormalization.A069004.Count420
import LeanOeisProofs.NewFormalization.A069004.Count440
import LeanOeisProofs.NewFormalization.A069004.Count460
import LeanOeisProofs.NewFormalization.A069004.Count480
import LeanOeisProofs.NewFormalization.A069004.Count500

/-! Glue independent countRange blocks into `Nat.primeCounting 512720`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

theorem cntBase : Nat.count (fun n => trialPrimeB n = true) 0 = 0 := by simp
theorem cnt0 : Nat.count (fun n => trialPrimeB n = true) 1000 = 168 :=
  count_step 0 1000 1000 168 0 168 (by omega) (by omega) hc0 cntBase
theorem cnt1 : Nat.count (fun n => trialPrimeB n = true) 2000 = 303 :=
  count_step 1000 1000 2000 135 168 303 (by omega) (by omega) hc1 cnt0
theorem cnt2 : Nat.count (fun n => trialPrimeB n = true) 3000 = 430 :=
  count_step 2000 1000 3000 127 303 430 (by omega) (by omega) hc2 cnt1
theorem cnt3 : Nat.count (fun n => trialPrimeB n = true) 4000 = 550 :=
  count_step 3000 1000 4000 120 430 550 (by omega) (by omega) hc3 cnt2
theorem cnt4 : Nat.count (fun n => trialPrimeB n = true) 5000 = 669 :=
  count_step 4000 1000 5000 119 550 669 (by omega) (by omega) hc4 cnt3
theorem cnt5 : Nat.count (fun n => trialPrimeB n = true) 6000 = 783 :=
  count_step 5000 1000 6000 114 669 783 (by omega) (by omega) hc5 cnt4
theorem cnt6 : Nat.count (fun n => trialPrimeB n = true) 7000 = 900 :=
  count_step 6000 1000 7000 117 783 900 (by omega) (by omega) hc6 cnt5
theorem cnt7 : Nat.count (fun n => trialPrimeB n = true) 8000 = 1007 :=
  count_step 7000 1000 8000 107 900 1007 (by omega) (by omega) hc7 cnt6
theorem cnt8 : Nat.count (fun n => trialPrimeB n = true) 9000 = 1117 :=
  count_step 8000 1000 9000 110 1007 1117 (by omega) (by omega) hc8 cnt7
theorem cnt9 : Nat.count (fun n => trialPrimeB n = true) 10000 = 1229 :=
  count_step 9000 1000 10000 112 1117 1229 (by omega) (by omega) hc9 cnt8
theorem cnt10 : Nat.count (fun n => trialPrimeB n = true) 11000 = 1335 :=
  count_step 10000 1000 11000 106 1229 1335 (by omega) (by omega) hc10 cnt9
theorem cnt11 : Nat.count (fun n => trialPrimeB n = true) 12000 = 1438 :=
  count_step 11000 1000 12000 103 1335 1438 (by omega) (by omega) hc11 cnt10
theorem cnt12 : Nat.count (fun n => trialPrimeB n = true) 13000 = 1547 :=
  count_step 12000 1000 13000 109 1438 1547 (by omega) (by omega) hc12 cnt11
theorem cnt13 : Nat.count (fun n => trialPrimeB n = true) 14000 = 1652 :=
  count_step 13000 1000 14000 105 1547 1652 (by omega) (by omega) hc13 cnt12
theorem cnt14 : Nat.count (fun n => trialPrimeB n = true) 15000 = 1754 :=
  count_step 14000 1000 15000 102 1652 1754 (by omega) (by omega) hc14 cnt13
theorem cnt15 : Nat.count (fun n => trialPrimeB n = true) 16000 = 1862 :=
  count_step 15000 1000 16000 108 1754 1862 (by omega) (by omega) hc15 cnt14
theorem cnt16 : Nat.count (fun n => trialPrimeB n = true) 17000 = 1960 :=
  count_step 16000 1000 17000 98 1862 1960 (by omega) (by omega) hc16 cnt15
theorem cnt17 : Nat.count (fun n => trialPrimeB n = true) 18000 = 2064 :=
  count_step 17000 1000 18000 104 1960 2064 (by omega) (by omega) hc17 cnt16
theorem cnt18 : Nat.count (fun n => trialPrimeB n = true) 19000 = 2158 :=
  count_step 18000 1000 19000 94 2064 2158 (by omega) (by omega) hc18 cnt17
theorem cnt19 : Nat.count (fun n => trialPrimeB n = true) 20000 = 2262 :=
  count_step 19000 1000 20000 104 2158 2262 (by omega) (by omega) hc19 cnt18
theorem cnt20 : Nat.count (fun n => trialPrimeB n = true) 21000 = 2360 :=
  count_step 20000 1000 21000 98 2262 2360 (by omega) (by omega) hc20 cnt19
theorem cnt21 : Nat.count (fun n => trialPrimeB n = true) 22000 = 2464 :=
  count_step 21000 1000 22000 104 2360 2464 (by omega) (by omega) hc21 cnt20
theorem cnt22 : Nat.count (fun n => trialPrimeB n = true) 23000 = 2564 :=
  count_step 22000 1000 23000 100 2464 2564 (by omega) (by omega) hc22 cnt21
theorem cnt23 : Nat.count (fun n => trialPrimeB n = true) 24000 = 2668 :=
  count_step 23000 1000 24000 104 2564 2668 (by omega) (by omega) hc23 cnt22
theorem cnt24 : Nat.count (fun n => trialPrimeB n = true) 25000 = 2762 :=
  count_step 24000 1000 25000 94 2668 2762 (by omega) (by omega) hc24 cnt23
theorem cnt25 : Nat.count (fun n => trialPrimeB n = true) 26000 = 2860 :=
  count_step 25000 1000 26000 98 2762 2860 (by omega) (by omega) hc25 cnt24
theorem cnt26 : Nat.count (fun n => trialPrimeB n = true) 27000 = 2961 :=
  count_step 26000 1000 27000 101 2860 2961 (by omega) (by omega) hc26 cnt25
theorem cnt27 : Nat.count (fun n => trialPrimeB n = true) 28000 = 3055 :=
  count_step 27000 1000 28000 94 2961 3055 (by omega) (by omega) hc27 cnt26
theorem cnt28 : Nat.count (fun n => trialPrimeB n = true) 29000 = 3153 :=
  count_step 28000 1000 29000 98 3055 3153 (by omega) (by omega) hc28 cnt27
theorem cnt29 : Nat.count (fun n => trialPrimeB n = true) 30000 = 3245 :=
  count_step 29000 1000 30000 92 3153 3245 (by omega) (by omega) hc29 cnt28
theorem cnt30 : Nat.count (fun n => trialPrimeB n = true) 31000 = 3340 :=
  count_step 30000 1000 31000 95 3245 3340 (by omega) (by omega) hc30 cnt29
theorem cnt31 : Nat.count (fun n => trialPrimeB n = true) 32000 = 3432 :=
  count_step 31000 1000 32000 92 3340 3432 (by omega) (by omega) hc31 cnt30
theorem cnt32 : Nat.count (fun n => trialPrimeB n = true) 33000 = 3538 :=
  count_step 32000 1000 33000 106 3432 3538 (by omega) (by omega) hc32 cnt31
theorem cnt33 : Nat.count (fun n => trialPrimeB n = true) 34000 = 3638 :=
  count_step 33000 1000 34000 100 3538 3638 (by omega) (by omega) hc33 cnt32
theorem cnt34 : Nat.count (fun n => trialPrimeB n = true) 35000 = 3732 :=
  count_step 34000 1000 35000 94 3638 3732 (by omega) (by omega) hc34 cnt33
theorem cnt35 : Nat.count (fun n => trialPrimeB n = true) 36000 = 3824 :=
  count_step 35000 1000 36000 92 3732 3824 (by omega) (by omega) hc35 cnt34
theorem cnt36 : Nat.count (fun n => trialPrimeB n = true) 37000 = 3923 :=
  count_step 36000 1000 37000 99 3824 3923 (by omega) (by omega) hc36 cnt35
theorem cnt37 : Nat.count (fun n => trialPrimeB n = true) 38000 = 4017 :=
  count_step 37000 1000 38000 94 3923 4017 (by omega) (by omega) hc37 cnt36
theorem cnt38 : Nat.count (fun n => trialPrimeB n = true) 39000 = 4107 :=
  count_step 38000 1000 39000 90 4017 4107 (by omega) (by omega) hc38 cnt37
theorem cnt39 : Nat.count (fun n => trialPrimeB n = true) 40000 = 4203 :=
  count_step 39000 1000 40000 96 4107 4203 (by omega) (by omega) hc39 cnt38
theorem cnt40 : Nat.count (fun n => trialPrimeB n = true) 41000 = 4291 :=
  count_step 40000 1000 41000 88 4203 4291 (by omega) (by omega) hc40 cnt39
theorem cnt41 : Nat.count (fun n => trialPrimeB n = true) 42000 = 4392 :=
  count_step 41000 1000 42000 101 4291 4392 (by omega) (by omega) hc41 cnt40
theorem cnt42 : Nat.count (fun n => trialPrimeB n = true) 43000 = 4494 :=
  count_step 42000 1000 43000 102 4392 4494 (by omega) (by omega) hc42 cnt41
theorem cnt43 : Nat.count (fun n => trialPrimeB n = true) 44000 = 4579 :=
  count_step 43000 1000 44000 85 4494 4579 (by omega) (by omega) hc43 cnt42
theorem cnt44 : Nat.count (fun n => trialPrimeB n = true) 45000 = 4675 :=
  count_step 44000 1000 45000 96 4579 4675 (by omega) (by omega) hc44 cnt43
theorem cnt45 : Nat.count (fun n => trialPrimeB n = true) 46000 = 4761 :=
  count_step 45000 1000 46000 86 4675 4761 (by omega) (by omega) hc45 cnt44
theorem cnt46 : Nat.count (fun n => trialPrimeB n = true) 47000 = 4851 :=
  count_step 46000 1000 47000 90 4761 4851 (by omega) (by omega) hc46 cnt45
theorem cnt47 : Nat.count (fun n => trialPrimeB n = true) 48000 = 4946 :=
  count_step 47000 1000 48000 95 4851 4946 (by omega) (by omega) hc47 cnt46
theorem cnt48 : Nat.count (fun n => trialPrimeB n = true) 49000 = 5035 :=
  count_step 48000 1000 49000 89 4946 5035 (by omega) (by omega) hc48 cnt47
theorem cnt49 : Nat.count (fun n => trialPrimeB n = true) 50000 = 5133 :=
  count_step 49000 1000 50000 98 5035 5133 (by omega) (by omega) hc49 cnt48
theorem cnt50 : Nat.count (fun n => trialPrimeB n = true) 51000 = 5222 :=
  count_step 50000 1000 51000 89 5133 5222 (by omega) (by omega) hc50 cnt49
theorem cnt51 : Nat.count (fun n => trialPrimeB n = true) 52000 = 5319 :=
  count_step 51000 1000 52000 97 5222 5319 (by omega) (by omega) hc51 cnt50
theorem cnt52 : Nat.count (fun n => trialPrimeB n = true) 53000 = 5408 :=
  count_step 52000 1000 53000 89 5319 5408 (by omega) (by omega) hc52 cnt51
theorem cnt53 : Nat.count (fun n => trialPrimeB n = true) 54000 = 5500 :=
  count_step 53000 1000 54000 92 5408 5500 (by omega) (by omega) hc53 cnt52
theorem cnt54 : Nat.count (fun n => trialPrimeB n = true) 55000 = 5590 :=
  count_step 54000 1000 55000 90 5500 5590 (by omega) (by omega) hc54 cnt53
theorem cnt55 : Nat.count (fun n => trialPrimeB n = true) 56000 = 5683 :=
  count_step 55000 1000 56000 93 5590 5683 (by omega) (by omega) hc55 cnt54
theorem cnt56 : Nat.count (fun n => trialPrimeB n = true) 57000 = 5782 :=
  count_step 56000 1000 57000 99 5683 5782 (by omega) (by omega) hc56 cnt55
theorem cnt57 : Nat.count (fun n => trialPrimeB n = true) 58000 = 5873 :=
  count_step 57000 1000 58000 91 5782 5873 (by omega) (by omega) hc57 cnt56
theorem cnt58 : Nat.count (fun n => trialPrimeB n = true) 59000 = 5963 :=
  count_step 58000 1000 59000 90 5873 5963 (by omega) (by omega) hc58 cnt57
theorem cnt59 : Nat.count (fun n => trialPrimeB n = true) 60000 = 6057 :=
  count_step 59000 1000 60000 94 5963 6057 (by omega) (by omega) hc59 cnt58
theorem cnt60 : Nat.count (fun n => trialPrimeB n = true) 61000 = 6145 :=
  count_step 60000 1000 61000 88 6057 6145 (by omega) (by omega) hc60 cnt59
theorem cnt61 : Nat.count (fun n => trialPrimeB n = true) 62000 = 6232 :=
  count_step 61000 1000 62000 87 6145 6232 (by omega) (by omega) hc61 cnt60
theorem cnt62 : Nat.count (fun n => trialPrimeB n = true) 63000 = 6320 :=
  count_step 62000 1000 63000 88 6232 6320 (by omega) (by omega) hc62 cnt61
theorem cnt63 : Nat.count (fun n => trialPrimeB n = true) 64000 = 6413 :=
  count_step 63000 1000 64000 93 6320 6413 (by omega) (by omega) hc63 cnt62
theorem cnt64 : Nat.count (fun n => trialPrimeB n = true) 65000 = 6493 :=
  count_step 64000 1000 65000 80 6413 6493 (by omega) (by omega) hc64 cnt63
theorem cnt65 : Nat.count (fun n => trialPrimeB n = true) 66000 = 6591 :=
  count_step 65000 1000 66000 98 6493 6591 (by omega) (by omega) hc65 cnt64
theorem cnt66 : Nat.count (fun n => trialPrimeB n = true) 67000 = 6675 :=
  count_step 66000 1000 67000 84 6591 6675 (by omega) (by omega) hc66 cnt65
theorem cnt67 : Nat.count (fun n => trialPrimeB n = true) 68000 = 6774 :=
  count_step 67000 1000 68000 99 6675 6774 (by omega) (by omega) hc67 cnt66
theorem cnt68 : Nat.count (fun n => trialPrimeB n = true) 69000 = 6854 :=
  count_step 68000 1000 69000 80 6774 6854 (by omega) (by omega) hc68 cnt67
theorem cnt69 : Nat.count (fun n => trialPrimeB n = true) 70000 = 6935 :=
  count_step 69000 1000 70000 81 6854 6935 (by omega) (by omega) hc69 cnt68
theorem cnt70 : Nat.count (fun n => trialPrimeB n = true) 71000 = 7033 :=
  count_step 70000 1000 71000 98 6935 7033 (by omega) (by omega) hc70 cnt69
theorem cnt71 : Nat.count (fun n => trialPrimeB n = true) 72000 = 7128 :=
  count_step 71000 1000 72000 95 7033 7128 (by omega) (by omega) hc71 cnt70
theorem cnt72 : Nat.count (fun n => trialPrimeB n = true) 73000 = 7218 :=
  count_step 72000 1000 73000 90 7128 7218 (by omega) (by omega) hc72 cnt71
theorem cnt73 : Nat.count (fun n => trialPrimeB n = true) 74000 = 7301 :=
  count_step 73000 1000 74000 83 7218 7301 (by omega) (by omega) hc73 cnt72
theorem cnt74 : Nat.count (fun n => trialPrimeB n = true) 75000 = 7393 :=
  count_step 74000 1000 75000 92 7301 7393 (by omega) (by omega) hc74 cnt73
theorem cnt75 : Nat.count (fun n => trialPrimeB n = true) 76000 = 7484 :=
  count_step 75000 1000 76000 91 7393 7484 (by omega) (by omega) hc75 cnt74
theorem cnt76 : Nat.count (fun n => trialPrimeB n = true) 77000 = 7567 :=
  count_step 76000 1000 77000 83 7484 7567 (by omega) (by omega) hc76 cnt75
theorem cnt77 : Nat.count (fun n => trialPrimeB n = true) 78000 = 7662 :=
  count_step 77000 1000 78000 95 7567 7662 (by omega) (by omega) hc77 cnt76
theorem cnt78 : Nat.count (fun n => trialPrimeB n = true) 79000 = 7746 :=
  count_step 78000 1000 79000 84 7662 7746 (by omega) (by omega) hc78 cnt77
theorem cnt79 : Nat.count (fun n => trialPrimeB n = true) 80000 = 7837 :=
  count_step 79000 1000 80000 91 7746 7837 (by omega) (by omega) hc79 cnt78
theorem cnt80 : Nat.count (fun n => trialPrimeB n = true) 81000 = 7925 :=
  count_step 80000 1000 81000 88 7837 7925 (by omega) (by omega) hc80 cnt79
theorem cnt81 : Nat.count (fun n => trialPrimeB n = true) 82000 = 8017 :=
  count_step 81000 1000 82000 92 7925 8017 (by omega) (by omega) hc81 cnt80
theorem cnt82 : Nat.count (fun n => trialPrimeB n = true) 83000 = 8106 :=
  count_step 82000 1000 83000 89 8017 8106 (by omega) (by omega) hc82 cnt81
theorem cnt83 : Nat.count (fun n => trialPrimeB n = true) 84000 = 8190 :=
  count_step 83000 1000 84000 84 8106 8190 (by omega) (by omega) hc83 cnt82
theorem cnt84 : Nat.count (fun n => trialPrimeB n = true) 85000 = 8277 :=
  count_step 84000 1000 85000 87 8190 8277 (by omega) (by omega) hc84 cnt83
theorem cnt85 : Nat.count (fun n => trialPrimeB n = true) 86000 = 8362 :=
  count_step 85000 1000 86000 85 8277 8362 (by omega) (by omega) hc85 cnt84
theorem cnt86 : Nat.count (fun n => trialPrimeB n = true) 87000 = 8450 :=
  count_step 86000 1000 87000 88 8362 8450 (by omega) (by omega) hc86 cnt85
theorem cnt87 : Nat.count (fun n => trialPrimeB n = true) 88000 = 8543 :=
  count_step 87000 1000 88000 93 8450 8543 (by omega) (by omega) hc87 cnt86
theorem cnt88 : Nat.count (fun n => trialPrimeB n = true) 89000 = 8619 :=
  count_step 88000 1000 89000 76 8543 8619 (by omega) (by omega) hc88 cnt87
theorem cnt89 : Nat.count (fun n => trialPrimeB n = true) 90000 = 8713 :=
  count_step 89000 1000 90000 94 8619 8713 (by omega) (by omega) hc89 cnt88
theorem cnt90 : Nat.count (fun n => trialPrimeB n = true) 91000 = 8802 :=
  count_step 90000 1000 91000 89 8713 8802 (by omega) (by omega) hc90 cnt89
theorem cnt91 : Nat.count (fun n => trialPrimeB n = true) 92000 = 8887 :=
  count_step 91000 1000 92000 85 8802 8887 (by omega) (by omega) hc91 cnt90
theorem cnt92 : Nat.count (fun n => trialPrimeB n = true) 93000 = 8984 :=
  count_step 92000 1000 93000 97 8887 8984 (by omega) (by omega) hc92 cnt91
theorem cnt93 : Nat.count (fun n => trialPrimeB n = true) 94000 = 9070 :=
  count_step 93000 1000 94000 86 8984 9070 (by omega) (by omega) hc93 cnt92
theorem cnt94 : Nat.count (fun n => trialPrimeB n = true) 95000 = 9157 :=
  count_step 94000 1000 95000 87 9070 9157 (by omega) (by omega) hc94 cnt93
theorem cnt95 : Nat.count (fun n => trialPrimeB n = true) 96000 = 9252 :=
  count_step 95000 1000 96000 95 9157 9252 (by omega) (by omega) hc95 cnt94
theorem cnt96 : Nat.count (fun n => trialPrimeB n = true) 97000 = 9336 :=
  count_step 96000 1000 97000 84 9252 9336 (by omega) (by omega) hc96 cnt95
theorem cnt97 : Nat.count (fun n => trialPrimeB n = true) 98000 = 9418 :=
  count_step 97000 1000 98000 82 9336 9418 (by omega) (by omega) hc97 cnt96
theorem cnt98 : Nat.count (fun n => trialPrimeB n = true) 99000 = 9505 :=
  count_step 98000 1000 99000 87 9418 9505 (by omega) (by omega) hc98 cnt97
theorem cnt99 : Nat.count (fun n => trialPrimeB n = true) 100000 = 9592 :=
  count_step 99000 1000 100000 87 9505 9592 (by omega) (by omega) hc99 cnt98
theorem cnt100 : Nat.count (fun n => trialPrimeB n = true) 101000 = 9673 :=
  count_step 100000 1000 101000 81 9592 9673 (by omega) (by omega) hc100 cnt99
theorem cnt101 : Nat.count (fun n => trialPrimeB n = true) 102000 = 9766 :=
  count_step 101000 1000 102000 93 9673 9766 (by omega) (by omega) hc101 cnt100
theorem cnt102 : Nat.count (fun n => trialPrimeB n = true) 103000 = 9853 :=
  count_step 102000 1000 103000 87 9766 9853 (by omega) (by omega) hc102 cnt101
theorem cnt103 : Nat.count (fun n => trialPrimeB n = true) 104000 = 9933 :=
  count_step 103000 1000 104000 80 9853 9933 (by omega) (by omega) hc103 cnt102
theorem cnt104 : Nat.count (fun n => trialPrimeB n = true) 105000 = 10024 :=
  count_step 104000 1000 105000 91 9933 10024 (by omega) (by omega) hc104 cnt103
theorem cnt105 : Nat.count (fun n => trialPrimeB n = true) 106000 = 10106 :=
  count_step 105000 1000 106000 82 10024 10106 (by omega) (by omega) hc105 cnt104
theorem cnt106 : Nat.count (fun n => trialPrimeB n = true) 107000 = 10198 :=
  count_step 106000 1000 107000 92 10106 10198 (by omega) (by omega) hc106 cnt105
theorem cnt107 : Nat.count (fun n => trialPrimeB n = true) 108000 = 10274 :=
  count_step 107000 1000 108000 76 10198 10274 (by omega) (by omega) hc107 cnt106
theorem cnt108 : Nat.count (fun n => trialPrimeB n = true) 109000 = 10365 :=
  count_step 108000 1000 109000 91 10274 10365 (by omega) (by omega) hc108 cnt107
theorem cnt109 : Nat.count (fun n => trialPrimeB n = true) 110000 = 10453 :=
  count_step 109000 1000 110000 88 10365 10453 (by omega) (by omega) hc109 cnt108
theorem cnt110 : Nat.count (fun n => trialPrimeB n = true) 111000 = 10536 :=
  count_step 110000 1000 111000 83 10453 10536 (by omega) (by omega) hc110 cnt109
theorem cnt111 : Nat.count (fun n => trialPrimeB n = true) 112000 = 10620 :=
  count_step 111000 1000 112000 84 10536 10620 (by omega) (by omega) hc111 cnt110
theorem cnt112 : Nat.count (fun n => trialPrimeB n = true) 113000 = 10701 :=
  count_step 112000 1000 113000 81 10620 10701 (by omega) (by omega) hc112 cnt111
theorem cnt113 : Nat.count (fun n => trialPrimeB n = true) 114000 = 10789 :=
  count_step 113000 1000 114000 88 10701 10789 (by omega) (by omega) hc113 cnt112
theorem cnt114 : Nat.count (fun n => trialPrimeB n = true) 115000 = 10871 :=
  count_step 114000 1000 115000 82 10789 10871 (by omega) (by omega) hc114 cnt113
theorem cnt115 : Nat.count (fun n => trialPrimeB n = true) 116000 = 10964 :=
  count_step 115000 1000 116000 93 10871 10964 (by omega) (by omega) hc115 cnt114
theorem cnt116 : Nat.count (fun n => trialPrimeB n = true) 117000 = 11045 :=
  count_step 116000 1000 117000 81 10964 11045 (by omega) (by omega) hc116 cnt115
theorem cnt117 : Nat.count (fun n => trialPrimeB n = true) 118000 = 11135 :=
  count_step 117000 1000 118000 90 11045 11135 (by omega) (by omega) hc117 cnt116
theorem cnt118 : Nat.count (fun n => trialPrimeB n = true) 119000 = 11214 :=
  count_step 118000 1000 119000 79 11135 11214 (by omega) (by omega) hc118 cnt117
theorem cnt119 : Nat.count (fun n => trialPrimeB n = true) 120000 = 11301 :=
  count_step 119000 1000 120000 87 11214 11301 (by omega) (by omega) hc119 cnt118
theorem cnt120 : Nat.count (fun n => trialPrimeB n = true) 121000 = 11389 :=
  count_step 120000 1000 121000 88 11301 11389 (by omega) (by omega) hc120 cnt119
theorem cnt121 : Nat.count (fun n => trialPrimeB n = true) 122000 = 11475 :=
  count_step 121000 1000 122000 86 11389 11475 (by omega) (by omega) hc121 cnt120
theorem cnt122 : Nat.count (fun n => trialPrimeB n = true) 123000 = 11563 :=
  count_step 122000 1000 123000 88 11475 11563 (by omega) (by omega) hc122 cnt121
theorem cnt123 : Nat.count (fun n => trialPrimeB n = true) 124000 = 11651 :=
  count_step 123000 1000 124000 88 11563 11651 (by omega) (by omega) hc123 cnt122
theorem cnt124 : Nat.count (fun n => trialPrimeB n = true) 125000 = 11734 :=
  count_step 124000 1000 125000 83 11651 11734 (by omega) (by omega) hc124 cnt123
theorem cnt125 : Nat.count (fun n => trialPrimeB n = true) 126000 = 11818 :=
  count_step 125000 1000 126000 84 11734 11818 (by omega) (by omega) hc125 cnt124
theorem cnt126 : Nat.count (fun n => trialPrimeB n = true) 127000 = 11901 :=
  count_step 126000 1000 127000 83 11818 11901 (by omega) (by omega) hc126 cnt125
theorem cnt127 : Nat.count (fun n => trialPrimeB n = true) 128000 = 11987 :=
  count_step 127000 1000 128000 86 11901 11987 (by omega) (by omega) hc127 cnt126
theorem cnt128 : Nat.count (fun n => trialPrimeB n = true) 129000 = 12076 :=
  count_step 128000 1000 129000 89 11987 12076 (by omega) (by omega) hc128 cnt127
theorem cnt129 : Nat.count (fun n => trialPrimeB n = true) 130000 = 12159 :=
  count_step 129000 1000 130000 83 12076 12159 (by omega) (by omega) hc129 cnt128
theorem cnt130 : Nat.count (fun n => trialPrimeB n = true) 131000 = 12244 :=
  count_step 130000 1000 131000 85 12159 12244 (by omega) (by omega) hc130 cnt129
theorem cnt131 : Nat.count (fun n => trialPrimeB n = true) 132000 = 12327 :=
  count_step 131000 1000 132000 83 12244 12327 (by omega) (by omega) hc131 cnt130
theorem cnt132 : Nat.count (fun n => trialPrimeB n = true) 133000 = 12414 :=
  count_step 132000 1000 133000 87 12327 12414 (by omega) (by omega) hc132 cnt131
theorem cnt133 : Nat.count (fun n => trialPrimeB n = true) 134000 = 12496 :=
  count_step 133000 1000 134000 82 12414 12496 (by omega) (by omega) hc133 cnt132
theorem cnt134 : Nat.count (fun n => trialPrimeB n = true) 135000 = 12576 :=
  count_step 134000 1000 135000 80 12496 12576 (by omega) (by omega) hc134 cnt133
theorem cnt135 : Nat.count (fun n => trialPrimeB n = true) 136000 = 12665 :=
  count_step 135000 1000 136000 89 12576 12665 (by omega) (by omega) hc135 cnt134
theorem cnt136 : Nat.count (fun n => trialPrimeB n = true) 137000 = 12761 :=
  count_step 136000 1000 137000 96 12665 12761 (by omega) (by omega) hc136 cnt135
theorem cnt137 : Nat.count (fun n => trialPrimeB n = true) 138000 = 12841 :=
  count_step 137000 1000 138000 80 12761 12841 (by omega) (by omega) hc137 cnt136
theorem cnt138 : Nat.count (fun n => trialPrimeB n = true) 139000 = 12926 :=
  count_step 138000 1000 139000 85 12841 12926 (by omega) (by omega) hc138 cnt137
theorem cnt139 : Nat.count (fun n => trialPrimeB n = true) 140000 = 13010 :=
  count_step 139000 1000 140000 84 12926 13010 (by omega) (by omega) hc139 cnt138
theorem cnt140 : Nat.count (fun n => trialPrimeB n = true) 141000 = 13097 :=
  count_step 140000 1000 141000 87 13010 13097 (by omega) (by omega) hc140 cnt139
theorem cnt141 : Nat.count (fun n => trialPrimeB n = true) 142000 = 13184 :=
  count_step 141000 1000 142000 87 13097 13184 (by omega) (by omega) hc141 cnt140
theorem cnt142 : Nat.count (fun n => trialPrimeB n = true) 143000 = 13266 :=
  count_step 142000 1000 143000 82 13184 13266 (by omega) (by omega) hc142 cnt141
theorem cnt143 : Nat.count (fun n => trialPrimeB n = true) 144000 = 13343 :=
  count_step 143000 1000 144000 77 13266 13343 (by omega) (by omega) hc143 cnt142
theorem cnt144 : Nat.count (fun n => trialPrimeB n = true) 145000 = 13422 :=
  count_step 144000 1000 145000 79 13343 13422 (by omega) (by omega) hc144 cnt143
theorem cnt145 : Nat.count (fun n => trialPrimeB n = true) 146000 = 13507 :=
  count_step 145000 1000 146000 85 13422 13507 (by omega) (by omega) hc145 cnt144
theorem cnt146 : Nat.count (fun n => trialPrimeB n = true) 147000 = 13591 :=
  count_step 146000 1000 147000 84 13507 13591 (by omega) (by omega) hc146 cnt145
theorem cnt147 : Nat.count (fun n => trialPrimeB n = true) 148000 = 13674 :=
  count_step 147000 1000 148000 83 13591 13674 (by omega) (by omega) hc147 cnt146
theorem cnt148 : Nat.count (fun n => trialPrimeB n = true) 149000 = 13757 :=
  count_step 148000 1000 149000 83 13674 13757 (by omega) (by omega) hc148 cnt147
theorem cnt149 : Nat.count (fun n => trialPrimeB n = true) 150000 = 13848 :=
  count_step 149000 1000 150000 91 13757 13848 (by omega) (by omega) hc149 cnt148
theorem cnt150 : Nat.count (fun n => trialPrimeB n = true) 151000 = 13933 :=
  count_step 150000 1000 151000 85 13848 13933 (by omega) (by omega) hc150 cnt149
theorem cnt151 : Nat.count (fun n => trialPrimeB n = true) 152000 = 14023 :=
  count_step 151000 1000 152000 90 13933 14023 (by omega) (by omega) hc151 cnt150
theorem cnt152 : Nat.count (fun n => trialPrimeB n = true) 153000 = 14111 :=
  count_step 152000 1000 153000 88 14023 14111 (by omega) (by omega) hc152 cnt151
theorem cnt153 : Nat.count (fun n => trialPrimeB n = true) 154000 = 14188 :=
  count_step 153000 1000 154000 77 14111 14188 (by omega) (by omega) hc153 cnt152
theorem cnt154 : Nat.count (fun n => trialPrimeB n = true) 155000 = 14272 :=
  count_step 154000 1000 155000 84 14188 14272 (by omega) (by omega) hc154 cnt153
theorem cnt155 : Nat.count (fun n => trialPrimeB n = true) 156000 = 14357 :=
  count_step 155000 1000 156000 85 14272 14357 (by omega) (by omega) hc155 cnt154
theorem cnt156 : Nat.count (fun n => trialPrimeB n = true) 157000 = 14433 :=
  count_step 156000 1000 157000 76 14357 14433 (by omega) (by omega) hc156 cnt155
theorem cnt157 : Nat.count (fun n => trialPrimeB n = true) 158000 = 14521 :=
  count_step 157000 1000 158000 88 14433 14521 (by omega) (by omega) hc157 cnt156
theorem cnt158 : Nat.count (fun n => trialPrimeB n = true) 159000 = 14598 :=
  count_step 158000 1000 159000 77 14521 14598 (by omega) (by omega) hc158 cnt157
theorem cnt159 : Nat.count (fun n => trialPrimeB n = true) 160000 = 14683 :=
  count_step 159000 1000 160000 85 14598 14683 (by omega) (by omega) hc159 cnt158
theorem cnt160 : Nat.count (fun n => trialPrimeB n = true) 161000 = 14768 :=
  count_step 160000 1000 161000 85 14683 14768 (by omega) (by omega) hc160 cnt159
theorem cnt161 : Nat.count (fun n => trialPrimeB n = true) 162000 = 14852 :=
  count_step 161000 1000 162000 84 14768 14852 (by omega) (by omega) hc161 cnt160
theorem cnt162 : Nat.count (fun n => trialPrimeB n = true) 163000 = 14933 :=
  count_step 162000 1000 163000 81 14852 14933 (by omega) (by omega) hc162 cnt161
theorem cnt163 : Nat.count (fun n => trialPrimeB n = true) 164000 = 15016 :=
  count_step 163000 1000 164000 83 14933 15016 (by omega) (by omega) hc163 cnt162
theorem cnt164 : Nat.count (fun n => trialPrimeB n = true) 165000 = 15093 :=
  count_step 164000 1000 165000 77 15016 15093 (by omega) (by omega) hc164 cnt163
theorem cnt165 : Nat.count (fun n => trialPrimeB n = true) 166000 = 15173 :=
  count_step 165000 1000 166000 80 15093 15173 (by omega) (by omega) hc165 cnt164
theorem cnt166 : Nat.count (fun n => trialPrimeB n = true) 167000 = 15254 :=
  count_step 166000 1000 167000 81 15173 15254 (by omega) (by omega) hc166 cnt165
theorem cnt167 : Nat.count (fun n => trialPrimeB n = true) 168000 = 15337 :=
  count_step 167000 1000 168000 83 15254 15337 (by omega) (by omega) hc167 cnt166
theorem cnt168 : Nat.count (fun n => trialPrimeB n = true) 169000 = 15410 :=
  count_step 168000 1000 169000 73 15337 15410 (by omega) (by omega) hc168 cnt167
theorem cnt169 : Nat.count (fun n => trialPrimeB n = true) 170000 = 15497 :=
  count_step 169000 1000 170000 87 15410 15497 (by omega) (by omega) hc169 cnt168
theorem cnt170 : Nat.count (fun n => trialPrimeB n = true) 171000 = 15584 :=
  count_step 170000 1000 171000 87 15497 15584 (by omega) (by omega) hc170 cnt169
theorem cnt171 : Nat.count (fun n => trialPrimeB n = true) 172000 = 15665 :=
  count_step 171000 1000 172000 81 15584 15665 (by omega) (by omega) hc171 cnt170
theorem cnt172 : Nat.count (fun n => trialPrimeB n = true) 173000 = 15754 :=
  count_step 172000 1000 173000 89 15665 15754 (by omega) (by omega) hc172 cnt171
theorem cnt173 : Nat.count (fun n => trialPrimeB n = true) 174000 = 15833 :=
  count_step 173000 1000 174000 79 15754 15833 (by omega) (by omega) hc173 cnt172
theorem cnt174 : Nat.count (fun n => trialPrimeB n = true) 175000 = 15916 :=
  count_step 174000 1000 175000 83 15833 15916 (by omega) (by omega) hc174 cnt173
theorem cnt175 : Nat.count (fun n => trialPrimeB n = true) 176000 = 15991 :=
  count_step 175000 1000 176000 75 15916 15991 (by omega) (by omega) hc175 cnt174
theorem cnt176 : Nat.count (fun n => trialPrimeB n = true) 177000 = 16086 :=
  count_step 176000 1000 177000 95 15991 16086 (by omega) (by omega) hc176 cnt175
theorem cnt177 : Nat.count (fun n => trialPrimeB n = true) 178000 = 16159 :=
  count_step 177000 1000 178000 73 16086 16159 (by omega) (by omega) hc177 cnt176
theorem cnt178 : Nat.count (fun n => trialPrimeB n = true) 179000 = 16248 :=
  count_step 178000 1000 179000 89 16159 16248 (by omega) (by omega) hc178 cnt177
theorem cnt179 : Nat.count (fun n => trialPrimeB n = true) 180000 = 16342 :=
  count_step 179000 1000 180000 94 16248 16342 (by omega) (by omega) hc179 cnt178
theorem cnt180 : Nat.count (fun n => trialPrimeB n = true) 181000 = 16413 :=
  count_step 180000 1000 181000 71 16342 16413 (by omega) (by omega) hc180 cnt179
theorem cnt181 : Nat.count (fun n => trialPrimeB n = true) 182000 = 16492 :=
  count_step 181000 1000 182000 79 16413 16492 (by omega) (by omega) hc181 cnt180
theorem cnt182 : Nat.count (fun n => trialPrimeB n = true) 183000 = 16583 :=
  count_step 182000 1000 183000 91 16492 16583 (by omega) (by omega) hc182 cnt181
theorem cnt183 : Nat.count (fun n => trialPrimeB n = true) 184000 = 16662 :=
  count_step 183000 1000 184000 79 16583 16662 (by omega) (by omega) hc183 cnt182
theorem cnt184 : Nat.count (fun n => trialPrimeB n = true) 185000 = 16745 :=
  count_step 184000 1000 185000 83 16662 16745 (by omega) (by omega) hc184 cnt183
theorem cnt185 : Nat.count (fun n => trialPrimeB n = true) 186000 = 16836 :=
  count_step 185000 1000 186000 91 16745 16836 (by omega) (by omega) hc185 cnt184
theorem cnt186 : Nat.count (fun n => trialPrimeB n = true) 187000 = 16915 :=
  count_step 186000 1000 187000 79 16836 16915 (by omega) (by omega) hc186 cnt185
theorem cnt187 : Nat.count (fun n => trialPrimeB n = true) 188000 = 17002 :=
  count_step 187000 1000 188000 87 16915 17002 (by omega) (by omega) hc187 cnt186
theorem cnt188 : Nat.count (fun n => trialPrimeB n = true) 189000 = 17082 :=
  count_step 188000 1000 189000 80 17002 17082 (by omega) (by omega) hc188 cnt187
theorem cnt189 : Nat.count (fun n => trialPrimeB n = true) 190000 = 17170 :=
  count_step 189000 1000 190000 88 17082 17170 (by omega) (by omega) hc189 cnt188
theorem cnt190 : Nat.count (fun n => trialPrimeB n = true) 191000 = 17245 :=
  count_step 190000 1000 191000 75 17170 17245 (by omega) (by omega) hc190 cnt189
theorem cnt191 : Nat.count (fun n => trialPrimeB n = true) 192000 = 17326 :=
  count_step 191000 1000 192000 81 17245 17326 (by omega) (by omega) hc191 cnt190
theorem cnt192 : Nat.count (fun n => trialPrimeB n = true) 193000 = 17415 :=
  count_step 192000 1000 193000 89 17326 17415 (by omega) (by omega) hc192 cnt191
theorem cnt193 : Nat.count (fun n => trialPrimeB n = true) 194000 = 17499 :=
  count_step 193000 1000 194000 84 17415 17499 (by omega) (by omega) hc193 cnt192
theorem cnt194 : Nat.count (fun n => trialPrimeB n = true) 195000 = 17573 :=
  count_step 194000 1000 195000 74 17499 17573 (by omega) (by omega) hc194 cnt193
theorem cnt195 : Nat.count (fun n => trialPrimeB n = true) 196000 = 17658 :=
  count_step 195000 1000 196000 85 17573 17658 (by omega) (by omega) hc195 cnt194
theorem cnt196 : Nat.count (fun n => trialPrimeB n = true) 197000 = 17734 :=
  count_step 196000 1000 197000 76 17658 17734 (by omega) (by omega) hc196 cnt195
theorem cnt197 : Nat.count (fun n => trialPrimeB n = true) 198000 = 17821 :=
  count_step 197000 1000 198000 87 17734 17821 (by omega) (by omega) hc197 cnt196
theorem cnt198 : Nat.count (fun n => trialPrimeB n = true) 199000 = 17907 :=
  count_step 198000 1000 199000 86 17821 17907 (by omega) (by omega) hc198 cnt197
theorem cnt199 : Nat.count (fun n => trialPrimeB n = true) 200000 = 17984 :=
  count_step 199000 1000 200000 77 17907 17984 (by omega) (by omega) hc199 cnt198
theorem cnt200 : Nat.count (fun n => trialPrimeB n = true) 201000 = 18061 :=
  count_step 200000 1000 201000 77 17984 18061 (by omega) (by omega) hc200 cnt199
theorem cnt201 : Nat.count (fun n => trialPrimeB n = true) 202000 = 18148 :=
  count_step 201000 1000 202000 87 18061 18148 (by omega) (by omega) hc201 cnt200
theorem cnt202 : Nat.count (fun n => trialPrimeB n = true) 203000 = 18226 :=
  count_step 202000 1000 203000 78 18148 18226 (by omega) (by omega) hc202 cnt201
theorem cnt203 : Nat.count (fun n => trialPrimeB n = true) 204000 = 18304 :=
  count_step 203000 1000 204000 78 18226 18304 (by omega) (by omega) hc203 cnt202
theorem cnt204 : Nat.count (fun n => trialPrimeB n = true) 205000 = 18381 :=
  count_step 204000 1000 205000 77 18304 18381 (by omega) (by omega) hc204 cnt203
theorem cnt205 : Nat.count (fun n => trialPrimeB n = true) 206000 = 18464 :=
  count_step 205000 1000 206000 83 18381 18464 (by omega) (by omega) hc205 cnt204
theorem cnt206 : Nat.count (fun n => trialPrimeB n = true) 207000 = 18547 :=
  count_step 206000 1000 207000 83 18464 18547 (by omega) (by omega) hc206 cnt205
theorem cnt207 : Nat.count (fun n => trialPrimeB n = true) 208000 = 18634 :=
  count_step 207000 1000 208000 87 18547 18634 (by omega) (by omega) hc207 cnt206
theorem cnt208 : Nat.count (fun n => trialPrimeB n = true) 209000 = 18719 :=
  count_step 208000 1000 209000 85 18634 18719 (by omega) (by omega) hc208 cnt207
theorem cnt209 : Nat.count (fun n => trialPrimeB n = true) 210000 = 18807 :=
  count_step 209000 1000 210000 88 18719 18807 (by omega) (by omega) hc209 cnt208
theorem cnt210 : Nat.count (fun n => trialPrimeB n = true) 211000 = 18891 :=
  count_step 210000 1000 211000 84 18807 18891 (by omega) (by omega) hc210 cnt209
theorem cnt211 : Nat.count (fun n => trialPrimeB n = true) 212000 = 18977 :=
  count_step 211000 1000 212000 86 18891 18977 (by omega) (by omega) hc211 cnt210
theorem cnt212 : Nat.count (fun n => trialPrimeB n = true) 213000 = 19046 :=
  count_step 212000 1000 213000 69 18977 19046 (by omega) (by omega) hc212 cnt211
theorem cnt213 : Nat.count (fun n => trialPrimeB n = true) 214000 = 19127 :=
  count_step 213000 1000 214000 81 19046 19127 (by omega) (by omega) hc213 cnt212
theorem cnt214 : Nat.count (fun n => trialPrimeB n = true) 215000 = 19213 :=
  count_step 214000 1000 215000 86 19127 19213 (by omega) (by omega) hc214 cnt213
theorem cnt215 : Nat.count (fun n => trialPrimeB n = true) 216000 = 19287 :=
  count_step 215000 1000 216000 74 19213 19287 (by omega) (by omega) hc215 cnt214
theorem cnt216 : Nat.count (fun n => trialPrimeB n = true) 217000 = 19363 :=
  count_step 216000 1000 217000 76 19287 19363 (by omega) (by omega) hc216 cnt215
theorem cnt217 : Nat.count (fun n => trialPrimeB n = true) 218000 = 19443 :=
  count_step 217000 1000 218000 80 19363 19443 (by omega) (by omega) hc217 cnt216
theorem cnt218 : Nat.count (fun n => trialPrimeB n = true) 219000 = 19527 :=
  count_step 218000 1000 219000 84 19443 19527 (by omega) (by omega) hc218 cnt217
theorem cnt219 : Nat.count (fun n => trialPrimeB n = true) 220000 = 19618 :=
  count_step 219000 1000 220000 91 19527 19618 (by omega) (by omega) hc219 cnt218
theorem cnt220 : Nat.count (fun n => trialPrimeB n = true) 221000 = 19696 :=
  count_step 220000 1000 221000 78 19618 19696 (by omega) (by omega) hc220 cnt219
theorem cnt221 : Nat.count (fun n => trialPrimeB n = true) 222000 = 19776 :=
  count_step 221000 1000 222000 80 19696 19776 (by omega) (by omega) hc221 cnt220
theorem cnt222 : Nat.count (fun n => trialPrimeB n = true) 223000 = 19857 :=
  count_step 222000 1000 223000 81 19776 19857 (by omega) (by omega) hc222 cnt221
theorem cnt223 : Nat.count (fun n => trialPrimeB n = true) 224000 = 19937 :=
  count_step 223000 1000 224000 80 19857 19937 (by omega) (by omega) hc223 cnt222
theorem cnt224 : Nat.count (fun n => trialPrimeB n = true) 225000 = 20020 :=
  count_step 224000 1000 225000 83 19937 20020 (by omega) (by omega) hc224 cnt223
theorem cnt225 : Nat.count (fun n => trialPrimeB n = true) 226000 = 20104 :=
  count_step 225000 1000 226000 84 20020 20104 (by omega) (by omega) hc225 cnt224
theorem cnt226 : Nat.count (fun n => trialPrimeB n = true) 227000 = 20180 :=
  count_step 226000 1000 227000 76 20104 20180 (by omega) (by omega) hc226 cnt225
theorem cnt227 : Nat.count (fun n => trialPrimeB n = true) 228000 = 20260 :=
  count_step 227000 1000 228000 80 20180 20260 (by omega) (by omega) hc227 cnt226
theorem cnt228 : Nat.count (fun n => trialPrimeB n = true) 229000 = 20349 :=
  count_step 228000 1000 229000 89 20260 20349 (by omega) (by omega) hc228 cnt227
theorem cnt229 : Nat.count (fun n => trialPrimeB n = true) 230000 = 20437 :=
  count_step 229000 1000 230000 88 20349 20437 (by omega) (by omega) hc229 cnt228
theorem cnt230 : Nat.count (fun n => trialPrimeB n = true) 231000 = 20521 :=
  count_step 230000 1000 231000 84 20437 20521 (by omega) (by omega) hc230 cnt229
theorem cnt231 : Nat.count (fun n => trialPrimeB n = true) 232000 = 20599 :=
  count_step 231000 1000 232000 78 20521 20599 (by omega) (by omega) hc231 cnt230
theorem cnt232 : Nat.count (fun n => trialPrimeB n = true) 233000 = 20675 :=
  count_step 232000 1000 233000 76 20599 20675 (by omega) (by omega) hc232 cnt231
theorem cnt233 : Nat.count (fun n => trialPrimeB n = true) 234000 = 20746 :=
  count_step 233000 1000 234000 71 20675 20746 (by omega) (by omega) hc233 cnt232
theorem cnt234 : Nat.count (fun n => trialPrimeB n = true) 235000 = 20833 :=
  count_step 234000 1000 235000 87 20746 20833 (by omega) (by omega) hc234 cnt233
theorem cnt235 : Nat.count (fun n => trialPrimeB n = true) 236000 = 20906 :=
  count_step 235000 1000 236000 73 20833 20906 (by omega) (by omega) hc235 cnt234
theorem cnt236 : Nat.count (fun n => trialPrimeB n = true) 237000 = 20982 :=
  count_step 236000 1000 237000 76 20906 20982 (by omega) (by omega) hc236 cnt235
theorem cnt237 : Nat.count (fun n => trialPrimeB n = true) 238000 = 21055 :=
  count_step 237000 1000 238000 73 20982 21055 (by omega) (by omega) hc237 cnt236
theorem cnt238 : Nat.count (fun n => trialPrimeB n = true) 239000 = 21142 :=
  count_step 238000 1000 239000 87 21055 21142 (by omega) (by omega) hc238 cnt237
theorem cnt239 : Nat.count (fun n => trialPrimeB n = true) 240000 = 21221 :=
  count_step 239000 1000 240000 79 21142 21221 (by omega) (by omega) hc239 cnt238
theorem cnt240 : Nat.count (fun n => trialPrimeB n = true) 241000 = 21301 :=
  count_step 240000 1000 241000 80 21221 21301 (by omega) (by omega) hc240 cnt239
theorem cnt241 : Nat.count (fun n => trialPrimeB n = true) 242000 = 21392 :=
  count_step 241000 1000 242000 91 21301 21392 (by omega) (by omega) hc241 cnt240
theorem cnt242 : Nat.count (fun n => trialPrimeB n = true) 243000 = 21468 :=
  count_step 242000 1000 243000 76 21392 21468 (by omega) (by omega) hc242 cnt241
theorem cnt243 : Nat.count (fun n => trialPrimeB n = true) 244000 = 21545 :=
  count_step 243000 1000 244000 77 21468 21545 (by omega) (by omega) hc243 cnt242
theorem cnt244 : Nat.count (fun n => trialPrimeB n = true) 245000 = 21633 :=
  count_step 244000 1000 245000 88 21545 21633 (by omega) (by omega) hc244 cnt243
theorem cnt245 : Nat.count (fun n => trialPrimeB n = true) 246000 = 21713 :=
  count_step 245000 1000 246000 80 21633 21713 (by omega) (by omega) hc245 cnt244
theorem cnt246 : Nat.count (fun n => trialPrimeB n = true) 247000 = 21797 :=
  count_step 246000 1000 247000 84 21713 21797 (by omega) (by omega) hc246 cnt245
theorem cnt247 : Nat.count (fun n => trialPrimeB n = true) 248000 = 21876 :=
  count_step 247000 1000 248000 79 21797 21876 (by omega) (by omega) hc247 cnt246
theorem cnt248 : Nat.count (fun n => trialPrimeB n = true) 249000 = 21964 :=
  count_step 248000 1000 249000 88 21876 21964 (by omega) (by omega) hc248 cnt247
theorem cnt249 : Nat.count (fun n => trialPrimeB n = true) 250000 = 22044 :=
  count_step 249000 1000 250000 80 21964 22044 (by omega) (by omega) hc249 cnt248
theorem cnt250 : Nat.count (fun n => trialPrimeB n = true) 251000 = 22115 :=
  count_step 250000 1000 251000 71 22044 22115 (by omega) (by omega) hc250 cnt249
theorem cnt251 : Nat.count (fun n => trialPrimeB n = true) 252000 = 22203 :=
  count_step 251000 1000 252000 88 22115 22203 (by omega) (by omega) hc251 cnt250
theorem cnt252 : Nat.count (fun n => trialPrimeB n = true) 253000 = 22281 :=
  count_step 252000 1000 253000 78 22203 22281 (by omega) (by omega) hc252 cnt251
theorem cnt253 : Nat.count (fun n => trialPrimeB n = true) 254000 = 22362 :=
  count_step 253000 1000 254000 81 22281 22362 (by omega) (by omega) hc253 cnt252
theorem cnt254 : Nat.count (fun n => trialPrimeB n = true) 255000 = 22438 :=
  count_step 254000 1000 255000 76 22362 22438 (by omega) (by omega) hc254 cnt253
theorem cnt255 : Nat.count (fun n => trialPrimeB n = true) 256000 = 22525 :=
  count_step 255000 1000 256000 87 22438 22525 (by omega) (by omega) hc255 cnt254
theorem cnt256 : Nat.count (fun n => trialPrimeB n = true) 257000 = 22597 :=
  count_step 256000 1000 257000 72 22525 22597 (by omega) (by omega) hc256 cnt255
theorem cnt257 : Nat.count (fun n => trialPrimeB n = true) 258000 = 22675 :=
  count_step 257000 1000 258000 78 22597 22675 (by omega) (by omega) hc257 cnt256
theorem cnt258 : Nat.count (fun n => trialPrimeB n = true) 259000 = 22761 :=
  count_step 258000 1000 259000 86 22675 22761 (by omega) (by omega) hc258 cnt257
theorem cnt259 : Nat.count (fun n => trialPrimeB n = true) 260000 = 22837 :=
  count_step 259000 1000 260000 76 22761 22837 (by omega) (by omega) hc259 cnt258
theorem cnt260 : Nat.count (fun n => trialPrimeB n = true) 261000 = 22914 :=
  count_step 260000 1000 261000 77 22837 22914 (by omega) (by omega) hc260 cnt259
theorem cnt261 : Nat.count (fun n => trialPrimeB n = true) 262000 = 22987 :=
  count_step 261000 1000 262000 73 22914 22987 (by omega) (by omega) hc261 cnt260
theorem cnt262 : Nat.count (fun n => trialPrimeB n = true) 263000 = 23066 :=
  count_step 262000 1000 263000 79 22987 23066 (by omega) (by omega) hc262 cnt261
theorem cnt263 : Nat.count (fun n => trialPrimeB n = true) 264000 = 23150 :=
  count_step 263000 1000 264000 84 23066 23150 (by omega) (by omega) hc263 cnt262
theorem cnt264 : Nat.count (fun n => trialPrimeB n = true) 265000 = 23230 :=
  count_step 264000 1000 265000 80 23150 23230 (by omega) (by omega) hc264 cnt263
theorem cnt265 : Nat.count (fun n => trialPrimeB n = true) 266000 = 23308 :=
  count_step 265000 1000 266000 78 23230 23308 (by omega) (by omega) hc265 cnt264
theorem cnt266 : Nat.count (fun n => trialPrimeB n = true) 267000 = 23395 :=
  count_step 266000 1000 267000 87 23308 23395 (by omega) (by omega) hc266 cnt265
theorem cnt267 : Nat.count (fun n => trialPrimeB n = true) 268000 = 23489 :=
  count_step 267000 1000 268000 94 23395 23489 (by omega) (by omega) hc267 cnt266
theorem cnt268 : Nat.count (fun n => trialPrimeB n = true) 269000 = 23564 :=
  count_step 268000 1000 269000 75 23489 23564 (by omega) (by omega) hc268 cnt267
theorem cnt269 : Nat.count (fun n => trialPrimeB n = true) 270000 = 23642 :=
  count_step 269000 1000 270000 78 23564 23642 (by omega) (by omega) hc269 cnt268
theorem cnt270 : Nat.count (fun n => trialPrimeB n = true) 271000 = 23726 :=
  count_step 270000 1000 271000 84 23642 23726 (by omega) (by omega) hc270 cnt269
theorem cnt271 : Nat.count (fun n => trialPrimeB n = true) 272000 = 23804 :=
  count_step 271000 1000 272000 78 23726 23804 (by omega) (by omega) hc271 cnt270
theorem cnt272 : Nat.count (fun n => trialPrimeB n = true) 273000 = 23887 :=
  count_step 272000 1000 273000 83 23804 23887 (by omega) (by omega) hc272 cnt271
theorem cnt273 : Nat.count (fun n => trialPrimeB n = true) 274000 = 23958 :=
  count_step 273000 1000 274000 71 23887 23958 (by omega) (by omega) hc273 cnt272
theorem cnt274 : Nat.count (fun n => trialPrimeB n = true) 275000 = 24038 :=
  count_step 274000 1000 275000 80 23958 24038 (by omega) (by omega) hc274 cnt273
theorem cnt275 : Nat.count (fun n => trialPrimeB n = true) 276000 = 24121 :=
  count_step 275000 1000 276000 83 24038 24121 (by omega) (by omega) hc275 cnt274
theorem cnt276 : Nat.count (fun n => trialPrimeB n = true) 277000 = 24204 :=
  count_step 276000 1000 277000 83 24121 24204 (by omega) (by omega) hc276 cnt275
theorem cnt277 : Nat.count (fun n => trialPrimeB n = true) 278000 = 24278 :=
  count_step 277000 1000 278000 74 24204 24278 (by omega) (by omega) hc277 cnt276
theorem cnt278 : Nat.count (fun n => trialPrimeB n = true) 279000 = 24359 :=
  count_step 278000 1000 279000 81 24278 24359 (by omega) (by omega) hc278 cnt277
theorem cnt279 : Nat.count (fun n => trialPrimeB n = true) 280000 = 24432 :=
  count_step 279000 1000 280000 73 24359 24432 (by omega) (by omega) hc279 cnt278
theorem cnt280 : Nat.count (fun n => trialPrimeB n = true) 281000 = 24519 :=
  count_step 280000 1000 281000 87 24432 24519 (by omega) (by omega) hc280 cnt279
theorem cnt281 : Nat.count (fun n => trialPrimeB n = true) 282000 = 24604 :=
  count_step 281000 1000 282000 85 24519 24604 (by omega) (by omega) hc281 cnt280
theorem cnt282 : Nat.count (fun n => trialPrimeB n = true) 283000 = 24681 :=
  count_step 282000 1000 283000 77 24604 24681 (by omega) (by omega) hc282 cnt281
theorem cnt283 : Nat.count (fun n => trialPrimeB n = true) 284000 = 24753 :=
  count_step 283000 1000 284000 72 24681 24753 (by omega) (by omega) hc283 cnt282
theorem cnt284 : Nat.count (fun n => trialPrimeB n = true) 285000 = 24843 :=
  count_step 284000 1000 285000 90 24753 24843 (by omega) (by omega) hc284 cnt283
theorem cnt285 : Nat.count (fun n => trialPrimeB n = true) 286000 = 24920 :=
  count_step 285000 1000 286000 77 24843 24920 (by omega) (by omega) hc285 cnt284
theorem cnt286 : Nat.count (fun n => trialPrimeB n = true) 287000 = 24991 :=
  count_step 286000 1000 287000 71 24920 24991 (by omega) (by omega) hc286 cnt285
theorem cnt287 : Nat.count (fun n => trialPrimeB n = true) 288000 = 25062 :=
  count_step 287000 1000 288000 71 24991 25062 (by omega) (by omega) hc287 cnt286
theorem cnt288 : Nat.count (fun n => trialPrimeB n = true) 289000 = 25139 :=
  count_step 288000 1000 289000 77 25062 25139 (by omega) (by omega) hc288 cnt287
theorem cnt289 : Nat.count (fun n => trialPrimeB n = true) 290000 = 25224 :=
  count_step 289000 1000 290000 85 25139 25224 (by omega) (by omega) hc289 cnt288
theorem cnt290 : Nat.count (fun n => trialPrimeB n = true) 291000 = 25308 :=
  count_step 290000 1000 291000 84 25224 25308 (by omega) (by omega) hc290 cnt289
theorem cnt291 : Nat.count (fun n => trialPrimeB n = true) 292000 = 25385 :=
  count_step 291000 1000 292000 77 25308 25385 (by omega) (by omega) hc291 cnt290
theorem cnt292 : Nat.count (fun n => trialPrimeB n = true) 293000 = 25463 :=
  count_step 292000 1000 293000 78 25385 25463 (by omega) (by omega) hc292 cnt291
theorem cnt293 : Nat.count (fun n => trialPrimeB n = true) 294000 = 25531 :=
  count_step 293000 1000 294000 68 25463 25531 (by omega) (by omega) hc293 cnt292
theorem cnt294 : Nat.count (fun n => trialPrimeB n = true) 295000 = 25616 :=
  count_step 294000 1000 295000 85 25531 25616 (by omega) (by omega) hc294 cnt293
theorem cnt295 : Nat.count (fun n => trialPrimeB n = true) 296000 = 25691 :=
  count_step 295000 1000 296000 75 25616 25691 (by omega) (by omega) hc295 cnt294
theorem cnt296 : Nat.count (fun n => trialPrimeB n = true) 297000 = 25773 :=
  count_step 296000 1000 297000 82 25691 25773 (by omega) (by omega) hc296 cnt295
theorem cnt297 : Nat.count (fun n => trialPrimeB n = true) 298000 = 25846 :=
  count_step 297000 1000 298000 73 25773 25846 (by omega) (by omega) hc297 cnt296
theorem cnt298 : Nat.count (fun n => trialPrimeB n = true) 299000 = 25919 :=
  count_step 298000 1000 299000 73 25846 25919 (by omega) (by omega) hc298 cnt297
theorem cnt299 : Nat.count (fun n => trialPrimeB n = true) 300000 = 25997 :=
  count_step 299000 1000 300000 78 25919 25997 (by omega) (by omega) hc299 cnt298
theorem cnt300 : Nat.count (fun n => trialPrimeB n = true) 301000 = 26082 :=
  count_step 300000 1000 301000 85 25997 26082 (by omega) (by omega) hc300 cnt299
theorem cnt301 : Nat.count (fun n => trialPrimeB n = true) 302000 = 26165 :=
  count_step 301000 1000 302000 83 26082 26165 (by omega) (by omega) hc301 cnt300
theorem cnt302 : Nat.count (fun n => trialPrimeB n = true) 303000 = 26237 :=
  count_step 302000 1000 303000 72 26165 26237 (by omega) (by omega) hc302 cnt301
theorem cnt303 : Nat.count (fun n => trialPrimeB n = true) 304000 = 26321 :=
  count_step 303000 1000 304000 84 26237 26321 (by omega) (by omega) hc303 cnt302
theorem cnt304 : Nat.count (fun n => trialPrimeB n = true) 305000 = 26409 :=
  count_step 304000 1000 305000 88 26321 26409 (by omega) (by omega) hc304 cnt303
theorem cnt305 : Nat.count (fun n => trialPrimeB n = true) 306000 = 26489 :=
  count_step 305000 1000 306000 80 26409 26489 (by omega) (by omega) hc305 cnt304
theorem cnt306 : Nat.count (fun n => trialPrimeB n = true) 307000 = 26571 :=
  count_step 306000 1000 307000 82 26489 26571 (by omega) (by omega) hc306 cnt305
theorem cnt307 : Nat.count (fun n => trialPrimeB n = true) 308000 = 26644 :=
  count_step 307000 1000 308000 73 26571 26644 (by omega) (by omega) hc307 cnt306
theorem cnt308 : Nat.count (fun n => trialPrimeB n = true) 309000 = 26720 :=
  count_step 308000 1000 309000 76 26644 26720 (by omega) (by omega) hc308 cnt307
theorem cnt309 : Nat.count (fun n => trialPrimeB n = true) 310000 = 26800 :=
  count_step 309000 1000 310000 80 26720 26800 (by omega) (by omega) hc309 cnt308
theorem cnt310 : Nat.count (fun n => trialPrimeB n = true) 311000 = 26879 :=
  count_step 310000 1000 311000 79 26800 26879 (by omega) (by omega) hc310 cnt309
theorem cnt311 : Nat.count (fun n => trialPrimeB n = true) 312000 = 26948 :=
  count_step 311000 1000 312000 69 26879 26948 (by omega) (by omega) hc311 cnt310
theorem cnt312 : Nat.count (fun n => trialPrimeB n = true) 313000 = 27034 :=
  count_step 312000 1000 313000 86 26948 27034 (by omega) (by omega) hc312 cnt311
theorem cnt313 : Nat.count (fun n => trialPrimeB n = true) 314000 = 27120 :=
  count_step 313000 1000 314000 86 27034 27120 (by omega) (by omega) hc313 cnt312
theorem cnt314 : Nat.count (fun n => trialPrimeB n = true) 315000 = 27196 :=
  count_step 314000 1000 315000 76 27120 27196 (by omega) (by omega) hc314 cnt313
theorem cnt315 : Nat.count (fun n => trialPrimeB n = true) 316000 = 27273 :=
  count_step 315000 1000 316000 77 27196 27273 (by omega) (by omega) hc315 cnt314
theorem cnt316 : Nat.count (fun n => trialPrimeB n = true) 317000 = 27357 :=
  count_step 316000 1000 317000 84 27273 27357 (by omega) (by omega) hc316 cnt315
theorem cnt317 : Nat.count (fun n => trialPrimeB n = true) 318000 = 27441 :=
  count_step 317000 1000 318000 84 27357 27441 (by omega) (by omega) hc317 cnt316
theorem cnt318 : Nat.count (fun n => trialPrimeB n = true) 319000 = 27522 :=
  count_step 318000 1000 319000 81 27441 27522 (by omega) (by omega) hc318 cnt317
theorem cnt319 : Nat.count (fun n => trialPrimeB n = true) 320000 = 27608 :=
  count_step 319000 1000 320000 86 27522 27608 (by omega) (by omega) hc319 cnt318
theorem cnt320 : Nat.count (fun n => trialPrimeB n = true) 321000 = 27687 :=
  count_step 320000 1000 321000 79 27608 27687 (by omega) (by omega) hc320 cnt319
theorem cnt321 : Nat.count (fun n => trialPrimeB n = true) 322000 = 27767 :=
  count_step 321000 1000 322000 80 27687 27767 (by omega) (by omega) hc321 cnt320
theorem cnt322 : Nat.count (fun n => trialPrimeB n = true) 323000 = 27848 :=
  count_step 322000 1000 323000 81 27767 27848 (by omega) (by omega) hc322 cnt321
theorem cnt323 : Nat.count (fun n => trialPrimeB n = true) 324000 = 27919 :=
  count_step 323000 1000 324000 71 27848 27919 (by omega) (by omega) hc323 cnt322
theorem cnt324 : Nat.count (fun n => trialPrimeB n = true) 325000 = 28006 :=
  count_step 324000 1000 325000 87 27919 28006 (by omega) (by omega) hc324 cnt323
theorem cnt325 : Nat.count (fun n => trialPrimeB n = true) 326000 = 28091 :=
  count_step 325000 1000 326000 85 28006 28091 (by omega) (by omega) hc325 cnt324
theorem cnt326 : Nat.count (fun n => trialPrimeB n = true) 327000 = 28164 :=
  count_step 326000 1000 327000 73 28091 28164 (by omega) (by omega) hc326 cnt325
theorem cnt327 : Nat.count (fun n => trialPrimeB n = true) 328000 = 28250 :=
  count_step 327000 1000 328000 86 28164 28250 (by omega) (by omega) hc327 cnt326
theorem cnt328 : Nat.count (fun n => trialPrimeB n = true) 329000 = 28323 :=
  count_step 328000 1000 329000 73 28250 28323 (by omega) (by omega) hc328 cnt327
theorem cnt329 : Nat.count (fun n => trialPrimeB n = true) 330000 = 28404 :=
  count_step 329000 1000 330000 81 28323 28404 (by omega) (by omega) hc329 cnt328
theorem cnt330 : Nat.count (fun n => trialPrimeB n = true) 331000 = 28484 :=
  count_step 330000 1000 331000 80 28404 28484 (by omega) (by omega) hc330 cnt329
theorem cnt331 : Nat.count (fun n => trialPrimeB n = true) 332000 = 28566 :=
  count_step 331000 1000 332000 82 28484 28566 (by omega) (by omega) hc331 cnt330
theorem cnt332 : Nat.count (fun n => trialPrimeB n = true) 333000 = 28638 :=
  count_step 332000 1000 333000 72 28566 28638 (by omega) (by omega) hc332 cnt331
theorem cnt333 : Nat.count (fun n => trialPrimeB n = true) 334000 = 28719 :=
  count_step 333000 1000 334000 81 28638 28719 (by omega) (by omega) hc333 cnt332
theorem cnt334 : Nat.count (fun n => trialPrimeB n = true) 335000 = 28796 :=
  count_step 334000 1000 335000 77 28719 28796 (by omega) (by omega) hc334 cnt333
theorem cnt335 : Nat.count (fun n => trialPrimeB n = true) 336000 = 28873 :=
  count_step 335000 1000 336000 77 28796 28873 (by omega) (by omega) hc335 cnt334
theorem cnt336 : Nat.count (fun n => trialPrimeB n = true) 337000 = 28957 :=
  count_step 336000 1000 337000 84 28873 28957 (by omega) (by omega) hc336 cnt335
theorem cnt337 : Nat.count (fun n => trialPrimeB n = true) 338000 = 29037 :=
  count_step 337000 1000 338000 80 28957 29037 (by omega) (by omega) hc337 cnt336
theorem cnt338 : Nat.count (fun n => trialPrimeB n = true) 339000 = 29114 :=
  count_step 338000 1000 339000 77 29037 29114 (by omega) (by omega) hc338 cnt337
theorem cnt339 : Nat.count (fun n => trialPrimeB n = true) 340000 = 29182 :=
  count_step 339000 1000 340000 68 29114 29182 (by omega) (by omega) hc339 cnt338
theorem cnt340 : Nat.count (fun n => trialPrimeB n = true) 341000 = 29266 :=
  count_step 340000 1000 341000 84 29182 29266 (by omega) (by omega) hc340 cnt339
theorem cnt341 : Nat.count (fun n => trialPrimeB n = true) 342000 = 29343 :=
  count_step 341000 1000 342000 77 29266 29343 (by omega) (by omega) hc341 cnt340
theorem cnt342 : Nat.count (fun n => trialPrimeB n = true) 343000 = 29420 :=
  count_step 342000 1000 343000 77 29343 29420 (by omega) (by omega) hc342 cnt341
theorem cnt343 : Nat.count (fun n => trialPrimeB n = true) 344000 = 29500 :=
  count_step 343000 1000 344000 80 29420 29500 (by omega) (by omega) hc343 cnt342
theorem cnt344 : Nat.count (fun n => trialPrimeB n = true) 345000 = 29580 :=
  count_step 344000 1000 345000 80 29500 29580 (by omega) (by omega) hc344 cnt343
theorem cnt345 : Nat.count (fun n => trialPrimeB n = true) 346000 = 29656 :=
  count_step 345000 1000 346000 76 29580 29656 (by omega) (by omega) hc345 cnt344
theorem cnt346 : Nat.count (fun n => trialPrimeB n = true) 347000 = 29736 :=
  count_step 346000 1000 347000 80 29656 29736 (by omega) (by omega) hc346 cnt345
theorem cnt347 : Nat.count (fun n => trialPrimeB n = true) 348000 = 29818 :=
  count_step 347000 1000 348000 82 29736 29818 (by omega) (by omega) hc347 cnt346
theorem cnt348 : Nat.count (fun n => trialPrimeB n = true) 349000 = 29895 :=
  count_step 348000 1000 349000 77 29818 29895 (by omega) (by omega) hc348 cnt347
theorem cnt349 : Nat.count (fun n => trialPrimeB n = true) 350000 = 29977 :=
  count_step 349000 1000 350000 82 29895 29977 (by omega) (by omega) hc349 cnt348
theorem cnt350 : Nat.count (fun n => trialPrimeB n = true) 351000 = 30051 :=
  count_step 350000 1000 351000 74 29977 30051 (by omega) (by omega) hc350 cnt349
theorem cnt351 : Nat.count (fun n => trialPrimeB n = true) 352000 = 30132 :=
  count_step 351000 1000 352000 81 30051 30132 (by omega) (by omega) hc351 cnt350
theorem cnt352 : Nat.count (fun n => trialPrimeB n = true) 353000 = 30214 :=
  count_step 352000 1000 353000 82 30132 30214 (by omega) (by omega) hc352 cnt351
theorem cnt353 : Nat.count (fun n => trialPrimeB n = true) 354000 = 30290 :=
  count_step 353000 1000 354000 76 30214 30290 (by omega) (by omega) hc353 cnt352
theorem cnt354 : Nat.count (fun n => trialPrimeB n = true) 355000 = 30377 :=
  count_step 354000 1000 355000 87 30290 30377 (by omega) (by omega) hc354 cnt353
theorem cnt355 : Nat.count (fun n => trialPrimeB n = true) 356000 = 30456 :=
  count_step 355000 1000 356000 79 30377 30456 (by omega) (by omega) hc355 cnt354
theorem cnt356 : Nat.count (fun n => trialPrimeB n = true) 357000 = 30523 :=
  count_step 356000 1000 357000 67 30456 30523 (by omega) (by omega) hc356 cnt355
theorem cnt357 : Nat.count (fun n => trialPrimeB n = true) 358000 = 30603 :=
  count_step 357000 1000 358000 80 30523 30603 (by omega) (by omega) hc357 cnt356
theorem cnt358 : Nat.count (fun n => trialPrimeB n = true) 359000 = 30686 :=
  count_step 358000 1000 359000 83 30603 30686 (by omega) (by omega) hc358 cnt357
theorem cnt359 : Nat.count (fun n => trialPrimeB n = true) 360000 = 30757 :=
  count_step 359000 1000 360000 71 30686 30757 (by omega) (by omega) hc359 cnt358
theorem cnt360 : Nat.count (fun n => trialPrimeB n = true) 361000 = 30825 :=
  count_step 360000 1000 361000 68 30757 30825 (by omega) (by omega) hc360 cnt359
theorem cnt361 : Nat.count (fun n => trialPrimeB n = true) 362000 = 30904 :=
  count_step 361000 1000 362000 79 30825 30904 (by omega) (by omega) hc361 cnt360
theorem cnt362 : Nat.count (fun n => trialPrimeB n = true) 363000 = 30980 :=
  count_step 362000 1000 363000 76 30904 30980 (by omega) (by omega) hc362 cnt361
theorem cnt363 : Nat.count (fun n => trialPrimeB n = true) 364000 = 31064 :=
  count_step 363000 1000 364000 84 30980 31064 (by omega) (by omega) hc363 cnt362
theorem cnt364 : Nat.count (fun n => trialPrimeB n = true) 365000 = 31141 :=
  count_step 364000 1000 365000 77 31064 31141 (by omega) (by omega) hc364 cnt363
theorem cnt365 : Nat.count (fun n => trialPrimeB n = true) 366000 = 31218 :=
  count_step 365000 1000 366000 77 31141 31218 (by omega) (by omega) hc365 cnt364
theorem cnt366 : Nat.count (fun n => trialPrimeB n = true) 367000 = 31303 :=
  count_step 366000 1000 367000 85 31218 31303 (by omega) (by omega) hc366 cnt365
theorem cnt367 : Nat.count (fun n => trialPrimeB n = true) 368000 = 31382 :=
  count_step 367000 1000 368000 79 31303 31382 (by omega) (by omega) hc367 cnt366
theorem cnt368 : Nat.count (fun n => trialPrimeB n = true) 369000 = 31454 :=
  count_step 368000 1000 369000 72 31382 31454 (by omega) (by omega) hc368 cnt367
theorem cnt369 : Nat.count (fun n => trialPrimeB n = true) 370000 = 31522 :=
  count_step 369000 1000 370000 68 31454 31522 (by omega) (by omega) hc369 cnt368
theorem cnt370 : Nat.count (fun n => trialPrimeB n = true) 371000 = 31592 :=
  count_step 370000 1000 371000 70 31522 31592 (by omega) (by omega) hc370 cnt369
theorem cnt371 : Nat.count (fun n => trialPrimeB n = true) 372000 = 31668 :=
  count_step 371000 1000 372000 76 31592 31668 (by omega) (by omega) hc371 cnt370
theorem cnt372 : Nat.count (fun n => trialPrimeB n = true) 373000 = 31749 :=
  count_step 372000 1000 373000 81 31668 31749 (by omega) (by omega) hc372 cnt371
theorem cnt373 : Nat.count (fun n => trialPrimeB n = true) 374000 = 31822 :=
  count_step 373000 1000 374000 73 31749 31822 (by omega) (by omega) hc373 cnt372
theorem cnt374 : Nat.count (fun n => trialPrimeB n = true) 375000 = 31904 :=
  count_step 374000 1000 375000 82 31822 31904 (by omega) (by omega) hc374 cnt373
theorem cnt375 : Nat.count (fun n => trialPrimeB n = true) 376000 = 31989 :=
  count_step 375000 1000 376000 85 31904 31989 (by omega) (by omega) hc375 cnt374
theorem cnt376 : Nat.count (fun n => trialPrimeB n = true) 377000 = 32069 :=
  count_step 376000 1000 377000 80 31989 32069 (by omega) (by omega) hc376 cnt375
theorem cnt377 : Nat.count (fun n => trialPrimeB n = true) 378000 = 32140 :=
  count_step 377000 1000 378000 71 32069 32140 (by omega) (by omega) hc377 cnt376
theorem cnt378 : Nat.count (fun n => trialPrimeB n = true) 379000 = 32217 :=
  count_step 378000 1000 379000 77 32140 32217 (by omega) (by omega) hc378 cnt377
theorem cnt379 : Nat.count (fun n => trialPrimeB n = true) 380000 = 32300 :=
  count_step 379000 1000 380000 83 32217 32300 (by omega) (by omega) hc379 cnt378
theorem cnt380 : Nat.count (fun n => trialPrimeB n = true) 381000 = 32372 :=
  count_step 380000 1000 381000 72 32300 32372 (by omega) (by omega) hc380 cnt379
theorem cnt381 : Nat.count (fun n => trialPrimeB n = true) 382000 = 32448 :=
  count_step 381000 1000 382000 76 32372 32448 (by omega) (by omega) hc381 cnt380
theorem cnt382 : Nat.count (fun n => trialPrimeB n = true) 383000 = 32522 :=
  count_step 382000 1000 383000 74 32448 32522 (by omega) (by omega) hc382 cnt381
theorem cnt383 : Nat.count (fun n => trialPrimeB n = true) 384000 = 32603 :=
  count_step 383000 1000 384000 81 32522 32603 (by omega) (by omega) hc383 cnt382
theorem cnt384 : Nat.count (fun n => trialPrimeB n = true) 385000 = 32681 :=
  count_step 384000 1000 385000 78 32603 32681 (by omega) (by omega) hc384 cnt383
theorem cnt385 : Nat.count (fun n => trialPrimeB n = true) 386000 = 32761 :=
  count_step 385000 1000 386000 80 32681 32761 (by omega) (by omega) hc385 cnt384
theorem cnt386 : Nat.count (fun n => trialPrimeB n = true) 387000 = 32839 :=
  count_step 386000 1000 387000 78 32761 32839 (by omega) (by omega) hc386 cnt385
theorem cnt387 : Nat.count (fun n => trialPrimeB n = true) 388000 = 32908 :=
  count_step 387000 1000 388000 69 32839 32908 (by omega) (by omega) hc387 cnt386
theorem cnt388 : Nat.count (fun n => trialPrimeB n = true) 389000 = 32983 :=
  count_step 388000 1000 389000 75 32908 32983 (by omega) (by omega) hc388 cnt387
theorem cnt389 : Nat.count (fun n => trialPrimeB n = true) 390000 = 33067 :=
  count_step 389000 1000 390000 84 32983 33067 (by omega) (by omega) hc389 cnt388
theorem cnt390 : Nat.count (fun n => trialPrimeB n = true) 391000 = 33148 :=
  count_step 390000 1000 391000 81 33067 33148 (by omega) (by omega) hc390 cnt389
theorem cnt391 : Nat.count (fun n => trialPrimeB n = true) 392000 = 33227 :=
  count_step 391000 1000 392000 79 33148 33227 (by omega) (by omega) hc391 cnt390
theorem cnt392 : Nat.count (fun n => trialPrimeB n = true) 393000 = 33313 :=
  count_step 392000 1000 393000 86 33227 33313 (by omega) (by omega) hc392 cnt391
theorem cnt393 : Nat.count (fun n => trialPrimeB n = true) 394000 = 33400 :=
  count_step 393000 1000 394000 87 33313 33400 (by omega) (by omega) hc393 cnt392
theorem cnt394 : Nat.count (fun n => trialPrimeB n = true) 395000 = 33475 :=
  count_step 394000 1000 395000 75 33400 33475 (by omega) (by omega) hc394 cnt393
theorem cnt395 : Nat.count (fun n => trialPrimeB n = true) 396000 = 33547 :=
  count_step 395000 1000 396000 72 33475 33547 (by omega) (by omega) hc395 cnt394
theorem cnt396 : Nat.count (fun n => trialPrimeB n = true) 397000 = 33622 :=
  count_step 396000 1000 397000 75 33547 33622 (by omega) (by omega) hc396 cnt395
theorem cnt397 : Nat.count (fun n => trialPrimeB n = true) 398000 = 33697 :=
  count_step 397000 1000 398000 75 33622 33697 (by omega) (by omega) hc397 cnt396
theorem cnt398 : Nat.count (fun n => trialPrimeB n = true) 399000 = 33779 :=
  count_step 398000 1000 399000 82 33697 33779 (by omega) (by omega) hc398 cnt397
theorem cnt399 : Nat.count (fun n => trialPrimeB n = true) 400000 = 33860 :=
  count_step 399000 1000 400000 81 33779 33860 (by omega) (by omega) hc399 cnt398
theorem cnt400 : Nat.count (fun n => trialPrimeB n = true) 401000 = 33930 :=
  count_step 400000 1000 401000 70 33860 33930 (by omega) (by omega) hc400 cnt399
theorem cnt401 : Nat.count (fun n => trialPrimeB n = true) 402000 = 34001 :=
  count_step 401000 1000 402000 71 33930 34001 (by omega) (by omega) hc401 cnt400
theorem cnt402 : Nat.count (fun n => trialPrimeB n = true) 403000 = 34077 :=
  count_step 402000 1000 403000 76 34001 34077 (by omega) (by omega) hc402 cnt401
theorem cnt403 : Nat.count (fun n => trialPrimeB n = true) 404000 = 34152 :=
  count_step 403000 1000 404000 75 34077 34152 (by omega) (by omega) hc403 cnt402
theorem cnt404 : Nat.count (fun n => trialPrimeB n = true) 405000 = 34222 :=
  count_step 404000 1000 405000 70 34152 34222 (by omega) (by omega) hc404 cnt403
theorem cnt405 : Nat.count (fun n => trialPrimeB n = true) 406000 = 34305 :=
  count_step 405000 1000 406000 83 34222 34305 (by omega) (by omega) hc405 cnt404
theorem cnt406 : Nat.count (fun n => trialPrimeB n = true) 407000 = 34372 :=
  count_step 406000 1000 407000 67 34305 34372 (by omega) (by omega) hc406 cnt405
theorem cnt407 : Nat.count (fun n => trialPrimeB n = true) 408000 = 34453 :=
  count_step 407000 1000 408000 81 34372 34453 (by omega) (by omega) hc407 cnt406
theorem cnt408 : Nat.count (fun n => trialPrimeB n = true) 409000 = 34532 :=
  count_step 408000 1000 409000 79 34453 34532 (by omega) (by omega) hc408 cnt407
theorem cnt409 : Nat.count (fun n => trialPrimeB n = true) 410000 = 34614 :=
  count_step 409000 1000 410000 82 34532 34614 (by omega) (by omega) hc409 cnt408
theorem cnt410 : Nat.count (fun n => trialPrimeB n = true) 411000 = 34687 :=
  count_step 410000 1000 411000 73 34614 34687 (by omega) (by omega) hc410 cnt409
theorem cnt411 : Nat.count (fun n => trialPrimeB n = true) 412000 = 34768 :=
  count_step 411000 1000 412000 81 34687 34768 (by omega) (by omega) hc411 cnt410
theorem cnt412 : Nat.count (fun n => trialPrimeB n = true) 413000 = 34842 :=
  count_step 412000 1000 413000 74 34768 34842 (by omega) (by omega) hc412 cnt411
theorem cnt413 : Nat.count (fun n => trialPrimeB n = true) 414000 = 34911 :=
  count_step 413000 1000 414000 69 34842 34911 (by omega) (by omega) hc413 cnt412
theorem cnt414 : Nat.count (fun n => trialPrimeB n = true) 415000 = 35001 :=
  count_step 414000 1000 415000 90 34911 35001 (by omega) (by omega) hc414 cnt413
theorem cnt415 : Nat.count (fun n => trialPrimeB n = true) 416000 = 35081 :=
  count_step 415000 1000 416000 80 35001 35081 (by omega) (by omega) hc415 cnt414
theorem cnt416 : Nat.count (fun n => trialPrimeB n = true) 417000 = 35148 :=
  count_step 416000 1000 417000 67 35081 35148 (by omega) (by omega) hc416 cnt415
theorem cnt417 : Nat.count (fun n => trialPrimeB n = true) 418000 = 35230 :=
  count_step 417000 1000 418000 82 35148 35230 (by omega) (by omega) hc417 cnt416
theorem cnt418 : Nat.count (fun n => trialPrimeB n = true) 419000 = 35315 :=
  count_step 418000 1000 419000 85 35230 35315 (by omega) (by omega) hc418 cnt417
theorem cnt419 : Nat.count (fun n => trialPrimeB n = true) 420000 = 35390 :=
  count_step 419000 1000 420000 75 35315 35390 (by omega) (by omega) hc419 cnt418
theorem cnt420 : Nat.count (fun n => trialPrimeB n = true) 421000 = 35465 :=
  count_step 420000 1000 421000 75 35390 35465 (by omega) (by omega) hc420 cnt419
theorem cnt421 : Nat.count (fun n => trialPrimeB n = true) 422000 = 35538 :=
  count_step 421000 1000 422000 73 35465 35538 (by omega) (by omega) hc421 cnt420
theorem cnt422 : Nat.count (fun n => trialPrimeB n = true) 423000 = 35615 :=
  count_step 422000 1000 423000 77 35538 35615 (by omega) (by omega) hc422 cnt421
theorem cnt423 : Nat.count (fun n => trialPrimeB n = true) 424000 = 35698 :=
  count_step 423000 1000 424000 83 35615 35698 (by omega) (by omega) hc423 cnt422
theorem cnt424 : Nat.count (fun n => trialPrimeB n = true) 425000 = 35779 :=
  count_step 424000 1000 425000 81 35698 35779 (by omega) (by omega) hc424 cnt423
theorem cnt425 : Nat.count (fun n => trialPrimeB n = true) 426000 = 35853 :=
  count_step 425000 1000 426000 74 35779 35853 (by omega) (by omega) hc425 cnt424
theorem cnt426 : Nat.count (fun n => trialPrimeB n = true) 427000 = 35924 :=
  count_step 426000 1000 427000 71 35853 35924 (by omega) (by omega) hc426 cnt425
theorem cnt427 : Nat.count (fun n => trialPrimeB n = true) 428000 = 36002 :=
  count_step 427000 1000 428000 78 35924 36002 (by omega) (by omega) hc427 cnt426
theorem cnt428 : Nat.count (fun n => trialPrimeB n = true) 429000 = 36073 :=
  count_step 428000 1000 429000 71 36002 36073 (by omega) (by omega) hc428 cnt427
theorem cnt429 : Nat.count (fun n => trialPrimeB n = true) 430000 = 36162 :=
  count_step 429000 1000 430000 89 36073 36162 (by omega) (by omega) hc429 cnt428
theorem cnt430 : Nat.count (fun n => trialPrimeB n = true) 431000 = 36238 :=
  count_step 430000 1000 431000 76 36162 36238 (by omega) (by omega) hc430 cnt429
theorem cnt431 : Nat.count (fun n => trialPrimeB n = true) 432000 = 36317 :=
  count_step 431000 1000 432000 79 36238 36317 (by omega) (by omega) hc431 cnt430
theorem cnt432 : Nat.count (fun n => trialPrimeB n = true) 433000 = 36401 :=
  count_step 432000 1000 433000 84 36317 36401 (by omega) (by omega) hc432 cnt431
theorem cnt433 : Nat.count (fun n => trialPrimeB n = true) 434000 = 36481 :=
  count_step 433000 1000 434000 80 36401 36481 (by omega) (by omega) hc433 cnt432
theorem cnt434 : Nat.count (fun n => trialPrimeB n = true) 435000 = 36566 :=
  count_step 434000 1000 435000 85 36481 36566 (by omega) (by omega) hc434 cnt433
theorem cnt435 : Nat.count (fun n => trialPrimeB n = true) 436000 = 36648 :=
  count_step 435000 1000 436000 82 36566 36648 (by omega) (by omega) hc435 cnt434
theorem cnt436 : Nat.count (fun n => trialPrimeB n = true) 437000 = 36721 :=
  count_step 436000 1000 437000 73 36648 36721 (by omega) (by omega) hc436 cnt435
theorem cnt437 : Nat.count (fun n => trialPrimeB n = true) 438000 = 36791 :=
  count_step 437000 1000 438000 70 36721 36791 (by omega) (by omega) hc437 cnt436
theorem cnt438 : Nat.count (fun n => trialPrimeB n = true) 439000 = 36866 :=
  count_step 438000 1000 439000 75 36791 36866 (by omega) (by omega) hc438 cnt437
theorem cnt439 : Nat.count (fun n => trialPrimeB n = true) 440000 = 36941 :=
  count_step 439000 1000 440000 75 36866 36941 (by omega) (by omega) hc439 cnt438
theorem cnt440 : Nat.count (fun n => trialPrimeB n = true) 441000 = 37020 :=
  count_step 440000 1000 441000 79 36941 37020 (by omega) (by omega) hc440 cnt439
theorem cnt441 : Nat.count (fun n => trialPrimeB n = true) 442000 = 37092 :=
  count_step 441000 1000 442000 72 37020 37092 (by omega) (by omega) hc441 cnt440
theorem cnt442 : Nat.count (fun n => trialPrimeB n = true) 443000 = 37177 :=
  count_step 442000 1000 443000 85 37092 37177 (by omega) (by omega) hc442 cnt441
theorem cnt443 : Nat.count (fun n => trialPrimeB n = true) 444000 = 37265 :=
  count_step 443000 1000 444000 88 37177 37265 (by omega) (by omega) hc443 cnt442
theorem cnt444 : Nat.count (fun n => trialPrimeB n = true) 445000 = 37347 :=
  count_step 444000 1000 445000 82 37265 37347 (by omega) (by omega) hc444 cnt443
theorem cnt445 : Nat.count (fun n => trialPrimeB n = true) 446000 = 37415 :=
  count_step 445000 1000 446000 68 37347 37415 (by omega) (by omega) hc445 cnt444
theorem cnt446 : Nat.count (fun n => trialPrimeB n = true) 447000 = 37483 :=
  count_step 446000 1000 447000 68 37415 37483 (by omega) (by omega) hc446 cnt445
theorem cnt447 : Nat.count (fun n => trialPrimeB n = true) 448000 = 37556 :=
  count_step 447000 1000 448000 73 37483 37556 (by omega) (by omega) hc447 cnt446
theorem cnt448 : Nat.count (fun n => trialPrimeB n = true) 449000 = 37626 :=
  count_step 448000 1000 449000 70 37556 37626 (by omega) (by omega) hc448 cnt447
theorem cnt449 : Nat.count (fun n => trialPrimeB n = true) 450000 = 37706 :=
  count_step 449000 1000 450000 80 37626 37706 (by omega) (by omega) hc449 cnt448
theorem cnt450 : Nat.count (fun n => trialPrimeB n = true) 451000 = 37798 :=
  count_step 450000 1000 451000 92 37706 37798 (by omega) (by omega) hc450 cnt449
theorem cnt451 : Nat.count (fun n => trialPrimeB n = true) 452000 = 37874 :=
  count_step 451000 1000 452000 76 37798 37874 (by omega) (by omega) hc451 cnt450
theorem cnt452 : Nat.count (fun n => trialPrimeB n = true) 453000 = 37937 :=
  count_step 452000 1000 453000 63 37874 37937 (by omega) (by omega) hc452 cnt451
theorem cnt453 : Nat.count (fun n => trialPrimeB n = true) 454000 = 38009 :=
  count_step 453000 1000 454000 72 37937 38009 (by omega) (by omega) hc453 cnt452
theorem cnt454 : Nat.count (fun n => trialPrimeB n = true) 455000 = 38083 :=
  count_step 454000 1000 455000 74 38009 38083 (by omega) (by omega) hc454 cnt453
theorem cnt455 : Nat.count (fun n => trialPrimeB n = true) 456000 = 38165 :=
  count_step 455000 1000 456000 82 38083 38165 (by omega) (by omega) hc455 cnt454
theorem cnt456 : Nat.count (fun n => trialPrimeB n = true) 457000 = 38238 :=
  count_step 456000 1000 457000 73 38165 38238 (by omega) (by omega) hc456 cnt455
theorem cnt457 : Nat.count (fun n => trialPrimeB n = true) 458000 = 38315 :=
  count_step 457000 1000 458000 77 38238 38315 (by omega) (by omega) hc457 cnt456
theorem cnt458 : Nat.count (fun n => trialPrimeB n = true) 459000 = 38390 :=
  count_step 458000 1000 459000 75 38315 38390 (by omega) (by omega) hc458 cnt457
theorem cnt459 : Nat.count (fun n => trialPrimeB n = true) 460000 = 38458 :=
  count_step 459000 1000 460000 68 38390 38458 (by omega) (by omega) hc459 cnt458
theorem cnt460 : Nat.count (fun n => trialPrimeB n = true) 461000 = 38535 :=
  count_step 460000 1000 461000 77 38458 38535 (by omega) (by omega) hc460 cnt459
theorem cnt461 : Nat.count (fun n => trialPrimeB n = true) 462000 = 38604 :=
  count_step 461000 1000 462000 69 38535 38604 (by omega) (by omega) hc461 cnt460
theorem cnt462 : Nat.count (fun n => trialPrimeB n = true) 463000 = 38678 :=
  count_step 462000 1000 463000 74 38604 38678 (by omega) (by omega) hc462 cnt461
theorem cnt463 : Nat.count (fun n => trialPrimeB n = true) 464000 = 38755 :=
  count_step 463000 1000 464000 77 38678 38755 (by omega) (by omega) hc463 cnt462
theorem cnt464 : Nat.count (fun n => trialPrimeB n = true) 465000 = 38840 :=
  count_step 464000 1000 465000 85 38755 38840 (by omega) (by omega) hc464 cnt463
theorem cnt465 : Nat.count (fun n => trialPrimeB n = true) 466000 = 38914 :=
  count_step 465000 1000 466000 74 38840 38914 (by omega) (by omega) hc465 cnt464
theorem cnt466 : Nat.count (fun n => trialPrimeB n = true) 467000 = 38983 :=
  count_step 466000 1000 467000 69 38914 38983 (by omega) (by omega) hc466 cnt465
theorem cnt467 : Nat.count (fun n => trialPrimeB n = true) 468000 = 39066 :=
  count_step 467000 1000 468000 83 38983 39066 (by omega) (by omega) hc467 cnt466
theorem cnt468 : Nat.count (fun n => trialPrimeB n = true) 469000 = 39151 :=
  count_step 468000 1000 469000 85 39066 39151 (by omega) (by omega) hc468 cnt467
theorem cnt469 : Nat.count (fun n => trialPrimeB n = true) 470000 = 39223 :=
  count_step 469000 1000 470000 72 39151 39223 (by omega) (by omega) hc469 cnt468
theorem cnt470 : Nat.count (fun n => trialPrimeB n = true) 471000 = 39310 :=
  count_step 470000 1000 471000 87 39223 39310 (by omega) (by omega) hc470 cnt469
theorem cnt471 : Nat.count (fun n => trialPrimeB n = true) 472000 = 39388 :=
  count_step 471000 1000 472000 78 39310 39388 (by omega) (by omega) hc471 cnt470
theorem cnt472 : Nat.count (fun n => trialPrimeB n = true) 473000 = 39461 :=
  count_step 472000 1000 473000 73 39388 39461 (by omega) (by omega) hc472 cnt471
theorem cnt473 : Nat.count (fun n => trialPrimeB n = true) 474000 = 39539 :=
  count_step 473000 1000 474000 78 39461 39539 (by omega) (by omega) hc473 cnt472
theorem cnt474 : Nat.count (fun n => trialPrimeB n = true) 475000 = 39619 :=
  count_step 474000 1000 475000 80 39539 39619 (by omega) (by omega) hc474 cnt473
theorem cnt475 : Nat.count (fun n => trialPrimeB n = true) 476000 = 39705 :=
  count_step 475000 1000 476000 86 39619 39705 (by omega) (by omega) hc475 cnt474
theorem cnt476 : Nat.count (fun n => trialPrimeB n = true) 477000 = 39780 :=
  count_step 476000 1000 477000 75 39705 39780 (by omega) (by omega) hc476 cnt475
theorem cnt477 : Nat.count (fun n => trialPrimeB n = true) 478000 = 39849 :=
  count_step 477000 1000 478000 69 39780 39849 (by omega) (by omega) hc477 cnt476
theorem cnt478 : Nat.count (fun n => trialPrimeB n = true) 479000 = 39934 :=
  count_step 478000 1000 479000 85 39849 39934 (by omega) (by omega) hc478 cnt477
theorem cnt479 : Nat.count (fun n => trialPrimeB n = true) 480000 = 40005 :=
  count_step 479000 1000 480000 71 39934 40005 (by omega) (by omega) hc479 cnt478
theorem cnt480 : Nat.count (fun n => trialPrimeB n = true) 481000 = 40082 :=
  count_step 480000 1000 481000 77 40005 40082 (by omega) (by omega) hc480 cnt479
theorem cnt481 : Nat.count (fun n => trialPrimeB n = true) 482000 = 40160 :=
  count_step 481000 1000 482000 78 40082 40160 (by omega) (by omega) hc481 cnt480
theorem cnt482 : Nat.count (fun n => trialPrimeB n = true) 483000 = 40242 :=
  count_step 482000 1000 483000 82 40160 40242 (by omega) (by omega) hc482 cnt481
theorem cnt483 : Nat.count (fun n => trialPrimeB n = true) 484000 = 40317 :=
  count_step 483000 1000 484000 75 40242 40317 (by omega) (by omega) hc483 cnt482
theorem cnt484 : Nat.count (fun n => trialPrimeB n = true) 485000 = 40382 :=
  count_step 484000 1000 485000 65 40317 40382 (by omega) (by omega) hc484 cnt483
theorem cnt485 : Nat.count (fun n => trialPrimeB n = true) 486000 = 40445 :=
  count_step 485000 1000 486000 63 40382 40445 (by omega) (by omega) hc485 cnt484
theorem cnt486 : Nat.count (fun n => trialPrimeB n = true) 487000 = 40527 :=
  count_step 486000 1000 487000 82 40445 40527 (by omega) (by omega) hc486 cnt485
theorem cnt487 : Nat.count (fun n => trialPrimeB n = true) 488000 = 40605 :=
  count_step 487000 1000 488000 78 40527 40605 (by omega) (by omega) hc487 cnt486
theorem cnt488 : Nat.count (fun n => trialPrimeB n = true) 489000 = 40688 :=
  count_step 488000 1000 489000 83 40605 40688 (by omega) (by omega) hc488 cnt487
theorem cnt489 : Nat.count (fun n => trialPrimeB n = true) 490000 = 40766 :=
  count_step 489000 1000 490000 78 40688 40766 (by omega) (by omega) hc489 cnt488
theorem cnt490 : Nat.count (fun n => trialPrimeB n = true) 491000 = 40844 :=
  count_step 490000 1000 491000 78 40766 40844 (by omega) (by omega) hc490 cnt489
theorem cnt491 : Nat.count (fun n => trialPrimeB n = true) 492000 = 40920 :=
  count_step 491000 1000 492000 76 40844 40920 (by omega) (by omega) hc491 cnt490
theorem cnt492 : Nat.count (fun n => trialPrimeB n = true) 493000 = 40987 :=
  count_step 492000 1000 493000 67 40920 40987 (by omega) (by omega) hc492 cnt491
theorem cnt493 : Nat.count (fun n => trialPrimeB n = true) 494000 = 41069 :=
  count_step 493000 1000 494000 82 40987 41069 (by omega) (by omega) hc493 cnt492
theorem cnt494 : Nat.count (fun n => trialPrimeB n = true) 495000 = 41149 :=
  count_step 494000 1000 495000 80 41069 41149 (by omega) (by omega) hc494 cnt493
theorem cnt495 : Nat.count (fun n => trialPrimeB n = true) 496000 = 41236 :=
  count_step 495000 1000 496000 87 41149 41236 (by omega) (by omega) hc495 cnt494
theorem cnt496 : Nat.count (fun n => trialPrimeB n = true) 497000 = 41304 :=
  count_step 496000 1000 497000 68 41236 41304 (by omega) (by omega) hc496 cnt495
theorem cnt497 : Nat.count (fun n => trialPrimeB n = true) 498000 = 41385 :=
  count_step 497000 1000 498000 81 41304 41385 (by omega) (by omega) hc497 cnt496
theorem cnt498 : Nat.count (fun n => trialPrimeB n = true) 499000 = 41457 :=
  count_step 498000 1000 499000 72 41385 41457 (by omega) (by omega) hc498 cnt497
theorem cnt499 : Nat.count (fun n => trialPrimeB n = true) 500000 = 41538 :=
  count_step 499000 1000 500000 81 41457 41538 (by omega) (by omega) hc499 cnt498
theorem cnt500 : Nat.count (fun n => trialPrimeB n = true) 501000 = 41617 :=
  count_step 500000 1000 501000 79 41538 41617 (by omega) (by omega) hc500 cnt499
theorem cnt501 : Nat.count (fun n => trialPrimeB n = true) 502000 = 41691 :=
  count_step 501000 1000 502000 74 41617 41691 (by omega) (by omega) hc501 cnt500
theorem cnt502 : Nat.count (fun n => trialPrimeB n = true) 503000 = 41758 :=
  count_step 502000 1000 503000 67 41691 41758 (by omega) (by omega) hc502 cnt501
theorem cnt503 : Nat.count (fun n => trialPrimeB n = true) 504000 = 41834 :=
  count_step 503000 1000 504000 76 41758 41834 (by omega) (by omega) hc503 cnt502
theorem cnt504 : Nat.count (fun n => trialPrimeB n = true) 505000 = 41910 :=
  count_step 504000 1000 505000 76 41834 41910 (by omega) (by omega) hc504 cnt503
theorem cnt505 : Nat.count (fun n => trialPrimeB n = true) 506000 = 41993 :=
  count_step 505000 1000 506000 83 41910 41993 (by omega) (by omega) hc505 cnt504
theorem cnt506 : Nat.count (fun n => trialPrimeB n = true) 507000 = 42069 :=
  count_step 506000 1000 507000 76 41993 42069 (by omega) (by omega) hc506 cnt505
theorem cnt507 : Nat.count (fun n => trialPrimeB n = true) 508000 = 42140 :=
  count_step 507000 1000 508000 71 42069 42140 (by omega) (by omega) hc507 cnt506
theorem cnt508 : Nat.count (fun n => trialPrimeB n = true) 509000 = 42216 :=
  count_step 508000 1000 509000 76 42140 42216 (by omega) (by omega) hc508 cnt507
theorem cnt509 : Nat.count (fun n => trialPrimeB n = true) 510000 = 42291 :=
  count_step 509000 1000 510000 75 42216 42291 (by omega) (by omega) hc509 cnt508
theorem cnt510 : Nat.count (fun n => trialPrimeB n = true) 511000 = 42363 :=
  count_step 510000 1000 511000 72 42291 42363 (by omega) (by omega) hc510 cnt509
theorem cnt511 : Nat.count (fun n => trialPrimeB n = true) 512000 = 42445 :=
  count_step 511000 1000 512000 82 42363 42445 (by omega) (by omega) hc511 cnt510
theorem cnt512 : Nat.count (fun n => trialPrimeB n = true) 512721 = 42493 :=
  count_step 512000 721 512721 48 42445 42493 (by omega) (by omega) hc512 cnt511

theorem primeCounting_512720 : Nat.primeCounting 512720 = 42493 := by
  rw [primeCounting_eq_count]
  exact cnt512
