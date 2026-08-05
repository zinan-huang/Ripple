/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBLateConcrete
import Mathlib.Tactic.IntervalCases

/-!
# Single-B high-cap bridge

This file installs the SPEC P high-cap bridge in the Lean-facing live-gap
form.  The public checkpoints are late co-cap checkpoints, from `5n/8` down to
`n/4`; the direction odds are derived from the physical live gap available
outside `SingleBandFrozen`.
-/

namespace Tri

open scoped ENNReal

/-! ## Finite table -/

def singleHighCapBridgeLength : Nat := 12

def singleHighCapPMDen : Nat := 10000

def singleHighCapCeilPM (pm n : Nat) : Nat :=
  (pm * n + (singleHighCapPMDen - 1)) / singleHighCapPMDen

def singleHighCapFloorPM (pm n : Nat) : Nat :=
  pm * n / singleHighCapPMDen

def singleHighCapCoCap (n : Nat) : Nat -> Nat
  | 0 => singleLateEntryCoCap n
  | 1 => 19 * n / 32
  | 2 => 18 * n / 32
  | 3 => 17 * n / 32
  | 4 => 16 * n / 32
  | 5 => 15 * n / 32
  | 6 => 14 * n / 32
  | 7 => 13 * n / 32
  | 8 => 12 * n / 32
  | 9 => 11 * n / 32
  | 10 => 10 * n / 32
  | 11 => 9 * n / 32
  | _ => n / 4

def singleHighCapDPM : Nat -> Nat
  | 0 => 141
  | 1 => 144
  | 2 => 145
  | 3 => 144
  | 4 => 141
  | 5 => 137
  | 6 => 131
  | 7 => 124
  | 8 => 115
  | 9 => 106
  | 10 => 95
  | 11 => 82
  | _ => 82

def singleHighCapBwPM : Nat -> Nat
  | 0 => 11
  | 1 => 12
  | 2 => 13
  | 3 => 14
  | 4 => 15
  | 5 => 15
  | 6 => 16
  | 7 => 15
  | 8 => 15
  | 9 => 14
  | 10 => 13
  | 11 => 11
  | _ => 11

def singleHighCapSretPM : Nat -> Nat
  | 0 => 1693
  | 1 => 1653
  | 2 => 1598
  | 3 => 1534
  | 4 => 1457
  | 5 => 1376
  | 6 => 1285
  | 7 => 1190
  | 8 => 1092
  | 9 => 987
  | 10 => 874
  | 11 => 758
  | _ => 758

def singleHighCapMPM : Nat -> Nat
  | 0 => 1373
  | 1 => 1268
  | 2 => 1172
  | 3 => 1086
  | 4 => 1006
  | 5 => 933
  | 6 => 865
  | 7 => 801
  | 8 => 741
  | 9 => 685
  | 10 => 631
  | 11 => 581
  | _ => 581

def singleHighCapCoFloorPM : Nat -> Nat
  | 0 => 677
  | 1 => 646
  | 2 => 611
  | 3 => 574
  | 4 => 537
  | 5 => 497
  | 6 => 458
  | 7 => 416
  | 8 => 373
  | 9 => 331
  | 10 => 290
  | 11 => 248
  | _ => 248

def singleHighCapMhiPM : Nat -> Nat
  | 0 => 6393
  | 1 => 5751
  | 2 => 5165
  | 3 => 4635
  | 4 => 4144
  | 5 => 3702
  | 6 => 3291
  | 7 => 2917
  | 8 => 2575
  | 9 => 2254
  | 10 => 1951
  | 11 => 1670
  | _ => 1670

def singleHighCapTPM : Nat -> Nat
  | 0 => 583932
  | 1 => 517589
  | 2 => 464051
  | 3 => 420997
  | 4 => 384139
  | 5 => 355055
  | 6 => 330075
  | 7 => 310372
  | 8 => 295964
  | 9 => 283756
  | 10 => 273470
  | 11 => 268145
  | _ => 268145

def singleHighCapP (n i : Nat) : Nat := singleHighCapCoCap n i

def singleHighCapQ (n i : Nat) : Nat := singleHighCapCoCap n (i + 1)

def singleHighCapLentry (n i : Nat) : Nat := 2 * n - singleHighCapP n i

def singleHighCapLexit (n i : Nat) : Nat := 2 * n - singleHighCapQ n i

def singleHighCapBw (n i : Nat) : Nat :=
  singleHighCapCeilPM (singleHighCapBwPM i) n

def singleHighCapD (n i : Nat) : Nat :=
  singleHighCapCeilPM (singleHighCapDPM i) n

def singleHighCapSret (n i : Nat) : Nat :=
  singleHighCapFloorPM (singleHighCapSretPM i) n

def singleHighCapM (n i : Nat) : Nat :=
  singleHighCapFloorPM (singleHighCapMPM i) n

def singleHighCapCoFloor (n i : Nat) : Nat :=
  singleHighCapFloorPM (singleHighCapCoFloorPM i) n

def singleHighCapMhi (n i : Nat) : Nat :=
  singleHighCapFloorPM (singleHighCapMhiPM i) n

def singleHighCapHorizon (n i : Nat) : Nat :=
  singleHighCapCeilPM (singleHighCapTPM i) n

def singleHighCapAlo (n i : Nat) : Nat :=
  singleHighCapLentry n i - singleHighCapBw n i

def singleHighCapLiveGap (n i : Nat) : Nat :=
  singleHighCapAlo n i + 1 - n - singleHighCapD n i

def singleHighCapH (n i : Nat) : Nat :=
  singleHighCapP n i + 2 * singleHighCapMhi n i +
    singleHighCapD n i + 1

def singleHighCapK (n i : Nat) : Nat :=
  singleHighCapH n i + singleHighCapM n i

def singleHighCapHi (n i : Nat) : Nat :=
  singleHighCapLexit n i + singleHighCapSret n i + singleHighCapD n i

/-! ## Direction and return constants -/

noncomputable def singleHighCapDirW : ENNReal :=
  ENNReal.ofReal ((19 : Real) / 20)

noncomputable def singleHighCapDirV : ENNReal :=
  ENNReal.ofReal ((20 : Real) / 19)

def singleHighCapDirP (n i : Nat) : Nat :=
  n - singleHighCapLiveGap n i

def singleHighCapDirQ (n i : Nat) : Nat :=
  n + singleHighCapLiveGap n i

noncomputable def singleHighCapDirU (n i : Nat) : ENNReal :=
  (singleHighCapDirP n i : ENNReal) / (singleHighCapDirQ n i : ENNReal)

noncomputable def singleHighCapDirEta (n i : Nat) : ENNReal :=
  singleHighCapDirW * (singleHighCapDirU n i + 1) /
    (singleHighCapDirU n i + singleHighCapDirW ^ 2)

noncomputable def singleHighCapRetEps (n i : Nat) : ENNReal :=
  ENNReal.ofReal ((1 : Real) / 1000)

theorem singleHighCapRetEps_le_one {n i : Nat} :
    singleHighCapRetEps n i <= 1 := by
  unfold singleHighCapRetEps
  rw [show (1 : ENNReal) = ENNReal.ofReal (1 : Real) by
    exact ENNReal.ofReal_one.symm]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-! ## Live-gap direction guard -/

theorem singleHighCap_direction_guard_arith
    (n d x y b : Nat)
    (hinv : x + y + b = n)
    (hgap : y + d <= x)
    (hdle : d <= n) :
    (n + d) * y <= (n - d) * x := by
  have hmain : ((n : Real) + d) * y <= ((n : Real) - d) * x := by
    have h2 : (2 : Real) * y + d <= n := by
      have hinvR : (x : Real) + y + b = n := by exact_mod_cast hinv
      have hgapR : (y : Real) + d <= x := by exact_mod_cast hgap
      nlinarith
    have hgapR : (y : Real) + d <= x := by exact_mod_cast hgap
    have hdleR : (d : Real) <= n := by exact_mod_cast hdle
    nlinarith [mul_nonneg (by positivity : (0 : Real) <= d)
      (by nlinarith : (0 : Real) <= (n : Real) - d)]
  exact_mod_cast hmain

theorem singleHighCap_hlive_ratio {n aLoΛ hiΛ D H d : Nat}
    (hgap : n + D + d <= aLoΛ + 1)
    (hdle : d <= n) :
    forall q : SingleLedger n, ¬ SingleBandFrozen n aLoΛ hiΛ D H q ->
      exists a : Nat, q.CorrectedLevel (a + 1) ∧
        (n + d) * q.cfg.1.y <= (n - d) * q.cfg.1.x := by
  intro q hB
  have hnotLow : ¬ (q.cfg.1.doubleLevel + q.cy <= aLoΛ + q.cx) :=
    fun h => hB (Or.inl h)
  obtain ⟨a, ha⟩ :
      exists a, q.cfg.1.doubleLevel + q.cy = (a + 1) + q.cx :=
    ⟨q.cfg.1.doubleLevel + q.cy - q.cx - 1, by omega⟩
  have hgapPhys : q.cfg.1.y + d <= q.cfg.1.x :=
    singleB_live_gap q hB hgap
  exact ⟨a, ha,
    singleHighCap_direction_guard_arith n d q.cfg.1.x q.cfg.1.y
      q.cfg.1.b q.cfg.2 hgapPhys hdle⟩

theorem singleHighCapDirU_le_w
    {n i : Nat} (hn : 0 < n)
    (hdle : singleHighCapLiveGap n i <= n)
    (hlarge : n <= 39 * singleHighCapLiveGap n i) :
    singleHighCapDirU n i <= singleHighCapDirW := by
  unfold singleHighCapDirU singleHighCapDirW singleHighCapDirP
    singleHighCapDirQ
  have hleftT :
      ((n - singleHighCapLiveGap n i : Nat) : ENNReal) /
          ((n + singleHighCapLiveGap n i : Nat) : ENNReal) ≠ ⊤ := by
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega)
  have hrightT :
      ENNReal.ofReal ((19 : Real) / 20) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  apply (ENNReal.toReal_le_toReal hleftT hrightT).mp
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
  rw [Nat.cast_sub hdle, Nat.cast_add]
  have hden : (0 : Real) < (n : Real) + singleHighCapLiveGap n i := by
    positivity
  rw [div_le_iff₀ hden]
  have hlargeR : (n : Real) <= 39 * (singleHighCapLiveGap n i : Real) := by
    exact_mod_cast hlarge
  norm_num
  nlinarith

theorem singleHighCapDir_params
    {n i : Nat} (hn : 0 < n)
    (hdlt : singleHighCapLiveGap n i < n)
    (hlarge : n <= 39 * singleHighCapLiveGap n i) :
    singleHighCapDirEta n i *
        (singleHighCapDirU n i + singleHighCapDirW ^ 2)
      = singleHighCapDirW * (singleHighCapDirU n i + 1) ∧
    singleHighCapDirW <= singleHighCapDirEta n i ∧
    1 <= singleHighCapDirEta n i ∧
    singleHighCapDirEta n i ≠ ⊤ ∧
    singleHighCapDirW <= 1 ∧
    singleHighCapDirW ≠ 0 ∧
    singleHighCapDirW ≠ ⊤ ∧
    singleHighCapDirW * singleHighCapDirV = 1 := by
  let u := singleHighCapDirU n i
  have hdle : singleHighCapLiveGap n i <= n := le_of_lt hdlt
  have huT : u ≠ ⊤ := by
    dsimp only [u, singleHighCapDirU, singleHighCapDirP, singleHighCapDirQ]
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega)
  have hu0 : u ≠ 0 := by
    dsimp only [u, singleHighCapDirU, singleHighCapDirP, singleHighCapDirQ]
    exact ENNReal.div_ne_zero.mpr
      ⟨(by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega),
      ENNReal.natCast_ne_top _⟩
  have hw1 : singleHighCapDirW <= 1 := by
    unfold singleHighCapDirW
    rw [show (1 : ENNReal) = ENNReal.ofReal (1 : Real) by
      exact ENNReal.ofReal_one.symm]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hwt : singleHighCapDirW ≠ ⊤ := by
    unfold singleHighCapDirW
    exact ENNReal.ofReal_ne_top
  have hw0 : singleHighCapDirW ≠ 0 := by
    unfold singleHighCapDirW
    simp [ENNReal.ofReal_eq_zero]
  have huw : u <= singleHighCapDirW :=
    singleHighCapDirU_le_w hn hdle hlarge
  have hden0 : u + singleHighCapDirW ^ 2 ≠ 0 := by
    intro h
    rw [add_eq_zero] at h
    exact hu0 h.1
  have hdent : u + singleHighCapDirW ^ 2 ≠ ⊤ := by
    dsimp only [u] at huT
    finiteness
  have hrel :
      singleHighCapDirEta n i *
          (singleHighCapDirU n i + singleHighCapDirW ^ 2)
        = singleHighCapDirW * (singleHighCapDirU n i + 1) := by
    unfold singleHighCapDirEta
    dsimp only [u] at hden0 hdent
    exact ENNReal.div_mul_cancel hden0 hdent
  have hwη : singleHighCapDirW <= singleHighCapDirEta n i := by
    unfold singleHighCapDirEta
    dsimp only [u] at hden0 hdent
    rw [ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdent)]
    have hw2 : singleHighCapDirW ^ 2 <= 1 := by
      calc singleHighCapDirW ^ 2 = singleHighCapDirW * singleHighCapDirW :=
          sq singleHighCapDirW
        _ <= 1 * 1 := mul_le_mul' hw1 hw1
        _ = 1 := one_mul 1
    gcongr
  have hη1 : 1 <= singleHighCapDirEta n i := by
    unfold singleHighCapDirEta
    dsimp only [u] at huT hu0 huw
    exact dir_eta_ge_one huT hu0 hw1 huw
  have hηt : singleHighCapDirEta n i ≠ ⊤ := by
    unfold singleHighCapDirEta
    dsimp only [u] at hden0
    exact ENNReal.div_ne_top (by finiteness) hden0
  have hwv : singleHighCapDirW * singleHighCapDirV = 1 := by
    unfold singleHighCapDirW singleHighCapDirV
    rw [← ENNReal.ofReal_mul
      (by norm_num : (0 : Real) <= (19 : Real) / 20)]
    norm_num
  exact ⟨hrel, hwη, hη1, hηt, hw1, hw0, hwt, hwv⟩

/-! ## Row arithmetic -/

theorem singleHighCap_entry {n i : Nat} (hi : i < singleHighCapBridgeLength) :
    singleHighCapLentry n i + singleHighCapP n i = 2 * n := by
  have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
  interval_cases i <;>
    simp [singleHighCapBridgeLength, singleHighCapLentry, singleHighCapP,
      singleHighCapCoCap, singleLateEntryCoCap] <;> omega

theorem singleHighCap_exit {n i : Nat} (hi : i < singleHighCapBridgeLength) :
    singleHighCapLexit n i + singleHighCapQ n i = 2 * n := by
  have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
  interval_cases i <;>
    simp [singleHighCapBridgeLength, singleHighCapLexit, singleHighCapQ,
      singleHighCapCoCap] <;> omega

theorem singleHighCap_aLo_bw {n i : Nat}
    (hnLarge : 65536 <= n) (hi : i < singleHighCapBridgeLength) :
    singleHighCapAlo n i + singleHighCapBw n i =
      singleHighCapLentry n i := by
  have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
  interval_cases i <;>
    simp [singleHighCapBridgeLength, singleHighCapAlo, singleHighCapBw,
      singleHighCapLentry, singleHighCapP, singleHighCapCoCap,
      singleLateEntryCoCap, singleHighCapCeilPM, singleHighCapBwPM,
      singleHighCapPMDen] <;> omega

theorem singleHighCap_hgap {n i : Nat}
    (hnLarge : 65536 <= n) (hi : i < singleHighCapBridgeLength) :
    n + singleHighCapD n i + singleHighCapLiveGap n i =
      singleHighCapAlo n i + 1 := by
  have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
  interval_cases i <;>
    simp [singleHighCapBridgeLength, singleHighCapLiveGap, singleHighCapAlo,
      singleHighCapBw, singleHighCapD, singleHighCapLentry,
      singleHighCapP, singleHighCapCoCap, singleLateEntryCoCap,
      singleHighCapCeilPM, singleHighCapBwPM, singleHighCapDPM,
      singleHighCapPMDen] <;> omega

theorem singleHighCap_vac {n i : Nat}
    (hnLarge : 65536 <= n) (hi : i < singleHighCapBridgeLength) :
    singleHighCapAlo n i + singleHighCapD n i <=
      singleHighCapLexit n i := by
  have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
  interval_cases i <;>
    simp [singleHighCapBridgeLength, singleHighCapAlo, singleHighCapBw,
      singleHighCapD, singleHighCapLentry, singleHighCapLexit,
      singleHighCapP, singleHighCapQ, singleHighCapCoCap,
      singleLateEntryCoCap, singleHighCapCeilPM, singleHighCapBwPM,
      singleHighCapDPM, singleHighCapPMDen] <;> omega

theorem singleHighCap_Ln {n i : Nat}
    (hnLarge : 65536 <= n) (hi : i < singleHighCapBridgeLength) :
    n + 1 <= singleHighCapLexit n i := by
  have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
  interval_cases i <;>
    simp [singleHighCapBridgeLength, singleHighCapLexit,
      singleHighCapQ, singleHighCapCoCap] <;> omega

theorem singleHighCap_slack {n i : Nat}
    (hi : i < singleHighCapBridgeLength) :
    singleHighCapLexit n i + singleHighCapSret n i +
        singleHighCapD n i <= singleHighCapHi n i := by
  simp [singleHighCapHi]

theorem singleHighCap_targetHi {n i : Nat}
    (hnLarge : 65536 <= n) (hi : i < singleHighCapBridgeLength) :
    singleHighCapLexit n i + singleHighCapD n i + 1 <=
      singleHighCapHi n i := by
  have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
  interval_cases i <;>
    simp [singleHighCapBridgeLength, singleHighCapHi, singleHighCapSret,
      singleHighCapFloorPM, singleHighCapSretPM, singleHighCapPMDen] <;>
    omega

theorem singleHighCap_coClock {n i : Nat}
    (hnLarge : 65536 <= n) (hi : i < singleHighCapBridgeLength) :
    singleHighCapHi n i + 2 * singleHighCapM n i +
        2 * singleHighCapCoFloor n i <= 2 * n + 1 := by
  have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
  interval_cases i <;>
    simp [singleHighCapBridgeLength, singleHighCapHi, singleHighCapLexit,
      singleHighCapQ, singleHighCapCoCap, singleHighCapSret,
      singleHighCapD, singleHighCapM, singleHighCapCoFloor,
      singleHighCapCeilPM, singleHighCapFloorPM, singleHighCapSretPM,
      singleHighCapDPM, singleHighCapMPM, singleHighCapCoFloorPM,
      singleHighCapPMDen] <;> omega

theorem singleHighCap_prodRoom {n i : Nat}
    (hnLarge : 65536 <= n) (hi : i < singleHighCapBridgeLength) :
    singleHighCapLiveGap n i + 2 * singleHighCapCoFloor n i <= n := by
  have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
  interval_cases i <;>
    simp [singleHighCapBridgeLength, singleHighCapLiveGap,
      singleHighCapAlo, singleHighCapBw, singleHighCapD,
      singleHighCapLentry, singleHighCapP, singleHighCapCoCap,
      singleLateEntryCoCap, singleHighCapCeilPM, singleHighCapFloorPM,
      singleHighCapBwPM, singleHighCapDPM, singleHighCapCoFloor,
      singleHighCapCoFloorPM, singleHighCapPMDen] <;> omega

theorem singleHighCap_d_pos {n i : Nat}
    (hnLarge : 65536 <= n) (hi : i < singleHighCapBridgeLength) :
    0 < singleHighCapLiveGap n i := by
  have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
  interval_cases i <;>
    simp [singleHighCapBridgeLength, singleHighCapLiveGap,
      singleHighCapAlo, singleHighCapBw, singleHighCapD,
      singleHighCapLentry, singleHighCapP, singleHighCapCoCap,
      singleLateEntryCoCap, singleHighCapCeilPM, singleHighCapBwPM,
      singleHighCapDPM, singleHighCapPMDen] <;> omega

theorem singleHighCap_d_lt_n {n i : Nat}
    (hnLarge : 65536 <= n) (hi : i < singleHighCapBridgeLength) :
    singleHighCapLiveGap n i < n := by
  have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
  interval_cases i <;>
    simp [singleHighCapBridgeLength, singleHighCapLiveGap,
      singleHighCapAlo, singleHighCapBw, singleHighCapD,
      singleHighCapLentry, singleHighCapP, singleHighCapCoCap,
      singleLateEntryCoCap, singleHighCapCeilPM, singleHighCapBwPM,
      singleHighCapDPM, singleHighCapPMDen] <;> omega

theorem singleHighCap_d_large {n i : Nat}
    (hnLarge : 65536 <= n) (hi : i < singleHighCapBridgeLength) :
    n <= 39 * singleHighCapLiveGap n i := by
  have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
  interval_cases i <;>
    simp [singleHighCapBridgeLength, singleHighCapLiveGap,
      singleHighCapAlo, singleHighCapBw, singleHighCapD,
      singleHighCapLentry, singleHighCapP, singleHighCapCoCap,
      singleLateEntryCoCap, singleHighCapCeilPM, singleHighCapBwPM,
      singleHighCapDPM, singleHighCapPMDen] <;> omega

theorem singleHighCap_horizon_pos {n i : Nat}
    (hnLarge : 65536 <= n) (hi : i < singleHighCapBridgeLength) :
    0 < singleHighCapHorizon n i := by
  have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
  interval_cases i <;>
    simp [singleHighCapBridgeLength, singleHighCapHorizon,
      singleHighCapCeilPM, singleHighCapTPM, singleHighCapPMDen] <;>
    omega

/-! ## Rungs and bridge composition -/

noncomputable def singleHighCapRungError (n i : Nat) : ENNReal :=
  singleLateRungError n (singleHighCapLiveGap n i)
    (singleHighCapCoFloor n i) (singleHighCapD n i) (singleHighCapD n i)
    (singleHighCapH n i) (singleHighCapM n i) (singleHighCapK n i)
    (singleHighCapHorizon n i) singleHighCapDirW
    (singleHighCapDirEta n i) (singleHighCapBw n i)
    (singleHighCapLentry n i)
    (singleHighCapLexit n i + singleHighCapD n i)
    (singleHighCapHi n i) (singleHighCapMhi n i)
    (singleHighCapQ n i + 1) (singleHighCapSret n i)
    (singleHighCapRetEps n i)

theorem singleHighCap_rung
    (n i : Nat) (hn : 2 <= n) (hnLarge : 65536 <= n)
    (hi : i < singleHighCapBridgeLength) :
    Reaches (singleStateStep n hn) (singleHighCapHorizon n i)
      (SingleLateCheckpoint n (singleHighCapP n i))
      (SingleLateCheckpoint n (singleHighCapQ n i))
      (singleHighCapRungError n i) := by
  have hn0 : 0 < n := by omega
  have hdlt := singleHighCap_d_lt_n (n := n) (i := i) hnLarge hi
  obtain ⟨hrel, hwη, hη1, hηt, hw1, hw0, hwt, hwv⟩ :=
    singleHighCapDir_params (n := n) (i := i) hn0 hdlt
      (singleHighCap_d_large (n := n) (i := i) hnLarge hi)
  have hq : singleHighCapDirQ n i ≠ 0 := by
    unfold singleHighCapDirQ
    omega
  have hHpos : 0 < singleHighCapH n i := by
    unfold singleHighCapH
    omega
  have hpp1 :
      singleBandProductivity n (singleHighCapLiveGap n i)
          (singleHighCapCoFloor n i) <= 1 :=
    singleBandProductivity_le_one_of_sum n hn
      (singleHighCapLiveGap n i) (singleHighCapCoFloor n i)
      (singleHighCap_prodRoom (n := n) (i := i) hnLarge hi)
  have hreach := singleLate_rung_checkpoint hn
    (singleHighCapP n i) (singleHighCapQ n i)
    (singleHighCapAlo n i) (singleHighCapHi n i)
    (singleHighCapD n i) (singleHighCapD n i)
    (singleHighCapH n i) (singleHighCapDirP n i)
    (singleHighCapDirQ n i) (singleHighCapBw n i)
    (singleHighCapM n i) (singleHighCapK n i)
    (singleHighCapHorizon n i)
    (singleHighCapLentry n i) (singleHighCapLexit n i)
    (singleHighCapSret n i) (singleHighCapQ n i + 1)
    (singleHighCapHi n i) (singleHighCapMhi n i)
    (singleHighCapLiveGap n i) (singleHighCapCoFloor n i)
    (singleHighCap_entry (n := n) (i := i) hi)
    (by
      have h := singleHighCap_exit (n := n) (i := i) hi
      omega)
    hHpos hq singleHighCapDirW singleHighCapDirV
    (singleHighCapDirEta n i) (singleHighCapDirU n i)
    (singleHighCapRetEps n i)
    singleHighCapRetEps_le_one
    rfl hrel hwη hwv hw1 hw0 hη1 hwt hηt
    (singleHighCap_hlive_ratio
      (n := n) (aLoΛ := singleHighCapAlo n i)
      (hiΛ := singleHighCapHi n i) (D := singleHighCapD n i)
      (H := singleHighCapH n i) (d := singleHighCapLiveGap n i)
      (by
        have h := singleHighCap_hgap (n := n) (i := i) hnLarge hi
        omega)
      (le_of_lt hdlt))
    (singleHighCap_aLo_bw (n := n) (i := i) hnLarge hi)
    (singleHighCap_vac (n := n) (i := i) hnLarge hi)
    (singleHighCap_Ln (n := n) (i := i) hnLarge hi)
    (by
      have h := singleHighCap_exit (n := n) (i := i) hi
      omega)
    (singleHighCap_slack (n := n) (i := i) hi)
    (singleHighCap_slack (n := n) (i := i) hi)
    (singleHighCap_targetHi (n := n) (i := i) hnLarge hi)
    (by
      unfold singleHighCapK
      omega)
    (singleHighCap_hgap (n := n) (i := i) hnLarge hi)
    (singleHighCap_coClock (n := n) (i := i) hnLarge hi)
    hpp1
    (by
      unfold singleHighCapH
      omega)
  simpa [singleHighCapRungError] using hreach

def singleHighCapBridgeHorizon (n : Nat) : Nat :=
  ∑ i ∈ Finset.range singleHighCapBridgeLength, singleHighCapHorizon n i

noncomputable def singleHighCapBridgeError (n : Nat) : ENNReal :=
  ∑ i ∈ Finset.range singleHighCapBridgeLength, singleHighCapRungError n i

theorem singleHighCap_bridge
    (n : Nat) (hn : 2 <= n) (hnLarge : 65536 <= n) :
    Reaches (singleStateStep n hn) (singleHighCapBridgeHorizon n)
      (SingleLateCheckpoint n (singleHighCapCoCap n 0))
      (SingleLateCheckpoint n (singleHighCapCoCap n singleHighCapBridgeLength))
      (singleHighCapBridgeError n) := by
  let Pstage : Nat -> SingleState n -> Prop :=
    fun i => SingleLateCheckpoint n (singleHighCapCoCap n i)
  let T : Nat -> Nat := fun i => singleHighCapHorizon n i
  let eps : Nat -> ENNReal := fun i => singleHighCapRungError n i
  have hrungs : forall i, i < singleHighCapBridgeLength ->
      Reaches (singleStateStep n hn) (T i) (Pstage i) (Pstage (i + 1))
        (eps i) := by
    intro i hi
    simpa [Pstage, T, eps, singleHighCapP, singleHighCapQ] using
      singleHighCap_rung n i hn hnLarge hi
  have hchain :=
    Reaches.chain (K := singleStateStep n hn) (P := Pstage)
      (T := T) (ε := eps) (k := singleHighCapBridgeLength) hrungs
  have hTsum :
      (∑ i ∈ Finset.range singleHighCapBridgeLength, T i) =
        singleHighCapBridgeHorizon n := by
    simp [T, singleHighCapBridgeHorizon]
  rw [hTsum] at hchain
  simpa [Pstage, eps, singleHighCapBridgeError] using hchain

theorem singleHighCap_bridge_lateEntry_to_quarter
    (n : Nat) (hn : 2 <= n) (hnLarge : 65536 <= n) :
    Reaches (singleStateStep n hn) (singleHighCapBridgeHorizon n)
      (SingleLateCheckpoint n (singleLateEntryCoCap n))
      (SingleLateCheckpoint n (n / 4))
      (singleHighCapBridgeError n) := by
  simpa [singleHighCapBridgeLength, singleHighCapCoCap] using
    singleHighCap_bridge n hn hnLarge

def singleMiddleHighCapHorizon (n : Nat) : Nat :=
  singleMiddleHorizon n + singleHighCapBridgeHorizon n

noncomputable def singleMiddleHighCapError (n : Nat) : ENNReal :=
  singleMiddleError n + singleHighCapBridgeError n

theorem singleMiddle_highCap_reaches_quarter
    (n : Nat) (hn : 2 <= n) (hlog : 30 <= Nat.log 2 n) :
    Reaches (singleStateStep n hn) (singleMiddleHighCapHorizon n)
      (SingleEarlyTarget n)
      (SingleLateCheckpoint n (n / 4))
      (singleMiddleHighCapError n) := by
  have hnLarge : 65536 <= n := by
    calc
      65536 = 2 ^ 16 := by norm_num
      _ <= 2 ^ Nat.log 2 n :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      _ <= n := Nat.pow_log_le_self 2 (by
        intro h0
        rw [h0, Nat.log_zero_right] at hlog
        omega)
  have hm := singleMiddle_reaches_lateEntry n hn hlog
  have hb := singleHighCap_bridge_lateEntry_to_quarter n hn hnLarge
  simpa [singleMiddleHighCapHorizon, singleMiddleHighCapError] using
    hm.comp hb

def singleMiddleHighCapConstLateHorizon (n gamma : Nat) : Nat :=
  singleMiddleHighCapHorizon n + singleLateConstDyadicLadderHorizon n gamma

noncomputable def singleMiddleHighCapConstLateError
    (n gamma : Nat) : ENNReal :=
  singleMiddleHighCapError n + singleLateConstDyadicLadderError n gamma

theorem singleMiddle_highCap_constLate_reaches_target
    (n gamma : Nat) (hn : 2 <= n)
    (hlog : 1024 <= Nat.log 2 n) (hgamma : 1 <= gamma)
    (hsize : 6 * gamma * Nat.log 2 n <= n) :
    Reaches (singleStateStep n hn)
      (singleMiddleHighCapConstLateHorizon n gamma)
      (SingleEarlyTarget n)
      (SingleLateCheckpoint n (singleLateTargetCap n gamma))
      (singleMiddleHighCapConstLateError n gamma) := by
  have hm := singleMiddle_highCap_reaches_quarter n hn
    (hlog.trans' (by norm_num))
  have hl := singleLate_const_dyadic_ladder n gamma hn hlog hgamma
    hsize
  simpa [singleMiddleHighCapConstLateHorizon,
    singleMiddleHighCapConstLateError] using hm.comp hl

section Inhabitation

example : singleHighCapBridgeLength = 12 := rfl

example :
    singleHighCapCoCap (2 ^ 16) 0 = 5 * (2 ^ 16) / 8 := by
  rfl

example :
    Reaches (singleStateStep (2 ^ 16) (by norm_num))
      (singleHighCapHorizon (2 ^ 16) 0)
      (SingleLateCheckpoint (2 ^ 16) (singleHighCapP (2 ^ 16) 0))
      (SingleLateCheckpoint (2 ^ 16) (singleHighCapQ (2 ^ 16) 0))
      (singleHighCapRungError (2 ^ 16) 0) := by
  exact singleHighCap_rung (2 ^ 16) 0 (by norm_num) (by norm_num)
    (by norm_num [singleHighCapBridgeLength])

end Inhabitation

end Tri

#print axioms Tri.singleHighCapBridgeLength
#print axioms Tri.singleHighCapDir_params
#print axioms Tri.singleHighCap_hlive_ratio
#print axioms Tri.singleHighCap_rung
#print axioms Tri.singleHighCap_bridge
#print axioms Tri.singleHighCap_bridge_lateEntry_to_quarter
#print axioms Tri.singleMiddle_highCap_reaches_quarter
#print axioms Tri.singleMiddleHighCapConstLateHorizon
#print axioms Tri.singleMiddleHighCapConstLateError
#print axioms Tri.singleMiddle_highCap_constLate_reaches_target
