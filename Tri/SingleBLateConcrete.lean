/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBLateLadder
import Tri.SingleBLateDirection

/-!
# Superseding concrete Single-B late subrung

This module starts replacing the relay scaffold's late scalar layer.  The old
`singleLate_subrung` remains available for dependency stability, but the theorem
below instantiates the structural late rung with the constant-base direction
constants from `SingleBLateDirection`.
-/

namespace Tri

open scoped ENNReal

/-- Raw horizon for the constant-base late subrung. -/
def singleLateConstSubHorizon (n : Nat) : Nat := 24 * n

/-- Resolution budget for the main structural deadline. -/
def singleLateConstM (R : Nat) : Nat := 7 * R

/-- Resolution budget for the high structural deadline. -/
def singleLateConstMhi (R : Nat) : Nat := 22 * R

/-- Co-return buffer for the constant-base late subrung. -/
def singleLateConstSret (R : Nat) : Nat := 5 * R

/-- Productive co-floor used by the resolved productive clock. -/
def singleLateConstCoFloor (R : Nat) : Nat := 5 * R

/-- Structural creation budget for a subrung entering with public co-cap `P`. -/
def singleLateConstH (P R : Nat) : Nat :=
  P + 2 * singleLateConstMhi R + R + 1

/-- Productive-count budget. -/
def singleLateConstK (P R : Nat) : Nat :=
  singleLateConstH P R + singleLateConstM R

/-- Co-return tilt.  This is the finite-`n` optimum for `T = 24n`,
`sret = 5R`, up to the harmless `(Q+1)` denominator. -/
noncomputable def singleLateConstRetEps (Q R : Nat) : ENNReal :=
  ENNReal.ofReal (((singleLateConstSret R + 1 : Nat) : Real) /
    (96 * ((Q + 1 : Nat) : Real)))

theorem singleLateConstRetEps_le_one {Q R : Nat}
    (h : singleLateConstSret R + 1 <= 96 * (Q + 1)) :
    singleLateConstRetEps Q R <= 1 := by
  unfold singleLateConstRetEps
  rw [show (1 : ENNReal) = ENNReal.ofReal (1 : Real) by
    exact ENNReal.ofReal_one.symm]
  apply ENNReal.ofReal_le_ofReal
  have hden : (0 : Real) < 96 * ((Q + 1 : Nat) : Real) := by positivity
  rw [div_le_one hden]
  exact_mod_cast h

/-- Error of one superseding constant-base late subrung. -/
noncomputable def singleLateConstSubRungError
    (n Qbase P Q R Lentry Lexit hiΛ d : Nat) : ENNReal :=
  singleLateRungError n d (singleLateConstCoFloor R) R R
    (singleLateConstH P R) (singleLateConstM R)
    (singleLateConstK P R) (singleLateConstSubHorizon n)
    singleLateDirW (singleLateDirEta n Qbase) R Lentry
    (Lexit + R) hiΛ (singleLateConstMhi R) (Q + 1)
    (singleLateConstSret R) (singleLateConstRetEps Q R)

/-- One concrete constant-base structural late subrung.  `Qbase` is the dyadic
stage scale used in the direction ratio; `P` and `Q` are the current subrung
entry/exit caps. -/
theorem singleLate_const_subrung_flex
    (n Qbase P Q R S Lentry Lexit aLoΛ hiΛ d : Nat) (hn : 2 <= n)
    (hR : 0 < R) (hQbase : 0 < Qbase)
    (hQdir : 4 * Qbase < n)
    (hRupper : 32 * R <= Qbase + 32)
    (hdguard : n + 1 <= d + 2 * Qbase + 2 * R)
    (hentry : Lentry + P = 2 * n)
    (hexit : Lexit + Q = 2 * n)
    (hS : 0 < S)
    (hstep : Lentry + S = Lexit)
    (haLo : aLoΛ + R = Lentry)
    (hhi : Lexit + 6 * R = hiΛ)
    (hgap : n + R + d = aLoΛ + 1)
    (hLn : n + 1 <= Lexit)
    (hcoClock : hiΛ + 2 * singleLateConstM R +
        2 * singleLateConstCoFloor R <= 2 * n + 1)
    (hprodRoom : d + 2 * singleLateConstCoFloor R <= n)
    (hε1 : singleLateConstRetEps Q R <= 1) :
    Reaches (singleStateStep n hn) (singleLateConstSubHorizon n)
      (SingleLateCheckpoint n P)
      (SingleLateCheckpoint n Q)
      (singleLateConstSubRungError n Qbase P Q R Lentry Lexit hiΛ d) := by
  have hn0 : 0 < n := by omega
  obtain ⟨hrel, hwη, hη1, hηt, hw1, hw0, hwt, hwv⟩ :=
    singleLateDir_params n Qbase hn0 hQbase hQdir
  have hq : n ≠ 0 := by omega
  have hpp1 :
      singleBandProductivity n d (singleLateConstCoFloor R) <= 1 := by
    exact singleBandProductivity_le_one_of_sum n hn d
      (singleLateConstCoFloor R) hprodRoom
  have hHpos : 0 < singleLateConstH P R := by
    unfold singleLateConstH
    omega
  have hreach := singleLate_rung_checkpoint hn P Q aLoΛ hiΛ R R
    (singleLateConstH P R) (singleLateDirP Qbase) n R
    (singleLateConstM R) (singleLateConstK P R)
    (singleLateConstSubHorizon n) Lentry Lexit
    (singleLateConstSret R) (Q + 1) hiΛ
    (singleLateConstMhi R) d (singleLateConstCoFloor R)
    hentry (by rw [hexit]) hHpos hq
    singleLateDirW singleLateDirV (singleLateDirEta n Qbase)
    (singleLateDirU n Qbase) (singleLateConstRetEps Q R) hε1
    rfl hrel hwη hwv hw1 hw0 hη1 hwt hηt
    (singleLate_hlive_ratio
      (n := n) (aLoΛ := aLoΛ) (hiΛ := hiΛ) (D := R)
      (H := singleLateConstH P R) (Q := Qbase) (R := R) (d := d)
      (by omega) rfl hdguard hRupper hQdir hQbase)
    haLo
    (by omega)
    hLn
    (by omega)
    (by
      unfold singleLateConstSret
      omega)
    (by
      unfold singleLateConstSret
      omega)
    (by omega)
    (by
      unfold singleLateConstK
      omega)
    hgap
    hcoClock
    hpp1
    (by
      unfold singleLateConstH singleLateConstMhi
      omega)
  simpa [singleLateConstSubRungError] using hreach

/-- One concrete constant-base structural late subrung with public climb equal
to the structural scale. -/
theorem singleLate_const_subrung
    (n Qbase P Q R Lentry Lexit aLoΛ hiΛ d : Nat) (hn : 2 <= n)
    (hR : 0 < R) (hQbase : 0 < Qbase)
    (hQdir : 4 * Qbase < n)
    (hRupper : 32 * R <= Qbase + 32)
    (hdguard : n + 1 <= d + 2 * Qbase + 2 * R)
    (hentry : Lentry + P = 2 * n)
    (hexit : Lexit + Q = 2 * n)
    (hstep : Lentry + R = Lexit)
    (haLo : aLoΛ + R = Lentry)
    (hhi : Lexit + 6 * R = hiΛ)
    (hgap : n + R + d = aLoΛ + 1)
    (hLn : n + 1 <= Lexit)
    (hcoClock : hiΛ + 2 * singleLateConstM R +
        2 * singleLateConstCoFloor R <= 2 * n + 1)
    (hprodRoom : d + 2 * singleLateConstCoFloor R <= n)
    (hε1 : singleLateConstRetEps Q R <= 1) :
    Reaches (singleStateStep n hn) (singleLateConstSubHorizon n)
      (SingleLateCheckpoint n P)
      (SingleLateCheckpoint n Q)
      (singleLateConstSubRungError n Qbase P Q R Lentry Lexit hiΛ d) := by
  exact singleLate_const_subrung_flex n Qbase P Q R R Lentry Lexit aLoΛ
    hiΛ d hn hR hQbase hQdir hRupper hdguard hentry hexit hR
    hstep haLo hhi hgap hLn hcoClock hprodRoom hε1

/-! ## Symbolic 32-subrung stage -/

/-- Number of constant-base subrungs in one dyadic late stage. -/
def singleLateConstStageLength : Nat := 32

/-- Horizon of one constant-base dyadic late stage. -/
def singleLateConstStageHorizon (n : Nat) : Nat :=
  singleLateConstStageLength * singleLateConstSubHorizon n

/-- Error of a symbolic 32-subrung constant-base stage. -/
noncomputable def singleLateConstStageError
    (n Qbase R : Nat) (Cap Lentry Lexit hiΛ d : Nat -> Nat) : ENNReal :=
  ∑ i ∈ Finset.range singleLateConstStageLength,
    singleLateConstSubRungError n Qbase (Cap i) (Cap (i + 1)) R
      (Lentry i) (Lexit i) (hiΛ i) (d i)

/-- Symbolic composition of thirty-two constant-base late subrungs.  Concrete
dyadic arithmetic is supplied by witness functions, keeping this theorem's
statement free of natural subtraction. -/
theorem singleLate_const_stage32_symbolic
    (n Qbase R : Nat)
    (Cap Lentry Lexit aLoΛ hiΛ d : Nat -> Nat)
    (hn : 2 <= n)
    (hR : 0 < R)
    (hQbase : 0 < Qbase)
    (hQsmall : 8 * Qbase <= n)
    (hRupper : 32 * R <= Qbase + 32)
    (hdguard : forall i, i < singleLateConstStageLength ->
      n + 1 <= d i + 2 * Qbase + 2 * R)
    (hentry : forall i, i < singleLateConstStageLength ->
      Lentry i + Cap i = 2 * n)
    (hexit : forall i, i < singleLateConstStageLength ->
      Lexit i + Cap (i + 1) = 2 * n)
    (hstep : forall i, i < singleLateConstStageLength ->
      Lentry i + R = Lexit i)
    (haLo : forall i, i < singleLateConstStageLength ->
      aLoΛ i + R = Lentry i)
    (hhi : forall i, i < singleLateConstStageLength ->
      Lexit i + 6 * R = hiΛ i)
    (hgap : forall i, i < singleLateConstStageLength ->
      n + R + d i = aLoΛ i + 1)
    (hLn : forall i, i < singleLateConstStageLength ->
      n + 1 <= Lexit i)
    (hcoClock : forall i, i < singleLateConstStageLength ->
      hiΛ i + 2 * singleLateConstM R +
          2 * singleLateConstCoFloor R <= 2 * n + 1)
    (hprodRoom : forall i, i < singleLateConstStageLength ->
      d i + 2 * singleLateConstCoFloor R <= n)
    (hε1 : forall i, i < singleLateConstStageLength ->
      singleLateConstRetEps (Cap (i + 1)) R <= 1) :
    Reaches (singleStateStep n hn) (singleLateConstStageHorizon n)
      (SingleLateCheckpoint n (Cap 0))
      (SingleLateCheckpoint n (Cap singleLateConstStageLength))
      (singleLateConstStageError n Qbase R Cap Lentry Lexit hiΛ d) := by
  let Pstage : Nat -> SingleState n -> Prop :=
    fun i => SingleLateCheckpoint n (Cap i)
  let T : Nat -> Nat := fun _ => singleLateConstSubHorizon n
  let eps : Nat -> ENNReal := fun i =>
    singleLateConstSubRungError n Qbase (Cap i) (Cap (i + 1)) R
      (Lentry i) (Lexit i) (hiΛ i) (d i)
  have hrungs : forall i, i < singleLateConstStageLength ->
      Reaches (singleStateStep n hn) (T i) (Pstage i) (Pstage (i + 1))
        (eps i) := by
    intro i hi
    exact singleLate_const_subrung n Qbase (Cap i) (Cap (i + 1)) R
      (Lentry i) (Lexit i) (aLoΛ i) (hiΛ i) (d i) hn hR hQbase
      (by omega) hRupper (hdguard i hi) (hentry i hi) (hexit i hi)
      (hstep i hi) (haLo i hi) (hhi i hi) (hgap i hi) (hLn i hi)
      (hcoClock i hi) (hprodRoom i hi) (hε1 i hi)
  have hchain :=
    Reaches.chain (K := singleStateStep n hn) (P := Pstage)
      (T := T) (ε := eps) (k := singleLateConstStageLength) hrungs
  have hTsum :
      (∑ i ∈ Finset.range singleLateConstStageLength, T i) =
        singleLateConstStageHorizon n := by
    simp [T, singleLateConstStageHorizon, singleLateConstStageLength]
  rw [hTsum] at hchain
  simpa [Pstage, eps, singleLateConstStageError] using hchain

/-! ## Concrete 32-subrung schedule -/

/-- Saturated index for a 32-subrung late stage. -/
def singleLateConstIdx32 (i : Nat) : Nat := min i singleLateConstStageLength

/-- Remaining cap multiplier for a 32-subrung late stage. -/
def singleLateConstRem32 (i : Nat) : Nat :=
  singleLateConstStageLength - singleLateConstIdx32 i

/-- Concrete cap schedule for one constant-base stage: `Q+32R` down to `Q`. -/
def singleLateConstCap32 (Q R i : Nat) : Nat :=
  Q + singleLateConstRem32 i * R

/-- Concrete entry-level witness schedule. -/
def singleLateConstLentry32 (L0 R i : Nat) : Nat :=
  L0 + singleLateConstIdx32 i * R

/-- Concrete exit-level witness schedule. -/
def singleLateConstLexit32 (L0 R i : Nat) : Nat :=
  L0 + (singleLateConstIdx32 i + 1) * R

/-- Concrete lower-band witness schedule. -/
def singleLateConstALo32 (A0 R i : Nat) : Nat :=
  A0 + singleLateConstIdx32 i * R

/-- Concrete high-band witness schedule. -/
def singleLateConstHi32 (L0 R i : Nat) : Nat :=
  L0 + (singleLateConstIdx32 i + 7) * R

/-- Concrete gap-floor witness schedule. -/
def singleLateConstD32 (d0 R i : Nat) : Nat :=
  d0 + singleLateConstIdx32 i * R

theorem singleLateConstIdx32_of_lt {i : Nat}
    (hi : i < singleLateConstStageLength) :
    singleLateConstIdx32 i = i := by
  unfold singleLateConstIdx32
  exact Nat.min_eq_left (Nat.le_of_lt hi)

theorem singleLateConstIdx32_succ_of_lt {i : Nat}
    (hi : i < singleLateConstStageLength) :
    singleLateConstIdx32 (i + 1) = i + 1 := by
  unfold singleLateConstIdx32
  have hle : i + 1 <= singleLateConstStageLength := by omega
  exact Nat.min_eq_left hle

/-- Concrete 32-subrung constant-base late stage. -/
theorem singleLate_const_stage32_concrete
    (n Q R L0 A0 d0 : Nat) (hn : 2 <= n)
    (hR : 0 < R)
    (hQ : 0 < Q)
    (hQsmall : 8 * Q <= n)
    (hRfit : 32 * R <= Q)
    (hentry0 : L0 + (Q + 32 * R) = 2 * n)
    (ha0 : A0 + R = L0)
    (hgap0 : n + R + d0 = A0 + 1)
    (hLn0 : n + 1 <= L0 + R)
    (hprodRoom0 : d0 + 41 * R <= n)
    (hRetRoom : singleLateConstSret R + 1 <= 96 * (Q + 1)) :
    Reaches (singleStateStep n hn) (singleLateConstStageHorizon n)
      (SingleLateCheckpoint n (Q + 32 * R))
      (SingleLateCheckpoint n Q)
      (singleLateConstStageError n Q R
        (singleLateConstCap32 Q R) (singleLateConstLentry32 L0 R)
        (singleLateConstLexit32 L0 R) (singleLateConstHi32 L0 R)
        (singleLateConstD32 d0 R)) := by
  have hstage := by
    refine singleLate_const_stage32_symbolic n Q R
      (singleLateConstCap32 Q R) (singleLateConstLentry32 L0 R)
      (singleLateConstLexit32 L0 R) (singleLateConstALo32 A0 R)
      (singleLateConstHi32 L0 R) (singleLateConstD32 d0 R)
      hn hR hQ hQsmall (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro i hi
      have hidx := singleLateConstIdx32_of_lt hi
      simp [singleLateConstD32, hidx, singleLateConstStageLength] at *
      omega
    · intro i hi
      have hidx := singleLateConstIdx32_of_lt hi
      have hrem : singleLateConstRem32 i = 32 - i := by
        unfold singleLateConstRem32
        simp [hidx, singleLateConstStageLength]
      have hmul : i * R + (32 - i) * R = 32 * R := by
        rw [← Nat.add_mul]
        have hi32 : i <= 32 := by
          unfold singleLateConstStageLength at hi
          omega
        have hsum : i + (32 - i) = 32 := by omega
        rw [hsum]
      simp [singleLateConstLentry32, singleLateConstCap32,
        hidx, hrem]
      nlinarith
    · intro i hi
      have hidx := singleLateConstIdx32_of_lt hi
      have hidxs := singleLateConstIdx32_succ_of_lt hi
      have hremS : singleLateConstRem32 (i + 1) = 31 - i := by
        unfold singleLateConstRem32
        simp [hidxs, singleLateConstStageLength]
      have hmul : (i + 1) * R + (31 - i) * R = 32 * R := by
        rw [← Nat.add_mul]
        have hi31 : i <= 31 := by
          unfold singleLateConstStageLength at hi
          omega
        have hsum : i + 1 + (31 - i) = 32 := by omega
        rw [hsum]
      simp [singleLateConstLexit32, singleLateConstCap32,
        hidx, hremS]
      nlinarith
    · intro i hi
      have hidx := singleLateConstIdx32_of_lt hi
      simp [singleLateConstLentry32, singleLateConstLexit32, hidx]
      ring
    · intro i hi
      have hidx := singleLateConstIdx32_of_lt hi
      simp [singleLateConstALo32, singleLateConstLentry32, hidx]
      omega
    · intro i hi
      have hidx := singleLateConstIdx32_of_lt hi
      simp [singleLateConstLexit32, singleLateConstHi32, hidx]
      ring
    · intro i hi
      have hidx := singleLateConstIdx32_of_lt hi
      simp [singleLateConstD32, singleLateConstALo32, hidx]
      omega
    · intro i hi
      have hidx := singleLateConstIdx32_of_lt hi
      simp [singleLateConstLexit32, hidx]
      omega
    · intro i hi
      have hidx := singleLateConstIdx32_of_lt hi
      simp [singleLateConstHi32, singleLateConstM, singleLateConstCoFloor,
        hidx]
      have hi31 : i <= 31 := by
        unfold singleLateConstStageLength at hi
        omega
      nlinarith
    · intro i hi
      have hidx := singleLateConstIdx32_of_lt hi
      have hi31 : i <= 31 := by
        unfold singleLateConstStageLength at hi
        omega
      have hcalc :
          singleLateConstD32 d0 R i + 2 * singleLateConstCoFloor R =
            d0 + (i + 10) * R := by
        simp [singleLateConstD32, singleLateConstCoFloor, hidx]
        ring
      rw [hcalc]
      have hi41 : i + 10 <= 41 := by omega
      exact le_trans
        (Nat.add_le_add_left (Nat.mul_le_mul_right R hi41) d0)
        hprodRoom0
    · intro i hi
      apply singleLateConstRetEps_le_one
      have hidxs := singleLateConstIdx32_succ_of_lt hi
      have hremS : singleLateConstRem32 (i + 1) = 31 - i := by
        unfold singleLateConstRem32
        simp [hidxs, singleLateConstStageLength]
      simp [singleLateConstCap32, hremS]
      omega
  simpa [singleLateConstCap32, singleLateConstRem32,
    singleLateConstIdx32, singleLateConstStageLength,
    singleLateConstStageError]
    using hstage

/-! ## Exact dyadic constant-base ladder -/

/-- Exact constant-base quota for a dyadic stage ending at `Q`. -/
def singleLateConstDyadicR (Q : Nat) : Nat := Q / 32

/-- Internal widened start cap for a constant-base dyadic stage ending at
`Q`. -/
def singleLateConstDyadicStartCap (Q : Nat) : Nat :=
  Q + 32 * singleLateConstDyadicR Q

/-- Internal entry-level base for a constant-base dyadic stage ending at
`Q`. -/
def singleLateConstDyadicL0 (n Q : Nat) : Nat :=
  2 * n - singleLateConstDyadicStartCap Q

/-- Internal lower-band base witness for a constant-base dyadic stage. -/
def singleLateConstDyadicA0 (n Q : Nat) : Nat :=
  singleLateConstDyadicL0 n Q - singleLateConstDyadicR Q

/-- Internal productive gap base for a constant-base dyadic stage. -/
def singleLateConstDyadicD0 (n Q : Nat) : Nat :=
  n - Q - 34 * singleLateConstDyadicR Q + 1

/-- Number of constant-base dyadic late stages after the high-cap bridge.
This starts at public cap `n/4 = phase2Scale n 2` and hides the natural
subtraction in the definition. -/
def singleLateConstDyadicStages (n gamma : Nat) : Nat :=
  phase2StageCount n gamma - 2

/-- Public cap schedule for the constant-base late ladder from `n/4`. -/
def singleLateConstDyadicCap (n _gamma i : Nat) : Nat :=
  phase2Scale n (2 + i)

/-- First flex subrung exit for a dyadic stage ending at `Q`. -/
def singleLateConstDyadicFlexExit (Q : Nat) : Nat :=
  Q + 31 * singleLateConstDyadicR Q

/-- Public climb of the first flex subrung. -/
def singleLateConstDyadicFlexS (P Q : Nat) : Nat :=
  P - singleLateConstDyadicFlexExit Q

/-- Direction scale for the first flex subrung, chosen as `ceil(P/2)`. -/
def singleLateConstDyadicFlexQbase (P : Nat) : Nat :=
  (P + 1) / 2

/-- Entry-level witness for the first flex subrung. -/
def singleLateConstDyadicFlexLentry (n P : Nat) : Nat :=
  2 * n - P

/-- Exit-level witness for the first flex subrung. -/
def singleLateConstDyadicFlexLexit (n Q : Nat) : Nat :=
  2 * n - singleLateConstDyadicFlexExit Q

/-- Lower-band witness for the first flex subrung. -/
def singleLateConstDyadicFlexAlo (n P Q : Nat) : Nat :=
  singleLateConstDyadicFlexLentry n P - singleLateConstDyadicR Q

/-- High-band witness for the first flex subrung. -/
def singleLateConstDyadicFlexHi (n Q : Nat) : Nat :=
  singleLateConstDyadicFlexLexit n Q + 6 * singleLateConstDyadicR Q

/-- Productive gap witness for the first flex subrung. -/
def singleLateConstDyadicFlexD (n P Q : Nat) : Nat :=
  n - P - 2 * singleLateConstDyadicR Q + 1

/-- Error of the first flex subrung in a dyadic stage. -/
noncomputable def singleLateConstDyadicFlexError
    (n P Q : Nat) : ENNReal :=
  singleLateConstSubRungError n (singleLateConstDyadicFlexQbase P)
    P (singleLateConstDyadicFlexExit Q) (singleLateConstDyadicR Q)
    (singleLateConstDyadicFlexLentry n P)
    (singleLateConstDyadicFlexLexit n Q)
    (singleLateConstDyadicFlexHi n Q)
    (singleLateConstDyadicFlexD n P Q)

/-- Horizon of one relaxed constant-base dyadic stage: one flex subrung plus
the old exact 32-subrung stage. -/
def singleLateConstRelaxedStageHorizon (n : Nat) : Nat :=
  singleLateConstSubHorizon n + singleLateConstStageHorizon n

/-- Error of one relaxed constant-base dyadic stage. -/
noncomputable def singleLateConstRelaxedStageError
    (n P Q : Nat) : ENNReal :=
  singleLateConstDyadicFlexError n P Q +
    singleLateConstStageError n Q (singleLateConstDyadicR Q)
      (singleLateConstCap32 Q (singleLateConstDyadicR Q))
      (singleLateConstLentry32 (singleLateConstDyadicL0 n Q)
        (singleLateConstDyadicR Q))
      (singleLateConstLexit32 (singleLateConstDyadicL0 n Q)
        (singleLateConstDyadicR Q))
      (singleLateConstHi32 (singleLateConstDyadicL0 n Q)
        (singleLateConstDyadicR Q))
      (singleLateConstD32 (singleLateConstDyadicD0 n Q)
        (singleLateConstDyadicR Q))

/-- Error of one constant-base dyadic late stage in the new schedule. -/
noncomputable def singleLateConstDyadicStepError
    (n gamma i : Nat) : ENNReal :=
  let P := singleLateConstDyadicCap n gamma i
  let Q := singleLateConstDyadicCap n gamma (i + 1)
  singleLateConstRelaxedStageError n P Q

/-- Horizon of the constant-base late ladder after the high-cap bridge. -/
def singleLateConstDyadicLadderHorizon (n gamma : Nat) : Nat :=
  singleLateConstDyadicStages n gamma * singleLateConstRelaxedStageHorizon n

/-- Error of the constant-base late ladder after the high-cap bridge. -/
noncomputable def singleLateConstDyadicLadderError
    (n gamma : Nat) : ENNReal :=
  ∑ i ∈ Finset.range (singleLateConstDyadicStages n gamma),
    singleLateConstDyadicStepError n gamma i

theorem singleLateConstDyadicR_upper (Q : Nat) :
    32 * singleLateConstDyadicR Q <= Q + 32 := by
  unfold singleLateConstDyadicR
  have hdiv := Nat.div_add_mod Q 32
  have hmod := Nat.mod_lt Q (by norm_num : 0 < 32)
  omega

theorem singleLateConstDyadic_coRoom
    {Q : Nat} (hQ : 512 <= Q) :
    30 * singleLateConstDyadicR Q <= Q + 1 := by
  unfold singleLateConstDyadicR
  have hdiv := Nat.div_add_mod Q 32
  have hmod := Nat.mod_lt Q (by norm_num : 0 < 32)
  omega

theorem singleLateConstDyadic_prodRoom
    {Q : Nat} (hQ : 512 <= Q) :
    7 * singleLateConstDyadicR Q + 1 <= Q := by
  unfold singleLateConstDyadicR
  have hdiv := Nat.div_add_mod Q 32
  have hmod := Nat.mod_lt Q (by norm_num : 0 < 32)
  omega

theorem singleLateConstDyadic_retRoom
    {Q : Nat} (hQ : 512 <= Q) :
    singleLateConstSret (singleLateConstDyadicR Q) + 1 <=
      96 * (Q + 1) := by
  unfold singleLateConstSret singleLateConstDyadicR
  have hdiv := Nat.div_add_mod Q 32
  have hmod := Nat.mod_lt Q (by norm_num : 0 < 32)
  omega

theorem singleLateConstDyadic_fit
    {n Q : Nat} (_hQ : 512 <= Q) (hQsmall : 8 * Q <= n) :
    Q + 34 * singleLateConstDyadicR Q <= n := by
  unfold singleLateConstDyadicR
  have hdiv := Nat.div_add_mod Q 32
  have hmod := Nat.mod_lt Q (by norm_num : 0 < 32)
  omega

theorem singleLate_phase2StageCount_two_le
    (n gamma : Nat) (hlog : 1024 <= Nat.log 2 n)
    (_hgamma : 1 <= gamma) (hsize : 6 * gamma * Nat.log 2 n <= n) :
    2 <= phase2StageCount n gamma := by
  by_contra hlt
  have hk : phase2StageCount n gamma = 0 ∨
      phase2StageCount n gamma = 1 := by omega
  cases hk with
  | inl h0 =>
      have hs := phase2StageCount_spec n gamma
      rw [h0] at hs
      norm_num at hs
      have hsize' : 6 * (gamma * Nat.log 2 n) <= n := by
        simpa [Nat.mul_assoc] using hsize
      have hqLarge : 2 <= n / 4 := by
        have hnLarge : 2 ^ 10 <= n := by
          calc
            2 ^ 10 <= 2 ^ Nat.log 2 n :=
              Nat.pow_le_pow_right (by norm_num)
                (by omega : 10 <= Nat.log 2 n)
            _ <= n := Nat.pow_log_le_self 2 (by
              intro hz
              rw [hz, Nat.log_zero_right] at hlog
              omega)
        omega
      have hdiv := Nat.div_add_mod n 4
      have hmod := Nat.mod_lt n (by norm_num : 0 < 4)
      omega
  | inr h1 =>
      have hs := phase2StageCount_spec n gamma
      rw [h1] at hs
      norm_num at hs
      have hsize' : 6 * (gamma * Nat.log 2 n) <= n := by
        simpa [Nat.mul_assoc] using hsize
      have hqLarge : 2 <= n / 8 := by
        have hnLarge : 2 ^ 10 <= n := by
          calc
            2 ^ 10 <= 2 ^ Nat.log 2 n :=
              Nat.pow_le_pow_right (by norm_num)
                (by omega : 10 <= Nat.log 2 n)
            _ <= n := Nat.pow_log_le_self 2 (by
              intro hz
              rw [hz, Nat.log_zero_right] at hlog
              omega)
        omega
      have hdiv := Nat.div_add_mod n 8
      have hmod := Nat.mod_lt n (by norm_num : 0 < 8)
      omega

/-- One relaxed constant-base dyadic late stage.  The first subrung absorbs
the dyadic floor remainder in its public climb, while the structural budgets
remain at the `Q/32` scale. -/
theorem singleLate_const_dyadic_stage
    (n P Q : Nat) (hn : 2 <= n)
    (hPlo : 2 * Q <= P)
    (hPhi : P <= 2 * Q + 1)
    (hQ : 512 <= Q)
    (hQsmall : 8 * Q <= n) :
    Reaches (singleStateStep n hn) (singleLateConstRelaxedStageHorizon n)
      (SingleLateCheckpoint n P)
      (SingleLateCheckpoint n Q)
      (singleLateConstRelaxedStageError n P Q) := by
  let R := singleLateConstDyadicR Q
  let E := singleLateConstDyadicFlexExit Q
  let S := singleLateConstDyadicFlexS P Q
  let Qbase := singleLateConstDyadicFlexQbase P
  let Lentry := singleLateConstDyadicFlexLentry n P
  let Lexit := singleLateConstDyadicFlexLexit n Q
  let Alo := singleLateConstDyadicFlexAlo n P Q
  let Hi := singleLateConstDyadicFlexHi n Q
  let d := singleLateConstDyadicFlexD n P Q
  let L0 := singleLateConstDyadicL0 n Q
  let A0 := singleLateConstDyadicA0 n Q
  let d0 := singleLateConstDyadicD0 n Q
  have hR : 0 < R := by
    dsimp only [R, singleLateConstDyadicR]
    omega
  have hQpos : 0 < Q := by omega
  have hQbaseDiv := Nat.div_add_mod (P + 1) 2
  have hQbaseMod := Nat.mod_lt (P + 1) (by norm_num : 0 < 2)
  have hP_le_twoQbase : P <= 2 * Qbase := by
    dsimp only [Qbase, singleLateConstDyadicFlexQbase] at hQbaseDiv hQbaseMod ⊢
    omega
  have hQbase_le_Q_succ : Qbase <= Q + 1 := by
    dsimp only [Qbase, singleLateConstDyadicFlexQbase] at hQbaseDiv hQbaseMod ⊢
    omega
  have hQ_le_Qbase : Q <= Qbase := by
    dsimp only [Qbase, singleLateConstDyadicFlexQbase] at hQbaseDiv hQbaseMod ⊢
    omega
  have hQbasePos : 0 < Qbase := by omega
  have hQbaseDir : 4 * Qbase < n := by
    have hlarge : 4 * (Q + 1) < 8 * Q := by omega
    omega
  have hRupper : 32 * R <= Q + 32 := by
    simpa only [R] using singleLateConstDyadicR_upper Q
  have hRfit : 32 * R <= Q := by
    dsimp only [R, singleLateConstDyadicR]
    rw [Nat.mul_comm]
    exact Nat.div_mul_le_self Q 32
  have hRupperFirst : 32 * R <= Qbase + 32 := by omega
  have hElt : E < 2 * Q := by
    dsimp only [E, R, singleLateConstDyadicFlexExit]
    have h31 : 31 * R < Q := by omega
    omega
  have hEstart : E <= singleLateConstDyadicStartCap Q := by
    dsimp only [E, R, singleLateConstDyadicFlexExit,
      singleLateConstDyadicStartCap]
    omega
  have hEleP : E <= P := by omega
  have hSpos : 0 < S := by
    dsimp only [S, singleLateConstDyadicFlexS]
    omega
  have hP2Rle : P + 2 * R <= n := by omega
  have hcoRoom : 30 * R <= Q + 1 := by
    simpa only [R] using singleLateConstDyadic_coRoom (Q := Q) hQ
  have hprodSmall : 7 * R + 1 <= Q := by
    simpa only [R] using singleLateConstDyadic_prodRoom (Q := Q) hQ
  have hfit : Q + 34 * R <= n := by
    simpa only [R] using singleLateConstDyadic_fit (n := n) (Q := Q)
      hQ hQsmall
  have hentry0 : L0 + (Q + 32 * R) = 2 * n := by
    dsimp only [L0, R, singleLateConstDyadicL0,
      singleLateConstDyadicStartCap]
    omega
  have ha0 : A0 + R = L0 := by
    dsimp only [A0, L0, R, singleLateConstDyadicA0,
      singleLateConstDyadicL0, singleLateConstDyadicStartCap]
    omega
  have hgap0 : n + R + d0 = A0 + 1 := by
    dsimp only [d0, A0, L0, R, singleLateConstDyadicD0,
      singleLateConstDyadicA0, singleLateConstDyadicL0,
      singleLateConstDyadicStartCap]
    omega
  have hLn0 : n + 1 <= L0 + R := by
    dsimp only [L0, R, singleLateConstDyadicL0,
      singleLateConstDyadicStartCap]
    omega
  have hprodRoom0 : d0 + 41 * R <= n := by
    dsimp only [d0, R, singleLateConstDyadicD0]
    omega
  have hRetRoom : singleLateConstSret R + 1 <= 96 * (Q + 1) := by
    simpa only [R] using singleLateConstDyadic_retRoom (Q := Q) hQ
  have hfirst : Reaches (singleStateStep n hn) (singleLateConstSubHorizon n)
      (SingleLateCheckpoint n P)
      (SingleLateCheckpoint n E)
      (singleLateConstDyadicFlexError n P Q) := by
    have hentry : Lentry + P = 2 * n := by
      dsimp only [Lentry, singleLateConstDyadicFlexLentry]
      omega
    have hexit : Lexit + E = 2 * n := by
      dsimp only [Lexit, E, singleLateConstDyadicFlexLexit]
      omega
    have hstep : Lentry + S = Lexit := by
      dsimp only [Lentry, Lexit, S, E,
        singleLateConstDyadicFlexLentry,
        singleLateConstDyadicFlexLexit,
        singleLateConstDyadicFlexS]
      omega
    have haLo : Alo + R = Lentry := by
      dsimp only [Alo, Lentry, singleLateConstDyadicFlexAlo,
        singleLateConstDyadicFlexLentry]
      omega
    have hhi : Lexit + 6 * R = Hi := by
      dsimp only [Hi, Lexit, singleLateConstDyadicFlexHi,
        singleLateConstDyadicFlexLexit]
    have hgap : n + R + d = Alo + 1 := by
      dsimp only [d, Alo, Lentry, singleLateConstDyadicFlexD,
        singleLateConstDyadicFlexAlo, singleLateConstDyadicFlexLentry]
      omega
    have hLn : n + 1 <= Lexit := by
      dsimp only [Lexit, E, singleLateConstDyadicFlexLexit,
        singleLateConstDyadicFlexExit]
      omega
    have hguard : n + 1 <= d + 2 * Qbase + 2 * R := by
      dsimp only [d, singleLateConstDyadicFlexD]
      omega
    have hcoClock : Hi + 2 * singleLateConstM R +
          2 * singleLateConstCoFloor R <= 2 * n + 1 := by
      dsimp only [Hi, Lexit, E, singleLateConstDyadicFlexHi,
        singleLateConstDyadicFlexLexit, singleLateConstDyadicFlexExit,
        singleLateConstM, singleLateConstCoFloor]
      omega
    have hprodRoom : d + 2 * singleLateConstCoFloor R <= n := by
      dsimp only [d, singleLateConstDyadicFlexD,
        singleLateConstCoFloor]
      omega
    have hRetRoomFirst :
        singleLateConstSret R + 1 <= 96 * (E + 1) := by
      dsimp only [E, singleLateConstDyadicFlexExit,
        singleLateConstSret]
      omega
    exact singleLate_const_subrung_flex n Qbase P E R S Lentry Lexit
      Alo Hi d hn hR hQbasePos hQbaseDir hRupperFirst hguard hentry
      hexit hSpos hstep haLo hhi hgap hLn hcoClock hprodRoom
      (singleLateConstRetEps_le_one hRetRoomFirst)
  have hstage := by
    refine singleLate_const_stage32_symbolic n Q R
      (singleLateConstCap32 Q R) (singleLateConstLentry32 L0 R)
      (singleLateConstLexit32 L0 R) (singleLateConstALo32 A0 R)
      (singleLateConstHi32 L0 R) (singleLateConstD32 d0 R)
      hn hR hQpos hQsmall hRupper ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro i hi
      have hidx := singleLateConstIdx32_of_lt hi
      simp [singleLateConstD32, hidx, singleLateConstStageLength] at *
      dsimp only [d0, R, singleLateConstDyadicD0,
        singleLateConstDyadicR]
      omega
    · intro i hi
      have hidx := singleLateConstIdx32_of_lt hi
      have hrem : singleLateConstRem32 i = 32 - i := by
        unfold singleLateConstRem32
        simp [hidx, singleLateConstStageLength]
      have hmul : i * R + (32 - i) * R = 32 * R := by
        rw [← Nat.add_mul]
        have hsum : i + (32 - i) = 32 := by
          unfold singleLateConstStageLength at hi
          omega
        rw [hsum]
      simp [singleLateConstLentry32, singleLateConstCap32,
        hidx, hrem]
      omega
    · intro i hi
      have hidx := singleLateConstIdx32_of_lt hi
      have hidxs := singleLateConstIdx32_succ_of_lt hi
      have hremS : singleLateConstRem32 (i + 1) = 31 - i := by
        unfold singleLateConstRem32
        simp [hidxs, singleLateConstStageLength]
      have hmul : (i + 1) * R + (31 - i) * R = 32 * R := by
        rw [← Nat.add_mul]
        have hsum : i + 1 + (31 - i) = 32 := by
          unfold singleLateConstStageLength at hi
          omega
        rw [hsum]
      simp [singleLateConstLexit32, singleLateConstCap32,
        hidx, hremS]
      omega
    · intro i hi
      have hidx := singleLateConstIdx32_of_lt hi
      simp [singleLateConstLentry32, singleLateConstLexit32, hidx]
      ring
    · intro i hi
      have hidx := singleLateConstIdx32_of_lt hi
      simp [singleLateConstALo32, singleLateConstLentry32, hidx]
      omega
    · intro i hi
      have hidx := singleLateConstIdx32_of_lt hi
      simp [singleLateConstLexit32, singleLateConstHi32, hidx]
      ring
    · intro i hi
      have hidx := singleLateConstIdx32_of_lt hi
      simp [singleLateConstD32, singleLateConstALo32, hidx]
      omega
    · intro i hi
      have hidx := singleLateConstIdx32_of_lt hi
      simp [singleLateConstLexit32, hidx]
      omega
    · intro i hi
      have hidx := singleLateConstIdx32_of_lt hi
      simp [singleLateConstHi32, singleLateConstM, singleLateConstCoFloor,
        hidx]
      have hi31 : i <= 31 := by
        unfold singleLateConstStageLength at hi
        omega
      nlinarith
    · intro i hi
      have hidx := singleLateConstIdx32_of_lt hi
      have hi31 : i <= 31 := by
        unfold singleLateConstStageLength at hi
        omega
      have hcalc :
          singleLateConstD32 d0 R i + 2 * singleLateConstCoFloor R =
            d0 + (i + 10) * R := by
        simp [singleLateConstD32, singleLateConstCoFloor, hidx]
        ring
      rw [hcalc]
      have hi41 : i + 10 <= 41 := by omega
      exact le_trans
        (Nat.add_le_add_left (Nat.mul_le_mul_right R hi41) d0)
        hprodRoom0
    · intro i hi
      apply singleLateConstRetEps_le_one
      have hidxs := singleLateConstIdx32_succ_of_lt hi
      have hremS : singleLateConstRem32 (i + 1) = 31 - i := by
        unfold singleLateConstRem32
        simp [hidxs, singleLateConstStageLength]
      simp [singleLateConstCap32, hremS]
      omega
  have hstageExact :
      Reaches (singleStateStep n hn) (singleLateConstStageHorizon n)
        (SingleLateCheckpoint n (singleLateConstDyadicStartCap Q))
        (SingleLateCheckpoint n Q)
        (singleLateConstStageError n Q (singleLateConstDyadicR Q)
          (singleLateConstCap32 Q (singleLateConstDyadicR Q))
          (singleLateConstLentry32 (singleLateConstDyadicL0 n Q)
            (singleLateConstDyadicR Q))
          (singleLateConstLexit32 (singleLateConstDyadicL0 n Q)
            (singleLateConstDyadicR Q))
          (singleLateConstHi32 (singleLateConstDyadicL0 n Q)
            (singleLateConstDyadicR Q))
          (singleLateConstD32 (singleLateConstDyadicD0 n Q)
            (singleLateConstDyadicR Q))) := by
    simpa [R, L0, A0, d0, singleLateConstCap32,
      singleLateConstRem32, singleLateConstIdx32,
      singleLateConstStageLength, singleLateConstDyadicStartCap,
      singleLateConstStageError] using hstage
  have htail :
      Reaches (singleStateStep n hn) (singleLateConstStageHorizon n)
        (SingleLateCheckpoint n E)
        (SingleLateCheckpoint n Q)
        (singleLateConstStageError n Q (singleLateConstDyadicR Q)
          (singleLateConstCap32 Q (singleLateConstDyadicR Q))
          (singleLateConstLentry32 (singleLateConstDyadicL0 n Q)
            (singleLateConstDyadicR Q))
          (singleLateConstLexit32 (singleLateConstDyadicL0 n Q)
            (singleLateConstDyadicR Q))
          (singleLateConstHi32 (singleLateConstDyadicL0 n Q)
            (singleLateConstDyadicR Q))
          (singleLateConstD32 (singleLateConstDyadicD0 n Q)
            (singleLateConstDyadicR Q))) := by
    intro s hs
    exact hstageExact s (by
      unfold SingleLateCheckpoint at hs ⊢
      omega)
  have hcomp := hfirst.comp htail
  simpa [singleLateConstRelaxedStageHorizon,
    singleLateConstRelaxedStageError, singleLateConstDyadicFlexError,
    R, E, S, Qbase, Lentry, Lexit, Alo, Hi, d]
    using hcomp

/-- Every selected exact constant-base late stage has the side conditions
required by `singleLate_const_dyadic_stage`. -/
theorem singleLate_const_dyadic_stage_from_schedule
    (n gamma i : Nat) (hn : 2 <= n)
    (hlog : 1024 <= Nat.log 2 n) (hgamma : 1 <= gamma)
    (hi : i < singleLateConstDyadicStages n gamma) :
    Reaches (singleStateStep n hn) (singleLateConstRelaxedStageHorizon n)
      (SingleLateCheckpoint n (singleLateConstDyadicCap n gamma i))
      (SingleLateCheckpoint n (singleLateConstDyadicCap n gamma (i + 1)))
      (singleLateConstDyadicStepError n gamma i) := by
  let P := singleLateConstDyadicCap n gamma i
  let Q := phase2Scale n (3 + i)
  have hcapQ :
      singleLateConstDyadicCap n gamma (i + 1) = Q := by
    simp only [singleLateConstDyadicCap, Q]
    congr 1
    omega
  have hk : i + 1 < phase2StageCount n gamma := by
    unfold singleLateConstDyadicStages at hi
    omega
  have hmin := phase2StageCount_minimal (n := n) (γ := gamma) hk
  have hminQ : gamma * Nat.log 2 n < 2 * Q := by
    dsimp only [Q, phase2Scale]
    simpa [show 2 + (i + 1) = 3 + i by omega] using hmin
  have hminQ' : gamma * Nat.log 2 n < 2 * (n / 2 ^ (3 + i)) := by
    simpa [Q, phase2Scale] using hminQ
  have hlogGamma : 1024 <= gamma * Nat.log 2 n := by
    calc
      1024 = 1 * 1024 := by norm_num
      _ <= gamma * Nat.log 2 n := Nat.mul_le_mul hgamma hlog
  have hQ : 512 <= Q := by
    dsimp only [Q, phase2Scale]
    omega
  have hQsmall : 8 * Q <= n := by
    dsimp only [Q, phase2Scale]
    have hden : 8 <= 2 ^ (3 + i) := by
      calc
        8 = 2 ^ 3 := by norm_num
        _ <= 2 ^ (3 + i) :=
          Nat.pow_le_pow_right (by norm_num : 1 <= 2) (by omega)
    have hmul : 2 ^ (3 + i) * (n / 2 ^ (3 + i)) <= n := by
      rw [Nat.mul_comm]
      exact Nat.div_mul_le_self n (2 ^ (3 + i))
    exact (Nat.mul_le_mul_right (n / 2 ^ (3 + i)) hden).trans hmul
  have hPscale :
      P = n / 2 ^ (2 + i) := by
    simp only [P, singleLateConstDyadicCap, phase2Scale]
  have hQscale :
      Q = n / 2 ^ (3 + i) := by
    rfl
  have hdenSucc :
      2 ^ (3 + i) = 2 * 2 ^ (2 + i) := by
    rw [show 3 + i = (2 + i) + 1 by omega, pow_succ]
    ring
  have hPlo : 2 * Q <= P := by
    rw [hPscale, hQscale, hdenSucc]
    set a := 2 ^ (2 + i)
    rw [Nat.le_div_iff_mul_le (by positivity : 0 < a)]
    calc
      (2 * (n / (2 * a))) * a = (n / (2 * a)) * (2 * a) := by ring
      _ <= n := Nat.div_mul_le_self n (2 * a)
  have hPhi : P <= 2 * Q + 1 := by
    rw [hPscale, hQscale, hdenSucc]
    let a := 2 ^ (2 + i)
    have ha : 0 < a := by dsimp only [a]; positivity
    change n / a <= 2 * (n / (2 * a)) + 1
    have hdiv := Nat.div_add_mod n (2 * a)
    have hmod := Nat.mod_lt n (by positivity : 0 < 2 * a)
    have hlt :
        n < a * (2 * (n / (2 * a)) + 2) := by
      calc
        n = 2 * a * (n / (2 * a)) + n % (2 * a) := by
          exact hdiv.symm
        _ = 2 * a * (n / (2 * a)) + n % (2 * a) := by ring
        _ < 2 * a * (n / (2 * a)) + 2 * a :=
          Nat.add_lt_add_left hmod _
        _ = a * (2 * (n / (2 * a)) + 2) := by ring
    have hlt' :
        n < (2 * (n / (2 * a)) + 2) * a := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlt
    have hdivlt :
        n / a < 2 * (n / (2 * a)) + 2 :=
      (@Nat.div_lt_iff_lt_mul a n (2 * (n / (2 * a)) + 2) ha).mpr hlt'
    omega
  have hstage := singleLate_const_dyadic_stage n
    (singleLateConstDyadicCap n gamma i) Q hn hPlo hPhi hQ hQsmall
  simpa [singleLateConstDyadicStepError, hcapQ, Q, P] using hstage

/-- The exact constant-base late ladder from the high-cap bridge exit
`n/4` down to the existing public Single-B late target cap. -/
theorem singleLate_const_dyadic_ladder
    (n gamma : Nat) (hn : 2 <= n)
    (hlog : 1024 <= Nat.log 2 n) (hgamma : 1 <= gamma)
    (hsize : 6 * gamma * Nat.log 2 n <= n) :
    Reaches (singleStateStep n hn)
      (singleLateConstDyadicLadderHorizon n gamma)
      (SingleLateCheckpoint n (n / 4))
      (SingleLateCheckpoint n (singleLateTargetCap n gamma))
      (singleLateConstDyadicLadderError n gamma) := by
  have htwo := singleLate_phase2StageCount_two_le n gamma hlog hgamma hsize
  let Pstage : Nat -> SingleState n -> Prop :=
    fun i => SingleLateCheckpoint n (singleLateConstDyadicCap n gamma i)
  let T : Nat -> Nat := fun _ => singleLateConstRelaxedStageHorizon n
  let eps : Nat -> ENNReal := fun i => singleLateConstDyadicStepError n gamma i
  have hrungs : forall i, i < singleLateConstDyadicStages n gamma ->
      Reaches (singleStateStep n hn) (T i) (Pstage i) (Pstage (i + 1))
        (eps i) := by
    intro i hi
    have hcapQ :
        singleLateConstDyadicCap n gamma (i + 1) =
          phase2Scale n (3 + i) := by
      simp only [singleLateConstDyadicCap]
      congr 1
      omega
    simpa only [Pstage, T, eps] using
      singleLate_const_dyadic_stage_from_schedule n gamma i hn hlog hgamma
        hi
  have hchain :=
    Reaches.chain (K := singleStateStep n hn) (P := Pstage)
      (T := T) (ε := eps) hrungs
  have hTsum :
      (∑ i ∈ Finset.range (singleLateConstDyadicStages n gamma), T i) =
        singleLateConstDyadicLadderHorizon n gamma := by
    simp only [T, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rfl
  rw [hTsum] at hchain
  have hstart :
      singleLateConstDyadicCap n gamma 0 = n / 4 := by
    norm_num [singleLateConstDyadicCap, phase2Scale]
  have htarget :
      singleLateConstDyadicCap n gamma
          (singleLateConstDyadicStages n gamma) =
        singleLateTargetCap n gamma := by
    have hne : ¬ singleLateDyadicStages n gamma = 0 := by
      unfold singleLateDyadicStages
      omega
    have hidx1 :
        2 + (phase2StageCount n gamma - 2) =
          phase2StageCount n gamma := by omega
    have hidx2 :
        1 + singleLateDyadicStages n gamma =
          phase2StageCount n gamma := by
      unfold singleLateDyadicStages
      omega
    simp [singleLateConstDyadicCap, singleLateConstDyadicStages,
      singleLateTargetCap, singleLateDyadicCap, hne, hidx1, hidx2]
  simpa [Pstage, eps, singleLateConstDyadicLadderError,
    singleLateConstDyadicLadderHorizon, hstart, htarget] using hchain

section Inhabitation

example : singleLateConstSubHorizon 10 = 240 := by
  rfl

example : singleLateConstH 64 2 = 155 := by
  norm_num [singleLateConstH, singleLateConstMhi]

example : singleLateConstStageLength = 32 := by
  rfl

example : singleLateConstStageHorizon 10 = 7680 := by
  norm_num [singleLateConstStageHorizon, singleLateConstStageLength,
    singleLateConstSubHorizon]

example : singleLateConstIdx32 40 = 32 := by
  norm_num [singleLateConstIdx32, singleLateConstStageLength]

example : singleLateConstRem32 0 = 32 := by
  norm_num [singleLateConstRem32, singleLateConstIdx32,
    singleLateConstStageLength]

example :
    Reaches (singleStateStep 256 (by norm_num)) (singleLateConstSubHorizon 256)
      (SingleLateCheckpoint 256 64)
      (SingleLateCheckpoint 256 63)
      (singleLateConstSubRungError 256 32 64 63 1 448 449 455 191) := by
  exact singleLate_const_subrung 256 32 64 63 1 448 449 447 455 191
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by norm_num [singleLateConstM, singleLateConstCoFloor])
    (by norm_num [singleLateConstCoFloor])
    (by
      unfold singleLateConstRetEps singleLateConstSret
      rw [show (1 : ENNReal) = ENNReal.ofReal (1 : Real) by
        exact ENNReal.ofReal_one.symm]
      apply ENNReal.ofReal_le_ofReal
      norm_num)

end Inhabitation

end Tri

#print axioms Tri.singleLateConstSubHorizon
#print axioms Tri.singleLateConstM
#print axioms Tri.singleLateConstMhi
#print axioms Tri.singleLateConstSret
#print axioms Tri.singleLateConstCoFloor
#print axioms Tri.singleLateConstH
#print axioms Tri.singleLateConstK
#print axioms Tri.singleLateConstRetEps
#print axioms Tri.singleLateConstRetEps_le_one
#print axioms Tri.singleLateConstSubRungError
#print axioms Tri.singleLate_const_subrung_flex
#print axioms Tri.singleLate_const_subrung
#print axioms Tri.singleLateConstStageLength
#print axioms Tri.singleLateConstStageHorizon
#print axioms Tri.singleLateConstStageError
#print axioms Tri.singleLate_const_stage32_symbolic
#print axioms Tri.singleLateConstIdx32
#print axioms Tri.singleLateConstRem32
#print axioms Tri.singleLateConstCap32
#print axioms Tri.singleLateConstLentry32
#print axioms Tri.singleLateConstLexit32
#print axioms Tri.singleLateConstALo32
#print axioms Tri.singleLateConstHi32
#print axioms Tri.singleLateConstD32
#print axioms Tri.singleLateConstIdx32_of_lt
#print axioms Tri.singleLateConstIdx32_succ_of_lt
#print axioms Tri.singleLate_const_stage32_concrete
#print axioms Tri.singleLateConstDyadicR
#print axioms Tri.singleLateConstDyadicStartCap
#print axioms Tri.singleLateConstDyadicFlexExit
#print axioms Tri.singleLateConstDyadicFlexS
#print axioms Tri.singleLateConstDyadicFlexQbase
#print axioms Tri.singleLateConstDyadicFlexLentry
#print axioms Tri.singleLateConstDyadicFlexLexit
#print axioms Tri.singleLateConstDyadicFlexAlo
#print axioms Tri.singleLateConstDyadicFlexHi
#print axioms Tri.singleLateConstDyadicFlexD
#print axioms Tri.singleLateConstDyadicFlexError
#print axioms Tri.singleLateConstDyadicL0
#print axioms Tri.singleLateConstDyadicA0
#print axioms Tri.singleLateConstDyadicD0
#print axioms Tri.singleLateConstDyadicStages
#print axioms Tri.singleLateConstDyadicCap
#print axioms Tri.singleLateConstRelaxedStageHorizon
#print axioms Tri.singleLateConstRelaxedStageError
#print axioms Tri.singleLateConstDyadicStepError
#print axioms Tri.singleLateConstDyadicLadderHorizon
#print axioms Tri.singleLateConstDyadicLadderError
#print axioms Tri.singleLateConstDyadicR_upper
#print axioms Tri.singleLateConstDyadic_coRoom
#print axioms Tri.singleLateConstDyadic_prodRoom
#print axioms Tri.singleLateConstDyadic_retRoom
#print axioms Tri.singleLateConstDyadic_fit
#print axioms Tri.singleLate_phase2StageCount_two_le
#print axioms Tri.singleLate_const_dyadic_stage
#print axioms Tri.singleLate_const_dyadic_stage_from_schedule
#print axioms Tri.singleLate_const_dyadic_ladder
