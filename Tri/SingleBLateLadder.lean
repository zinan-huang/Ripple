/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBMiddleConstants
import Tri.SingleBLateRung
import Tri.SingleBClockRung
import Tri.Phase2Additive
import Mathlib.Tactic.IntervalCases

/-!
# Single-B late co-level ladder

The public late checkpoints are additive co-level caps:
`2*n <= level + P`.  This avoids exposing truncated natural subtraction in
the theorem interface.  The first bridge converts the middle physical gap
checkpoint into the late entry co-cap.
-/

namespace Tri

open scoped ENNReal

/-- Public Single-B late checkpoint: the doubled co-level is at most `P`,
written additively through `doubleLevel + doubleCoLevel = 2*n`. -/
def SingleLateCheckpoint (n P : Nat) (s : SingleState n) : Prop :=
  2 * n <= s.1.doubleLevel + P

instance (n P : Nat) : DecidablePred (SingleLateCheckpoint n P) := fun _ =>
  inferInstanceAs (Decidable (_ <= _))

/-- Entry co-cap after the fixed-unit middle extension. -/
def singleLateEntryCoCap (n : Nat) : Nat := 5 * n / 8

/-- Fixed raw horizon for one structural late subrung. -/
def singleLateSubHorizon (n : Nat) : Nat := 65536 * n

/-- Number of subrungs in one late dyadic stage. -/
def singleLateStageLength : Nat := 16

/-- Horizon of one 16-subrung late stage. -/
def singleLateStageHorizon (n : Nat) : Nat :=
  singleLateStageLength * singleLateSubHorizon n

/-- Constant co-return tilt used by the late subrung wrapper. -/
noncomputable def singleLateRetEps : ENNReal :=
  ENNReal.ofReal ((1 : Real) / 1300)

/-- The middle gap `98332 * (n / 2^18)` already implies the late entry
additive co-cap once `n` is large enough for the floor losses. -/
theorem singleMiddleGap_plus_lateEntryCoCap
    {n : Nat} (hlog : 30 <= Nat.log 2 n) :
    n <=
      (132 * singleMiddleUnit n + singleMiddleRungs * singleMiddleUnit n) +
        singleLateEntryCoCap n := by
  unfold singleMiddleUnit singleMiddleRungs singleMiddleBootstrapRungs
    singleMiddleMainRungs singleLateEntryCoCap
  have hdiv := Nat.div_add_mod n 262144
  have hmod := Nat.mod_lt n (by norm_num : 0 < 262144)
  have hdiv8 := Nat.div_add_mod (5 * n) 8
  have hmod8 := Nat.mod_lt (5 * n) (by norm_num : 0 < 8)
  have huLarge : 3511 <= n / 262144 := by
    have hnLarge : 3511 * 262144 <= n := by
      calc
        3511 * 262144 <= 2 ^ 30 := by norm_num
        _ <= 2 ^ Nat.log 2 n :=
          Nat.pow_le_pow_right (by norm_num) hlog
        _ <= n := Nat.pow_log_le_self 2 (by
          intro h0
          rw [h0, Nat.log_zero_right] at hlog
          omega)
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 262144)).2 hnLarge
  omega

/-- Middle checkpoint exported as the additive late entry checkpoint. -/
theorem singleMiddleCheckpoint_to_lateEntry
    {n : Nat} (hlog : 30 <= Nat.log 2 n) (s : SingleState n)
    (hs : SingleMiddleCheckpoint n s) :
    SingleLateCheckpoint n (singleLateEntryCoCap n) s := by
  unfold SingleMiddleCheckpoint SingleGapCheckpoint at hs
  unfold SingleLateCheckpoint
  have hcap := singleMiddleGap_plus_lateEntryCoCap (n := n) hlog
  omega

/-- The middle extension lands directly at the additive late-ladder entry. -/
theorem singleMiddle_reaches_lateEntry
    (n : Nat) (hn : 2 <= n) (hlog : 30 <= Nat.log 2 n) :
    Reaches (singleStateStep n hn) (singleMiddleHorizon n)
      (SingleEarlyTarget n)
      (SingleLateCheckpoint n (singleLateEntryCoCap n))
      (singleMiddleError n) := by
  exact (singleMiddle_reaches n hn hlog).mono_post
    (singleMiddleCheckpoint_to_lateEntry (n := n) hlog)

/-- A direct productivity-floor probability bound from the elementary
`d + 2*c <= n` room inequality. -/
theorem singleBandProductivity_le_one_of_sum
    (n : Nat) (hn : 2 <= n) (d c : Nat)
    (hdc : d + 2 * c <= n) :
    singleBandProductivity n d c <= 1 := by
  have hS : ((d : Real) + 2 * (c : Real)) <= (n : Real) := by
    exact_mod_cast hdc
  have hSnonneg : 0 <= (d : Real) + 2 * (c : Real) := by positivity
  have hnnonneg : 0 <= (n : Real) := by positivity
  have hSsq : ((d : Real) + 2 * (c : Real)) ^ 2 <= (n : Real) ^ 2 := by
    rw [sq_le_sq]
    rw [abs_of_nonneg hSnonneg, abs_of_nonneg hnnonneg]
    exact hS
  have h8 : 8 * (d : Real) * (c : Real)
      <= ((d : Real) + 2 * (c : Real)) ^ 2 := by
    nlinarith [sq_nonneg ((d : Real) - 2 * (c : Real))]
  have hn4 : (n : Real) ^ 2 <= 4 * (n : Real) * ((n : Real) - 1) := by
    have hnR : (2 : Real) <= n := by exact_mod_cast hn
    nlinarith
  have hmulR : 2 * (d : Real) * (c : Real)
      <= (n : Real) * ((n : Real) - 1) := by
    nlinarith
  have hmulR' : ((2 * (d * c) : Nat) : Real)
      <= ((n * (n - 1) : Nat) : Real) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_mul,
      Nat.cast_sub (by omega : 1 <= n), Nat.cast_one]
    simpa [mul_assoc] using hmulR
  have hmul2 : 2 * (d * c) <= n * (n - 1) := by
    exact_mod_cast hmulR'
  have hchoose : 2 * Nat.choose n 2 = n * (n - 1) := by
    have h := two_mul_choose_two_succ (n - 1)
    simpa only [Nat.sub_add_cancel (by omega : 1 <= n)] using h
  have hmul : d * c <= Nat.choose n 2 := by omega
  have hden0 : ((Nat.choose n 2 : Nat) : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hn).ne'
  have hdenT : ((Nat.choose n 2 : Nat) : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  calc
    singleBandProductivity n d c
        <= ((Nat.choose n 2 : Nat) : ENNReal) /
          ((Nat.choose n 2 : Nat) : ENNReal) := by
      unfold singleBandProductivity
      exact ENNReal.div_le_div_right (by exact_mod_cast hmul) _
    _ = 1 := ENNReal.div_self hden0 hdenT

/-- Additive-checkpoint form of a structural late rung.  The caller supplies
the arithmetic identifying `Lentry` with co-cap `P` and making `Lexit` strong
enough for co-cap `Q`; all analytic side conditions remain those of
`singleLate_rung_resolved`. -/
theorem singleLate_rung_checkpoint
    {n : Nat} (hn : 2 <= n)
    (P Q aLoΛ hiΛ D D₂ H p qRat Bw M K T Lentry Lexit sret Bret
      Lhi Mhi d c : Nat)
    (hentry : Lentry + P = 2 * n)
    (hexit : 2 * n <= Lexit + Q)
    (hH : 0 < H) (hq : qRat ≠ 0)
    (w v η u epsRet : ENNReal) (hε1 : epsRet <= 1)
    (hu : u = (p : ENNReal) / (qRat : ENNReal))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w <= η)
    (hwv : w * v = 1) (hw1 : w <= 1) (hw0 : w ≠ 0)
    (hη1 : 1 <= η) (hwt : w ≠ ⊤) (hηt : η ≠ ⊤)
    (hlive : forall q : SingleLedger n,
      ¬ SingleBandFrozen n aLoΛ hiΛ D H q ->
        exists a : Nat, q.CorrectedLevel (a + 1) ∧
          qRat * q.cfg.1.y <= p * q.cfg.1.x)
    (hBw : aLoΛ + Bw = Lentry)
    (hvac : aLoΛ + D₂ <= Lexit)
    (hLn : n + 1 <= Lexit)
    (hBret : Lexit + Bret = 2 * n + 1)
    (hslack : Lexit + sret + D <= hiΛ)
    (hLhiReturn : Lexit + sret + D <= Lhi)
    (htargetHi : Lexit + D + 1 <= hiΛ)
    (hK : H + M <= K)
    (hgap : n + D + d = aLoΛ + 1)
    (hcoClock : hiΛ + 2 * M + 2 * c <= 2 * n + 1)
    (hpp1 : singleBandProductivity n d c <= 1)
    (hboundaryH : P + 2 * Mhi + D + 1 <= H) :
    Reaches (singleStateStep n hn) T
      (SingleLateCheckpoint n P)
      (SingleLateCheckpoint n Q)
      (singleLateRungError n d c D D₂ H M K T w η Bw Lentry
        (Lexit + D) Lhi Mhi Bret sret epsRet) := by
  have hr := singleLate_rung_resolved hn aLoΛ hiΛ D D₂ H p qRat Bw M K T
    Lentry Lexit sret Bret Lhi Mhi P d c hH hq w v η u epsRet hε1
    hu hrel hwη hwv hw1 hw0 hη1 hwt hηt hlive hBw hvac hLn hBret
    hslack hLhiReturn htargetHi hK hgap hcoClock hpp1 ?_ hboundaryH
  · have hrpre :
        Reaches (singleStateStep n hn) T
          (SingleLateCheckpoint n P)
          (fun s : SingleState n => Lexit <= s.1.doubleLevel)
          (singleLateRungError n d c D D₂ H M K T w η Bw Lentry
            (Lexit + D) Lhi Mhi Bret sret epsRet) := by
      intro s hs
      unfold SingleLateCheckpoint at hs
      exact hr s (by omega)
    exact hrpre.mono_post (by
      intro s hs
      unfold SingleLateCheckpoint
      omega)
  · intro s hs
    have hadd := doubleLevel_add_doubleCoLevel s
    omega

/-- Explicit error of one additive-witness late subrung. -/
noncomputable def singleLateSubRungError
    (n P Q R Lentry Lexit hiΛ d : Nat) : ENNReal :=
  singleLateRungError n d (4 * R) R R (P + 5 * R + 1) (2 * R)
    (P + 7 * R + 1) (singleLateSubHorizon n)
    (singleRungDirW n d) (singleRungDirEta n d) R Lentry
    (Lexit + R) hiΛ (2 * R) (Q + 1) R singleLateRetEps

/-- One concrete structural late subrung, stated only with additive witnesses.
The rung lowers the public co-cap from `P` to `Q`; the caller supplies the
level witnesses that identify the physical band endpoints without exposing
natural subtraction. -/
theorem singleLate_subrung
    (n P Q R Lentry Lexit aLoΛ hiΛ d : Nat) (hn : 2 <= n)
    (hR : 0 < R) (hdpos : 0 < d)
    (hentry : Lentry + P = 2 * n)
    (hexit : Lexit + Q = 2 * n)
    (hstep : Lentry + R = Lexit)
    (haLo : aLoΛ + R = Lentry)
    (hhi : Lexit + 2 * R = hiΛ)
    (hgap : n + R + d = aLoΛ + 1)
    (hLn : n + 1 <= Lexit)
    (hcoRoom : 15 * R <= P + 1)
    (hprodRoom : d + 8 * R <= n) :
    Reaches (singleStateStep n hn) (singleLateSubHorizon n)
      (SingleLateCheckpoint n P)
      (SingleLateCheckpoint n Q)
      (singleLateSubRungError n P Q R Lentry Lexit hiΛ d) := by
  have hn0 : 0 < n := by omega
  obtain ⟨hrel, hwη, hη1, hηt, hw1, hw0, hwt, hwv⟩ :=
    singleRungDir_params n d hn0 hdpos
  have hε1 : singleLateRetEps <= 1 := by
    unfold singleLateRetEps
    rw [show (1 : ENNReal) = ENNReal.ofReal (1 : Real) by
      exact ENNReal.ofReal_one.symm]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hq : n + d ≠ 0 := by omega
  have hpp1 : singleBandProductivity n d (4 * R) <= 1 := by
    apply singleBandProductivity_le_one_of_sum n hn d (4 * R)
    omega
  have hreach := singleLate_rung_checkpoint hn P Q aLoΛ hiΛ R R
    (P + 5 * R + 1) n (n + d) R (2 * R) (P + 7 * R + 1)
    (singleLateSubHorizon n) Lentry Lexit R (Q + 1) hiΛ (2 * R) d
    (4 * R)
    hentry (by rw [hexit]) (by omega) hq
    (singleRungDirW n d) (singleRungDirV n d) (singleRungDirEta n d)
    (singleRungDirU n d) singleLateRetEps hε1
    rfl hrel hwη hwv hw1 hw0 hη1 hwt hηt
    (singleBand_hlive_ratio (n := n) (aLoΛ := aLoΛ) (hiΛ := hiΛ)
      (D := R) (H := P + 5 * R + 1) (g := d) (by omega))
    haLo
    (by omega)
    hLn
    (by omega)
    (by omega)
    (by omega)
    (by omega)
    (by omega)
    hgap
    (by omega)
    hpp1
    (by omega)
  simpa [singleLateSubRungError] using hreach

/-- Error of a symbolic 16-subrung late stage.  The witness functions are
kept explicit so that no truncated natural subtraction is hidden in the public
stage statement. -/
noncomputable def singleLateStageError
    (n R : Nat) (Cap Lentry Lexit hiΛ d : Nat -> Nat) : ENNReal :=
  ∑ i ∈ Finset.range singleLateStageLength,
    singleLateSubRungError n (Cap i) (Cap (i + 1)) R
      (Lentry i) (Lexit i) (hiΛ i) (d i)

/-- Symbolic composition of sixteen late subrungs.  All endpoint arithmetic is
provided by additive witnesses, keeping the stage theorem subtraction-free. -/
theorem singleLate_stage16_symbolic
    (n R : Nat)
    (Cap Lentry Lexit aLoΛ hiΛ d : Nat -> Nat)
    (hn : 2 <= n)
    (hR : 0 < R)
    (hdpos : forall i, i < singleLateStageLength -> 0 < d i)
    (hentry : forall i, i < singleLateStageLength ->
      Lentry i + Cap i = 2 * n)
    (hexit : forall i, i < singleLateStageLength ->
      Lexit i + Cap (i + 1) = 2 * n)
    (hstep : forall i, i < singleLateStageLength ->
      Lentry i + R = Lexit i)
    (haLo : forall i, i < singleLateStageLength ->
      aLoΛ i + R = Lentry i)
    (hhi : forall i, i < singleLateStageLength ->
      Lexit i + 2 * R = hiΛ i)
    (hgap : forall i, i < singleLateStageLength ->
      n + R + d i = aLoΛ i + 1)
    (hLn : forall i, i < singleLateStageLength ->
      n + 1 <= Lexit i)
    (hcoRoom : forall i, i < singleLateStageLength ->
      15 * R <= Cap i + 1)
    (hprodRoom : forall i, i < singleLateStageLength ->
      d i + 8 * R <= n) :
    Reaches (singleStateStep n hn) (singleLateStageHorizon n)
      (SingleLateCheckpoint n (Cap 0))
      (SingleLateCheckpoint n (Cap singleLateStageLength))
      (singleLateStageError n R Cap Lentry Lexit hiΛ d) := by
  let Pstage : Nat -> SingleState n -> Prop :=
    fun i => SingleLateCheckpoint n (Cap i)
  let T : Nat -> Nat := fun _ => singleLateSubHorizon n
  let ε : Nat -> ENNReal := fun i =>
    singleLateSubRungError n (Cap i) (Cap (i + 1)) R
      (Lentry i) (Lexit i) (hiΛ i) (d i)
  have hrungs : forall i, i < singleLateStageLength ->
      Reaches (singleStateStep n hn) (T i) (Pstage i) (Pstage (i + 1))
        (ε i) := by
    intro i hi
    exact singleLate_subrung n (Cap i) (Cap (i + 1)) R
      (Lentry i) (Lexit i) (aLoΛ i) (hiΛ i) (d i) hn hR
      (hdpos i hi) (hentry i hi) (hexit i hi) (hstep i hi)
      (haLo i hi) (hhi i hi) (hgap i hi) (hLn i hi)
      (hcoRoom i hi) (hprodRoom i hi)
  have hchain :=
    Reaches.chain (K := singleStateStep n hn) (P := Pstage)
      (T := T) (ε := ε) (k := singleLateStageLength) hrungs
  have hTsum :
      (∑ i ∈ Finset.range singleLateStageLength, T i) =
        singleLateStageHorizon n := by
    simp [T, singleLateStageHorizon, singleLateStageLength]
  rw [hTsum] at hchain
  simpa [Pstage, ε, singleLateStageError] using hchain

/-- Start/end form of the symbolic 16-subrung late stage. -/
theorem singleLate_stage16_witnessed
    (n P Q R : Nat)
    (Cap Lentry Lexit aLoΛ hiΛ d : Nat -> Nat)
    (hn : 2 <= n)
    (hCap0 : Cap 0 = P)
    (hCapEnd : Cap singleLateStageLength = Q)
    (hR : 0 < R)
    (hdpos : forall i, i < singleLateStageLength -> 0 < d i)
    (hentry : forall i, i < singleLateStageLength ->
      Lentry i + Cap i = 2 * n)
    (hexit : forall i, i < singleLateStageLength ->
      Lexit i + Cap (i + 1) = 2 * n)
    (hstep : forall i, i < singleLateStageLength ->
      Lentry i + R = Lexit i)
    (haLo : forall i, i < singleLateStageLength ->
      aLoΛ i + R = Lentry i)
    (hhi : forall i, i < singleLateStageLength ->
      Lexit i + 2 * R = hiΛ i)
    (hgap : forall i, i < singleLateStageLength ->
      n + R + d i = aLoΛ i + 1)
    (hLn : forall i, i < singleLateStageLength ->
      n + 1 <= Lexit i)
    (hcoRoom : forall i, i < singleLateStageLength ->
      15 * R <= Cap i + 1)
    (hprodRoom : forall i, i < singleLateStageLength ->
      d i + 8 * R <= n) :
    Reaches (singleStateStep n hn) (singleLateStageHorizon n)
      (SingleLateCheckpoint n P)
      (SingleLateCheckpoint n Q)
      (singleLateStageError n R Cap Lentry Lexit hiΛ d) := by
  have hstage := singleLate_stage16_symbolic n R Cap Lentry Lexit aLoΛ hiΛ d
    hn hR hdpos hentry hexit hstep haLo hhi hgap hLn hcoRoom hprodRoom
  simpa [hCap0, hCapEnd] using hstage

/-- Saturated index used by the concrete 16-subrung late stage. -/
def singleLateIdx16 : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | 9 => 9
  | 10 => 10
  | 11 => 11
  | 12 => 12
  | 13 => 13
  | 14 => 14
  | 15 => 15
  | _ => 16

/-- Remaining cap multiplier used by the concrete 16-subrung late stage. -/
def singleLateRem16 : Nat -> Nat
  | 0 => 16
  | 1 => 15
  | 2 => 14
  | 3 => 13
  | 4 => 12
  | 5 => 11
  | 6 => 10
  | 7 => 9
  | 8 => 8
  | 9 => 7
  | 10 => 6
  | 11 => 5
  | 12 => 4
  | 13 => 3
  | 14 => 2
  | 15 => 1
  | _ => 0

/-- Concrete cap schedule for one 16-subrung stage: `Q+16R` down to `Q`. -/
def singleLateCap16 (Q R i : Nat) : Nat :=
  Q + singleLateRem16 i * R

/-- Concrete entry-level witness schedule for one 16-subrung stage. -/
def singleLateLentry16 (L0 R i : Nat) : Nat :=
  L0 + singleLateIdx16 i * R

/-- Concrete exit-level witness schedule for one 16-subrung stage. -/
def singleLateLexit16 (L0 R i : Nat) : Nat :=
  L0 + (singleLateIdx16 i + 1) * R

/-- Concrete lower-band witness schedule for one 16-subrung stage. -/
def singleLateALo16 (A0 R i : Nat) : Nat :=
  A0 + singleLateIdx16 i * R

/-- Concrete high-band witness schedule for one 16-subrung stage. -/
def singleLateHi16 (L0 R i : Nat) : Nat :=
  L0 + (singleLateIdx16 i + 3) * R

/-- Concrete gap-floor witness schedule for one 16-subrung stage. -/
def singleLateD16 (d0 R i : Nat) : Nat :=
  d0 + singleLateIdx16 i * R

/-- Dyadic-stage quota, rounded up enough to cover floor losses. -/
def singleLateDyadicR (Q : Nat) : Nat := Q / 16 + 1

/-- Internal widened start cap for a dyadic stage ending at `Q`. -/
def singleLateDyadicStartCap (Q : Nat) : Nat :=
  Q + 16 * singleLateDyadicR Q

/-- Internal entry-level base for a dyadic stage ending at `Q`. -/
def singleLateDyadicL0 (n Q : Nat) : Nat :=
  2 * n - singleLateDyadicStartCap Q

/-- Internal lower-band base witness for a dyadic stage ending at `Q`. -/
def singleLateDyadicA0 (n Q : Nat) : Nat :=
  singleLateDyadicL0 n Q - singleLateDyadicR Q

/-- Internal productive gap base for a dyadic stage ending at `Q`. -/
def singleLateDyadicD0 (n Q : Nat) : Nat :=
  n - Q - 18 * singleLateDyadicR Q + 1

/-- First late target cap after the middle-to-late entry bridge. -/
def singleLateFirstCap (n : Nat) : Nat := 3 * n / 8

/-- Error of the first rounded dyadic stage from the middle-entry cap. -/
noncomputable def singleLateFirstError (n : Nat) : ENNReal :=
  singleLateStageError n (singleLateDyadicR (singleLateFirstCap n))
    (singleLateCap16 (singleLateFirstCap n)
      (singleLateDyadicR (singleLateFirstCap n)))
    (singleLateLentry16 (singleLateDyadicL0 n (singleLateFirstCap n))
      (singleLateDyadicR (singleLateFirstCap n)))
    (singleLateLexit16 (singleLateDyadicL0 n (singleLateFirstCap n))
      (singleLateDyadicR (singleLateFirstCap n)))
    (singleLateHi16 (singleLateDyadicL0 n (singleLateFirstCap n))
      (singleLateDyadicR (singleLateFirstCap n)))
    (singleLateD16 (singleLateDyadicD0 n (singleLateFirstCap n))
      (singleLateDyadicR (singleLateFirstCap n)))

/-- The rounded dyadic quota is small enough for the co-room side condition
once the target cap is at least `104`. -/
theorem singleLateDyadic_coRoom
    {Q : Nat} (hQ : 104 <= Q) :
    14 * singleLateDyadicR Q <= Q + 1 := by
  unfold singleLateDyadicR
  have hdiv := Nat.div_add_mod Q 16
  have hmod := Nat.mod_lt Q (by norm_num : 0 < 16)
  omega

/-- The rounded dyadic quota is small enough for the productivity-room side
condition. -/
theorem singleLateDyadic_prodRoom
    {Q : Nat} (hQ : 104 <= Q) :
    5 * singleLateDyadicR Q + 1 <= Q := by
  unfold singleLateDyadicR
  have hdiv := Nat.div_add_mod Q 16
  have hmod := Nat.mod_lt Q (by norm_num : 0 < 16)
  omega

/-- Concrete 16-subrung late stage.  The caller provides only the additive
base witnesses; the internal schedules are fixed finite tables, not natural
subtractions. -/
theorem singleLate_stage16_concrete
    (n Q R L0 A0 d0 : Nat) (hn : 2 <= n)
    (hR : 0 < R)
    (hd0 : 0 < d0)
    (hentry0 : L0 + (Q + 16 * R) = 2 * n)
    (ha0 : A0 + R = L0)
    (hgap0 : n + R + d0 = A0 + 1)
    (hLn0 : n + 1 <= L0 + R)
    (hcoRoom : 14 * R <= Q + 1)
    (hprodRoom : d0 + 23 * R <= n) :
    Reaches (singleStateStep n hn) (singleLateStageHorizon n)
      (SingleLateCheckpoint n (Q + 16 * R))
      (SingleLateCheckpoint n Q)
      (singleLateStageError n R
        (singleLateCap16 Q R) (singleLateLentry16 L0 R)
        (singleLateLexit16 L0 R) (singleLateHi16 L0 R)
        (singleLateD16 d0 R)) := by
  apply singleLate_stage16_witnessed n (Q + 16 * R) Q R
    (singleLateCap16 Q R) (singleLateLentry16 L0 R)
    (singleLateLexit16 L0 R) (singleLateALo16 A0 R)
    (singleLateHi16 L0 R) (singleLateD16 d0 R) hn
  · simp [singleLateCap16, singleLateRem16]
  · simp [singleLateStageLength, singleLateCap16, singleLateRem16]
  · exact hR
  · intro i hi
    have hi16 : i < 16 := by simpa [singleLateStageLength] using hi
    interval_cases i <;> simp [singleLateD16, singleLateIdx16] <;> omega
  · intro i hi
    have hi16 : i < 16 := by simpa [singleLateStageLength] using hi
    interval_cases i <;>
      simp [singleLateCap16, singleLateRem16, singleLateLentry16,
        singleLateIdx16] <;> omega
  · intro i hi
    have hi16 : i < 16 := by simpa [singleLateStageLength] using hi
    interval_cases i <;>
      simp [singleLateCap16, singleLateRem16, singleLateLexit16,
        singleLateIdx16] <;> omega
  · intro i hi
    have hi16 : i < 16 := by simpa [singleLateStageLength] using hi
    interval_cases i <;>
      simp [singleLateLentry16, singleLateLexit16, singleLateIdx16] <;>
      omega
  · intro i hi
    have hi16 : i < 16 := by simpa [singleLateStageLength] using hi
    interval_cases i <;>
      simp [singleLateALo16, singleLateLentry16, singleLateIdx16] <;>
      omega
  · intro i hi
    have hi16 : i < 16 := by simpa [singleLateStageLength] using hi
    interval_cases i <;>
      simp [singleLateLexit16, singleLateHi16, singleLateIdx16] <;> omega
  · intro i hi
    have hi16 : i < 16 := by simpa [singleLateStageLength] using hi
    interval_cases i <;>
      simp [singleLateALo16, singleLateD16, singleLateIdx16] <;> omega
  · intro i hi
    have hi16 : i < 16 := by simpa [singleLateStageLength] using hi
    interval_cases i <;>
      simp [singleLateLexit16, singleLateIdx16] <;> omega
  · intro i hi
    have hi16 : i < 16 := by simpa [singleLateStageLength] using hi
    interval_cases i <;>
      simp [singleLateCap16, singleLateRem16] <;> omega
  · intro i hi
    have hi16 : i < 16 := by simpa [singleLateStageLength] using hi
    interval_cases i <;>
      simp [singleLateD16, singleLateIdx16] <;> omega

/-- Concrete 16-subrung late stage with a possibly stronger public start cap.
This is the form used by dyadic floor arithmetic: the finite stage is built
for `Q+16R`, while the incoming checkpoint may have any smaller cap `P`. -/
theorem singleLate_stage16_concrete_of_start_le
    (n P Q R L0 A0 d0 : Nat) (hn : 2 <= n)
    (hP : P <= Q + 16 * R)
    (hR : 0 < R)
    (hd0 : 0 < d0)
    (hentry0 : L0 + (Q + 16 * R) = 2 * n)
    (ha0 : A0 + R = L0)
    (hgap0 : n + R + d0 = A0 + 1)
    (hLn0 : n + 1 <= L0 + R)
    (hcoRoom : 14 * R <= Q + 1)
    (hprodRoom : d0 + 23 * R <= n) :
    Reaches (singleStateStep n hn) (singleLateStageHorizon n)
      (SingleLateCheckpoint n P)
      (SingleLateCheckpoint n Q)
      (singleLateStageError n R
        (singleLateCap16 Q R) (singleLateLentry16 L0 R)
        (singleLateLexit16 L0 R) (singleLateHi16 L0 R)
        (singleLateD16 d0 R)) := by
  have hstage := singleLate_stage16_concrete n Q R L0 A0 d0 hn
    hR hd0 hentry0 ha0 hgap0 hLn0 hcoRoom hprodRoom
  intro s hs
  exact hstage s (by
    unfold SingleLateCheckpoint at hs ⊢
    omega)

/-- One rounded dyadic late stage.  The public start cap `P` may be any cap
that fits under the widened internal start cap for target `Q`; the fit
condition is additive and keeps the internal truncated witnesses honest. -/
theorem singleLate_dyadic_stage
    (n P Q : Nat) (hn : 2 <= n)
    (hP : P <= singleLateDyadicStartCap Q)
    (hQ : 104 <= Q)
    (hfit : Q + 18 * singleLateDyadicR Q <= n) :
    Reaches (singleStateStep n hn) (singleLateStageHorizon n)
      (SingleLateCheckpoint n P)
      (SingleLateCheckpoint n Q)
      (singleLateStageError n (singleLateDyadicR Q)
        (singleLateCap16 Q (singleLateDyadicR Q))
        (singleLateLentry16 (singleLateDyadicL0 n Q) (singleLateDyadicR Q))
        (singleLateLexit16 (singleLateDyadicL0 n Q) (singleLateDyadicR Q))
        (singleLateHi16 (singleLateDyadicL0 n Q) (singleLateDyadicR Q))
        (singleLateD16 (singleLateDyadicD0 n Q) (singleLateDyadicR Q))) := by
  let R := singleLateDyadicR Q
  have hR : 0 < R := by
    dsimp only [R, singleLateDyadicR]
    omega
  have hentry0 :
      singleLateDyadicL0 n Q + (Q + 16 * R) = 2 * n := by
    dsimp only [R, singleLateDyadicL0, singleLateDyadicStartCap]
    omega
  have ha0 :
      singleLateDyadicA0 n Q + R = singleLateDyadicL0 n Q := by
    dsimp only [R, singleLateDyadicA0, singleLateDyadicL0,
      singleLateDyadicStartCap]
    omega
  have hgap0 :
      n + R + singleLateDyadicD0 n Q =
        singleLateDyadicA0 n Q + 1 := by
    dsimp only [R, singleLateDyadicD0, singleLateDyadicA0,
      singleLateDyadicL0, singleLateDyadicStartCap]
    omega
  have hd0 : 0 < singleLateDyadicD0 n Q := by
    change Q + 18 * R <= n at hfit
    dsimp only [singleLateDyadicD0]
    omega
  have hLn0 :
      n + 1 <= singleLateDyadicL0 n Q + R := by
    change Q + 18 * R <= n at hfit
    dsimp only [singleLateDyadicL0, singleLateDyadicStartCap]
    omega
  have hprod :
      singleLateDyadicD0 n Q + 23 * R <= n := by
    have hsmall := singleLateDyadic_prodRoom (Q := Q) hQ
    change 5 * R + 1 <= Q at hsmall
    change Q + 18 * R <= n at hfit
    dsimp only [singleLateDyadicD0]
    omega
  have hco := singleLateDyadic_coRoom (Q := Q) hQ
  exact singleLate_stage16_concrete_of_start_le n P Q R
    (singleLateDyadicL0 n Q) (singleLateDyadicA0 n Q)
    (singleLateDyadicD0 n Q) hn hP hR hd0 hentry0 ha0 hgap0
    hLn0 (by simpa only [R] using hco) hprod

/-- The middle-entry cap `5n/8` feeds the rounded dyadic late stage whose
target cap is `3n/8`. -/
theorem singleLate_first_stage
    (n : Nat) (hn : 2 <= n) (hlog : 30 <= Nat.log 2 n) :
    Reaches (singleStateStep n hn) (singleLateStageHorizon n)
      (SingleLateCheckpoint n (singleLateEntryCoCap n))
      (SingleLateCheckpoint n (singleLateFirstCap n))
      (singleLateFirstError n) := by
  have hnLarge : 2 ^ 30 <= n := by
    calc
      2 ^ 30 <= 2 ^ Nat.log 2 n :=
        Nat.pow_le_pow_right (by norm_num) hlog
      _ <= n := Nat.pow_log_le_self 2 (by
        intro h0
        rw [h0, Nat.log_zero_right] at hlog
        omega)
  let Q := singleLateFirstCap n
  let R := singleLateDyadicR Q
  have hQ : 104 <= Q := by
    dsimp only [Q, singleLateFirstCap]
    have hdiv := Nat.div_add_mod (3 * n) 8
    have hmod := Nat.mod_lt (3 * n) (by norm_num : 0 < 8)
    omega
  have hP :
      singleLateEntryCoCap n <= singleLateDyadicStartCap Q := by
    dsimp only [Q, R, singleLateEntryCoCap, singleLateDyadicStartCap,
      singleLateDyadicR, singleLateFirstCap]
    have hdiv5 := Nat.div_add_mod (5 * n) 8
    have hmod5 := Nat.mod_lt (5 * n) (by norm_num : 0 < 8)
    have hdiv3 := Nat.div_add_mod (3 * n) 8
    have hmod3 := Nat.mod_lt (3 * n) (by norm_num : 0 < 8)
    have hdivQ := Nat.div_add_mod ((3 * n) / 8) 16
    have hmodQ := Nat.mod_lt ((3 * n) / 8) (by norm_num : 0 < 16)
    omega
  have hfit : Q + 18 * singleLateDyadicR Q <= n := by
    dsimp only [Q, R, singleLateDyadicR, singleLateFirstCap]
    have hdiv3 := Nat.div_add_mod (3 * n) 8
    have hmod3 := Nat.mod_lt (3 * n) (by norm_num : 0 < 8)
    have hdivQ := Nat.div_add_mod ((3 * n) / 8) 16
    have hmodQ := Nat.mod_lt ((3 * n) / 8) (by norm_num : 0 < 16)
    omega
  have hstage := singleLate_dyadic_stage n (singleLateEntryCoCap n) Q hn
    hP hQ hfit
  simpa [singleLateFirstError, Q] using hstage

/-! ## Dyadic late co-cap ladder -/

/-- Number of dyadic Single-B late stages after the first `3n/8` stage.
The public theorem uses this definition instead of exposing natural
subtraction in its statement. -/
def singleLateDyadicStages (n gamma : Nat) : Nat :=
  phase2StageCount n gamma - 1

/-- Public cap schedule for the dyadic late ladder.  Index `0` is the
post-entry cap `3n/8`; subsequent caps are the phase-2 dyadic scales. -/
def singleLateDyadicCap (n _gamma i : Nat) : Nat :=
  if i = 0 then singleLateFirstCap n else phase2Scale n (1 + i)

/-- Target cap reached by the dyadic late ladder. -/
def singleLateTargetCap (n gamma : Nat) : Nat :=
  singleLateDyadicCap n gamma (singleLateDyadicStages n gamma)

/-- Error of one dyadic late stage in the public cap schedule. -/
noncomputable def singleLateDyadicStepError (n gamma i : Nat) : ENNReal :=
  let Q := singleLateDyadicCap n gamma (i + 1)
  singleLateStageError n (singleLateDyadicR Q)
    (singleLateCap16 Q (singleLateDyadicR Q))
    (singleLateLentry16 (singleLateDyadicL0 n Q) (singleLateDyadicR Q))
    (singleLateLexit16 (singleLateDyadicL0 n Q) (singleLateDyadicR Q))
    (singleLateHi16 (singleLateDyadicL0 n Q) (singleLateDyadicR Q))
    (singleLateD16 (singleLateDyadicD0 n Q) (singleLateDyadicR Q))

/-- Horizon of the dyadic late ladder after the first stage. -/
def singleLateDyadicLadderHorizon (n gamma : Nat) : Nat :=
  singleLateDyadicStages n gamma * singleLateStageHorizon n

/-- Error of the dyadic late ladder after the first stage. -/
noncomputable def singleLateDyadicLadderError (n gamma : Nat) : ENNReal :=
  ∑ i ∈ Finset.range (singleLateDyadicStages n gamma),
    singleLateDyadicStepError n gamma i

theorem singleLate_phase2Scale_antitone {n i j : Nat} (hij : i <= j) :
    phase2Scale n j <= phase2Scale n i := by
  unfold phase2Scale
  exact Nat.div_le_div_left
    (Nat.pow_le_pow_right (by norm_num : 1 <= 2) hij)
    (by positivity : 0 < 2 ^ i)

theorem singleLate_phase2Scale_fit
    {n Q : Nat} (hnLarge : 39 <= n) (hQ : Q <= n / 4) :
    Q + 18 * (Q / 16 + 1) <= n := by
  have h4Q : 4 * Q <= n := by
    calc
      4 * Q <= 4 * (n / 4) := Nat.mul_le_mul_left 4 hQ
      _ <= n := by
        rw [Nat.mul_comm]
        exact Nat.div_mul_le_self n 4
  have hdiv : 16 * (Q / 16) <= Q := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_le_self Q 16
  omega

theorem singleLate_phase2Scale_start_le
    {n gamma i Q : Nat}
    (hQ : Q = phase2Scale n (2 + i)) :
    singleLateDyadicCap n gamma i <= Q + 16 * (singleLateDyadicR Q) := by
  cases i with
  | zero =>
      simp only [singleLateDyadicCap, if_true, singleLateFirstCap,
        singleLateDyadicR]
      rw [hQ]
      unfold phase2Scale
      have hdiv8 := Nat.div_add_mod (3 * n) 8
      have hmod8 := Nat.mod_lt (3 * n) (by norm_num : 0 < 8)
      have hdiv4 := Nat.div_add_mod n 4
      have hmod4 := Nat.mod_lt n (by norm_num : 0 < 4)
      have hdivQ := Nat.div_add_mod (n / 2 ^ (2 + 0)) 16
      have hmodQ := Nat.mod_lt (n / 2 ^ (2 + 0)) (by norm_num : 0 < 16)
      omega
  | succ j =>
      have hne : ¬ j + 1 = 0 := by omega
      simp only [singleLateDyadicCap, if_neg hne, singleLateDyadicR]
      rw [hQ]
      unfold phase2Scale
      have hsucc :
          n / 2 ^ (2 + (j + 1)) =
            n / 2 ^ (1 + (j + 1)) / 2 := by
        rw [show 2 + (j + 1) = (1 + (j + 1)) + 1 by omega,
          pow_succ, Nat.div_div_eq_div_mul]
      have hfloor :
          n / 2 ^ (1 + (j + 1)) <=
            2 * (n / 2 ^ (2 + (j + 1))) + 1 := by
        rw [hsucc]
        omega
      have hroom :
          2 * (n / 2 ^ (2 + (j + 1))) + 1 <=
            n / 2 ^ (2 + (j + 1)) +
              16 * (n / 2 ^ (2 + (j + 1)) / 16 + 1) := by
        have hdiv := Nat.div_add_mod (n / 2 ^ (2 + (j + 1))) 16
        have hmod := Nat.mod_lt (n / 2 ^ (2 + (j + 1)))
          (by norm_num : 0 < 16)
        omega
      omega

/-- Every selected dyadic Single-B late stage has the arithmetic side
conditions required by `singleLate_dyadic_stage`. -/
theorem singleLate_dyadic_stage_from_schedule
    (n gamma i : Nat) (hn : 2 <= n)
    (hlog : 256 <= Nat.log 2 n) (hgamma : 1 <= gamma)
    (hi : i < singleLateDyadicStages n gamma) :
    Reaches (singleStateStep n hn) (singleLateStageHorizon n)
      (SingleLateCheckpoint n (singleLateDyadicCap n gamma i))
      (SingleLateCheckpoint n (singleLateDyadicCap n gamma (i + 1)))
      (singleLateDyadicStepError n gamma i) := by
  let Q := phase2Scale n (2 + i)
  have hcapQ :
      singleLateDyadicCap n gamma (i + 1) = Q := by
    have hne : ¬ i + 1 = 0 := by omega
    simp only [singleLateDyadicCap, if_neg hne, Q]
    congr 1
    omega
  have hik : i < phase2StageCount n gamma := by
    unfold singleLateDyadicStages at hi
    omega
  have hmin := phase2StageCount_minimal (n := n) (γ := gamma) hik
  have hlogGamma : 256 <= gamma * Nat.log 2 n :=
    hlog.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hQ : 104 <= Q := by
    dsimp only [Q, phase2Scale]
    omega
  have hQle : Q <= n / 4 := by
    dsimp only [Q, phase2Scale]
    apply Nat.div_le_div_left
    · calc
        4 = 2 ^ 2 := by norm_num
        _ <= 2 ^ (2 + i) :=
          Nat.pow_le_pow_right (by norm_num : 1 <= 2) (by omega)
    · norm_num
  have hnLarge : 39 <= n := by
    calc
      39 <= 2 ^ 8 := by norm_num
      _ <= 2 ^ Nat.log 2 n :=
        Nat.pow_le_pow_right (by norm_num : 1 <= 2) (by omega)
      _ <= n := Nat.pow_log_le_self 2 (by
        intro h0
        rw [h0, Nat.log_zero_right] at hlog
        omega)
  have hP :
      singleLateDyadicCap n gamma i <=
        Q + 16 * singleLateDyadicR Q :=
    singleLate_phase2Scale_start_le (n := n) (gamma := gamma)
      (i := i) (Q := Q) rfl
  have hfit : Q + 18 * singleLateDyadicR Q <= n := by
    dsimp only [singleLateDyadicR]
    exact singleLate_phase2Scale_fit hnLarge hQle
  have hstage := singleLate_dyadic_stage n
    (singleLateDyadicCap n gamma i) Q hn hP hQ hfit
  simpa [singleLateDyadicStepError, hcapQ, Q] using hstage

/-- Dyadic Single-B late ladder from the first late cap down to the target
`O(gamma log n)` co-cap. -/
theorem singleLate_dyadic_ladder
    (n gamma : Nat) (hn : 2 <= n)
    (hlog : 256 <= Nat.log 2 n) (hgamma : 1 <= gamma) :
    Reaches (singleStateStep n hn) (singleLateDyadicLadderHorizon n gamma)
      (SingleLateCheckpoint n (singleLateFirstCap n))
      (SingleLateCheckpoint n (singleLateTargetCap n gamma))
      (singleLateDyadicLadderError n gamma) := by
  let P : Nat -> SingleState n -> Prop :=
    fun i => SingleLateCheckpoint n (singleLateDyadicCap n gamma i)
  let T : Nat -> Nat := fun _ => singleLateStageHorizon n
  let eps : Nat -> ENNReal := fun i => singleLateDyadicStepError n gamma i
  have hrungs : forall i, i < singleLateDyadicStages n gamma ->
      Reaches (singleStateStep n hn) (T i) (P i) (P (i + 1)) (eps i) := by
    intro i hi
    simpa only [P, T, eps] using
      singleLate_dyadic_stage_from_schedule n gamma i hn hlog hgamma hi
  have hchain :=
    Reaches.chain
      (K := singleStateStep n hn) (P := P) (T := T) (ε := eps) hrungs
  have hsum :
      (∑ i ∈ Finset.range (singleLateDyadicStages n gamma), T i) =
        singleLateDyadicLadderHorizon n gamma := by
    simp only [T, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rfl
  rw [hsum] at hchain
  simpa [P, eps, singleLateDyadicLadderError, singleLateTargetCap,
    singleLateDyadicLadderHorizon, singleLateDyadicCap] using hchain

/-- Total Single-B late route from the middle-entry co-cap to the dyadic
target co-cap. -/
theorem singleLate_reaches_target
    (n gamma : Nat) (hn : 2 <= n)
    (hlog : 256 <= Nat.log 2 n) (hgamma : 1 <= gamma) :
    Reaches (singleStateStep n hn)
      (singleLateStageHorizon n + singleLateDyadicLadderHorizon n gamma)
      (SingleLateCheckpoint n (singleLateEntryCoCap n))
      (SingleLateCheckpoint n (singleLateTargetCap n gamma))
      (singleLateFirstError n + singleLateDyadicLadderError n gamma) := by
  have hfirst := singleLate_first_stage n hn (hlog.trans' (by norm_num))
  have hladder := singleLate_dyadic_ladder n gamma hn hlog hgamma
  exact hfirst.comp hladder

section Inhabitation

example :
    singleLateEntryCoCap (2 ^ 30) = 671088640 := by
  norm_num [singleLateEntryCoCap]

example :
    exists s : SingleState (2 ^ 30),
      SingleLateCheckpoint (2 ^ 30) (singleLateEntryCoCap (2 ^ 30)) s := by
  refine ⟨⟨⟨2 ^ 30, 0, 0⟩, by norm_num [BiCfg.DoubleInv]⟩, ?_⟩
  norm_num [SingleLateCheckpoint, singleLateEntryCoCap, BiCfg.doubleLevel]

example :
    Reaches (singleStateStep 160 (by norm_num)) (singleLateSubHorizon 160)
      (SingleLateCheckpoint 160 80)
      (SingleLateCheckpoint 160 76)
      (singleLateSubRungError 160 80 76 4 240 244 252 73) := by
  exact singleLate_subrung 160 80 76 4 240 244 236 252 73
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example :
    Reaches (singleStateStep 200 (by norm_num)) (singleLateStageHorizon 200)
      (SingleLateCheckpoint 200 (56 + 16 * 4))
      (SingleLateCheckpoint 200 56)
      (singleLateStageError 200 4
        (singleLateCap16 56 4) (singleLateLentry16 280 4)
        (singleLateLexit16 280 4) (singleLateHi16 280 4)
        (singleLateD16 73 4)) := by
  exact singleLate_stage16_concrete 200 56 4 280 276 73
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

example :
    Reaches (singleStateStep 200 (by norm_num)) (singleLateStageHorizon 200)
      (SingleLateCheckpoint 200 100)
      (SingleLateCheckpoint 200 56)
      (singleLateStageError 200 4
        (singleLateCap16 56 4) (singleLateLentry16 280 4)
        (singleLateLexit16 280 4) (singleLateHi16 280 4)
        (singleLateD16 73 4)) := by
  exact singleLate_stage16_concrete_of_start_le 200 100 56 4 280 276 73
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example :
    Reaches (singleStateStep 400 (by norm_num)) (singleLateStageHorizon 400)
      (SingleLateCheckpoint 400 300)
      (SingleLateCheckpoint 400 160)
      (singleLateStageError 400 (singleLateDyadicR 160)
        (singleLateCap16 160 (singleLateDyadicR 160))
        (singleLateLentry16 (singleLateDyadicL0 400 160)
          (singleLateDyadicR 160))
        (singleLateLexit16 (singleLateDyadicL0 400 160)
          (singleLateDyadicR 160))
        (singleLateHi16 (singleLateDyadicL0 400 160)
          (singleLateDyadicR 160))
        (singleLateD16 (singleLateDyadicD0 400 160)
          (singleLateDyadicR 160))) := by
  exact singleLate_dyadic_stage 400 300 160 (by norm_num)
    (by norm_num [singleLateDyadicStartCap, singleLateDyadicR])
    (by norm_num)
    (by norm_num [singleLateDyadicR])

example :
    Reaches (singleStateStep (2 ^ 30) (by norm_num))
      (singleLateStageHorizon (2 ^ 30))
      (SingleLateCheckpoint (2 ^ 30) (singleLateEntryCoCap (2 ^ 30)))
      (SingleLateCheckpoint (2 ^ 30) (singleLateFirstCap (2 ^ 30)))
      (singleLateFirstError (2 ^ 30)) := by
  exact singleLate_first_stage (2 ^ 30) (by norm_num)
    (Nat.le_log_of_pow_le (by norm_num) (by norm_num))

example :
    Reaches (singleStateStep (2 ^ 256) (by norm_num))
      (singleLateStageHorizon (2 ^ 256) +
        singleLateDyadicLadderHorizon (2 ^ 256) 1)
      (SingleLateCheckpoint (2 ^ 256) (singleLateEntryCoCap (2 ^ 256)))
      (SingleLateCheckpoint (2 ^ 256) (singleLateTargetCap (2 ^ 256) 1))
      (singleLateFirstError (2 ^ 256) +
        singleLateDyadicLadderError (2 ^ 256) 1) := by
  exact singleLate_reaches_target (2 ^ 256) 1 (by norm_num)
    (Nat.le_log_of_pow_le (by norm_num)
      (le_rfl : 2 ^ 256 <= 2 ^ 256))
    (by norm_num)

end Inhabitation

end Tri

#print axioms Tri.singleMiddleGap_plus_lateEntryCoCap
#print axioms Tri.singleMiddleCheckpoint_to_lateEntry
#print axioms Tri.singleMiddle_reaches_lateEntry
#print axioms Tri.singleBandProductivity_le_one_of_sum
#print axioms Tri.singleLate_rung_checkpoint
#print axioms Tri.singleLateSubRungError
#print axioms Tri.singleLate_subrung
#print axioms Tri.singleLateStageError
#print axioms Tri.singleLate_stage16_symbolic
#print axioms Tri.singleLate_stage16_witnessed
#print axioms Tri.singleLateIdx16
#print axioms Tri.singleLateRem16
#print axioms Tri.singleLateCap16
#print axioms Tri.singleLateLentry16
#print axioms Tri.singleLateLexit16
#print axioms Tri.singleLateALo16
#print axioms Tri.singleLateHi16
#print axioms Tri.singleLateD16
#print axioms Tri.singleLateDyadicR
#print axioms Tri.singleLateDyadicStartCap
#print axioms Tri.singleLateDyadicL0
#print axioms Tri.singleLateDyadicA0
#print axioms Tri.singleLateDyadicD0
#print axioms Tri.singleLateFirstCap
#print axioms Tri.singleLateFirstError
#print axioms Tri.singleLateDyadicStages
#print axioms Tri.singleLateDyadicCap
#print axioms Tri.singleLateTargetCap
#print axioms Tri.singleLateDyadicStepError
#print axioms Tri.singleLateDyadicLadderHorizon
#print axioms Tri.singleLateDyadicLadderError
#print axioms Tri.singleLateDyadic_coRoom
#print axioms Tri.singleLateDyadic_prodRoom
#print axioms Tri.singleLate_stage16_concrete
#print axioms Tri.singleLate_stage16_concrete_of_start_le
#print axioms Tri.singleLate_dyadic_stage
#print axioms Tri.singleLate_first_stage
#print axioms Tri.singleLate_phase2Scale_antitone
#print axioms Tri.singleLate_phase2Scale_fit
#print axioms Tri.singleLate_phase2Scale_start_le
#print axioms Tri.singleLate_dyadic_stage_from_schedule
#print axioms Tri.singleLate_dyadic_ladder
#print axioms Tri.singleLate_reaches_target
