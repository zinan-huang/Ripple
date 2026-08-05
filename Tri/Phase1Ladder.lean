/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Phase1Staged
import Tri.Ladder

/-!
# The unconditional phase-1 doubling ladder

This module turns the state-local contractions from `Tri.Phase1Staged` into a
finite ladder.  Rung `i` starts at the subtraction-free checkpoint

    n + 2^i * sqrt(γ * n * lg n) ≤ 2 * x

and reaches the checkpoint with the gap doubled.  Checkpoints are capped at
`phase1Target n`, so `lg n` rungs suffice.  Every rung uses its own lower
boundary, geometric base, and contraction factor.  The stopped-band estimates
are transferred back to `triChain` and composed by `Reaches.chain`.
-/

namespace Tri

open scoped ENNReal

/-- The number of rungs in the phase-1 ladder. -/
def phase1LadderRungs (n : ℕ) : ℕ :=
  Nat.log 2 n

/-- The canonical, initial-state-independent phase-1 gap supplied by the
headline square-gap assumption. -/
def phase1LadderSeed (n γ : ℕ) : ℕ :=
  Nat.sqrt (γ * n * Nat.log 2 n)

/-- Checkpoint `i`, capped at the first phase-1 exit state.  The uncapped term
is `ceil((n + 2^i * seed) / 2)`, expressed without natural subtraction. -/
def phase1LadderLevel (n γ i : ℕ) : ℕ :=
  min (phase1Target n)
    ((n + 2 ^ i * phase1LadderSeed n γ + 1) / 2)

/-- Membership in checkpoint `i` of the phase-1 ladder. -/
def Phase1LadderCheckpoint (n γ i x : ℕ) : Prop :=
  phase1LadderLevel n γ i ≤ x

/-- Membership in a phase-1 ladder checkpoint is decidable. -/
instance (n γ i : ℕ) : DecidablePred (Phase1LadderCheckpoint n γ i) := by
  intro x
  unfold Phase1LadderCheckpoint
  infer_instance

/-- The stopped lower boundary immediately below checkpoint `i`. -/
def phase1LadderLower (n γ i : ℕ) : ℕ :=
  phase1LadderLevel n γ i - 1

/-- The complementary population parameter at the lower boundary of rung
`i`. -/
def phase1LadderLowerMinority (n γ i : ℕ) : ℕ :=
  n - phase1LadderLower n γ i - 2

/-- The stopped upper boundary of rung `i`, namely checkpoint `i+1`. -/
def phase1LadderUpper (n γ i : ℕ) : ℕ :=
  phase1LadderLevel n γ (i + 1)

/-- The return threshold immediately below the upper boundary of rung `i`. -/
def phase1LadderReturnLo (n γ i : ℕ) : ℕ :=
  phase1LadderLower n γ (i + 1)

/-- The complementary population parameter at the return threshold of rung
`i`. -/
def phase1LadderReturnMinority (n γ i : ℕ) : ℕ :=
  phase1LadderLowerMinority n γ (i + 1)

/-- The exact-time block assigned to each rung. -/
def phase1LadderHorizon (C₁ n γ _i : ℕ) : ℕ :=
  C₁ * γ * n

/-- The canonical ladder seed is no larger than any gap witnessing the
headline square-gap assumption. -/
theorem phase1LadderSeed_le_gap {n γ gap : ℕ}
    (hgap : γ * n * Nat.log 2 n ≤ gap ^ 2) :
    phase1LadderSeed n γ ≤ gap := by
  have hsq : gap ^ 2 < (gap + 1) ^ 2 := by
    simp only [Nat.pow_two]
    nlinarith
  have hlt : γ * n * Nat.log 2 n < (gap + 1) ^ 2 := by
    exact hgap.trans_lt hsq
  exact Nat.lt_succ_iff.mp ((Nat.sqrt_lt').2 hlt)

/-- Under the phase-1 size assumptions the canonical seed is at least two. -/
theorem phase1LadderSeed_ge_two {n γ : ℕ} (hn : 12 ≤ n) (hγ : 1 ≤ γ) :
    2 ≤ phase1LadderSeed n γ := by
  have hlog : 1 ≤ Nat.log 2 n :=
    Nat.log_pos (by norm_num) (by omega)
  have hfour : 2 ^ 2 ≤ γ * n * Nat.log 2 n := by
    calc
      2 ^ 2 ≤ 1 * 12 * 1 := by norm_num
      _ ≤ γ * n * Nat.log 2 n :=
        Nat.mul_le_mul (Nat.mul_le_mul hγ hn) hlog
  exact (Nat.le_sqrt').2 hfour

/-- Every admissible initial state lies above the first canonical checkpoint. -/
theorem phase1LadderLevel_zero_le_initial {n γ x : ℕ}
    (hx : AssemblyInitial n γ x) :
    phase1LadderLevel n γ 0 ≤ x := by
  obtain ⟨gap, hgapStart, hgapSq⟩ := hx.2
  have hseedStart : n + phase1LadderSeed n γ ≤ 2 * x := by
    have hseed := phase1LadderSeed_le_gap hgapSq
    omega
  apply (min_le_right (phase1Target n)
    ((n + 2 ^ 0 * phase1LadderSeed n γ + 1) / 2)).trans
  simp only [pow_zero, one_mul]
  rw [Nat.div_le_iff_le_mul (by norm_num : 0 < (2 : ℕ))]
  omega

/-- The phase-1 target leaves at least two physical states above it. -/
theorem phase1Target_add_two_le {n : ℕ} (hn : 12 ≤ n) :
    phase1Target n + 2 ≤ n := by
  obtain ⟨hpop, _hreturnPos, hbReturnPos, _hmaj, hsucc, _htargetN⟩ :=
    phase1Return_arithmetic hn
  omega

/-- Every ladder checkpoint is strictly above the majority midpoint. -/
theorem phase1BandLo_lt_ladderLevel {n γ i : ℕ} (hn : 12 ≤ n)
    (hseed : 1 ≤ phase1LadderSeed n γ) :
    phase1BandLo n < phase1LadderLevel n γ i := by
  have htarget : phase1BandLo n < phase1Target n := by
    have hhalf : 2 * phase1BandLo n ≤ n := by
      exact Nat.mul_div_le n 2
    have hthreshold :=
      (phase1Target_le_iff n (phase1Target n)).1 le_rfl
    omega
  have hpow : 0 < 2 ^ i * phase1LadderSeed n γ := by
    positivity
  have hceil : phase1BandLo n <
      (n + 2 ^ i * phase1LadderSeed n γ + 1) / 2 := by
    rw [Nat.lt_div_iff_mul_lt (by norm_num : 0 < (2 : ℕ))]
    have hhalf : 2 * phase1BandLo n ≤ n := by
      exact Nat.mul_div_le n 2
    omega
  exact lt_min htarget hceil

/-- A checkpoint is exactly one state above its stopped lower boundary. -/
theorem phase1LadderLower_succ {n γ i : ℕ} (hn : 12 ≤ n)
    (hseed : 1 ≤ phase1LadderSeed n γ) :
    phase1LadderLower n γ i + 1 = phase1LadderLevel n γ i := by
  have hpos : 0 < phase1LadderLevel n γ i :=
    (phase1BandLo_lt_ladderLevel hn hseed).trans_le' (Nat.zero_le _)
  unfold phase1LadderLower
  omega

/-- Arithmetic data at every stopped lower boundary. -/
theorem phase1LadderLower_arithmetic {n γ i : ℕ} (hn : 12 ≤ n)
    (hseed : 1 ≤ phase1LadderSeed n γ) :
    phase1LadderLower n γ i + phase1LadderLowerMinority n γ i + 2 = n ∧
      0 < phase1LadderLower n γ i ∧
      0 < phase1LadderLowerMinority n γ i ∧
      phase1LadderLowerMinority n γ i < phase1LadderLower n γ i := by
  have hsucc : phase1LadderLower n γ i + 1 =
      phase1LadderLevel n γ i :=
    phase1LadderLower_succ (i := i) hn hseed
  have hlevelTarget : phase1LadderLevel n γ i ≤ phase1Target n :=
    min_le_left _ _
  have htarget := phase1Target_add_two_le hn
  have hlowerMid : phase1BandLo n ≤ phase1LadderLower n γ i := by
    have hmid : phase1BandLo n < phase1LadderLevel n γ i :=
      phase1BandLo_lt_ladderLevel (i := i) hn hseed
    omega
  have hdecomp : 2 * phase1BandLo n + n % 2 = n := by
    simpa [phase1BandLo, Nat.mul_comm] using Nat.div_add_mod n 2
  have hmod : n % 2 < 2 := Nat.mod_lt n (by norm_num)
  unfold phase1LadderLowerMinority
  constructor
  · omega
  constructor
  · have hhalfPos : 0 < phase1BandLo n := by
      unfold phase1BandLo
      omega
    omega
  constructor <;> omega

/-- The ladder checkpoints are monotone. -/
theorem phase1LadderLevel_mono (n γ i : ℕ) :
    phase1LadderLevel n γ i ≤ phase1LadderLevel n γ (i + 1) := by
  unfold phase1LadderLevel
  apply min_le_min_left
  apply Nat.div_le_div_right
  have hpow : 2 ^ i ≤ 2 ^ (i + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  exact Nat.add_le_add_right
    (Nat.add_le_add_left
      (Nat.mul_le_mul_right (phase1LadderSeed n γ) hpow) n) 1

/-- After `lg n` doublings, the capped checkpoint is exactly the phase-1
target. -/
theorem phase1LadderLevel_final {n γ : ℕ} (hn : 12 ≤ n) (hγ : 1 ≤ γ) :
    phase1LadderLevel n γ (phase1LadderRungs n) = phase1Target n := by
  have hseed := phase1LadderSeed_ge_two hn hγ
  have hpow : n < 2 ^ (Nat.log 2 n + 1) := by
    simpa using Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n
  have hlarge : n ≤ 2 ^ Nat.log 2 n * phase1LadderSeed n γ := by
    rw [pow_succ] at hpow
    have htwo : 2 ^ Nat.log 2 n * 2 ≤
        2 ^ Nat.log 2 n * phase1LadderSeed n γ :=
      Nat.mul_le_mul_left _ hseed
    omega
  have hnceil : n ≤
      (n + 2 ^ Nat.log 2 n * phase1LadderSeed n γ + 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < (2 : ℕ))]
    omega
  have htargetN := (phase1Return_arithmetic hn).2.2.2.2.2
  unfold phase1LadderLevel phase1LadderRungs
  exact min_eq_left (htargetN.trans hnceil)

/-- The `lg n` equal rung blocks sum to the fixed phase-1 horizon. -/
theorem phase1LadderHorizon_sum (C₁ n γ : ℕ) :
    (∑ i ∈ Finset.range (phase1LadderRungs n),
      phase1LadderHorizon C₁ n γ i) = phase1Horizon C₁ n γ := by
  simp [phase1LadderRungs, phase1LadderHorizon, phase1Horizon]
  ring

/-- The productive-counter allowance included in one ladder rung. -/
noncomputable def phase1LadderProductiveError
    (n γ i T : ℕ) : ℝ≥0∞ :=
  ((phase1LadderLowerMinority n γ i : ℝ≥0∞) /
      (phase1LadderLower n γ i : ℝ≥0∞)) ^ 1 +
    ((43 : ℝ≥0∞) / 64 + (21 : ℝ≥0∞) / 64 *
      phase1RungBase (phase1LadderLower n γ i)
        (phase1LadderLowerMinority n γ i)) ^ T *
      phase1RungBase (phase1LadderLower n γ i)
        (phase1LadderLowerMinority n γ i) ^ 0 /
      phase1RungBase (phase1LadderLower n γ i)
        (phase1LadderLowerMinority n γ i) ^ 1

/-- The stopped-band error of rung `i`, including both signed progress and the
productive-counter checkpoint. -/
noncomputable def phase1LadderDirectionError
    (n γ i T : ℕ) : ℝ≥0∞ :=
  ((phase1LadderLowerMinority n γ i : ℝ≥0∞) /
      (phase1LadderLower n γ i : ℝ≥0∞)) ^ 1 +
    phase1RungPhi n (phase1LadderLower n γ i)
        (phase1LadderLowerMinority n γ i) (phase1LadderUpper n γ i) ^ T *
      phase1RungBase (phase1LadderLower n γ i)
          (phase1LadderLowerMinority n γ i) ^ phase1LadderLevel n γ i /
        phase1RungBase (phase1LadderLower n γ i)
          (phase1LadderLowerMinority n γ i) ^ phase1LadderUpper n γ i

/-- The stopped-band error of rung `i`, including both signed progress and the
productive-counter checkpoint. -/
noncomputable def phase1LadderBandError
    (n γ i T : ℕ) : ℝ≥0∞ :=
  phase1LadderDirectionError n γ i T +
    phase1LadderProductiveError n γ i T

/-- The complete error of rung `i`, after transferring its stopped upper hit
back to the original chain. -/
noncomputable def phase1LadderRungError
    (n γ i T : ℕ) : ℝ≥0∞ :=
  phase1LadderBandError n γ i T +
    ((phase1LadderReturnMinority n γ i : ℝ≥0∞) /
      (phase1LadderReturnLo n γ i : ℝ≥0∞)) ^ 1

/-- The sum of the errors of all `lg n` phase-1 rungs. -/
noncomputable def phase1LadderError (C₁ n γ : ℕ) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range (phase1LadderRungs n),
    phase1LadderRungError n γ i (phase1LadderHorizon C₁ n γ i)

/-- Every ladder upper boundary lies in the productive phase-1 region used by
`band_rung_bound`. -/
theorem phase1LadderUpper_phase_bound {n γ i : ℕ} :
    8 * phase1LadderUpper n γ i ≤ 7 * n + 7 := by
  have hupper : phase1LadderUpper n γ i ≤ phase1Target n :=
    min_le_left _ _
  have htarget : 6 * phase1Target n ≤ 5 * n + 5 := by
    unfold phase1Target
    simpa [Nat.mul_comm] using Nat.mul_div_le (5 * n + 5) 6
  omega

/-- The `phase1RungPhi` chosen for every ladder rung is a strict contraction. -/
theorem phase1LadderPhi_lt_one
    (n γ i : ℕ) (hn : 12 ≤ n) (hγ : 1 ≤ γ) :
    phase1RungPhi n (phase1LadderLower n γ i)
      (phase1LadderLowerMinority n γ i) (phase1LadderUpper n γ i) < 1 := by
  have hseed2 := phase1LadderSeed_ge_two hn hγ
  have hseed1 : 1 ≤ phase1LadderSeed n γ := hseed2.trans' (by omega)
  obtain ⟨hpop, hlowerPos, _hbLowerPos, hbias⟩ :=
    phase1LadderLower_arithmetic (i := i) hn hseed1
  exact phase1RungPhi_lt_one n (phase1LadderLower n γ i)
    (phase1LadderLowerMinority n γ i) (phase1LadderUpper n γ i)
    (by omega) hpop hlowerPos hbias

/-- On one rung, the local scalar contraction and productive-count estimate
give a stopped-band upper-boundary reachability theorem. -/
theorem phase1_ladder_band_rung
    (n γ i T : ℕ) (hn : 12 ≤ n) (hγ : 1 ≤ γ) :
    Reaches
      (bandCount n (phase1LadderLower n γ i) (phase1LadderUpper n γ i)) T
      (fun s => phase1LadderLevel n γ i ≤ s.1 ∧ s.2 = 0)
      (fun s => phase1LadderUpper n γ i ≤ s.1)
      (phase1LadderBandError n γ i T) := by
  have h3 : 3 ≤ n := by omega
  have hseed2 := phase1LadderSeed_ge_two hn hγ
  have hseed1 : 1 ≤ phase1LadderSeed n γ := hseed2.trans' (by omega)
  obtain ⟨hpopLower, hlowerPos, hbLowerPos, hbias⟩ :=
    phase1LadderLower_arithmetic (i := i) hn hseed1
  have hstart : phase1LadderLower n γ i + 1 =
      phase1LadderLevel n γ i :=
    phase1LadderLower_succ (i := i) hn hseed1
  have hupperPhysical : phase1LadderUpper n γ i ≤ n := by
    have htargetN := (phase1Return_arithmetic hn).2.2.2.2.2
    exact (min_le_left _ _).trans htargetN
  have hbase := phase1RungBase_spec hlowerPos hbias
  have hbase0 : phase1RungBase (phase1LadderLower n γ i)
      (phase1LadderLowerMinority n γ i) ≠ 0 := hbase.1.ne'
  have hbase1 : phase1RungBase (phase1LadderLower n γ i)
      (phase1LadderLowerMinority n γ i) ≤ 1 := hbase.2.1.le
  have hratio :
      (phase1LadderLowerMinority n γ i : ℝ≥0∞) /
          (phase1LadderLower n γ i : ℝ≥0∞) ≤ 1 := by
    have hlower0 : (phase1LadderLower n γ i : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    have hlowerTop : (phase1LadderLower n γ i : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.natCast_ne_top _
    calc
      (phase1LadderLowerMinority n γ i : ℝ≥0∞) /
          (phase1LadderLower n γ i : ℝ≥0∞) ≤
          (phase1LadderLower n γ i : ℝ≥0∞) /
            (phase1LadderLower n γ i : ℝ≥0∞) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr hbias.le) _
      _ = 1 := ENNReal.div_self hlower0 hlowerTop
  have hsigned : Reaches
      (bandCount n (phase1LadderLower n γ i) (phase1LadderUpper n γ i)) T
      (fun s => phase1LadderLevel n γ i ≤ s.1 ∧ s.2 = 0)
      (fun s => phase1LadderUpper n γ i ≤ s.1)
      (phase1LadderDirectionError n γ i T) := by
    rintro ⟨z, c⟩ ⟨hzStart, hc⟩
    change phase1LadderLevel n γ i ≤ z at hzStart
    change c = 0 at hc
    subst c
    by_cases hzUpper : phase1LadderUpper n γ i ≤ z
    · have hiter : iter (directionStop n (phase1LadderLower n γ i)
          (phase1LadderUpper n γ i)) T z = PMF.pure z :=
        iter_freeze_of_mem z (Or.inr hzUpper) T
      calc
        (∑' q, if phase1LadderUpper n γ i ≤ q.1 then 0 else
            iter (bandCount n (phase1LadderLower n γ i)
              (phase1LadderUpper n γ i)) T (z, 0) q) =
            ∑' q, if phase1LadderUpper n γ i ≤ q then 0 else
              iter (directionStop n (phase1LadderLower n γ i)
                (phase1LadderUpper n γ i)) T z q :=
          bandCount_upper_failure_eq_directionStop n
            (phase1LadderLower n γ i) (phase1LadderUpper n γ i) T z 0
        _ = 0 := by
          rw [hiter, ENNReal.tsum_eq_zero]
          intro q
          by_cases hq : phase1LadderUpper n γ i ≤ q
          · simp [hq]
          · have hqz : q ≠ z := by
              intro hqz
              subst q
              exact hq hzUpper
            simp [hq, PMF.pure_apply, hqz]
        _ ≤ phase1LadderDirectionError n γ i T := bot_le
    · have hzUpper' : z < phase1LadderUpper n γ i := by omega
      have hlowerZ : phase1LadderLower n γ i < z := by omega
      obtain ⟨kz, hkz⟩ := Nat.le.dest hlowerZ.le
      obtain ⟨d, hd⟩ := Nat.le.dest hzUpper'.le
      have hkzPos : 0 < kz := by omega
      have hdPos : 0 < d := by omega
      have hprogress := DirectionProgress.phase1_direction_progress
        n (phase1LadderLower n γ i) (phase1LadderLowerMinority n γ i)
        kz d T h3 hpopLower hlowerPos hbLowerPos hbias.le hkzPos hdPos
        (by omega)
        (phase1RungBase (phase1LadderLower n γ i)
          (phase1LadderLowerMinority n γ i))
        (phase1RungPhi n (phase1LadderLower n γ i)
          (phase1LadderLowerMinority n γ i) (phase1LadderUpper n γ i))
        hbase1 hbase0 (by
          intro a b hpop haLower haUpper
          exact phase1_rung_scalar_contraction n
            (phase1LadderLower n γ i) (phase1LadderLowerMinority n γ i)
            (phase1LadderUpper n γ i) a b h3 hpopLower hlowerPos hbias
            hpop haLower (by omega))
      have hprogress' :
          (∑' q, if phase1LadderUpper n γ i ≤ q then 0 else
            iter (directionStop n (phase1LadderLower n γ i)
              (phase1LadderUpper n γ i)) T z q) ≤
            ((phase1LadderLowerMinority n γ i : ℝ≥0∞) /
              (phase1LadderLower n γ i : ℝ≥0∞)) ^ kz +
              phase1RungPhi n (phase1LadderLower n γ i)
                  (phase1LadderLowerMinority n γ i)
                  (phase1LadderUpper n γ i) ^ T *
                phase1RungBase (phase1LadderLower n γ i)
                    (phase1LadderLowerMinority n γ i) ^ z /
                  phase1RungBase (phase1LadderLower n γ i)
                    (phase1LadderLowerMinority n γ i) ^
                      phase1LadderUpper n γ i := by
        simpa only [hkz, hd] using hprogress
      have hsafety :
          ((phase1LadderLowerMinority n γ i : ℝ≥0∞) /
            (phase1LadderLower n γ i : ℝ≥0∞)) ^ kz ≤
          ((phase1LadderLowerMinority n γ i : ℝ≥0∞) /
            (phase1LadderLower n γ i : ℝ≥0∞)) ^ 1 :=
        pow_le_pow_right_of_le_one' hratio (by omega)
      have hstartPow :
          phase1RungBase (phase1LadderLower n γ i)
              (phase1LadderLowerMinority n γ i) ^ z ≤
            phase1RungBase (phase1LadderLower n γ i)
              (phase1LadderLowerMinority n γ i) ^
                phase1LadderLevel n γ i :=
        pow_le_pow_right_of_le_one' hbase1 hzStart
      calc
        (∑' q, if phase1LadderUpper n γ i ≤ q.1 then 0 else
            iter (bandCount n (phase1LadderLower n γ i)
              (phase1LadderUpper n γ i)) T (z, 0) q) =
            ∑' q, if phase1LadderUpper n γ i ≤ q then 0 else
              iter (directionStop n (phase1LadderLower n γ i)
                (phase1LadderUpper n γ i)) T z q :=
          bandCount_upper_failure_eq_directionStop n
            (phase1LadderLower n γ i) (phase1LadderUpper n γ i) T z 0
        _ ≤ ((phase1LadderLowerMinority n γ i : ℝ≥0∞) /
              (phase1LadderLower n γ i : ℝ≥0∞)) ^ kz +
              phase1RungPhi n (phase1LadderLower n γ i)
                  (phase1LadderLowerMinority n γ i)
                  (phase1LadderUpper n γ i) ^ T *
                phase1RungBase (phase1LadderLower n γ i)
                    (phase1LadderLowerMinority n γ i) ^ z /
                  phase1RungBase (phase1LadderLower n γ i)
                    (phase1LadderLowerMinority n γ i) ^
                      phase1LadderUpper n γ i := hprogress'
        _ ≤ phase1LadderDirectionError n γ i T := by
          unfold phase1LadderDirectionError
          apply add_le_add hsafety
          exact ENNReal.div_le_div_right
            (mul_le_mul_right hstartPow _) _
  have hproductive : Reaches
      (bandCount n (phase1LadderLower n γ i) (phase1LadderUpper n γ i)) T
      (fun s => phase1LadderLevel n γ i ≤ s.1 ∧ s.2 = 0)
      (fun s => phase1LadderLower n γ i < s.1 ∧
        (phase1LadderUpper n γ i ≤ s.1 ∨ 1 < s.2))
      (phase1LadderProductiveError n γ i T) := by
    rintro ⟨z, c⟩ ⟨hzStart, hc⟩
    change phase1LadderLevel n γ i ≤ z at hzStart
    change c = 0 at hc
    subst c
    have hlowerZ : phase1LadderLower n γ i < z := by omega
    obtain ⟨kz, hkz⟩ := Nat.le.dest hlowerZ.le
    have hkzPos : 0 < kz := by omega
    have hrung := band_rung_bound n (phase1LadderLower n γ i)
      (phase1LadderUpper n γ i) (phase1LadderLowerMinority n γ i)
      kz T 1 0 hpopLower hbLowerPos hbias phase1LadderUpper_phase_bound
      (phase1RungBase (phase1LadderLower n γ i)
        (phase1LadderLowerMinority n γ i)) hbase1 hbase0
    have hsafety :
        ((phase1LadderLowerMinority n γ i : ℝ≥0∞) /
          (phase1LadderLower n γ i : ℝ≥0∞)) ^ kz ≤
        ((phase1LadderLowerMinority n γ i : ℝ≥0∞) /
          (phase1LadderLower n γ i : ℝ≥0∞)) ^ 1 :=
      pow_le_pow_right_of_le_one' hratio (by omega)
    have herror :
        ((phase1LadderLowerMinority n γ i : ℝ≥0∞) /
            (phase1LadderLower n γ i : ℝ≥0∞)) ^ kz +
          ((43 : ℝ≥0∞) / 64 + (21 : ℝ≥0∞) / 64 *
            phase1RungBase (phase1LadderLower n γ i)
              (phase1LadderLowerMinority n γ i)) ^ T *
            phase1RungBase (phase1LadderLower n γ i)
              (phase1LadderLowerMinority n γ i) ^ 0 /
            phase1RungBase (phase1LadderLower n γ i)
              (phase1LadderLowerMinority n γ i) ^ 1 ≤
          phase1LadderProductiveError n γ i T := by
      unfold phase1LadderProductiveError
      exact add_le_add hsafety le_rfl
    have hrung' := hrung.mono_error herror
    exact hrung' (z, 0) (by simp only [hkz])
  have hboth := hsigned.inter hproductive
  exact hboth.mono_post (by
    intro s hs
    exact hs.1)

/-- The stopped estimate for rung `i` transfers to an exact-time rung on
`triChain`; the only added cost is its explicit upper-return term. -/
theorem phase1_ladder_rung
    (n γ i T : ℕ) (hn : 12 ≤ n) (hγ : 1 ≤ γ) :
    Reaches (triChain n) T
      (Phase1LadderCheckpoint n γ i)
      (Phase1LadderCheckpoint n γ (i + 1))
      (phase1LadderRungError n γ i T) := by
  have h3 : 3 ≤ n := by omega
  have hseed2 := phase1LadderSeed_ge_two hn hγ
  have hseed1 : 1 ≤ phase1LadderSeed n γ := hseed2.trans' (by omega)
  obtain ⟨hpopReturn, hreturnPos, hbReturnPos, hbReturnBias⟩ :=
    phase1LadderLower_arithmetic (i := i + 1) hn hseed1
  have hreturnNext : phase1LadderReturnLo n γ i + 1 =
      phase1LadderUpper n γ i := by
    exact phase1LadderLower_succ (i := i + 1) hn hseed1
  have hreturnCheckpoint : phase1LadderReturnLo n γ i + 1 =
      phase1LadderLevel n γ (i + 1) := by
    simpa only [phase1LadderReturnLo] using
      phase1LadderLower_succ (i := i + 1) hn hseed1
  have hlevelMono := phase1LadderLevel_mono n γ i
  have hstart := phase1LadderLower_succ (i := i) hn hseed1
  have hbandAll := phase1_ladder_band_rung n γ i T hn hγ
  intro z hz
  have hband : Reaches
      (bandCount n (phase1LadderLower n γ i) (phase1LadderUpper n γ i)) T
      (fun s => s = (z, 0))
      (fun s => phase1LadderLevel n γ (i + 1) ≤ s.1)
      (phase1LadderBandError n γ i T) := by
    intro s hs
    subst s
    simpa only [phase1LadderUpper] using
      hbandAll (z, 0) ⟨hz, rfl⟩
  calc
    (∑' q, if Phase1LadderCheckpoint n γ (i + 1) q then 0 else
        iter (triChain n) T z q) ≤
        (∑' s, if phase1LadderLevel n γ (i + 1) ≤ s.1 then 0 else
          iter (bandCount n (phase1LadderLower n γ i)
            (phase1LadderUpper n γ i)) T (z, 0) s) +
          ((phase1LadderReturnMinority n γ i : ℝ≥0∞) /
            (phase1LadderReturnLo n γ i : ℝ≥0∞)) ^ 1 := by
      unfold Phase1LadderCheckpoint
      exact band_rung_transfer_upper n (phase1LadderLower n γ i)
        (phase1LadderUpper n γ i) (phase1LadderReturnLo n γ i)
        (phase1LadderReturnMinority n γ i) 1 T z 0 h3 hpopReturn
        hreturnPos hbReturnPos hbReturnBias.le (by omega)
        (fun q => phase1LadderLevel n γ (i + 1) ≤ q)
        (by
          intro q hq
          omega)
        (by
          intro q hq
          omega)
    _ ≤ phase1LadderBandError n γ i T +
          ((phase1LadderReturnMinority n γ i : ℝ≥0∞) /
            (phase1LadderReturnLo n γ i : ℝ≥0∞)) ^ 1 :=
      add_le_add (hband (z, 0) rfl) le_rfl
    _ = phase1LadderRungError n γ i T := rfl

/-- The `lg n` original-chain rungs compose to the phase-1 target with summed
horizons and errors. -/
theorem phase1_ladder_chain
    (C₁ n γ : ℕ) (hn : 12 ≤ n) (hγ : 1 ≤ γ) :
    Reaches (triChain n) (phase1Horizon C₁ n γ)
      (Phase1LadderCheckpoint n γ 0)
      (fun z => phase1Target n ≤ z)
      (phase1LadderError C₁ n γ) := by
  let P : ℕ → ℕ → Prop := fun i => Phase1LadderCheckpoint n γ i
  let rungTime : ℕ → ℕ := phase1LadderHorizon C₁ n γ
  let rungError : ℕ → ℝ≥0∞ := fun i =>
    phase1LadderRungError n γ i (phase1LadderHorizon C₁ n γ i)
  have hrungs : ∀ i < phase1LadderRungs n,
      Reaches (triChain n) (rungTime i) (P i) (P (i + 1))
        (rungError i) := by
    intro i _hi
    exact phase1_ladder_rung n γ i (phase1LadderHorizon C₁ n γ i) hn hγ
  have hchain := Reaches.chain
    (K := triChain n) (P := P) (T := rungTime) (ε := rungError) hrungs
  have hfinal := phase1LadderLevel_final hn hγ
  have hchain' : Reaches (triChain n) (phase1Horizon C₁ n γ)
      (P 0) (P (phase1LadderRungs n)) (phase1LadderError C₁ n γ) := by
    simpa only [rungTime, rungError, phase1LadderHorizon_sum,
      phase1LadderError] using hchain
  exact hchain'.mono_post (by
    intro z hz
    change phase1LadderLevel n γ (phase1LadderRungs n) ≤ z at hz
    rwa [hfinal] at hz)

/-- The canonical ladder starts from every `AssemblyInitial` state and reaches
the subtraction-free phase-1 upper threshold. -/
theorem phase1_ladder_reaches
    (C₁ n γ : ℕ) (h3 : 3 ≤ n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    Reaches (triChain n) (phase1Horizon C₁ n γ)
      (AssemblyInitial n γ) (fun z => 5 * n ≤ 6 * z)
      (phase1LadderError C₁ n γ) := by
  have hn := phase1_size_ge_twelve h3 hγ hsize
  have hchain := phase1_ladder_chain C₁ n γ hn hγ
  have hupper := hchain.mono_post (by
    intro z hz
    exact (phase1Target_le_iff n z).1 hz)
  intro x hx
  exact hupper x (phase1LadderLevel_zero_le_initial hx)

/-- Phase 1 is unconditional: the only assumptions are the headline
arithmetic side conditions and the arithmetic initial-state predicate. -/
theorem phase1_reaches_unconditional
    (C₁ n γ : ℕ) (h3 : 3 ≤ n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    Reaches (triChain n) (phase1Horizon C₁ n γ)
      (AssemblyInitial n γ) (Phase1Exit n)
      (phase1LadderError C₁ n γ) := by
  classical
  exact (phase1_ladder_reaches C₁ n γ h3 hγ hsize).phase1Exit_of_upper
    h3 (fun x hx => hx.1)

/-- The bridge error includes the endpoint-return allowance required by
`Phase1BandBridge`; the endpoint is already absorbing, so this last allowance
is conservative. -/
noncomputable def phase1LadderBridgeError (C₁ n γ : ℕ) : ℝ≥0∞ :=
  phase1LadderError C₁ n γ +
    ((phase1ReturnMinority n : ℝ≥0∞) /
      (phase1ReturnLo n : ℝ≥0∞)) ^ (phase1ReturnMinority n + 2)

/-- Stopping `triChain` at `0` and `n` leaves the kernel unchanged because
both population endpoints are already absorbing. -/
theorem phase1EndpointBandChain_eq_triChain (n : ℕ) :
    bandChain n 0 n = triChain n := by
  funext z
  unfold bandChain freeze
  by_cases hz : z ≤ 0 ∨ n ≤ z
  · rw [if_pos hz]
    rcases hz with hz0 | hzn
    · have hz0' : z = 0 := by omega
      subst z
      exact (consensus_absorbing n 0 (Or.inl rfl)).symm
    · by_cases hzeq : z = n
      · subst z
        exact (consensus_absorbing n n (Or.inr rfl)).symm
      · unfold triChain
        rw [dif_neg]
        omega
  · rw [if_neg hz]

/-- The first-coordinate failure mass of the endpoint-stopped counting chain
is exactly the corresponding failure mass of `triChain`. -/
theorem phase1EndpointBandCount_failure_eq_triChain
    (n T x c₀ : ℕ) (A : ℕ → Prop) [DecidablePred A] :
    (∑' s, if A s.1 then 0 else iter (bandCount n 0 n) T (x, c₀) s) =
      ∑' z, if A z then 0 else iter (triChain n) T x z := by
  let V : ℕ → ℝ≥0∞ := fun z => if A z then 0 else 1
  have hmap : (iter (bandCount n 0 n) T (x, c₀)).map Prod.fst =
      iter (bandChain n 0 n) T x :=
    iter_map_of_step_map _ _ _ (bandCount_map_fst n 0 n) T _
  calc
    (∑' s, if A s.1 then 0 else iter (bandCount n 0 n) T (x, c₀) s) =
        expect (iter (bandCount n 0 n) T (x, c₀)) (fun s => V s.1) := by
      unfold expect V
      apply tsum_congr
      intro s
      by_cases hs : A s.1 <;> simp [hs]
    _ = expect ((iter (bandCount n 0 n) T (x, c₀)).map Prod.fst) V := by
      rw [expect_map]
    _ = expect (iter (bandChain n 0 n) T x) V := by rw [hmap]
    _ = expect (iter (triChain n) T x) V := by
      rw [phase1EndpointBandChain_eq_triChain n]
    _ = ∑' z, if A z then 0 else iter (triChain n) T x z := by
      unfold expect V
      apply tsum_congr
      intro z
      by_cases hz : A z <;> simp [hz]

/-- An original-chain reachability theorem lifts to the counting chain stopped
only at the already-absorbing population endpoints. -/
theorem Reaches.to_phase1EndpointBandCount
    (n T x c₀ : ℕ) (A : ℕ → Prop) [DecidablePred A] (ε : ℝ≥0∞)
    (h : Reaches (triChain n) T (fun z => z = x) A ε) :
    Reaches (bandCount n 0 n) T
      (fun s => s = (x, c₀)) (fun s => A s.1) ε := by
  intro s hs
  subst s
  rw [phase1EndpointBandCount_failure_eq_triChain n T x c₀ A]
  exact h x rfl

/-- Predicate-form lifting from `triChain` to the common endpoint-stopped
counting kernel.  The initial counter may be arbitrary. -/
theorem Reaches.to_phase1EndpointBandCount_pred
    {n T : ℕ} {P A : ℕ → Prop} [DecidablePred A] {ε : ℝ≥0∞}
    (h : Reaches (triChain n) T P A ε) :
    Reaches (bandCount n 0 n) T
      (fun s => P s.1) (fun s => A s.1) ε := by
  rintro ⟨x, c⟩ hx
  rw [phase1EndpointBandCount_failure_eq_triChain n T x c A]
  exact h x hx

/-- After lifting every transferred rung to the same endpoint-stopped kernel,
`Reaches.chain` gives the requested `bandCount` ladder with summed time and
error. -/
theorem phase1_ladder_band_chain
    (C₁ n γ : ℕ) (hn : 12 ≤ n) (hγ : 1 ≤ γ) :
    Reaches (bandCount n 0 n) (phase1Horizon C₁ n γ)
      (fun s => Phase1LadderCheckpoint n γ 0 s.1)
      (fun s => phase1Target n ≤ s.1)
      (phase1LadderError C₁ n γ) := by
  let P : ℕ → ℕ × ℕ → Prop := fun i s =>
    Phase1LadderCheckpoint n γ i s.1
  let rungTime : ℕ → ℕ := phase1LadderHorizon C₁ n γ
  let rungError : ℕ → ℝ≥0∞ := fun i =>
    phase1LadderRungError n γ i (phase1LadderHorizon C₁ n γ i)
  have hrungs : ∀ i < phase1LadderRungs n,
      Reaches (bandCount n 0 n) (rungTime i) (P i) (P (i + 1))
        (rungError i) := by
    intro i _hi
    exact Reaches.to_phase1EndpointBandCount_pred
      (phase1_ladder_rung n γ i (phase1LadderHorizon C₁ n γ i) hn hγ)
  have hchain := Reaches.chain
    (K := bandCount n 0 n) (P := P) (T := rungTime) (ε := rungError) hrungs
  have hchain' : Reaches (bandCount n 0 n) (phase1Horizon C₁ n γ)
      (P 0) (P (phase1LadderRungs n)) (phase1LadderError C₁ n γ) := by
    simpa only [rungTime, rungError, phase1LadderHorizon_sum,
      phase1LadderError] using hchain
  have hfinal := phase1LadderLevel_final hn hγ
  exact hchain'.mono_post (by
    intro s hs
    change phase1LadderLevel n γ (phase1LadderRungs n) ≤ s.1 at hs
    rwa [hfinal] at hs)

/-- The common endpoint `bandCount` ladder has the lifted
`AssemblyInitial`/`Phase1Exit` type. -/
theorem phase1_ladder_band_reaches
    (C₁ n γ : ℕ) (h3 : 3 ≤ n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    Reaches (bandCount n 0 n) (phase1Horizon C₁ n γ)
      (fun s => AssemblyInitial n γ s.1)
      (fun s => Phase1Exit n s.1)
      (phase1LadderError C₁ n γ) := by
  exact Reaches.to_phase1EndpointBandCount_pred
    (phase1_reaches_unconditional C₁ n γ h3 hγ hsize)

/-- The unconditional ladder as the exact `Phase1BandBridge` consumed by
`theorem1b_of_fewer`.  It carries no probabilistic hypothesis. -/
noncomputable def phase1_bridge_unconditional
    (C₁ n γ x : ℕ) (h3 : 3 ≤ n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n)
    (hx : AssemblyInitial n γ x) :
    Phase1BandBridge n x (phase1Horizon C₁ n γ)
      (phase1LadderBridgeError C₁ n γ) := by
  have hn := phase1_size_ge_twelve h3 hγ hsize
  obtain ⟨hreturnPop, hreturnPos, hbReturnPos, hbReturnMaj,
      hreturnSucc, _htargetN⟩ := phase1Return_arithmetic hn
  have hbandAll := phase1_ladder_band_reaches C₁ n γ h3 hγ hsize
  have hbandUpper := hbandAll.mono_post (by
    intro s hs
    exact hs.2)
  have hband : Reaches (bandCount n 0 n) (phase1Horizon C₁ n γ)
      (fun s => s = (x, 0)) (fun s => 5 * n ≤ 6 * s.1)
      (phase1LadderError C₁ n γ) := by
    intro s hs
    subst s
    exact hbandUpper (x, 0) hx
  refine
    { bandLo := 0
      aHi := n
      returnLo := phase1ReturnLo n
      bHi := phase1ReturnMinority n
      k := phase1ReturnMinority n + 2
      c₀ := 0
      εband := phase1LadderError C₁ n γ
      hpop := hreturnPop
      hreturnLo := hreturnPos
      hbHi := hbReturnPos
      hmaj := hbReturnMaj
      hgap := by omega
      hlower := by
        intro z hz
        omega
      hfailure := by
        intro z hz
        have hzTarget : ¬ phase1Target n ≤ z := by
          intro h
          exact hz ((phase1Target_le_iff n z).1 h)
        omega
      hband := hband
      herror := by rfl }

/-- The bridge family has exactly the type required by
`theorem1b_of_fewer`, with only its arithmetic side conditions. -/
noncomputable def hphase1_bridges_unconditional
    (C₁ n₀ : ℕ) (hn₀ : 3 ≤ n₀) :
    ∀ n γ x : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n → AssemblyInitial n γ x →
      Phase1BandBridge n x (phase1Horizon C₁ n γ)
        (phase1LadderBridgeError C₁ n γ) := by
  intro n γ x hn hγ hsize hx
  exact phase1_bridge_unconditional C₁ n γ x (hn₀.trans hn) hγ hsize hx

#print axioms phase1LadderSeed_le_gap
#print axioms phase1LadderSeed_ge_two
#print axioms phase1LadderLevel_zero_le_initial
#print axioms phase1Target_add_two_le
#print axioms phase1BandLo_lt_ladderLevel
#print axioms phase1LadderLower_succ
#print axioms phase1LadderLower_arithmetic
#print axioms phase1LadderLevel_mono
#print axioms phase1LadderLevel_final
#print axioms phase1LadderHorizon_sum
#print axioms phase1LadderUpper_phase_bound
#print axioms phase1LadderPhi_lt_one
#print axioms phase1_ladder_band_rung
#print axioms phase1_ladder_rung
#print axioms phase1_ladder_chain
#print axioms phase1_ladder_reaches
#print axioms phase1_reaches_unconditional
#print axioms phase1EndpointBandChain_eq_triChain
#print axioms phase1EndpointBandCount_failure_eq_triChain
#print axioms Reaches.to_phase1EndpointBandCount
#print axioms Reaches.to_phase1EndpointBandCount_pred
#print axioms phase1_ladder_band_chain
#print axioms phase1_ladder_band_reaches
#print axioms phase1_bridge_unconditional
#print axioms hphase1_bridges_unconditional

end Tri
