/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveClock
import Tri.RatioExp

/-!
# Concrete phase-0 raw-clock constants for multi-species Tri

At productive probability `p = 1/(8m)`, the test value `w = 1/2` and raw
horizon `32m(M+L)` make the probability of seeing at most `M` productive
events at most `exp(-L)`, as long as the phase-0 floor remains valid.
-/

namespace Tri.Multi

open scoped ENNReal

variable {m n : ℕ}

/-- Concrete raw interaction horizon for accumulating `M` productive events
with exponential slack `L`. -/
def multiPhase0ClockHorizon (m M L : ℕ) : ℕ :=
  32 * m * (M + L)

/-- The concrete Bernoulli clock expression is exponentially small. -/
theorem multiPhase0_clock_error_le
    (m M L : ℕ) (hm : 1 ≤ m) :
    ((1 - (1 : ℝ≥0∞) / (8 * m : ℕ)) +
          ((1 : ℝ≥0∞) / (8 * m : ℕ)) *
            ((1 : ℝ≥0∞) / 2)) ^
          multiPhase0ClockHorizon m M L /
        ((1 : ℝ≥0∞) / 2) ^ M ≤
      ENNReal.ofReal (Real.exp (-(L : ℝ))) := by
  let p : ℝ≥0∞ := (1 : ℝ≥0∞) / (8 * m : ℕ)
  let p' : ℝ≥0∞ := 1 - p
  let half : ℝ≥0∞ := (1 : ℝ≥0∞) / 2
  let x : ℝ≥0∞ := p * half
  let δ : ℝ := 1 / (16 * (m : ℝ))
  let δe : ℝ≥0∞ := ENNReal.ofReal δ
  let T : ℕ := multiPhase0ClockHorizon m M L
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hδ0 : 0 ≤ δ := by
    dsimp only [δ]
    positivity
  have hδ1 : δ ≤ 1 := by
    dsimp only [δ]
    rw [div_le_one (by positivity : (0 : ℝ) < 16 * m)]
    nlinarith
  have hpLe : p ≤ 1 := by
    dsimp only [p]
    have hdenNat : 1 ≤ 8 * m := by omega
    have hden : (1 : ℝ≥0∞) ≤ ((8 * m : ℕ) : ℝ≥0∞) := by
      exact_mod_cast hdenNat
    exact ENNReal.div_le_of_le_mul (by simpa using hden)
  have hppsum : p + p' = 1 := by
    dsimp only [p']
    rw [add_comm]
    exact tsub_add_cancel_of_le hpLe
  have hhalfCancel : (2 : ℝ≥0∞) * half = 1 := by
    dsimp only [half]
    rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  have hhalfAdd : half + half = 1 := by
    calc
      half + half = 2 * half := by ring
      _ = 1 := hhalfCancel
  have hxx : x + x = p := by
    dsimp only [x]
    calc
      p * half + p * half = p * (half + half) := by ring
      _ = p := by rw [hhalfAdd, mul_one]
  have hxδ : x = δe := by
    have hδe :
        δe = (1 : ℝ≥0∞) / (16 * m : ℕ) := by
      dsimp only [δe, δ]
      rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 16 * m),
        ENNReal.ofReal_one]
      congr 1
      norm_num [Nat.cast_mul, ENNReal.ofReal_natCast]
    rw [hδe]
    dsimp only [x, p, half]
    simp only [one_div]
    rw [← ENNReal.mul_inv
      (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ∞))
      (Or.inl (ENNReal.natCast_ne_top (8 * m)))]
    congr 1
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hphiSum : (p' + x) + δe ≤ 1 := by
    rw [← hxδ]
    calc
      (p' + x) + x = p' + (x + x) := by ring
      _ = p' + p := by rw [hxx]
      _ = 1 := by rw [add_comm, hppsum]
      _ ≤ 1 := le_rfl
  have hδtop : δe ≠ ⊤ := by
    dsimp only [δe]
    exact ENNReal.ofReal_ne_top
  have hphiSub : p' + x ≤ 1 - δe :=
    ENNReal.le_sub_of_add_le_right hδtop hphiSum
  have hsub : 1 - δe = ENNReal.ofReal (1 - δ) := by
    dsimp only [δe]
    rw [ENNReal.ofReal_sub 1 hδ0, ENNReal.ofReal_one]
  have hphi : p' + x ≤ ENNReal.ofReal (1 - δ) := by
    rwa [← hsub]
  have hnum :
      (p' + x) ^ T ≤
        ENNReal.ofReal (Real.exp (-(δ * (T : ℝ)))) :=
    enn_pow_le_ofReal_exp (p' + x) δ T hδ0 hδ1 hphi
  have hdiv :
      (p' + x) ^ T / half ^ M ≤
        ENNReal.ofReal (Real.exp (-(δ * (T : ℝ)))) /
          half ^ M :=
    ENNReal.div_le_div_right hnum _
  have hhalf :
      half = ENNReal.ofReal (1 / 2 : ℝ) := by
    dsimp only [half]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hquot :
      ENNReal.ofReal (Real.exp (-(δ * (T : ℝ)))) /
          half ^ M =
        ENNReal.ofReal
          (Real.exp
            (-(δ * (T : ℝ)) + (M : ℝ) * Real.log 2)) := by
    rw [hhalf, ← ENNReal.ofReal_pow
      (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [← ENNReal.ofReal_div_of_pos
      (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ M)]
    congr 2
    have hhalfReal :
        (1 / 2 : ℝ) ^ M =
          Real.exp (-(M : ℝ) * Real.log 2) := by
      rw [← Real.exp_log
        (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ M),
        Real.log_pow]
      have hlogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
        rw [one_div, Real.log_inv]
      rw [hlogHalf]
      congr 1
      ring
    rw [hhalfReal, ← Real.exp_sub]
    congr 1
    ring
  have hT :
      (T : ℝ) = 32 * (m : ℝ) * ((M : ℝ) + (L : ℝ)) := by
    dsimp only [T, multiPhase0ClockHorizon]
    push_cast
    ring
  have hδT :
      δ * (T : ℝ) = 2 * ((M : ℝ) + (L : ℝ)) := by
    rw [hT]
    dsimp only [δ]
    field_simp
    ring
  have hlog2 : Real.log 2 ≤ 1 := by
    have h :=
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hexponent :
      -(δ * (T : ℝ)) + (M : ℝ) * Real.log 2 ≤ -(L : ℝ) := by
    rw [hδT]
    have hscaled :
        (M : ℝ) * Real.log 2 ≤ (M : ℝ) :=
      by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hlog2 hM0
    nlinarith [show (0 : ℝ) ≤ L by positivity]
  change (p' + x) ^ T / half ^ M ≤ _
  exact hdiv.trans (hquot.le.trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexponent)))

/-- After `32m(M+L)` raw interactions, the mass of phase-0-live paths with at
most `M` productive events is at most `exp(-L)`. -/
theorem multiPhase0ClockStop_productivity_deadline
    (h3 : 3 ≤ n) (X : Species m) (hnm : 2 * m ≤ n)
    (M L : ℕ) (q0 : Config m n × ℕ)
    (hq0 : ¬ Phase0ClockBoundary X q0)
    (hc0 : q0.2 = 0) :
    (∑' q, if q.2 ≤ M ∧ ¬ Phase0ClockBoundary X q then
        iter (multiPhase0ClockStop h3 X)
          (multiPhase0ClockHorizon m M L) q0 q else 0) ≤
      ENNReal.ofReal (Real.exp (-(L : ℝ))) := by
  have hm : 1 ≤ m := by
    have := X.isLt
    omega
  have htail :=
    multiPhase0ClockStop_productivity_tail_floor
      h3 X hnm ((1 : ℝ≥0∞) / 2)
      (by norm_num) (by norm_num)
      (multiPhase0ClockHorizon m M L) M q0
  rw [if_neg hq0, hc0, pow_zero, mul_one] at htail
  exact htail.trans (multiPhase0_clock_error_le m M L hm)

/-- Conservative raw horizon for the paper's full phase-0 region.  Replacing
the proved floor `1/(108m)` by the smaller `1/(112m)=1/(8·14m)` lets us reuse
the preceding scalar estimate exactly. -/
def multiPaperPhase0ClockHorizon (m M L : ℕ) : ℕ :=
  multiPhase0ClockHorizon (14 * m) M L

/-- Concrete exponential clock estimate for the paper's full phase-0 floor. -/
theorem multiPaperPhase0_clock_error_le
    (m M L : ℕ) (hm : 1 ≤ m) :
    ((1 - (1 : ℝ≥0∞) / (108 * m : ℕ)) +
          ((1 : ℝ≥0∞) / (108 * m : ℕ)) *
            ((1 : ℝ≥0∞) / 2)) ^
          multiPaperPhase0ClockHorizon m M L /
        ((1 : ℝ≥0∞) / 2) ^ M ≤
      ENNReal.ofReal (Real.exp (-(L : ℝ))) := by
  let p : ℝ≥0∞ := (1 : ℝ≥0∞) / (108 * m : ℕ)
  let q : ℝ≥0∞ := (1 : ℝ≥0∞) / (8 * (14 * m) : ℕ)
  let half : ℝ≥0∞ := (1 : ℝ≥0∞) / 2
  have hpLe : p ≤ 1 := by
    dsimp only [p]
    have hdenNat : 1 ≤ 108 * m := by omega
    have hden : (1 : ℝ≥0∞) ≤ ((108 * m : ℕ) : ℝ≥0∞) := by
      exact_mod_cast hdenNat
    exact ENNReal.div_le_of_le_mul (by simpa using hden)
  have hqLe : q ≤ 1 := by
    dsimp only [q]
    have hdenNat : 1 ≤ 8 * (14 * m) := by omega
    have hden : (1 : ℝ≥0∞) ≤
        ((8 * (14 * m) : ℕ) : ℝ≥0∞) := by
      exact_mod_cast hdenNat
    exact ENNReal.div_le_of_le_mul (by simpa using hden)
  have hpSum : p + (1 - p) = 1 := by
    rw [add_comm]
    exact tsub_add_cancel_of_le hpLe
  have hqSum : q + (1 - q) = 1 := by
    rw [add_comm]
    exact tsub_add_cancel_of_le hqLe
  have hqp : q ≤ p := by
    dsimp only [q, p]
    have hden :
        ((108 * m : ℕ) : ℝ≥0∞) ≤
          ((8 * (14 * m) : ℕ) : ℝ≥0∞) := by
      exact_mod_cast (by omega : 108 * m ≤ 8 * (14 * m))
    exact ENNReal.div_le_div_left hden 1
  have hfactor :
      (1 - p) + p * half ≤ (1 - q) + q * half :=
    step_factor_antitone_ennreal
      hqSum hpSum (by dsimp only [half]; norm_num) hqp
  have hpow :
      ((1 - p) + p * half) ^
          multiPaperPhase0ClockHorizon m M L ≤
        ((1 - q) + q * half) ^
          multiPaperPhase0ClockHorizon m M L :=
    pow_le_pow_left' hfactor _
  calc
    ((1 - p) + p * half) ^
          multiPaperPhase0ClockHorizon m M L / half ^ M ≤
        ((1 - q) + q * half) ^
          multiPaperPhase0ClockHorizon m M L / half ^ M :=
      ENNReal.div_le_div_right hpow _
    _ ≤ ENNReal.ofReal (Real.exp (-(L : ℝ))) := by
      simpa only [q, half, multiPaperPhase0ClockHorizon] using
        multiPhase0_clock_error_le (14 * m) M L (by omega)

/-- Full paper phase 0: after the conservative raw deadline, phase-live paths
with at most `M` productive events have mass at most `exp(-L)`. -/
theorem multiPaperPhase0ClockStop_productivity_deadline
    (h3 : 3 ≤ n) (X : Species m) (D : ℕ)
    (hD : 3 * D ≤ n) (hnm : 6 * m ≤ n)
    (M L : ℕ) (q0 : Config m n × ℕ)
    (hq0 : ¬ PaperPhase0ClockBoundary X D q0)
    (hc0 : q0.2 = 0) :
    (∑' q, if q.2 ≤ M ∧
        ¬ PaperPhase0ClockBoundary X D q then
        iter (multiPaperPhase0ClockStop h3 X D)
          (multiPaperPhase0ClockHorizon m M L) q0 q else 0) ≤
      ENNReal.ofReal (Real.exp (-(L : ℝ))) := by
  have hm : 1 ≤ m := by
    have := X.isLt
    omega
  have htail :=
    multiPaperPhase0ClockStop_productivity_tail_floor
      h3 X D hD hnm ((1 : ℝ≥0∞) / 2)
      (by norm_num) (by norm_num)
      (multiPaperPhase0ClockHorizon m M L) M q0
  rw [if_neg hq0, hc0, pow_zero, mul_one] at htail
  exact htail.trans (multiPaperPhase0_clock_error_le m M L hm)

end Tri.Multi

#print axioms Tri.Multi.multiPhase0_clock_error_le
#print axioms Tri.Multi.multiPhase0ClockStop_productivity_deadline
#print axioms Tri.Multi.multiPaperPhase0_clock_error_le
#print axioms Tri.Multi.multiPaperPhase0ClockStop_productivity_deadline
