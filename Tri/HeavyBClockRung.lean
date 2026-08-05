/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBClockConstants

/-!
# A concrete Heavy-B rung using the joint raw-interaction clock

Direction, ruin, and upper-return parameters are unchanged from the Heavy-B
band rung.  The productive-clock starvation term is replaced by the joint
normal/blank occupation-clock envelope.
-/

namespace Tri

open scoped ENNReal

/-- Exact finite error of one concrete joint-clock Heavy-B rung, with the two
clock terms already replaced by their uniform envelope. -/
noncomputable def heavyBandJointRungError
    (n g a B aLo bHiR _hi thr k M
      returnLo bHiRet kRet : ℕ) : ℝ≥0∞ :=
  let w : ℝ≥0∞ := ENNReal.ofReal (heavyBandW a B)
  let η : ℝ≥0∞ := ENNReal.ofReal (heavyBandEta a B)
  ((((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k +
      w ^ (aLo + k) / (w ^ thr * η ^ M) +
      heavyJointClockEnvelope n g M) +
    ((bHiRet : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ kRet)

/-- The exact joint-clock phase error is below the concrete envelope used by
the public rung. -/
theorem heavyBandJointClockError_le_envelope
    (n g a B aLo bHiR hi thr k M
      returnLo bHiRet kRet : ℕ)
    (hn : 0 < n) (hg : g ≤ n)
    (hstart : aLo + k ≤ hi)
    (hwidth : hi ≤ aLo + k + g) :
    heavyBandJointClockError
        n g aLo bHiR hi thr k M
        (heavyClockBudget n M) (heavyClockHalfHorizon n M)
        (ENNReal.ofReal (heavyBandW a B))
        (ENNReal.ofReal (heavyBandEta a B))
        returnLo bHiRet kRet ≤
      heavyBandJointRungError
        n g a B aLo bHiR hi thr k M returnLo bHiRet kRet := by
  unfold heavyBandJointClockError heavyBandJointRungError
  exact add_le_add
    (add_le_add le_rfl
      (heavyJointClockError_le
        n g (aLo + k) hi M hn hg hstart hwidth))
    le_rfl

/-- One fully instantiated early Heavy-B band rung with the joint clock.  Only
natural-number geometry and clock-budget witnesses remain visible. -/
theorem heavyBandJointRung
    (n : ℕ) (hn : 3 ≤ n)
    (g a B aLo bHiR hi thr k M cL : ℕ)
    (hg : g ≤ n)
    (hfloorClock : n + g ≤ 2 * (aLo + 1))
    (hsmall : 16 * hi ≤ 9 * n)
    (ha : 0 < a) (hB : 0 < B)
    (hparam : a + 2 * B = n)
    (_hquarter : 4 * B ≤ n)
    (hfloorGuard : n + 2 * B ≤ 2 * (aLo + 1))
    (haLohi : aLo < hi)
    (hthr : thr + 1 = hi)
    (hstartClock : aLo + k ≤ hi)
    (hwidthClock : hi ≤ aLo + k + g)
    (hstartCo : aLo + k + cL = n)
    (hK : cL + 3 * M ≤ heavyClockBudget n M)
    (hpopR : aLo + bHiR + 2 = n)
    (haLo : 0 < aLo) (hbHiR : 0 < bHiR)
    (hmajR : bHiR ≤ aLo)
    (returnLo bHiRet kRet : ℕ)
    (hpopRet : returnLo + bHiRet + 2 = n)
    (hreturnLo : 0 < returnLo) (hbHiRet : 0 < bHiRet)
    (hmajRet : bHiRet ≤ returnLo)
    (hlowerTarget : aLo < returnLo + 1)
    (htargetHi : returnLo + 1 ≤ hi)
    (hreturnGap : returnLo + kRet ≤ hi) :
    Reaches (heavyStateStep n) (heavyClockHorizon n M)
      (fun s => aLo + k ≤ BiCfg.heavyLevel s.1)
      (fun s => returnLo + 1 ≤ BiCfg.heavyLevel s.1)
      (heavyBandJointRungError
        n g a B aLo bHiR hi thr k M returnLo bHiRet kRet) := by
  let w : ℝ≥0∞ := ENNReal.ofReal (heavyBandW a B)
  let η : ℝ≥0∞ := ENNReal.ofReal (heavyBandEta a B)
  let u : ℝ≥0∞ := (a : ℝ≥0∞) / ((a + 4 * B : ℕ) : ℝ≥0∞)
  have hparams := heavyBand_params_enn ha hB hparam
  dsimp only at hparams
  rcases hparams with ⟨hrel, hwη, hw1, hw0, hη1, hηt, _hwt⟩
  have hq : a + 4 * B ≠ 0 := by omega
  have hguard : ∀ s : HeavyTrace n,
      aLo + 1 ≤ BiCfg.heavyLevel s.cfg.1 →
      BiCfg.heavyLevel s.cfg.1 + 1 ≤ hi →
      (a + 4 * B) * s.cfg.1.y ≤ a * s.cfg.1.x := by
    intro s hlive _
    exact heavyBand_window_guard_params hparam hfloorGuard s hlive
  have hr :=
    heavyState_band_phase_reaches_joint_clock_mono
      n hn g aLo bHiR hi thr k M
      (heavyClockBudget n M)
      (heavyClockHorizon n M) (heavyClockHalfHorizon n M) cL
      hfloorClock hsmall (two_heavyClockHalfHorizon n M).le
      haLohi hthr hstartCo hK
      hpopR haLo hbHiR hmajR
      a (a + 4 * B) hq hguard
      w η u rfl hrel hwη hw1 hw0 hη1 hηt
      returnLo bHiRet kRet hpopRet hreturnLo hbHiRet hmajRet
      hlowerTarget htargetHi hreturnGap
  exact hr.mono_error
    (by
      simpa only [w, η] using
        heavyBandJointClockError_le_envelope
          n g a B aLo bHiR hi thr k M returnLo bHiRet kRet
          (by omega) hg hstartClock hwidthClock)

/-- Inhabitation gate for the early-ladder-shaped Heavy-B joint-clock rung. -/
example :
    Reaches (heavyStateStep 3200) (heavyClockHorizon 3200 10)
      (fun s => 1739 ≤ BiCfg.heavyLevel s.1)
      (fun s => 1740 ≤ BiCfg.heavyLevel s.1)
      (heavyBandJointRungError
        3200 80 3120 40 1639 1559 1780 1779 100 10
        1739 1459 1) := by
  exact heavyBandJointRung
    (n := 3200) (hn := by norm_num)
    (g := 80) (a := 3120) (B := 40)
    (aLo := 1639) (bHiR := 1559)
    (hi := 1780) (thr := 1779)
    (k := 100) (M := 10) (cL := 1461)
    (hg := by norm_num)
    (hfloorClock := by norm_num)
    (hsmall := by norm_num)
    (ha := by norm_num) (hB := by norm_num)
    (hparam := by norm_num)
    (_hquarter := by norm_num)
    (hfloorGuard := by norm_num)
    (haLohi := by norm_num)
    (hthr := by norm_num)
    (hstartClock := by norm_num)
    (hwidthClock := by norm_num)
    (hstartCo := by norm_num)
    (hK := by norm_num [heavyClockBudget])
    (hpopR := by norm_num)
    (haLo := by norm_num) (hbHiR := by norm_num)
    (hmajR := by norm_num)
    (returnLo := 1739) (bHiRet := 1459) (kRet := 1)
    (hpopRet := by norm_num)
    (hreturnLo := by norm_num) (hbHiRet := by norm_num)
    (hmajRet := by norm_num)
    (hlowerTarget := by norm_num)
    (htargetHi := by norm_num)
    (hreturnGap := by norm_num)

end Tri

#print axioms Tri.heavyBandJointClockError_le_envelope
#print axioms Tri.heavyBandJointRung
