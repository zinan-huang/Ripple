/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBClockProjection
import Tri.DoubleBBandParams
import Tri.Phase1Staged

/-!
# A concrete Double-B rung using the joint raw-interaction clock

This is the replacement for the early-band use of `doubleBandRung`.  Direction,
ruin, and upper-return parameters are unchanged; the obsolete level-only
productivity term is replaced by the normal/blank occupation errors.
-/

namespace Tri

open scoped ENNReal

/-- Exact finite error of one concrete joint-clock Double-B rung. -/
noncomputable def doubleBandJointRungError
    (n g aLo bHiR bHiD hi k M H
      returnLo bHiRet kRet : ℕ) : ℝ≥0∞ :=
  let u : ℝ≥0∞ := (bHiD : ℝ≥0∞) / (aLo : ℝ≥0∞)
  let w : ℝ≥0∞ := phase1RungBase aLo bHiD
  let η : ℝ≥0∞ := doubleDirectionEta u w
  doubleBandJointClockError
    n g aLo bHiR hi k M H w η returnLo bHiRet kRet

/-- One fully instantiated early Double-B band rung with the joint clock.
Only natural-number geometry and clock budgets remain visible. -/
theorem doubleBandJointRung
    (n : ℕ) (hn : 2 ≤ n)
    (g aLo bHiR bHiD hi k M T H : ℕ)
    (hnLo : n + g ≤ aLo)
    (hsmall : 8 * hi ≤ 9 * n)
    (hH : 2 * H ≤ T)
    (haLohi : aLo < hi)
    (hpopR : aLo + bHiR + 2 = 2 * n)
    (haLo : 0 < aLo) (hbHiR : 0 < bHiR)
    (hmajR : bHiR ≤ aLo)
    (heqD : aLo + bHiD = 2 * n)
    (hbiasD : bHiD < aLo)
    (hhi : hi ≤ 2 * n)
    (returnLo bHiRet kRet : ℕ)
    (hpopRet : returnLo + bHiRet + 2 = 2 * n)
    (hreturnLo : 0 < returnLo) (hbHiRet : 0 < bHiRet)
    (hmajRet : bHiRet ≤ returnLo)
    (hlowerTarget : aLo < returnLo + 1)
    (htargetHi : returnLo + 1 ≤ hi)
    (hreturnGap : returnLo + kRet ≤ hi) :
    Reaches (doubleStateStep n hn) T
      (fun s => aLo + k ≤ s.1.doubleLevel)
      (fun s => returnLo + 1 ≤ s.1.doubleLevel)
      (doubleBandJointRungError
        n g aLo bHiR bHiD hi k M H
        returnLo bHiRet kRet) := by
  let u : ℝ≥0∞ := (bHiD : ℝ≥0∞) / (aLo : ℝ≥0∞)
  let w : ℝ≥0∞ := phase1RungBase aLo bHiD
  let η : ℝ≥0∞ := doubleDirectionEta u w
  have hwSpec := phase1RungBase_spec haLo hbiasD
  have hu0 : 0 < u := by
    unfold u
    apply ENNReal.div_pos
    · simp only [ne_eq, Nat.cast_eq_zero]
      omega
    · exact ENNReal.natCast_ne_top _
  have huw : u < w := by
    simpa only [u, w] using hwSpec.2.2
  have hwlt : w < 1 := by
    simpa only [w] using hwSpec.2.1
  have hηSpec := doubleDirectionEta_spec hu0 huw hwlt
  have hr :=
    doubleState_band_phase_reaches_joint_clock_mono
      n hn g aLo bHiR bHiD hi k M T H
      hnLo hsmall hH haLohi hpopR haLo hbHiR hmajR
      heqD hbiasD.le hhi w η u rfl hηSpec.1 hηSpec.2.1
      hwlt.le hwSpec.1.ne' hηSpec.2.2.1 hηSpec.2.2.2
      returnLo bHiRet kRet hpopRet hreturnLo hbHiRet hmajRet
      hlowerTarget htargetHi hreturnGap
  simpa only [doubleBandJointRungError, u, w, η] using hr

end Tri

#print axioms Tri.doubleBandJointRung
