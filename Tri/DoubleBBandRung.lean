/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBBandParams
import Tri.Phase1Staged

/-!
# A concrete Double-B band rung

This file instantiates the abstract phase brick with:

* the midpoint harmonic base `phase1RungBase aLo bHiD`;
* its exact reciprocal resolution contraction `doubleDirectionEta`;
* productivity base `1/2`;
* the level-dependent floor `doubleBandProductivity`.

The resulting theorem has only natural-number band geometry left to
instantiate.
-/

namespace Tri

open scoped ENNReal

/-- The explicit error of one concrete Double-B band rung. -/
noncomputable def doubleBandRungError
    (n aLo bHiR bHiD hi k M T returnLo bHiRet kRet : ℕ) : ℝ≥0∞ :=
  let u : ℝ≥0∞ := (bHiD : ℝ≥0∞) / (aLo : ℝ≥0∞)
  let w : ℝ≥0∞ := phase1RungBase aLo bHiD
  let η : ℝ≥0∞ := doubleDirectionEta u w
  let pp : ℝ≥0∞ := doubleBandProductivity n aLo hi
  let pp' : ℝ≥0∞ := 1 - pp
  ((((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k
      + w ^ (aLo + k) / (w ^ (hi - 1) * η ^ M)
      + (pp' + pp * ((1 : ℝ≥0∞) / 2)) ^ T /
        ((1 : ℝ≥0∞) / 2) ^ ((2 * n - (aLo + k)) + 3 * M))
    + ((bHiRet : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ kRet)

/-- One fully instantiated Double-B band rung.  Only the integer geometry,
resolution budget `M`, and interaction horizon `T` remain visible. -/
theorem doubleBandRung
    (n : ℕ) (hn : 2 ≤ n)
    (aLo bHiR bHiD hi k M T : ℕ)
    (haLohi : aLo < hi) (hwidth : aLo + 2 ≤ hi)
    (hpopR : aLo + bHiR + 2 = 2 * n)
    (haLo : 0 < aLo) (hbHiR : 0 < bHiR)
    (hmajR : bHiR ≤ aLo)
    (heqD : aLo + bHiD = 2 * n)
    (hbiasD : bHiD < aLo)
    (hhi : hi ≤ 2 * n) (hnLo : n ≤ aLo + 1)
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
      (doubleBandRungError n aLo bHiR bHiD hi k M T
        returnLo bHiRet kRet) := by
  let u : ℝ≥0∞ := (bHiD : ℝ≥0∞) / (aLo : ℝ≥0∞)
  let w : ℝ≥0∞ := phase1RungBase aLo bHiD
  let η : ℝ≥0∞ := doubleDirectionEta u w
  let pp : ℝ≥0∞ := doubleBandProductivity n aLo hi
  let pp' : ℝ≥0∞ := 1 - pp
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
  have hw1 : w ≤ 1 := hwlt.le
  have hw0 : w ≠ 0 := hwSpec.1.ne'
  have hpp1 : pp ≤ 1 := by
    exact doubleBandProductivity_le_one n hn aLo hi hnLo hwidth hhi
  have hpp : pp + pp' = 1 := by
    exact doubleBandProductivity_add_compl n hn aLo hi hnLo hwidth hhi
  have hppT : pp ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hpp1
  have hpp'1 : pp' ≤ 1 := by
    exact tsub_le_self
  have hpp'T : pp' ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hpp'1
  have hBprod : ∀ q : DoubleTrace n,
      ¬ (q.cfg.1.doubleLevel ≤ aLo ∨ hi ≤ q.cfg.1.doubleLevel) →
      pp ≤ (dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2
          simp only [BiCfg.DoubleInv] at this
          omega) .xy
        + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2
          simp only [BiCfg.DoubleInv] at this
          omega) .xb
        + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2
          simp only [BiCfg.DoubleInv] at this
          omega) .yb) := by
    intro q hq
    exact doubleBandProductivity_le n hn aLo hi hnLo hhi q.cfg hq
  have hr := doubleState_band_phase_reaches_mono n hn
    aLo bHiR bHiD hi k M T haLohi hpopR haLo hbHiR hmajR
    heqD hbiasD.le hhi w η u rfl hηSpec.1 hηSpec.2.1
    hw1 hw0 hηSpec.2.2.1 hηSpec.2.2.2
    ((1 : ℝ≥0∞) / 2) pp pp'
    (by norm_num) (by norm_num) hpp (by norm_num) hppT hpp'T hBprod
    returnLo bHiRet kRet hpopRet hreturnLo hbHiRet hmajRet
    hlowerTarget htargetHi hreturnGap
  simpa only [doubleBandRungError, u, w, η, pp, pp', mul_one] using hr

end Tri
