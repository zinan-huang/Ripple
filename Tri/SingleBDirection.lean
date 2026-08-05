/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBResolutionPort
import Tri.SingleBGapRecovery
import Tri.SingleBCreationStep
import Tri.DoubleBDirection
import Tri.Freeze

/-!
# Single-B guarded direction supermartingale

The Single-B direction potential is the Double-B direction potential evaluated
on the corrected doubled level.  The corrected level is carried additively by
`SingleLedger.CorrectedLevel`; the potential keeps the same information without
using natural subtraction:

`Theta(q) = w^(2*x+b+cy) * v^cx * eta^(rx+ry)`, with `w*v = 1`.

Creation and inert labels leave this potential unchanged.  The two resolution
labels reproduce the Double-B scalar drift, with the regional ratio guard
`qRat*y <= p*x` supplying `down <= up*(p/qRat)`.
-/

namespace Tri

open scoped ENNReal

/-- The Single-B direction potential:
`w^(2x+b+cy) * v^cx * eta^(rx+ry)`. -/
noncomputable def singleTheta (w v η : ℝ≥0∞) {n : ℕ}
    (q : SingleLedger n) : ℝ≥0∞ :=
  w ^ (q.cfg.1.doubleLevel + q.cy) * v ^ q.cx * η ^ (q.rx + q.ry)

/-- On a state carrying corrected level `L`, `w*v=1` collapses the two encoded
factors to the Double-B form `w^L * eta^resolve`. -/
theorem singleTheta_of_correctedLevel {n L : ℕ} (w v η : ℝ≥0∞)
    (q : SingleLedger n) (hL : q.CorrectedLevel L) (hwv : w * v = 1) :
    singleTheta w v η q = w ^ L * η ^ (q.rx + q.ry) := by
  unfold SingleLedger.CorrectedLevel at hL
  unfold singleTheta
  rw [hL, pow_add]
  calc
    (w ^ L * w ^ q.cx) * v ^ q.cx * η ^ (q.rx + q.ry)
        = w ^ L * (w ^ q.cx * v ^ q.cx) * η ^ (q.rx + q.ry) := by ring
    _ = w ^ L * ((w * v) ^ q.cx) * η ^ (q.rx + q.ry) := by
        rw [← mul_pow]
    _ = w ^ L * η ^ (q.rx + q.ry) := by
        rw [hwv, one_pow]
        ring

/-- `XX` leaves `Theta` unchanged. -/
theorem singleTheta_xx {n : ℕ} (w v η : ℝ≥0∞) (q : SingleLedger n) :
    singleTheta w v η (SingleComp.nextSingleLedger q .xx)
      = singleTheta w v η q := by
  unfold singleTheta SingleComp.nextSingleLedger
  split_ifs <;> simp [SingleComp.next, SingleComp.cxInc, SingleComp.cyInc,
    SingleComp.rxInc, SingleComp.ryInc]

/-- `YY` leaves `Theta` unchanged. -/
theorem singleTheta_yy {n : ℕ} (w v η : ℝ≥0∞) (q : SingleLedger n) :
    singleTheta w v η (SingleComp.nextSingleLedger q .yy)
      = singleTheta w v η q := by
  unfold singleTheta SingleComp.nextSingleLedger
  split_ifs <;> simp [SingleComp.next, SingleComp.cxInc, SingleComp.cyInc,
    SingleComp.rxInc, SingleComp.ryInc]

/-- `BB` leaves `Theta` unchanged. -/
theorem singleTheta_bb {n : ℕ} (w v η : ℝ≥0∞) (q : SingleLedger n) :
    singleTheta w v η (SingleComp.nextSingleLedger q .bb)
      = singleTheta w v η q := by
  unfold singleTheta SingleComp.nextSingleLedger
  split_ifs <;> simp [SingleComp.next, SingleComp.cxInc, SingleComp.cyInc,
    SingleComp.rxInc, SingleComp.ryInc]

/-- `X+Y -> X+B` leaves `Theta` unchanged; the extra `w` is cancelled by the
extra `v`. -/
theorem singleTheta_xyToX {n : ℕ} (w v η : ℝ≥0∞) (q : SingleLedger n)
    (hwv : w * v = 1) :
    singleTheta w v η (SingleComp.nextSingleLedger q .xyToX)
      = singleTheta w v η q := by
  unfold singleTheta SingleComp.nextSingleLedger
  split_ifs with hw
  · rfl
  · rcases q with ⟨⟨⟨x, y, b⟩, hinv⟩, cx, cy, rx, ry⟩
    simp only [SingleComp.next, BiCfg.doubleLevel, SingleComp.cxInc,
      SingleComp.cyInc, SingleComp.rxInc, SingleComp.ryInc]
    simp only [Nat.add_zero]
    have hpow : 2 * x + (b + 1) + cy = 2 * x + b + cy + 1 := by omega
    rw [hpow, pow_succ, pow_succ]
    calc
      (w ^ (2 * x + b + cy) * w) * (v ^ cx * v) * η ^ (rx + ry)
          = (w * v) * (w ^ (2 * x + b + cy) * v ^ cx * η ^ (rx + ry)) := by ring
      _ = w ^ (2 * x + b + cy) * v ^ cx * η ^ (rx + ry) := by
          rw [hwv, one_mul]

/-- `X+Y -> Y+B` leaves `Theta` unchanged; the physical level drop is exactly
paid by the `cy` increment. -/
theorem singleTheta_xyToY {n : ℕ} (w v η : ℝ≥0∞) (q : SingleLedger n) :
    singleTheta w v η (SingleComp.nextSingleLedger q .xyToY)
      = singleTheta w v η q := by
  unfold singleTheta SingleComp.nextSingleLedger
  split_ifs with hw
  · rfl
  · rcases q with ⟨⟨⟨x, y, b⟩, hinv⟩, cx, cy, rx, ry⟩
    simp only [SingleComp.next, BiCfg.doubleLevel, SingleComp.weight,
      SingleComp.cxInc, SingleComp.cyInc, SingleComp.rxInc, SingleComp.ryInc] at hw ⊢
    simp only [Nat.add_zero] at hw ⊢
    have hx0 : x ≠ 0 := fun hx => hw (by simp [hx])
    have hx : 1 ≤ x := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hx0)
    have hpow : 2 * (x - 1) + (b + 1) + (cy + 1) = 2 * x + b + cy := by omega
    rw [hpow]

theorem singleTheta_xb_of_correctedLevel {n a : ℕ} (w v η : ℝ≥0∞)
    (q : SingleLedger n) (hL : q.CorrectedLevel (a + 1))
    (hw : SingleComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b .xb ≠ 0)
    (hwv : w * v = 1) :
    singleTheta w v η (SingleComp.nextSingleLedger q .xb)
      = w ^ (a + 2) * η ^ (q.rx + q.ry + 1) := by
  have hnext := SingleComp.nextSingleLedger_correctedLevel_xb q hL hw
  rw [singleTheta_of_correctedLevel w v η
    (SingleComp.nextSingleLedger q .xb) hnext hwv]
  unfold SingleComp.nextSingleLedger
  rw [dif_neg hw]
  simp only [SingleComp.rxInc, SingleComp.ryInc]
  ring

theorem singleTheta_yb_of_correctedLevel {n a : ℕ} (w v η : ℝ≥0∞)
    (q : SingleLedger n) (hL : q.CorrectedLevel (a + 1))
    (hw : SingleComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b .yb ≠ 0)
    (hwv : w * v = 1) :
    singleTheta w v η (SingleComp.nextSingleLedger q .yb)
      = w ^ a * η ^ (q.rx + q.ry + 1) := by
  have hnext := SingleComp.nextSingleLedger_correctedLevel_yb (Lambda := a) q hL hw
  rw [singleTheta_of_correctedLevel w v η
    (SingleComp.nextSingleLedger q .yb) hnext hwv]
  unfold SingleComp.nextSingleLedger
  rw [dif_neg hw]
  simp only [SingleComp.rxInc, SingleComp.ryInc]
  ring

/-- Expectation expansion for `Theta`, grouped as down/neutral/up at corrected
levels `a`, `a+1`, and `a+2`. -/
theorem singleLedgerStep_theta_expect (n : ℕ) (hn : 2 ≤ n) (q : SingleLedger n)
    (a : ℕ) (hL : q.CorrectedLevel (a + 1)) (w v η : ℝ≥0∞)
    (hwv : w * v = 1) :
    expect (singleLedgerStep n hn q) (singleTheta w v η)
      = singleResolveDown q * (w ^ a * η ^ (q.rx + q.ry + 1))
        + singleNeutralMass q (by
            have h := q.cfg.2
            simp only [BiCfg.DoubleInv] at h
            omega) * (w ^ (a + 1) * η ^ (q.rx + q.ry))
        + singleResolveUp q * (w ^ (a + 2) * η ^ (q.rx + q.ry + 1)) := by
  have hq2 : 2 ≤ q.cfg.1.x + q.cfg.1.y + q.cfg.1.b := by
    have h := q.cfg.2
    simp only [BiCfg.DoubleInv] at h
    omega
  rw [expect_singleLedgerStep, singleComp_sum_expand_direction]
  change
    singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hq2 .yb
        * singleTheta w v η (SingleComp.nextSingleLedger q .yb)
      + (singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hq2 .xx
          * singleTheta w v η (SingleComp.nextSingleLedger q .xx)
        + singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hq2 .xyToX
          * singleTheta w v η (SingleComp.nextSingleLedger q .xyToX)
        + singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hq2 .xyToY
          * singleTheta w v η (SingleComp.nextSingleLedger q .xyToY)
        + singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hq2 .yy
          * singleTheta w v η (SingleComp.nextSingleLedger q .yy)
        + singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hq2 .bb
          * singleTheta w v η (SingleComp.nextSingleLedger q .bb))
      + singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hq2 .xb
        * singleTheta w v η (SingleComp.nextSingleLedger q .xb)
      =
    singleResolveDown q * (w ^ a * η ^ (q.rx + q.ry + 1))
      + singleNeutralMass q hq2 * (w ^ (a + 1) * η ^ (q.rx + q.ry))
      + singleResolveUp q * (w ^ (a + 2) * η ^ (q.rx + q.ry + 1))
  set P := singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hq2 with hP
  have hqTheta :
      singleTheta w v η q = w ^ (a + 1) * η ^ (q.rx + q.ry) :=
    singleTheta_of_correctedLevel w v η q hL hwv
  have hxx : P .xx * singleTheta w v η (SingleComp.nextSingleLedger q .xx)
      = P .xx * (w ^ (a + 1) * η ^ (q.rx + q.ry)) := by
    rw [singleTheta_xx, hqTheta]
  have hxyX : P .xyToX * singleTheta w v η (SingleComp.nextSingleLedger q .xyToX)
      = P .xyToX * (w ^ (a + 1) * η ^ (q.rx + q.ry)) := by
    rw [singleTheta_xyToX w v η q hwv, hqTheta]
  have hxyY : P .xyToY * singleTheta w v η (SingleComp.nextSingleLedger q .xyToY)
      = P .xyToY * (w ^ (a + 1) * η ^ (q.rx + q.ry)) := by
    rw [singleTheta_xyToY, hqTheta]
  have hyy : P .yy * singleTheta w v η (SingleComp.nextSingleLedger q .yy)
      = P .yy * (w ^ (a + 1) * η ^ (q.rx + q.ry)) := by
    rw [singleTheta_yy, hqTheta]
  have hbb : P .bb * singleTheta w v η (SingleComp.nextSingleLedger q .bb)
      = P .bb * (w ^ (a + 1) * η ^ (q.rx + q.ry)) := by
    rw [singleTheta_bb, hqTheta]
  have hxb : P .xb * singleTheta w v η (SingleComp.nextSingleLedger q .xb)
      = singleResolveUp q * (w ^ (a + 2) * η ^ (q.rx + q.ry + 1)) := by
    by_cases hw : SingleComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b .xb = 0
    · have hp0 : P .xb = 0 := by
        rw [hP]
        exact singleCompPMF_zero_of_weight_zero hw
      rw [← singleResolveUp_eq_pmf q hq2, ← hP, hp0]
      simp
    · rw [hP, singleResolveUp_eq_pmf q hq2,
        singleTheta_xb_of_correctedLevel w v η q hL hw hwv]
  have hyb : P .yb * singleTheta w v η (SingleComp.nextSingleLedger q .yb)
      = singleResolveDown q * (w ^ a * η ^ (q.rx + q.ry + 1)) := by
    by_cases hw : SingleComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b .yb = 0
    · have hp0 : P .yb = 0 := by
        rw [hP]
        exact singleCompPMF_zero_of_weight_zero hw
      rw [← singleResolveDown_eq_pmf q hq2, ← hP, hp0]
      simp
    · rw [hP, singleResolveDown_eq_pmf q hq2,
        singleTheta_yb_of_correctedLevel w v η q hL hw hwv]
  rw [hxx, hxyX, hxyY, hyy, hbb, hxb, hyb]
  unfold singleNeutralMass
  ring

/-- Guarded one-step Single-B direction drift.  The ratio guard is deliberately
regional: callers supply `qRat*y <= p*x` only at live states. -/
theorem singleLedgerStep_theta_super (n : ℕ) (hn : 2 ≤ n) (q : SingleLedger n)
    (a p qRat : ℕ) (hL : q.CorrectedLevel (a + 1)) (w v η u : ℝ≥0∞)
    (hu : u = (p : ℝ≥0∞) / (qRat : ℝ≥0∞))
    (hq : qRat ≠ 0) (hguard : qRat * q.cfg.1.y ≤ p * q.cfg.1.x)
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hwv : w * v = 1) (hwt : w ≠ ⊤) (hηt : η ≠ ⊤) :
    expect (singleLedgerStep n hn q) (singleTheta w v η) ≤ singleTheta w v η q := by
  have hq2 : 2 ≤ q.cfg.1.x + q.cfg.1.y + q.cfg.1.b := by
    have h := q.cfg.2
    simp only [BiCfg.DoubleInv] at h
    omega
  set dn := singleResolveDown q with hdn
  set neu := singleNeutralMass q hq2 with hneu
  set up := singleResolveUp q with hup
  have hexp : expect (singleLedgerStep n hn q) (singleTheta w v η)
      = dn * (w ^ a * η ^ (q.rx + q.ry + 1))
        + neu * (w ^ (a + 1) * η ^ (q.rx + q.ry))
        + up * (w ^ (a + 2) * η ^ (q.rx + q.ry + 1)) := by
    simpa [hdn, hneu, hup] using
      singleLedgerStep_theta_expect n hn q a hL w v η hwv
  rw [hexp]
  have hdle : dn ≤ up * u := by
    rw [hu]
    exact single_dir_guard_ratio q hq hguard
  have hsum : dn + neu + up = 1 := by
    simpa [hdn, hneu, hup] using single_mass_sum q hq2
  have hdt : dn ≠ ⊤ := by
    rw [hdn, ← singleResolveDown_eq_pmf q hq2]
    exact PMF.apply_ne_top _ _
  have hut : up ≠ ⊤ := by
    rw [hup, ← singleResolveUp_eq_pmf q hq2]
    exact PMF.apply_ne_top _ _
  have hnt : neu ≠ ⊤ := by
    intro ht
    rw [ht] at hsum
    simp at hsum
  have huT : u ≠ ⊤ := by
    rw [hu]
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top p)
      (by simpa using hq)
  have hscalar : neu * w + η * (dn + up * w ^ 2) ≤ w :=
    doubleDir_scalar dn neu up u w η hsum hdle hrel hwη
      hdt hnt hut hwt hηt huT
  have hLhs :
      dn * (w ^ a * η ^ (q.rx + q.ry + 1))
        + neu * (w ^ (a + 1) * η ^ (q.rx + q.ry))
        + up * (w ^ (a + 2) * η ^ (q.rx + q.ry + 1))
        = (w ^ a * η ^ (q.rx + q.ry)) * (neu * w + η * (dn + up * w ^ 2)) := by
    ring
  have hRhs :
      singleTheta w v η q = (w ^ a * η ^ (q.rx + q.ry)) * w := by
    rw [singleTheta_of_correctedLevel w v η q hL hwv]
    ring
  rw [hLhs, hRhs]
  gcongr

/-- Arbitrary frozen-set version.  Frozen states satisfy the step by
`expect_pure`; live states discharge the corrected-level and ratio hypotheses
through `hlive`. -/
theorem singleTheta_frozen_super (n : ℕ) (hn : 2 ≤ n)
    (P : SingleLedger n → Prop) [DecidablePred P]
    (p qRat : ℕ) (w v η u : ℝ≥0∞)
    (hu : u = (p : ℝ≥0∞) / (qRat : ℝ≥0∞))
    (hq : qRat ≠ 0)
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hwv : w * v = 1) (hwt : w ≠ ⊤) (hηt : η ≠ ⊤)
    (hlive : ∀ q, ¬ P q →
      ∃ a : ℕ, q.CorrectedLevel (a + 1) ∧ qRat * q.cfg.1.y ≤ p * q.cfg.1.x) :
    ∀ q, expect (freeze P (singleLedgerStep n hn) q) (singleTheta w v η)
      ≤ singleTheta w v η q := by
  intro q
  by_cases hP : P q
  · rw [freeze_of_mem q hP, expect_pure]
  · rw [freeze_of_not_mem q hP]
    obtain ⟨a, hL, hguard⟩ := hlive q hP
    exact singleLedgerStep_theta_super n hn q a p qRat hL w v η u
      hu hq hguard hrel hwη hwv hwt hηt

/-- Iterated supermartingale corollary for any frozen Single-B direction chain. -/
theorem singleTheta_frozen_iter_le (n : ℕ) (hn : 2 ≤ n)
    (P : SingleLedger n → Prop) [DecidablePred P]
    (p qRat T : ℕ) (w v η u : ℝ≥0∞)
    (hu : u = (p : ℝ≥0∞) / (qRat : ℝ≥0∞))
    (hq : qRat ≠ 0)
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hwv : w * v = 1) (hwt : w ≠ ⊤) (hηt : η ≠ ⊤)
    (hlive : ∀ q, ¬ P q →
      ∃ a : ℕ, q.CorrectedLevel (a + 1) ∧ qRat * q.cfg.1.y ≤ p * q.cfg.1.x)
    (q₀ : SingleLedger n) :
    expect (iter (freeze P (singleLedgerStep n hn)) T q₀) (singleTheta w v η)
      ≤ singleTheta w v η q₀ := by
  have hiter := expect_iter_le (freeze P (singleLedgerStep n hn))
    (singleTheta w v η) 1
    (by
      intro q
      rw [one_mul]
      exact singleTheta_frozen_super n hn P p qRat w v η u
        hu hq hrel hwη hwv hwt hηt hlive q)
    T q₀
  simpa using hiter

section Inhabitation

example :
    let q : SingleLedger 4 :=
      { cfg := ⟨⟨2, 1, 1⟩, by norm_num [BiCfg.DoubleInv]⟩
        cx := 0
        cy := 0
        rx := 0
        ry := 0 }
    expect (singleLedgerStep 4 (by norm_num) q)
        (singleTheta ((1 : ℝ≥0∞) / 2) 2 1)
      ≤ singleTheta ((1 : ℝ≥0∞) / 2) 2 1 q := by
  intro q
  refine singleLedgerStep_theta_super
    (n := 4) (hn := by norm_num) (q := q) (a := 4) (p := 1) (qRat := 2)
    (w := (1 : ℝ≥0∞) / 2) (v := 2)
    (η := 1) (u := (1 : ℝ≥0∞) / 2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · norm_num [SingleLedger.CorrectedLevel, BiCfg.doubleLevel]
  · norm_num
  · norm_num
  · norm_num
  · ring
  · norm_num
  · rw [mul_comm]
    rw [one_div]
    exact ENNReal.mul_inv_cancel (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
  · exact ENNReal.div_ne_top ENNReal.one_ne_top (by norm_num)
  · exact ENNReal.one_ne_top

example :
    let q : SingleLedger 3 :=
      { cfg := ⟨⟨1, 1, 1⟩, by norm_num [BiCfg.DoubleInv]⟩
        cx := 0
        cy := 0
        rx := 0
        ry := 0 }
    singleTheta ((1 : ℝ≥0∞) / 2) 2 1
        (SingleComp.nextSingleLedger q .xyToX)
      = singleTheta ((1 : ℝ≥0∞) / 2) 2 1 q := by
  intro q
  exact singleTheta_xyToX ((1 : ℝ≥0∞) / 2) 2 1 q (by
    rw [mul_comm]
    rw [one_div]
    exact ENNReal.mul_inv_cancel (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num))

end Inhabitation

end Tri

#print axioms Tri.singleTheta_of_correctedLevel
#print axioms Tri.singleTheta_xx
#print axioms Tri.singleTheta_yy
#print axioms Tri.singleTheta_bb
#print axioms Tri.singleTheta_xyToX
#print axioms Tri.singleTheta_xyToY
#print axioms Tri.singleTheta_xb_of_correctedLevel
#print axioms Tri.singleTheta_yb_of_correctedLevel
#print axioms Tri.singleLedgerStep_theta_expect
#print axioms Tri.singleLedgerStep_theta_super
#print axioms Tri.singleTheta_frozen_super
#print axioms Tri.singleTheta_frozen_iter_le
