/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBMass
import Tri.SingleBLevel
import Tri.DoubleBResolution

/-!
# Single-B resolution masses for the direction port

The seven-event Single-B scheduler uses the doubled denominator
`2 * C(entities, 2)`.  The resolution labels carry doubled weights
`2*x*b` and `2*y*b`, so their normalized masses are literally the Double-B
resolution masses `x*b/C(n,2)` and `y*b/C(n,2)` on the fixed-population
ledger.
-/

namespace Tri

open scoped ENNReal

/-- Resolution-up mass for the oriented Single-B ledger: `x*b / C(n,2)`. -/
noncomputable def singleResolveUp {n : ℕ} (q : SingleLedger n) : ℝ≥0∞ :=
  ((q.cfg.1.x * q.cfg.1.b : ℕ) : ℝ≥0∞) / (Nat.choose n 2 : ℝ≥0∞)

/-- Resolution-down mass for the oriented Single-B ledger: `y*b / C(n,2)`. -/
noncomputable def singleResolveDown {n : ℕ} (q : SingleLedger n) : ℝ≥0∞ :=
  ((q.cfg.1.y * q.cfg.1.b : ℕ) : ℝ≥0∞) / (Nat.choose n 2 : ℝ≥0∞)

/-- Total resolution mass. -/
noncomputable def singleResolveMass {n : ℕ} (q : SingleLedger n) : ℝ≥0∞ :=
  singleResolveUp q + singleResolveDown q

/-- The Single-B up-resolution mass is definitionally Double-B's. -/
theorem singleResolveUp_eq_doubleResolveUp {n : ℕ} (q : SingleLedger n) :
    singleResolveUp q = doubleResolveUp q.cfg := rfl

/-- The Single-B down-resolution mass is definitionally Double-B's. -/
theorem singleResolveDown_eq_doubleResolveDown {n : ℕ} (q : SingleLedger n) :
    singleResolveDown q = doubleResolveDown q.cfg := rfl

/-- The five labels that do not change the corrected level by a resolution. -/
noncomputable def singleNeutralMass {n : ℕ} (q : SingleLedger n)
    (h : 2 ≤ q.cfg.1.x + q.cfg.1.y + q.cfg.1.b) : ℝ≥0∞ :=
  singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b h .xx
    + singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b h .xyToX
    + singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b h .xyToY
    + singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b h .yy
    + singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b h .bb

/-- The `xb` event mass is the literal `x*b/C(n,2)` resolution-up mass. -/
theorem singleResolveUp_eq_pmf {n : ℕ} (q : SingleLedger n)
    (h : 2 ≤ q.cfg.1.x + q.cfg.1.y + q.cfg.1.b) :
    singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b h .xb = singleResolveUp q := by
  have hpop : q.cfg.1.x + q.cfg.1.y + q.cfg.1.b = n := q.cfg.2
  rw [singleCompPMF_apply]
  unfold singleResolveUp
  rw [hpop]
  simp only [SingleComp.weight]
  simpa [Nat.cast_mul, mul_assoc] using
    ennreal_two_mul_div_two_mul
      ((q.cfg.1.x * q.cfg.1.b : ℕ) : ℝ≥0∞)
      ((Nat.choose n 2 : ℕ) : ℝ≥0∞)

/-- The `yb` event mass is the literal `y*b/C(n,2)` resolution-down mass. -/
theorem singleResolveDown_eq_pmf {n : ℕ} (q : SingleLedger n)
    (h : 2 ≤ q.cfg.1.x + q.cfg.1.y + q.cfg.1.b) :
    singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b h .yb = singleResolveDown q := by
  have hpop : q.cfg.1.x + q.cfg.1.y + q.cfg.1.b = n := q.cfg.2
  rw [singleCompPMF_apply]
  unfold singleResolveDown
  rw [hpop]
  simp only [SingleComp.weight]
  simpa [Nat.cast_mul, mul_assoc] using
    ennreal_two_mul_div_two_mul
      ((q.cfg.1.y * q.cfg.1.b : ℕ) : ℝ≥0∞)
      ((Nat.choose n 2 : ℕ) : ℝ≥0∞)

/-- Reuse of `SingleBMass`: the up-oriented creation plus up-resolution mass. -/
theorem singleCompPMF_up_mass_of_resolve {n : ℕ} (q : SingleLedger n)
    (h : 2 ≤ q.cfg.1.x + q.cfg.1.y + q.cfg.1.b) :
    singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b h .xyToX
        + singleResolveUp q =
      ((q.cfg.1.x * q.cfg.1.y + 2 * (q.cfg.1.x * q.cfg.1.b) : ℕ) : ℝ≥0∞) /
        ((2 * Nat.choose n 2 : ℕ) : ℝ≥0∞) := by
  have hpop : q.cfg.1.x + q.cfg.1.y + q.cfg.1.b = n := q.cfg.2
  rw [← singleResolveUp_eq_pmf q h]
  rw [singleCompPMF_up_mass q.cfg.1.x q.cfg.1.y q.cfg.1.b h, hpop]

/-- Reuse of `SingleBMass`: the down-oriented creation plus down-resolution mass. -/
theorem singleCompPMF_down_mass_of_resolve {n : ℕ} (q : SingleLedger n)
    (h : 2 ≤ q.cfg.1.x + q.cfg.1.y + q.cfg.1.b) :
    singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b h .xyToY
        + singleResolveDown q =
      ((q.cfg.1.x * q.cfg.1.y + 2 * (q.cfg.1.y * q.cfg.1.b) : ℕ) : ℝ≥0∞) /
        ((2 * Nat.choose n 2 : ℕ) : ℝ≥0∞) := by
  have hpop : q.cfg.1.x + q.cfg.1.y + q.cfg.1.b = n := q.cfg.2
  rw [← singleResolveDown_eq_pmf q h]
  rw [singleCompPMF_down_mass q.cfg.1.x q.cfg.1.y q.cfg.1.b h, hpop]

/-- The seven Single-B event masses sum to one. -/
theorem singleCompPMF_sum_seven (x y b : ℕ) (h : 2 ≤ x + y + b) :
    singleCompPMF x y b h .xx
      + singleCompPMF x y b h .xyToX
      + singleCompPMF x y b h .xyToY
      + singleCompPMF x y b h .yy
      + singleCompPMF x y b h .xb
      + singleCompPMF x y b h .yb
      + singleCompPMF x y b h .bb = 1 := by
  have htot : ∑ k : SingleComp, singleCompPMF x y b h k = 1 := by
    have h' := (singleCompPMF x y b h).tsum_coe
    rwa [tsum_fintype] at h'
  rw [show (Finset.univ : Finset SingleComp) =
      {SingleComp.xx, SingleComp.xyToX, SingleComp.xyToY, SingleComp.yy,
        SingleComp.xb, SingleComp.yb, SingleComp.bb} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at htot
  rw [← htot]
  ring

/-- Direction grouping of the seven-event alphabet. -/
theorem singleComp_sum_expand_direction (F : SingleComp → ℝ≥0∞) :
    ∑ k : SingleComp, F k
      = F .yb + (F .xx + F .xyToX + F .xyToY + F .yy + F .bb) + F .xb := by
  rw [show (Finset.univ : Finset SingleComp) =
      {SingleComp.xx, SingleComp.xyToX, SingleComp.xyToY, SingleComp.yy,
        SingleComp.xb, SingleComp.yb, SingleComp.bb} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

/-- The resolution/neutral direction masses partition one Single-B step. -/
theorem single_mass_sum {n : ℕ} (q : SingleLedger n)
    (h : 2 ≤ q.cfg.1.x + q.cfg.1.y + q.cfg.1.b) :
    singleResolveDown q + singleNeutralMass q h + singleResolveUp q = 1 := by
  have hsum := singleCompPMF_sum_seven q.cfg.1.x q.cfg.1.y q.cfg.1.b h
  have hup := singleResolveUp_eq_pmf q h
  have hdn := singleResolveDown_eq_pmf q h
  rw [← hup, ← hdn]
  unfold singleNeutralMass
  rw [← hsum]
  ring

/-- The blank factor cancels in the resolution odds cross-multiplication. -/
theorem single_resolution_odds_cross {n p qRat : ℕ} (s : SingleLedger n)
    (hguard : qRat * s.cfg.1.y ≤ p * s.cfg.1.x) :
    qRat * (s.cfg.1.y * s.cfg.1.b) ≤ p * (s.cfg.1.x * s.cfg.1.b) := by
  calc
    qRat * (s.cfg.1.y * s.cfg.1.b)
        = (qRat * s.cfg.1.y) * s.cfg.1.b := by ring
    _ ≤ (p * s.cfg.1.x) * s.cfg.1.b := Nat.mul_le_mul_right _ hguard
    _ = p * (s.cfg.1.x * s.cfg.1.b) := by ring

/-- The usable ratio guard: `q*y <= p*x` gives `down <= up*(p/q)`. -/
theorem single_dir_guard_ratio {n p qRat : ℕ} (s : SingleLedger n)
    (hq : qRat ≠ 0) (hguard : qRat * s.cfg.1.y ≤ p * s.cfg.1.x) :
    singleResolveDown s
      ≤ singleResolveUp s * ((p : ℝ≥0∞) / (qRat : ℝ≥0∞)) := by
  unfold singleResolveDown singleResolveUp
  have hq0 : (qRat : ℝ≥0∞) ≠ 0 := by simpa using hq
  have hqt : (qRat : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top qRat
  have hnat := single_resolution_odds_cross s hguard
  have hcast : (qRat : ℝ≥0∞) * ((s.cfg.1.y * s.cfg.1.b : ℕ) : ℝ≥0∞)
      ≤ (p : ℝ≥0∞) * ((s.cfg.1.x * s.cfg.1.b : ℕ) : ℝ≥0∞) := by
    have : ((qRat * (s.cfg.1.y * s.cfg.1.b) : ℕ) : ℝ≥0∞)
        ≤ ((p * (s.cfg.1.x * s.cfg.1.b) : ℕ) : ℝ≥0∞) := Nat.cast_le.mpr hnat
    simpa [Nat.cast_mul] using this
  rw [← ENNReal.mul_le_mul_iff_left hq0 hqt, mul_assoc,
    ENNReal.div_mul_cancel hq0 hqt]
  calc ((s.cfg.1.y * s.cfg.1.b : ℕ) : ℝ≥0∞)
        / (Nat.choose n 2 : ℝ≥0∞) * (qRat : ℝ≥0∞)
      = ((qRat : ℝ≥0∞) * ((s.cfg.1.y * s.cfg.1.b : ℕ) : ℝ≥0∞))
          / (Nat.choose n 2 : ℝ≥0∞) := by
        simp only [div_eq_mul_inv]
        ring
    _ ≤ ((p : ℝ≥0∞) * ((s.cfg.1.x * s.cfg.1.b : ℕ) : ℝ≥0∞))
          / (Nat.choose n 2 : ℝ≥0∞) := by gcongr
    _ = ((s.cfg.1.x * s.cfg.1.b : ℕ) : ℝ≥0∞)
          / (Nat.choose n 2 : ℝ≥0∞) * (p : ℝ≥0∞) := by
        simp only [div_eq_mul_inv]
        ring

end Tri

#print axioms Tri.singleResolveUp_eq_pmf
#print axioms Tri.singleResolveDown_eq_pmf
#print axioms Tri.singleResolveUp_eq_doubleResolveUp
#print axioms Tri.singleResolveDown_eq_doubleResolveDown
#print axioms Tri.singleCompPMF_up_mass_of_resolve
#print axioms Tri.singleCompPMF_down_mass_of_resolve
#print axioms Tri.singleCompPMF_sum_seven
#print axioms Tri.singleComp_sum_expand_direction
#print axioms Tri.single_mass_sum
#print axioms Tri.single_resolution_odds_cross
#print axioms Tri.single_dir_guard_ratio
