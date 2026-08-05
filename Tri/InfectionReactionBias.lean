/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Basic
import Tri.InfectionKernel

/-!
# Directional bias of productive active infection reactions

Among the two productive all-active reactions, `activeXXY` converts a `Y`
to an `X`, while `activeXYY` converts an `X` to a `Y`.  Before the active
`Y-X` gap exceeds `G`, and once at least `a` molecules are active, the adverse
type-(2) mass is at most `(1/2 + G/a)` of their combined mass.

The slightly relaxed denominator `a` absorbs the two removed participants in
the exact conditional probability `(ay-1)/(ax+ay-2)`.  The assumption
`4 ≤ a` is precisely what licenses that relaxation.
-/

namespace Tri

open scoped ENNReal

/-- Cross-multiplied natural-number core of the type-(2) bias bound. -/
theorem typeTwo_weight_bias_nat
    (a G x y : ℕ)
    (ha : 4 ≤ a)
    (hactive : a ≤ x + y)
    (hgap : y ≤ x + G) :
    2 * a * (x * Nat.choose y 2) ≤
      (a + 2 * G) *
        (Nat.choose x 2 * y + x * Nat.choose y 2) := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  have hx1 : 1 ≤ x := by omega
  have hy1 : 1 ≤ y := by omega
  have htwoX := two_mul_choose_two x
  have htwoY := two_mul_choose_two y
  have hchooseX :
      2 * (Nat.choose x 2 : ℝ) =
        (x : ℝ) * ((x : ℝ) - 1) := by
    exact_mod_cast htwoX
  have hchooseY :
      2 * (Nat.choose y 2 : ℝ) =
        (y : ℝ) * ((y : ℝ) - 1) := by
    exact_mod_cast htwoY
  have haR : (4 : ℝ) ≤ (a : ℝ) := by
    exact_mod_cast ha
  have hactiveR :
      (a : ℝ) ≤ (x : ℝ) + (y : ℝ) := by
    exact_mod_cast hactive
  have hgapR :
      (y : ℝ) ≤ (x : ℝ) + (G : ℝ) := by
    exact_mod_cast hgap
  have hroom :
      (a : ℝ) ≤
        2 * ((x : ℝ) + (y : ℝ) - 2) := by
    nlinarith
  have hgapScaled :
      (a : ℝ) * ((y : ℝ) - (x : ℝ)) ≤
        (a : ℝ) * (G : ℝ) := by
    exact
      mul_le_mul_of_nonneg_left
        (by linarith) (by positivity)
  have hroomScaled :
      (a : ℝ) * (G : ℝ) ≤
        2 * (G : ℝ) *
          ((x : ℝ) + (y : ℝ) - 2) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hroom
        (by positivity : (0 : ℝ) ≤ (G : ℝ))
    nlinarith
  have hcore :
      2 * (a : ℝ) * ((y : ℝ) - 1) ≤
        ((a : ℝ) + 2 * (G : ℝ)) *
          (((x : ℝ) - 1) + ((y : ℝ) - 1)) := by
    nlinarith
  have hmul :=
    mul_le_mul_of_nonneg_left hcore
      (by
        positivity :
        (0 : ℝ) ≤ (x : ℝ) * (y : ℝ) / 2)
  have hreal :
      2 * (a : ℝ) *
          ((x : ℝ) * (Nat.choose y 2 : ℝ)) ≤
        ((a : ℝ) + 2 * (G : ℝ)) *
          ((Nat.choose x 2 : ℝ) * (y : ℝ) +
            (x : ℝ) * (Nat.choose y 2 : ℝ)) := by
    rw [
      show
        (Nat.choose x 2 : ℝ) =
          (x : ℝ) * ((x : ℝ) - 1) / 2 by
        nlinarith [hchooseX],
      show
        (Nat.choose y 2 : ℝ) =
          (y : ℝ) * ((y : ℝ) - 1) / 2 by
        nlinarith [hchooseY]]
    nlinarith [hmul]
  exact_mod_cast hreal

/-- Raw mass of productive type (1), which converts `Y` to `X`. -/
noncomputable def infectionTypeOneMass
    (s : InfectionCfg) (h : 3 ≤ s.total) : ℝ≥0∞ :=
  infectionEventPMF s h .activeXXY

/-- Raw mass of productive type (2), which converts `X` to `Y`. -/
noncomputable def infectionTypeTwoMass
    (s : InfectionCfg) (h : 3 ≤ s.total) : ℝ≥0∞ :=
  infectionEventPMF s h .activeXYY

/-- Combined raw mass of the two opinion-changing active reactions. -/
noncomputable def infectionProductiveActiveMass
    (s : InfectionCfg) (h : 3 ≤ s.total) : ℝ≥0∞ :=
  infectionTypeOneMass s h + infectionTypeTwoMass s h

/-- Statewise type-(2) bias bound on the raw interaction law. -/
theorem infectionTypeTwoMass_le_bias
    (s : InfectionCfg) (h : 3 ≤ s.total)
    (a G : ℕ)
    (ha : 4 ≤ a)
    (hactive : a ≤ s.active)
    (hgap : s.ay ≤ s.ax + G) :
    infectionTypeTwoMass s h ≤
      ((a + 2 * G : ℕ) : ℝ≥0∞) /
          ((2 * a : ℕ) : ℝ≥0∞) *
        infectionProductiveActiveMass s h := by
  let w₁ : ℕ := Nat.choose s.ax 2 * s.ay
  let w₂ : ℕ := s.ax * Nat.choose s.ay 2
  let W : ℕ := w₁ + w₂
  let d : ℕ := Nat.choose s.total 3
  have hnat :
      2 * a * w₂ ≤ (a + 2 * G) * W := by
    exact
      typeTwo_weight_bias_nat
        a G s.ax s.ay ha hactive hgap
  have hcast :
      ((2 * a : ℕ) : ℝ≥0∞) *
          (w₂ : ℝ≥0∞) ≤
        (a + 2 * G : ℝ≥0∞) *
          (W : ℝ≥0∞) := by
    exact_mod_cast hnat
  have h2a0 :
      ((2 * a : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (show 2 * a ≠ 0 by omega)
  have h2atop :
      ((2 * a : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hweight :
      (w₂ : ℝ≥0∞) ≤
        ((a + 2 * G : ℕ) : ℝ≥0∞) /
            ((2 * a : ℕ) : ℝ≥0∞) *
          (W : ℝ≥0∞) := by
    rw [show
      ((a + 2 * G : ℕ) : ℝ≥0∞) /
            ((2 * a : ℕ) : ℝ≥0∞) *
          (W : ℝ≥0∞) =
        (((a + 2 * G : ℕ) : ℝ≥0∞) *
          (W : ℝ≥0∞)) /
            ((2 * a : ℕ) : ℝ≥0∞) by
      simp only [div_eq_mul_inv]
      ring]
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl h2a0) (Or.inl h2atop)).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      hcast
  simp only [infectionTypeTwoMass,
    infectionProductiveActiveMass,
    infectionTypeOneMass,
    infectionEventPMF_apply,
    InfectionEvent.weight]
  change
    (w₂ : ℝ≥0∞) / (d : ℝ≥0∞) ≤
      ((a + 2 * G : ℕ) : ℝ≥0∞) /
          ((2 * a : ℕ) : ℝ≥0∞) *
        ((w₁ : ℝ≥0∞) / (d : ℝ≥0∞) +
          (w₂ : ℝ≥0∞) / (d : ℝ≥0∞))
  rw [← ENNReal.add_div]
  rw [show
      (w₁ : ℝ≥0∞) + (w₂ : ℝ≥0∞) =
        (W : ℝ≥0∞) by
      simp [W]]
  rw [show
      ((a + 2 * G : ℕ) : ℝ≥0∞) /
            ((2 * a : ℕ) : ℝ≥0∞) *
          ((W : ℝ≥0∞) / (d : ℝ≥0∞)) =
        (((a + 2 * G : ℕ) : ℝ≥0∞) /
            ((2 * a : ℕ) : ℝ≥0∞) *
          (W : ℝ≥0∞)) / (d : ℝ≥0∞) by
      simp only [div_eq_mul_inv]
      ring]
  exact ENNReal.div_le_div_right hweight _

end Tri

#print axioms Tri.typeTwo_weight_bias_nat
#print axioms Tri.infectionTypeTwoMass_le_bias
