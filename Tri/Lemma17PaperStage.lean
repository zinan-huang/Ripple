/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17DoublingClock
import Tri.Lemma17PoolTail

/-!
# A paper-scale Lemma 17 doubling stage

The stage horizon is `cStar * n`.  A natural parameter `r` upper-bounds the
cubic all-active mean through the subtraction-free condition `A³ ≤ r n²`.
The active-reaction cap is `2 cStar r`, while the label, direction, and gap
budgets use the paper constants `1`, `2`, and `19`.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- The four explicit exceptional terms for one paper-scale stage. -/
noncomputable def lemma17StageError
    (a q cStar rho r : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(a : ℝ))) +
    lemma16UrnError q +
    ENNReal.ofReal
      (Real.exp
        (-(((cStar * r : ℕ) : ℝ) / 20))) +
    ENNReal.ofReal
      (Real.exp
        (-(((2 * cStar * rho : ℕ) : ℝ) ^ 2 /
          (8 * ((2 * (cStar * r) : ℕ) : ℝ)))))

/-- At the fixed tilt `4/3`, twice the cubic mean budget has the exponential
tail needed in one Lemma 17 stage. -/
theorem lemma17_allActive_term_le
    (n A cStar r : ℕ)
    (h3 : 3 ≤ n)
    (hA : A ≤ n)
    (hmean : A ^ 3 ≤ r * n ^ 2) :
    (infectionAllActiveCubeCompl n A +
        infectionAllActiveCube n A *
          ((4 : ℝ≥0∞) / 3)) ^ (cStar * n) /
      (((4 : ℝ≥0∞) / 3) ^
        (2 * (cStar * r) + 1))
    ≤ ENNReal.ofReal
        (Real.exp
          (-(((cStar * r : ℕ) : ℝ) / 20))) := by
  let m : ℕ := cStar * r
  let T : ℕ := cStar * n
  let cube : ℝ≥0∞ := infectionAllActiveCube n A
  let cubeCompl : ℝ≥0∞ :=
    infectionAllActiveCubeCompl n A
  let w : ℝ≥0∞ := (4 : ℝ≥0∞) / 3
  have hpartition : cubeCompl + cube = 1 := by
    simpa [cube, cubeCompl, add_comm] using
      infectionAllActiveCube_add_compl n A h3 hA
  have hmu :
      (T : ℝ≥0∞) * cube ≤ (m : ℝ≥0∞) := by
    simpa [T, m, cube, infectionAllActiveCube] using
      lemma16_cube_mean_le n A 1 r cStar h3
        (by simpa using hmean)
  have hw1 : (1 : ℝ≥0∞) ≤ w := by
    dsimp only [w]
    rw [ENNReal.le_div_iff_mul_le
      (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
  have hden :
      w ^ (4 * m / 3 + 1) ≤
        w ^ (2 * m + 1) := by
    apply pow_le_pow_right₀ hw1
    omega
  calc
    (infectionAllActiveCubeCompl n A +
          infectionAllActiveCube n A *
            ((4 : ℝ≥0∞) / 3)) ^ (cStar * n) /
        (((4 : ℝ≥0∞) / 3) ^
          (2 * (cStar * r) + 1))
      =
        (cubeCompl + cube * w) ^ T /
          w ^ (2 * m + 1) := by rfl
    _ ≤
        (cubeCompl + cube * w) ^ T /
          w ^ (4 * m / 3 + 1) :=
      ENNReal.div_le_div_left hden _
    _ ≤ ENNReal.ofReal
          (Real.exp (-((m : ℝ) / 20))) := by
      simpa [w] using
        four_thirds_floor_tail_ennreal
          hpartition T m hmu
    _ =
        ENNReal.ofReal
          (Real.exp
            (-(((cStar * r : ℕ) : ℝ) / 20))) := by
      rfl

/-- Paper-constant one-stage Lemma 17 bound at the linear raw horizon. -/
theorem lemma17CountedPath_paper_stage
    (n q rho a k u nu R B A cStar r : ℕ)
    (h3 : 3 ≤ n)
    (ha : 4 ≤ a)
    (hquarter : 4 * a ≤ n)
    (hquarterLabel : 4 * (k + 1) ≤ nu + 1)
    (hAupper : A ≤ 2 * a)
    (hAle : A ≤ n)
    (hcStar : 128 ≤ cStar)
    (hcTwo : 2 ≤ cStar)
    (hrho : 1 ≤ rho)
    (hbias : 38 * cStar * rho ≤ a)
    (hactiveScale : 76 * cStar * r ≤ a)
    (hmean : A ^ 3 ≤ r * n ^ 2)
    (hqa : q * (k + 1) ≤ rho ^ 2)
    (huk : u + k + 1 = nu)
    (hRB : R + B = nu)
    (hmajor : R ≤ B)
    (s : InfectionRevealPhysicalState n)
    (hstartActive : a ≤ s.coarse.1.active)
    (hanchorActive : s.coarse.1.active + k = A)
    (hstartGap :
      s.coarse.1.ay ≤
        s.coarse.1.ax + 14 * cStar * rho)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk0 : 0 < k) :
    terminalFailureMass
        (iter
          (lemma17CountedPathStep n h3 k A
            (19 * cStar * rho))
          (cStar * n)
          (lemma17CountedPathInitial s))
        (Lemma17StageGood A
          (19 * cStar * rho))
      ≤ lemma17StageError a q cStar rho r := by
  have hbudget :
      14 * cStar * rho + (rho + 1) +
          2 * (2 * cStar * rho) ≤
        19 * cStar * rho := by
    have hsmall : rho + 1 ≤ cStar * rho := by
      calc
        rho + 1 ≤ 2 * rho := by omega
        _ ≤ cStar * rho :=
          Nat.mul_le_mul_right rho hcTwo
    calc
      14 * cStar * rho + (rho + 1) +
          2 * (2 * cStar * rho) =
        18 * cStar * rho + (rho + 1) := by ring
      _ ≤ 18 * cStar * rho + cStar * rho :=
        Nat.add_le_add_left hsmall _
      _ = 19 * cStar * rho := by ring
  have hH : 0 < 2 * (cStar * r) := by
    have hr : 0 < r := by
      by_contra hz
      have hzero : r = 0 := Nat.eq_zero_of_not_pos hz
      rw [hzero] at hmean
      simp only [zero_mul] at hmean
      have hApow : A ^ 3 = 0 :=
        Nat.eq_zero_of_le_zero hmean
      have hAzero : A = 0 :=
        (Nat.pow_eq_zero.mp hApow).1
      omega
    exact Nat.mul_pos (by omega)
      (Nat.mul_pos (by omega) hr)
  have hG : 2 * (19 * cStar * rho) ≤ a := by
    calc
      2 * (19 * cStar * rho) =
          38 * cStar * rho := by ring
      _ ≤ a := hbias
  have hdrift :
      4 * (19 * cStar * rho) *
          (2 * (cStar * r)) ≤
        a * (2 * cStar * rho) := by
    calc
      4 * (19 * cStar * rho) *
          (2 * (cStar * r)) =
        (76 * cStar * r) *
          (2 * cStar * rho) := by ring
      _ ≤ a * (2 * cStar * rho) :=
        Nat.mul_le_mul_right
          (2 * cStar * rho) hactiveScale
  have hw1 :
      (1 : ℝ≥0∞) ≤ (4 : ℝ≥0∞) / 3 := by
    rw [ENNReal.le_div_iff_mul_le
      (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
  have hwt : (4 : ℝ≥0∞) / 3 ≠ ⊤ := by
    finiteness
  have hraw :=
    lemma17CountedPath_stage
      n h3 a k A (19 * cStar * rho)
      (14 * cStar * rho) (rho + 1)
      (2 * cStar * rho) (2 * (cStar * r))
      (cStar * n)
      ha hG hAle s hstartActive hanchorActive
      hstartGap hbudget hH hdrift
      ((4 : ℝ≥0∞) / 3) hw1 hwt
      (ENNReal.ofReal (Real.exp (-(a : ℝ))))
      (lemma16UrnError q)
      (lemma17CountedPath_doubling_deadline_padded
        n a A k (19 * cStar * rho) cStar
        h3 (by omega) hquarter hAupper hcStar s
        hstartActive hanchorActive)
      (lemma17CountedPath_label_tail_pool
        n h3 q rho (k + 1) k u nu R B
        A (19 * cStar * rho) (cStar * n) s
        hanchorActive hqa rfl huk hRB
        hquarterLabel hmajor hx0 hy0 hk0)
  calc
    terminalFailureMass
        (iter
          (lemma17CountedPathStep n h3 k A
            (19 * cStar * rho))
          (cStar * n)
          (lemma17CountedPathInitial s))
        (Lemma17StageGood A
          (19 * cStar * rho))
      ≤
        ENNReal.ofReal (Real.exp (-(a : ℝ))) +
          lemma16UrnError q +
          (infectionAllActiveCubeCompl n A +
              infectionAllActiveCube n A *
                ((4 : ℝ≥0∞) / 3)) ^ (cStar * n) /
            (((4 : ℝ≥0∞) / 3) ^
              (2 * (cStar * r) + 1)) +
          ENNReal.ofReal
            (Real.exp
              (-(((2 * cStar * rho : ℕ) : ℝ) ^ 2 /
                (8 *
                  ((2 * (cStar * r) : ℕ) : ℝ))))) :=
      hraw
    _ ≤ lemma17StageError a q cStar rho r := by
      unfold lemma17StageError
      gcongr
      exact
        lemma17_allActive_term_le
          n A cStar r h3 hAle hmean

end

end Tri

#print axioms Tri.lemma17_allActive_term_le
#print axioms Tri.lemma17CountedPath_paper_stage
