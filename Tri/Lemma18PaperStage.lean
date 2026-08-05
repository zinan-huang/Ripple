/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma18BlockTail
import Tri.Lemma17PaperStage

/-!
# The paper-scale decisive Lemma 18 stage

All five exceptional events in the decisive doubling stage are instantiated
on the same `cStar * n` raw horizon: epidemic completion, activation-prefix
labels, the strongly biased endpoint block, all-active exposure, and the
guarded productive-reaction direction.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- The five explicit exceptional terms in the decisive paper stage. -/
noncomputable def lemma18StageError
    (qPrefix qEnd a cStar r D : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(a : ℝ))) +
    lemma16UrnError qPrefix +
    lemma16UrnError qEnd +
    ENNReal.ofReal
      (Real.exp
        (-(((cStar * r : ℕ) : ℝ) / 20))) +
    ENNReal.ofReal
      (Real.exp
        (-(((7 * D : ℕ) : ℝ) ^ 2 /
          (8 * ((10 * cStar * r : ℕ) : ℝ)))))

/-- Fully instantiated decisive stage at the paper constants. -/
theorem lemma18CountedPath_paper
    (n qPrefix qEnd rhoPrefix rhoEnd D d
      a k u nu R B A cStar r : ℕ)
    (h3 : 3 ≤ n)
    (ha : 4 ≤ a)
    (hquarterClock : 4 * a ≤ n)
    (hAeq : A = 2 * a)
    (hAle : A ≤ n)
    (hcStar : 128 ≤ cStar)
    (hprefixRadius : rhoPrefix + 1 = D)
    (hendRadius : rhoEnd + 1 = 12 * D)
    (hprefixQa :
      qPrefix * (k + 1) ≤ rhoPrefix ^ 2)
    (hendQa :
      qEnd * (k + 1) ≤ rhoEnd ^ 2)
    (huk : u + k + 1 = nu)
    (hRB : R + B = nu)
    (hquarterPool : 4 * (k + 1) ≤ nu + 1)
    (hpoolScale : nu ≤ k * d)
    (hpoolGap : R + 60 * d * D ≤ B)
    (hmeanActive : A ^ 3 ≤ r * n ^ 2)
    (hguardScale : 60 * D ≤ a)
    (hreactionScale : 1200 * cStar * r ≤ 7 * a)
    (s : InfectionRevealPhysicalState n)
    (hstartActive : a ≤ s.coarse.1.active)
    (hanchorActive : s.coarse.1.active + k = A)
    (hprior :
      s.coarse.1.ay ≤ s.coarse.1.ax + 14 * D)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk0 : 0 < k) :
    terminalFailureMass
        (iter
          (lemma17CountedPathStep n h3 k A (30 * D))
          (cStar * n)
          (lemma17CountedPathInitial s))
        (Lemma18StageGood A (2 * D))
      ≤
        lemma18StageError
          qPrefix qEnd a cStar r D := by
  have hr : 0 < r := by
    by_contra hnot
    have hr0 : r = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hr0] at hmeanActive
    simp only [zero_mul] at hmeanActive
    have hA3 : A ^ 3 = 0 :=
      Nat.eq_zero_of_le_zero hmeanActive
    have hA0 : A = 0 :=
      (Nat.pow_eq_zero.mp hA3).1
    omega
  have hH : 0 < 10 * cStar * r := by
    positivity
  have hG : 2 * (30 * D) ≤ a := by
    omega
  have hdrift :
      4 * (30 * D) * (10 * cStar * r) ≤
        a * (7 * D) := by
    calc
      4 * (30 * D) * (10 * cStar * r) =
          (1200 * cStar * r) * D := by ring
      _ ≤ (7 * a) * D :=
        Nat.mul_le_mul_right D hreactionScale
      _ = a * (7 * D) := by ring
  have hw1 :
      (1 : ℝ≥0∞) ≤ (4 : ℝ≥0∞) / 3 := by
    rw [ENNReal.le_div_iff_mul_le
      (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
  have hwt : (4 : ℝ≥0∞) / 3 ≠ ⊤ := by
    finiteness
  have hclock :=
    lemma17CountedPath_doubling_deadline_padded
      n a A k (30 * D) cStar h3 (by omega)
      hquarterClock hAeq.le hcStar s hstartActive
      hanchorActive
  have hprefix :=
    lemma17CountedPath_label_tail_pool
      n h3 qPrefix rhoPrefix (k + 1) k
      u nu R B A (30 * D) (cStar * n) s
      hanchorActive hprefixQa rfl huk hRB
      hquarterPool (by omega) hx0 hy0 hk0
  have hend :=
    lemma18CountedPath_paper_end_tail
      n h3 qEnd rhoEnd D d k u nu R B A
      (cStar * n) s hanchorActive hendRadius
      hendQa huk hRB hquarterPool hpoolScale
      hpoolGap hx0 hy0 hk0
  have hactive :=
    lemma17CountedPath_allActive_tail
      n h3 k A (30 * D) hAle s hanchorActive
      ((4 : ℝ≥0∞) / 3) hw1 hwt
      (cStar * n) (10 * cStar * r + 1)
  have hreaction :=
    lemma17CountedPath_reaction_tail
      n h3 a k A (30 * D) ha hG s
      hstartActive hanchorActive
      (cStar * n) (10 * cStar * r) (7 * D)
      hH hdrift
  have hraw :=
    lemma18CountedPath_paper_stage
      n h3 k A (cStar * n) (10 * cStar * r) D
      s hanchorActive hprior
      (ENNReal.ofReal (Real.exp (-(a : ℝ))))
      (lemma16UrnError qPrefix)
      (lemma16UrnError qEnd)
      ((infectionAllActiveCubeCompl n A +
          infectionAllActiveCube n A *
            ((4 : ℝ≥0∞) / 3)) ^ (cStar * n) /
        (((4 : ℝ≥0∞) / 3) ^
          (10 * cStar * r + 1)))
      (ENNReal.ofReal
        (Real.exp
          (-(((7 * D : ℕ) : ℝ) ^ 2 /
            (8 * ((10 * cStar * r : ℕ) : ℝ))))))
      hclock
      (by simpa [hprefixRadius] using hprefix)
      hend hactive hreaction
  calc
    terminalFailureMass
        (iter
          (lemma17CountedPathStep n h3 k A (30 * D))
          (cStar * n)
          (lemma17CountedPathInitial s))
        (Lemma18StageGood A (2 * D))
      ≤
        ENNReal.ofReal (Real.exp (-(a : ℝ))) +
          lemma16UrnError qPrefix +
          lemma16UrnError qEnd +
          (infectionAllActiveCubeCompl n A +
              infectionAllActiveCube n A *
                ((4 : ℝ≥0∞) / 3)) ^ (cStar * n) /
            (((4 : ℝ≥0∞) / 3) ^
              (10 * cStar * r + 1)) +
          ENNReal.ofReal
            (Real.exp
              (-(((7 * D : ℕ) : ℝ) ^ 2 /
                (8 *
                  ((10 * cStar * r : ℕ) : ℝ))))) :=
      hraw
    _ ≤
        lemma18StageError
          qPrefix qEnd a cStar r D := by
      unfold lemma18StageError
      gcongr
      calc
        (infectionAllActiveCubeCompl n A +
              infectionAllActiveCube n A *
                ((4 : ℝ≥0∞) / 3)) ^ (cStar * n) /
            (((4 : ℝ≥0∞) / 3) ^
              (10 * cStar * r + 1))
          ≤
            (infectionAllActiveCubeCompl n A +
                infectionAllActiveCube n A *
                  ((4 : ℝ≥0∞) / 3)) ^ (cStar * n) /
              (((4 : ℝ≥0∞) / 3) ^
                (2 * (cStar * r) + 1)) := by
              apply ENNReal.div_le_div_left
              apply pow_le_pow_right₀ hw1
              calc
                2 * (cStar * r) + 1 ≤
                    10 * (cStar * r) + 1 :=
                  Nat.add_le_add_right
                    (Nat.mul_le_mul_right
                      (cStar * r) (by omega)) 1
                _ = 10 * cStar * r + 1 := by ring
        _ ≤
            ENNReal.ofReal
              (Real.exp
                (-(((cStar * r : ℕ) : ℝ) / 20))) :=
          lemma17_allActive_term_le
            n A cStar r h3 hAle hmeanActive

end

end Tri

#print axioms Tri.lemma18CountedPath_paper
