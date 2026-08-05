/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductive
import Tri.Progress

/-!
# The raw productive clock for multi-species Tri

The physical multi-species kernel is augmented with a counter that increments
exactly when the sampled triple fires.  In the phase-0 region, the uniform
`1 / (8m)` productive-mass floor therefore gives an adapted raw-clock lower
tail without any independence assumption.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- Total mass of physical samples that do not fire. -/
noncomputable def nonproductiveMass
    (c : Config m n) (h3 : 3 ≤ n) : ℝ≥0∞ := by
  classical
  exact ∑' t : TripleSample c,
    if IsProductiveSample t then 0 else triplePMF c h3 t

/-- Productive and nonproductive physical samples partition one interaction. -/
theorem productiveMass_add_nonproductiveMass
    (c : Config m n) (h3 : 3 ≤ n) :
    productiveMass c h3 + nonproductiveMass c h3 = 1 := by
  classical
  unfold productiveMass nonproductiveMass
  simp only [tsum_fintype, ← Finset.sum_add_distrib]
  calc
    ∑ t : TripleSample c,
        ((if IsProductiveSample t then triplePMF c h3 t else 0) +
          if IsProductiveSample t then 0 else triplePMF c h3 t) =
        ∑ t : TripleSample c, triplePMF c h3 t := by
      apply Finset.sum_congr rfl
      intro t _ht
      by_cases ht : IsProductiveSample t <;> simp [ht]
    _ = ∑' t : TripleSample c, triplePMF c h3 t := by
      rw [tsum_fintype]
    _ = 1 := PMF.tsum_coe _

/-- The physical multi-species chain augmented by its productive-event count. -/
noncomputable def multiProductiveCount
    (h3 : 3 ≤ n) :
    Config m n × ℕ → PMF (Config m n × ℕ) := by
  classical
  exact fun q =>
    (triplePMF q.1 h3).map fun t =>
      (sampleNext q.1 t,
        if IsProductiveSample t then q.2 + 1 else q.2)

/-- Forgetting the counter recovers the physical multi-species kernel. -/
theorem multiProductiveCount_map_fst
    (h3 : 3 ≤ n) (q : Config m n × ℕ) :
    (multiProductiveCount h3 q).map Prod.fst =
      multiStep q.1 h3 := by
  unfold multiProductiveCount multiStep
  rw [PMF.map_comp]
  apply congrArg (fun f => PMF.map f (triplePMF q.1 h3))
  funext t
  rfl

/-- Exact two-way decomposition of the counter potential. -/
theorem expect_multiProductiveCount
    (c : Config m n) (h3 : 3 ≤ n) (k : ℕ) (w : ℝ≥0∞) :
    expect (multiProductiveCount h3 (c, k)) (fun q => w ^ q.2) =
      nonproductiveMass c h3 * w ^ k +
        productiveMass c h3 * w ^ (k + 1) := by
  classical
  unfold multiProductiveCount
  rw [expect_map]
  unfold expect productiveMass nonproductiveMass
  simp only [tsum_fintype]
  calc
    ∑ t : TripleSample c,
        triplePMF c h3 t *
          w ^ (if IsProductiveSample t then k + 1 else k) =
      ∑ t : TripleSample c,
        ((if IsProductiveSample t then 0 else triplePMF c h3 t) * w ^ k +
          (if IsProductiveSample t then triplePMF c h3 t else 0) *
            w ^ (k + 1)) := by
        apply Finset.sum_congr rfl
        intro t _ht
        by_cases ht : IsProductiveSample t <;> simp [ht]
    _ = (∑ t : TripleSample c,
          if IsProductiveSample t then 0 else triplePMF c h3 t) * w ^ k +
        (∑ t : TripleSample c,
          if IsProductiveSample t then triplePMF c h3 t else 0) *
            w ^ (k + 1) := by
      rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]

/-- A lower bound on physical productive mass gives the one-step adapted
counter contraction. -/
theorem multiProductiveCount_step_of_lower
    (c : Config m n) (h3 : 3 ≤ n) (k : ℕ)
    (w p p' : ℝ≥0∞)
    (hw : w ≤ 1) (hp : p + p' = 1)
    (hpq : p ≤ productiveMass c h3) :
    expect (multiProductiveCount h3 (c, k)) (fun q => w ^ q.2) ≤
      (p' + p * w) * w ^ k := by
  apply count_step_of_masses
    (q := productiveMass c h3)
    (q' := nonproductiveMass c h3)
    (p := p) (p' := p')
  · exact productiveMass_add_nonproductiveMass c h3
  · exact hp
  · exact hw
  · exact hpq
  · exact expect_multiProductiveCount c h3 k w

/-- Leaving the phase-0 region means that `X` is no longer maximal or its
aggregate complement has dropped below half the population. -/
def Phase0ClockBoundary
    (X : Species m) (q : Config m n × ℕ) : Prop :=
  ¬ (IsMaxSpecies q.1 X ∧ n ≤ 2 * zSum q.1 X)

noncomputable instance phase0ClockBoundaryDecidable
    (X : Species m) :
    DecidablePred (Phase0ClockBoundary X :
      Config m n × ℕ → Prop) :=
  Classical.decPred _

/-- The counted physical kernel frozen on first exit from the phase-0
productive-floor region. -/
noncomputable def multiPhase0ClockStop
    (h3 : 3 ≤ n) (X : Species m) :
    Config m n × ℕ → PMF (Config m n × ℕ) :=
  freeze (Phase0ClockBoundary X) (multiProductiveCount h3)

/-- The counter potential, killed on phase-0 exit, contracts at the Bernoulli
factor associated with any lower bound `p ≤ 1/(8m)`. -/
theorem multiPhase0ClockStop_count_super
    (h3 : 3 ≤ n) (X : Species m) (hnm : 2 * m ≤ n)
    (w p p' : ℝ≥0∞)
    (hw : w ≤ 1) (hp : p + p' = 1)
    (hpFloor : p ≤ (1 : ℝ≥0∞) / (8 * m : ℕ)) :
    ∀ q,
      expect (multiPhase0ClockStop h3 X q)
          (fun z =>
            if Phase0ClockBoundary X z then 0 else w ^ z.2) ≤
        (p' + p * w) *
          (if Phase0ClockBoundary X q then 0 else w ^ q.2) := by
  intro q
  by_cases hq : Phase0ClockBoundary X q
  · rw [multiPhase0ClockStop, freeze_of_mem q hq, expect_pure]
    simp [hq]
  · rw [multiPhase0ClockStop, freeze_of_not_mem q hq, if_neg hq]
    have hlive :
        IsMaxSpecies q.1 X ∧ n ≤ 2 * zSum q.1 X :=
      Classical.not_not.mp hq
    have hprod : p ≤ productiveMass q.1 h3 :=
      hpFloor.trans
        (one_div_eight_species_le_productiveMass
          q.1 X h3 hlive.1 hlive.2 hnm)
    calc
      expect (multiProductiveCount h3 q)
          (fun z =>
            if Phase0ClockBoundary X z then 0 else w ^ z.2) ≤
          expect (multiProductiveCount h3 q)
            (fun z => w ^ z.2) := by
              unfold expect
              exact ENNReal.tsum_le_tsum fun z =>
                mul_le_mul_right (by
                  change
                    (if Phase0ClockBoundary X z then 0 else w ^ z.2) ≤
                      w ^ z.2
                  split_ifs <;> simp) _
      _ ≤ (p' + p * w) * w ^ q.2 := by
        simpa only using
          multiProductiveCount_step_of_lower
            q.1 h3 q.2 w p p' hw hp hprod

/-- Adapted raw-clock lower tail in the phase-0 region.  It bounds paths that
remain in the region but have accumulated at most `M` productive reactions
after `T` physical interactions. -/
theorem multiPhase0ClockStop_productivity_tail
    (h3 : 3 ≤ n) (X : Species m) (hnm : 2 * m ≤ n)
    (w p p' : ℝ≥0∞)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hp : p + p' = 1)
    (hpFloor : p ≤ (1 : ℝ≥0∞) / (8 * m : ℕ))
    (T M : ℕ) (q0 : Config m n × ℕ) :
    (∑' q, if q.2 ≤ M ∧ ¬ Phase0ClockBoundary X q then
        iter (multiPhase0ClockStop h3 X) T q0 q else 0) ≤
      (p' + p * w) ^ T *
        (if Phase0ClockBoundary X q0 then 0 else w ^ q0.2) /
          w ^ M := by
  let V : Config m n × ℕ → ℝ≥0∞ := fun q =>
    if Phase0ClockBoundary X q then 0 else w ^ q.2
  let θ : ℝ≥0∞ := w ^ M
  have hwtop : w ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hw1
  have hθ0 : θ ≠ 0 := pow_ne_zero _ hw0
  have hθtop : θ ≠ ⊤ := ENNReal.pow_ne_top hwtop
  have hsub : ∀ q,
      (if q.2 ≤ M ∧ ¬ Phase0ClockBoundary X q then
          iter (multiPhase0ClockStop h3 X) T q0 q else 0) ≤
        (if θ ≤ V q then
          iter (multiPhase0ClockStop h3 X) T q0 q else 0) := by
    intro q
    by_cases hq : q.2 ≤ M ∧ ¬ Phase0ClockBoundary X q
    · have hle : θ ≤ V q := by
        simp only [V, hq.2, if_false, θ]
        exact pow_le_pow_right_of_le_one' hw1 hq.1
      simp [hq, hle]
    · simp [hq]
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  refine le_trans
    (markov_div
      (iter (multiPhase0ClockStop h3 X) T q0)
      V θ hθ0 hθtop) ?_
  have hiter :=
    expect_iter_le
      (multiPhase0ClockStop h3 X)
      V (p' + p * w)
      (by
        simpa only [V] using
          multiPhase0ClockStop_count_super
            h3 X hnm w p p' hw1 hp hpFloor)
      T q0
  exact ENNReal.div_le_div_right
    (by simpa only [V] using hiter) θ

/-- The phase-0 clock tail instantiated at the proved physical floor
`p = 1/(8m)`. -/
theorem multiPhase0ClockStop_productivity_tail_floor
    (h3 : 3 ≤ n) (X : Species m) (hnm : 2 * m ≤ n)
    (w : ℝ≥0∞) (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (T M : ℕ) (q0 : Config m n × ℕ) :
    (∑' q, if q.2 ≤ M ∧ ¬ Phase0ClockBoundary X q then
        iter (multiPhase0ClockStop h3 X) T q0 q else 0) ≤
      ((1 - (1 : ℝ≥0∞) / (8 * m : ℕ)) +
          ((1 : ℝ≥0∞) / (8 * m : ℕ)) * w) ^ T *
        (if Phase0ClockBoundary X q0 then 0 else w ^ q0.2) /
          w ^ M := by
  let p : ℝ≥0∞ := (1 : ℝ≥0∞) / (8 * m : ℕ)
  have hm : 0 < m := Nat.zero_lt_of_lt X.isLt
  have hdenNat : 1 ≤ 8 * m := by omega
  have hden : (1 : ℝ≥0∞) ≤ ((8 * m : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hdenNat
  have hpLe : p ≤ 1 := by
    dsimp only [p]
    exact ENNReal.div_le_of_le_mul (by simpa using hden)
  have hpSum : p + (1 - p) = 1 := by
    rw [add_comm]
    exact tsub_add_cancel_of_le hpLe
  simpa only [p] using
    multiPhase0ClockStop_productivity_tail
      h3 X hnm w p (1 - p)
      hw1 hw0 hpSum le_rfl T M q0

/-- Exit from the paper's full phase-0 floor region with additive slack `D`. -/
def PaperPhase0ClockBoundary
    (X : Species m) (D : ℕ) (q : Config m n × ℕ) : Prop :=
  ¬ (IsMaxSpecies q.1 X ∧ count q.1 X ≤ zSum q.1 X + D)

noncomputable instance paperPhase0ClockBoundaryDecidable
    (X : Species m) (D : ℕ) :
    DecidablePred (PaperPhase0ClockBoundary X D :
      Config m n × ℕ → Prop) :=
  Classical.decPred _

/-- Counted physical kernel frozen on exit from the paper's phase-0 region. -/
noncomputable def multiPaperPhase0ClockStop
    (h3 : 3 ≤ n) (X : Species m) (D : ℕ) :
    Config m n × ℕ → PMF (Config m n × ℕ) :=
  freeze (PaperPhase0ClockBoundary X D) (multiProductiveCount h3)

/-- Killed counter contraction on the full paper phase-0 region. -/
theorem multiPaperPhase0ClockStop_count_super
    (h3 : 3 ≤ n) (X : Species m) (D : ℕ)
    (hD : 3 * D ≤ n) (hnm : 6 * m ≤ n)
    (w p p' : ℝ≥0∞)
    (hw : w ≤ 1) (hp : p + p' = 1)
    (hpFloor : p ≤ (1 : ℝ≥0∞) / (108 * m : ℕ)) :
    ∀ q,
      expect (multiPaperPhase0ClockStop h3 X D q)
          (fun z =>
            if PaperPhase0ClockBoundary X D z then 0 else w ^ z.2) ≤
        (p' + p * w) *
          (if PaperPhase0ClockBoundary X D q then 0 else w ^ q.2) := by
  intro q
  by_cases hq : PaperPhase0ClockBoundary X D q
  · rw [multiPaperPhase0ClockStop, freeze_of_mem q hq, expect_pure]
    simp [hq]
  · rw [multiPaperPhase0ClockStop, freeze_of_not_mem q hq, if_neg hq]
    have hlive :
        IsMaxSpecies q.1 X ∧ count q.1 X ≤ zSum q.1 X + D :=
      Classical.not_not.mp hq
    have hprod : p ≤ productiveMass q.1 h3 :=
      hpFloor.trans
        (one_div_108_species_le_productiveMass
          q.1 X D h3 hlive.1 hlive.2 hD hnm)
    calc
      expect (multiProductiveCount h3 q)
          (fun z =>
            if PaperPhase0ClockBoundary X D z then 0 else w ^ z.2) ≤
          expect (multiProductiveCount h3 q)
            (fun z => w ^ z.2) := by
              unfold expect
              exact ENNReal.tsum_le_tsum fun z =>
                mul_le_mul_right (by
                  change
                    (if PaperPhase0ClockBoundary X D z then 0
                      else w ^ z.2) ≤ w ^ z.2
                  split_ifs <;> simp) _
      _ ≤ (p' + p * w) * w ^ q.2 := by
        simpa only using
          multiProductiveCount_step_of_lower
            q.1 h3 q.2 w p p' hw hp hprod

/-- Adapted raw-clock lower tail on the paper's full phase-0 region. -/
theorem multiPaperPhase0ClockStop_productivity_tail
    (h3 : 3 ≤ n) (X : Species m) (D : ℕ)
    (hD : 3 * D ≤ n) (hnm : 6 * m ≤ n)
    (w p p' : ℝ≥0∞)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hp : p + p' = 1)
    (hpFloor : p ≤ (1 : ℝ≥0∞) / (108 * m : ℕ))
    (T M : ℕ) (q0 : Config m n × ℕ) :
    (∑' q, if q.2 ≤ M ∧
        ¬ PaperPhase0ClockBoundary X D q then
        iter (multiPaperPhase0ClockStop h3 X D) T q0 q else 0) ≤
      (p' + p * w) ^ T *
        (if PaperPhase0ClockBoundary X D q0 then 0 else w ^ q0.2) /
          w ^ M := by
  let V : Config m n × ℕ → ℝ≥0∞ := fun q =>
    if PaperPhase0ClockBoundary X D q then 0 else w ^ q.2
  let θ : ℝ≥0∞ := w ^ M
  have hwtop : w ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hw1
  have hθ0 : θ ≠ 0 := pow_ne_zero _ hw0
  have hθtop : θ ≠ ⊤ := ENNReal.pow_ne_top hwtop
  have hsub : ∀ q,
      (if q.2 ≤ M ∧ ¬ PaperPhase0ClockBoundary X D q then
          iter (multiPaperPhase0ClockStop h3 X D) T q0 q else 0) ≤
        (if θ ≤ V q then
          iter (multiPaperPhase0ClockStop h3 X D) T q0 q else 0) := by
    intro q
    by_cases hq : q.2 ≤ M ∧ ¬ PaperPhase0ClockBoundary X D q
    · have hle : θ ≤ V q := by
        simp only [V, hq.2, if_false, θ]
        exact pow_le_pow_right_of_le_one' hw1 hq.1
      simp [hq, hle]
    · simp [hq]
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  refine le_trans
    (markov_div
      (iter (multiPaperPhase0ClockStop h3 X D) T q0)
      V θ hθ0 hθtop) ?_
  have hiter :=
    expect_iter_le
      (multiPaperPhase0ClockStop h3 X D)
      V (p' + p * w)
      (by
        simpa only [V] using
          multiPaperPhase0ClockStop_count_super
            h3 X D hD hnm w p p' hw1 hp hpFloor)
      T q0
  exact ENNReal.div_le_div_right
    (by simpa only [V] using hiter) θ

/-- Full phase-0 clock tail instantiated at the physical floor
`p = 1/(108m)`. -/
theorem multiPaperPhase0ClockStop_productivity_tail_floor
    (h3 : 3 ≤ n) (X : Species m) (D : ℕ)
    (hD : 3 * D ≤ n) (hnm : 6 * m ≤ n)
    (w : ℝ≥0∞) (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (T M : ℕ) (q0 : Config m n × ℕ) :
    (∑' q, if q.2 ≤ M ∧
        ¬ PaperPhase0ClockBoundary X D q then
        iter (multiPaperPhase0ClockStop h3 X D) T q0 q else 0) ≤
      ((1 - (1 : ℝ≥0∞) / (108 * m : ℕ)) +
          ((1 : ℝ≥0∞) / (108 * m : ℕ)) * w) ^ T *
        (if PaperPhase0ClockBoundary X D q0 then 0 else w ^ q0.2) /
          w ^ M := by
  let p : ℝ≥0∞ := (1 : ℝ≥0∞) / (108 * m : ℕ)
  have hm : 0 < m := Nat.zero_lt_of_lt X.isLt
  have hdenNat : 1 ≤ 108 * m := by omega
  have hden : (1 : ℝ≥0∞) ≤ ((108 * m : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hdenNat
  have hpLe : p ≤ 1 := by
    dsimp only [p]
    exact ENNReal.div_le_of_le_mul (by simpa using hden)
  have hpSum : p + (1 - p) = 1 := by
    rw [add_comm]
    exact tsub_add_cancel_of_le hpLe
  simpa only [p] using
    multiPaperPhase0ClockStop_productivity_tail
      h3 X D hD hnm w p (1 - p)
      hw1 hw0 hpSum le_rfl T M q0

end Tri.Multi

#print axioms Tri.Multi.productiveMass_add_nonproductiveMass
#print axioms Tri.Multi.multiProductiveCount_map_fst
#print axioms Tri.Multi.expect_multiProductiveCount
#print axioms Tri.Multi.multiProductiveCount_step_of_lower
#print axioms Tri.Multi.multiPhase0ClockStop_count_super
#print axioms Tri.Multi.multiPhase0ClockStop_productivity_tail
#print axioms Tri.Multi.multiPhase0ClockStop_productivity_tail_floor
#print axioms Tri.Multi.multiPaperPhase0ClockStop_count_super
#print axioms Tri.Multi.multiPaperPhase0ClockStop_productivity_tail_floor
