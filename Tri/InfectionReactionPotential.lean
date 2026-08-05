/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionReactionBias
import Tri.InfectionActiveCount
import Tri.TimeChangeHitting

/-!
# A stopped exponential potential for active-reaction excess

The trace counts the two productive all-active reactions separately.  While
the active `Y-X` gap is at most `G`, the statewise bias bound from
`InfectionReactionBias` controls the adverse type-(2) mass.  The potential
uses bases `3/4` and `4/3`, together with one inverse step factor per
productive reaction.

The exported finite-horizon tail is adapted: it needs no independence
assumption and remains valid when the process is stopped either at an active
population target or at the gap barrier.
-/

namespace Tri

open scoped ENNReal

theorem weighted_two_mass_mono_real
    {m₁ m₂ p p' v w : ℝ}
    (hp : p + p' = 1)
    (hbad : m₂ ≤ p * (m₁ + m₂))
    (hvw : v ≤ w) :
    m₁ * v + m₂ * w ≤
      (m₁ + m₂) * (p' * v + p * w) := by
  have hnonneg :
      0 ≤ (p * (m₁ + m₂) - m₂) * (w - v) :=
    mul_nonneg (sub_nonneg.mpr hbad)
      (sub_nonneg.mpr hvw)
  rw [show p' = 1 - p by linarith] at *
  nlinarith

theorem weighted_two_mass_mono_ennreal
    {m₁ m₂ p p' v w : ℝ≥0∞}
    (hm₁ : m₁ ≠ ⊤) (hm₂ : m₂ ≠ ⊤)
    (hp : p + p' = 1)
    (hbad : m₂ ≤ p * (m₁ + m₂))
    (hvw : v ≤ w)
    (hpTop : p ≠ ⊤) (hp'Top : p' ≠ ⊤)
    (hvTop : v ≠ ⊤) (hwTop : w ≠ ⊤) :
    m₁ * v + m₂ * w ≤
      (m₁ + m₂) * (p' * v + p * w) := by
  have hsumTop : m₁ + m₂ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hm₁, hm₂⟩
  have hleftTop :
      m₁ * v + m₂ * w ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top hm₁ hvTop,
        ENNReal.mul_ne_top hm₂ hwTop⟩
  have hmixTop :
      p' * v + p * w ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top hp'Top hvTop,
        ENNReal.mul_ne_top hpTop hwTop⟩
  have hrightTop :
      (m₁ + m₂) * (p' * v + p * w) ≠ ⊤ :=
    ENNReal.mul_ne_top hsumTop hmixTop
  rw [← ENNReal.toReal_le_toReal hleftTop hrightTop]
  rw [ENNReal.toReal_add
      (ENNReal.mul_ne_top hm₁ hvTop)
      (ENNReal.mul_ne_top hm₂ hwTop),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_mul,
    ENNReal.toReal_add hm₁ hm₂,
    ENNReal.toReal_add
      (ENNReal.mul_ne_top hp'Top hvTop)
      (ENNReal.mul_ne_top hpTop hwTop),
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  apply weighted_two_mass_mono_real
  · have h := congrArg ENNReal.toReal hp
    rwa [ENNReal.toReal_add hpTop hp'Top,
      ENNReal.toReal_one] at h
  · have hbadReal :=
      (ENNReal.toReal_le_toReal hm₂
        (ENNReal.mul_ne_top hpTop hsumTop)).mpr
        hbad
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_add hm₁ hm₂] at hbadReal
    exact hbadReal
  · exact
      (ENNReal.toReal_le_toReal hvTop hwTop).mpr hvw

noncomputable def infectionReactionBias
    (a G : ℕ) : ℝ≥0∞ :=
  ((a + 2 * G : ℕ) : ℝ≥0∞) /
    ((2 * a : ℕ) : ℝ≥0∞)

noncomputable def infectionReactionBiasCompl
    (a G : ℕ) : ℝ≥0∞ :=
  1 - infectionReactionBias a G

theorem infectionReactionBias_le_one
    (a G : ℕ) (ha : 0 < a) (hG : 2 * G ≤ a) :
    infectionReactionBias a G ≤ 1 := by
  unfold infectionReactionBias
  have hden0 :
      ((2 * a : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (show 2 * a ≠ 0 by omega)
  have hdenTop :
      ((2 * a : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  apply (ENNReal.div_le_iff hden0 hdenTop).2
  exact_mod_cast (by omega : a + 2 * G ≤ 1 * (2 * a))

theorem infectionReactionBias_add_compl
    (a G : ℕ) (ha : 0 < a) (hG : 2 * G ≤ a) :
    infectionReactionBias a G +
        infectionReactionBiasCompl a G = 1 := by
  unfold infectionReactionBiasCompl
  rw [add_comm]
  exact tsub_add_cancel_of_le
    (infectionReactionBias_le_one a G ha hG)

theorem infection_productive_weighted_bias
    (s : InfectionCfg) (h : 3 ≤ s.total)
    (a G : ℕ)
    (ha : 4 ≤ a)
    (hG : 2 * G ≤ a)
    (hactive : a ≤ s.active)
    (hgap : s.ay ≤ s.ax + G)
    (v w : ℝ≥0∞)
    (hvw : v ≤ w)
    (hvTop : v ≠ ⊤)
    (hwTop : w ≠ ⊤) :
    infectionTypeOneMass s h * v +
        infectionTypeTwoMass s h * w ≤
      infectionProductiveActiveMass s h *
        (infectionReactionBiasCompl a G * v +
          infectionReactionBias a G * w) := by
  apply weighted_two_mass_mono_ennreal
  · exact PMF.apply_ne_top _ _
  · exact PMF.apply_ne_top _ _
  · exact infectionReactionBias_add_compl
      a G (by omega) hG
  · exact infectionTypeTwoMass_le_bias
      s h a G ha hactive hgap
  · exact hvw
  · unfold infectionReactionBias
    finiteness
  · unfold infectionReactionBiasCompl
    finiteness
  · exact hvTop
  · exact hwTop

noncomputable def infectionReactionDown : ℝ≥0∞ :=
  (3 : ℝ≥0∞) / 4

noncomputable def infectionReactionUp : ℝ≥0∞ :=
  (4 : ℝ≥0∞) / 3

noncomputable def infectionReactionFactor
    (a G : ℕ) : ℝ≥0∞ :=
  infectionReactionBiasCompl a G * infectionReactionDown +
    infectionReactionBias a G * infectionReactionUp

theorem infectionReactionBias_half_le
    (a G : ℕ) (ha : 0 < a) :
    (1 : ℝ≥0∞) / 2 ≤ infectionReactionBias a G := by
  unfold infectionReactionBias
  have hden0 :
      ((2 * a : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (show 2 * a ≠ 0 by omega)
  have hdenTop :
      ((2 * a : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl hden0) (Or.inl hdenTop)).2
  rw [show
      (1 : ℝ≥0∞) / 2 *
          ((2 * a : ℕ) : ℝ≥0∞) =
        (a : ℝ≥0∞) by
      push_cast
      rw [div_eq_mul_inv]
      simp only [one_mul]
      rw [← mul_assoc,
        ENNReal.inv_mul_cancel
          (by norm_num) (by norm_num),
        one_mul]]
  exact_mod_cast (Nat.le_add_right a (2 * G))

theorem infectionReactionFactor_ge_one
    (a G : ℕ) (ha : 0 < a) (hG : 2 * G ≤ a) :
    1 ≤ infectionReactionFactor a G := by
  let p := infectionReactionBias a G
  let p' := infectionReactionBiasCompl a G
  have hpLe : p ≤ 1 :=
    infectionReactionBias_le_one a G ha hG
  have hpTop : p ≠ ⊤ := ne_top_of_le_ne_top
    ENNReal.one_ne_top hpLe
  have hp'Top : p' ≠ ⊤ := by
    dsimp only [p', infectionReactionBiasCompl]
    finiteness
  have hdownTop : infectionReactionDown ≠ ⊤ := by
    unfold infectionReactionDown
    finiteness
  have hupTop : infectionReactionUp ≠ ⊤ := by
    unfold infectionReactionUp
    finiteness
  have hfactorTop :
      infectionReactionFactor a G ≠ ⊤ := by
    unfold infectionReactionFactor
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top hp'Top hdownTop,
        ENNReal.mul_ne_top hpTop hupTop⟩
  rw [← ENNReal.toReal_le_toReal
    ENNReal.one_ne_top hfactorTop]
  rw [ENNReal.toReal_one]
  unfold infectionReactionFactor
  rw [ENNReal.toReal_add
      (ENNReal.mul_ne_top hp'Top hdownTop)
      (ENNReal.mul_ne_top hpTop hupTop),
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  have hpRealLe : p.toReal ≤ 1 := by
    simpa using
      (ENNReal.toReal_le_toReal hpTop
        ENNReal.one_ne_top).mpr hpLe
  have hpHalf :
      (1 : ℝ) / 2 ≤ p.toReal := by
    have h :=
      (ENNReal.toReal_le_toReal
        (by finiteness : (1 / 2 : ℝ≥0∞) ≠ ⊤)
        hpTop).mpr
        (infectionReactionBias_half_le a G ha)
    norm_num at h ⊢
    exact h
  have hp'Real :
      p'.toReal = 1 - p.toReal := by
    dsimp only [p', infectionReactionBiasCompl]
    rw [ENNReal.toReal_sub_of_le hpLe
      ENNReal.one_ne_top, ENNReal.toReal_one]
  rw [hp'Real]
  unfold infectionReactionDown infectionReactionUp
  norm_num [ENNReal.toReal_ofNat, ENNReal.toReal_div]
  nlinarith

theorem infectionReactionFactor_ne_zero
    (a G : ℕ) (ha : 0 < a) (hG : 2 * G ≤ a) :
    infectionReactionFactor a G ≠ 0 := by
  exact ne_of_gt
    (lt_of_lt_of_le zero_lt_one
      (infectionReactionFactor_ge_one a G ha hG))

theorem infectionReactionFactor_ne_top
    (a G : ℕ) (ha : 0 < a) :
    infectionReactionFactor a G ≠ ⊤ := by
  have hden0 :
      ((2 * a : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (show 2 * a ≠ 0 by omega)
  unfold infectionReactionFactor
    infectionReactionBiasCompl
    infectionReactionBias
    infectionReactionDown
    infectionReactionUp
  apply ENNReal.add_ne_top.mpr
  constructor
  · apply ENNReal.mul_ne_top
    · finiteness
    · finiteness
  · apply ENNReal.mul_ne_top
    · exact ENNReal.div_ne_top
        (ENNReal.natCast_ne_top _) hden0
    · finiteness

noncomputable def infectionNonProductiveActiveMass
    (s : InfectionCfg) (h : 3 ≤ s.total) : ℝ≥0∞ :=
  infectionEventPMF s h .activeXXX +
    infectionEventPMF s h .activeYYY +
    infectionNotAllActiveMass s h

theorem infectionProductiveActiveMass_le_allActive
    (s : InfectionCfg) (h : 3 ≤ s.total) :
    infectionProductiveActiveMass s h ≤
      infectionAllActiveMass s h := by
  unfold infectionProductiveActiveMass
    infectionTypeOneMass infectionTypeTwoMass
    infectionAllActiveMass
  calc
    infectionEventPMF s h .activeXXY +
          infectionEventPMF s h .activeXYY ≤
        (infectionEventPMF s h .activeXXX +
          infectionEventPMF s h .activeXXY) +
          infectionEventPMF s h .activeXYY := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right
          (show
            infectionEventPMF s h .activeXXY ≤
              infectionEventPMF s h .activeXXX +
                infectionEventPMF s h .activeXXY from
            le_add_left le_rfl)
          (infectionEventPMF s h .activeXYY)
    _ ≤
        (infectionEventPMF s h .activeXXX +
          infectionEventPMF s h .activeXXY) +
          infectionEventPMF s h .activeXYY +
          infectionEventPMF s h .activeYYY :=
      le_add_right le_rfl
    _ = infectionEventPMF s h .activeXXX +
          infectionEventPMF s h .activeXXY +
          infectionEventPMF s h .activeXYY +
          infectionEventPMF s h .activeYYY := by
      ring

theorem infectionProductiveActiveMass_le_one
    (s : InfectionCfg) (h : 3 ≤ s.total) :
    infectionProductiveActiveMass s h ≤ 1 := by
  calc
    infectionProductiveActiveMass s h ≤
        infectionAllActiveMass s h :=
      infectionProductiveActiveMass_le_allActive s h
    _ ≤ 1 := by
      rw [← infectionAllActiveMasses_sum s h]
      exact le_add_right le_rfl

theorem infectionProductiveActiveMass_add_compl
    (s : InfectionCfg) (h : 3 ≤ s.total) :
    infectionProductiveActiveMass s h +
        infectionNonProductiveActiveMass s h = 1 := by
  unfold infectionProductiveActiveMass
    infectionTypeOneMass infectionTypeTwoMass
    infectionNonProductiveActiveMass
  rw [← infectionAllActiveMasses_sum s h]
  unfold infectionAllActiveMass
  ring

theorem infection_productive_weighted_compensated
    (s : InfectionCfg) (h : 3 ≤ s.total)
    (a G : ℕ)
    (ha : 4 ≤ a)
    (hG : 2 * G ≤ a)
    (hactive : a ≤ s.active)
    (hgap : s.ay ≤ s.ax + G) :
    (infectionReactionFactor a G)⁻¹ *
        (infectionTypeOneMass s h *
            infectionReactionDown +
          infectionTypeTwoMass s h *
            infectionReactionUp) ≤
      infectionProductiveActiveMass s h := by
  have hweighted :=
    infection_productive_weighted_bias
      s h a G ha hG hactive hgap
      infectionReactionDown infectionReactionUp
      (by
        unfold infectionReactionDown
          infectionReactionUp
        apply (ENNReal.div_le_iff
          (by norm_num) (by norm_num)).2
        rw [show
            (4 : ℝ≥0∞) / 3 * 4 =
              (16 : ℝ≥0∞) / 3 by
          simp only [div_eq_mul_inv]
          ring]
        apply (ENNReal.le_div_iff_mul_le
          (Or.inl (by norm_num))
          (Or.inl (by norm_num))).2
        norm_num)
      (by
        unfold infectionReactionDown
        finiteness)
      (by
        unfold infectionReactionUp
        finiteness)
  calc
    (infectionReactionFactor a G)⁻¹ *
        (infectionTypeOneMass s h *
            infectionReactionDown +
          infectionTypeTwoMass s h *
            infectionReactionUp)
        ≤ (infectionReactionFactor a G)⁻¹ *
          (infectionProductiveActiveMass s h *
            infectionReactionFactor a G) :=
      mul_le_mul_left' hweighted _
    _ = infectionProductiveActiveMass s h := by
      rw [mul_comm
          (infectionProductiveActiveMass s h)
          (infectionReactionFactor a G),
        ← mul_assoc,
        ENNReal.inv_mul_cancel
          (infectionReactionFactor_ne_zero
            a G (by omega) hG)
          (infectionReactionFactor_ne_top
            a G (by omega)),
        one_mul]

namespace InfectionEvent

def typeOneInc : InfectionEvent → ℕ
  | .activeXXY => 1
  | _ => 0

def typeTwoInc : InfectionEvent → ℕ
  | .activeXYY => 1
  | _ => 0

theorem typeOneInc_add_typeTwoInc
    (e : InfectionEvent) :
    e.typeOneInc + e.typeTwoInc =
      e.productiveActiveInc := by
  cases e <;>
    simp [typeOneInc, typeTwoInc,
      productiveActiveInc]

end InfectionEvent

structure InfectionReactionTraceState (n : ℕ) where
  current : InfectionState n
  typeOneCount : ℕ
  typeTwoCount : ℕ

noncomputable def InfectionReactionTraceState.afterEvent
    {n : ℕ} (q : InfectionReactionTraceState n)
    (e : InfectionEvent) :
    InfectionReactionTraceState n where
  current := InfectionEvent.nextState q.current e
  typeOneCount := q.typeOneCount + e.typeOneInc
  typeTwoCount := q.typeTwoCount + e.typeTwoInc

def InfectionReactionTraceStop
    {n : ℕ} (A G : ℕ)
    (q : InfectionReactionTraceState n) : Prop :=
  A ≤ q.current.1.active ∨
    q.current.1.ax + G < q.current.1.ay

noncomputable instance infectionReactionTraceStopDecidable
    {n : ℕ} (A G : ℕ) :
    DecidablePred
      (@InfectionReactionTraceStop n A G) :=
  Classical.decPred _

noncomputable def infectionReactionTraceStep
    (n : ℕ) (h3 : 3 ≤ n) (A G : ℕ) :
    InfectionReactionTraceState n →
      PMF (InfectionReactionTraceState n)
  | q =>
      if InfectionReactionTraceStop A G q then
        PMF.pure q
      else
        (infectionEventPMF q.current.1 (by
          have hq := q.current.2
          simp only [InfectionCfg.Inv] at hq
          omega)).map q.afterEvent

noncomputable def infectionReactionPotential
    {n : ℕ} (a G : ℕ)
    (q : InfectionReactionTraceState n) : ℝ≥0∞ :=
  (infectionReactionFactor a G)⁻¹ ^
      (q.typeOneCount + q.typeTwoCount) *
    infectionReactionDown ^ q.typeOneCount *
    infectionReactionUp ^ q.typeTwoCount

theorem infectionReactionPotential_afterEvent
    {n : ℕ} (a G : ℕ)
    (q : InfectionReactionTraceState n)
    (e : InfectionEvent) :
    infectionReactionPotential a G (q.afterEvent e) =
      match e with
      | .activeXXY =>
          (infectionReactionFactor a G)⁻¹ *
            infectionReactionDown *
              infectionReactionPotential a G q
      | .activeXYY =>
          (infectionReactionFactor a G)⁻¹ *
            infectionReactionUp *
              infectionReactionPotential a G q
      | _ => infectionReactionPotential a G q := by
  cases e <;>
    simp [infectionReactionPotential,
      InfectionReactionTraceState.afterEvent,
      InfectionEvent.typeOneInc,
      InfectionEvent.typeTwoInc,
      pow_succ] <;>
    ring

theorem expect_infectionReactionTraceStep_potential_of_live
    (n : ℕ) (h3 : 3 ≤ n)
    (a A G : ℕ)
    (ha : 4 ≤ a)
    (hG : 2 * G ≤ a)
    (q : InfectionReactionTraceState n)
    (hlive : ¬ InfectionReactionTraceStop A G q)
    (hactive : a ≤ q.current.1.active) :
    expect (infectionReactionTraceStep n h3 A G q)
        (infectionReactionPotential a G) ≤
      infectionReactionPotential a G q := by
  have hgap :
      q.current.1.ay ≤ q.current.1.ax + G := by
    unfold InfectionReactionTraceStop at hlive
    push Not at hlive
    omega
  have htotal : q.current.1.total = n :=
    q.current.2
  let hn : 3 ≤ q.current.1.total := by
    omega
  let P := infectionReactionPotential a G q
  have hcomp :=
    infection_productive_weighted_compensated
      q.current.1 hn a G ha hG hactive hgap
  have hpartition :=
    infectionProductiveActiveMass_add_compl
      q.current.1 hn
  unfold infectionReactionTraceStep
  rw [if_neg hlive, expect_map]
  unfold expect
  rw [tsum_fintype]
  rw [show
      (Finset.univ : Finset InfectionEvent) =
        {InfectionEvent.activeXXX,
          InfectionEvent.activeXXY,
          InfectionEvent.activeXYY,
          InfectionEvent.activeYYY,
          InfectionEvent.activateOneX,
          InfectionEvent.activateOneY,
          InfectionEvent.activateTwoXX,
          InfectionEvent.activateTwoXY,
          InfectionEvent.activateTwoYY,
          InfectionEvent.inactiveOnly} from rfl]
  simp only [infectionReactionPotential_afterEvent]
  have hweighted :
      infectionNonProductiveActiveMass
            q.current.1 hn * P +
          ((infectionReactionFactor a G)⁻¹ *
            (infectionTypeOneMass q.current.1 hn *
                infectionReactionDown +
              infectionTypeTwoMass q.current.1 hn *
                infectionReactionUp)) * P ≤
        P := by
    calc
      infectionNonProductiveActiveMass
              q.current.1 hn * P +
            ((infectionReactionFactor a G)⁻¹ *
              (infectionTypeOneMass q.current.1 hn *
                  infectionReactionDown +
                infectionTypeTwoMass q.current.1 hn *
                  infectionReactionUp)) * P
          ≤ infectionNonProductiveActiveMass
                q.current.1 hn * P +
              infectionProductiveActiveMass
                q.current.1 hn * P :=
        by
          simpa [mul_comm, mul_left_comm,
            mul_assoc, add_comm, add_left_comm,
            add_assoc] using
            add_le_add_left
              (mul_le_mul_right hcomp P)
              (infectionNonProductiveActiveMass
                q.current.1 hn * P)
      _ = P := by
        rw [← add_mul, add_comm,
          hpartition, one_mul]
  have heq :
      (∑ x ∈
          {InfectionEvent.activeXXX,
            InfectionEvent.activeXXY,
            InfectionEvent.activeXYY,
            InfectionEvent.activeYYY,
            InfectionEvent.activateOneX,
            InfectionEvent.activateOneY,
            InfectionEvent.activateTwoXX,
            InfectionEvent.activateTwoXY,
            InfectionEvent.activateTwoYY,
            InfectionEvent.inactiveOnly},
          infectionEventPMF q.current.1 hn x *
            match x with
            | .activeXXY =>
                (infectionReactionFactor a G)⁻¹ *
                  infectionReactionDown *
                    infectionReactionPotential a G q
            | .activeXYY =>
                (infectionReactionFactor a G)⁻¹ *
                  infectionReactionUp *
                    infectionReactionPotential a G q
            | _ =>
                infectionReactionPotential a G q) =
        infectionNonProductiveActiveMass
              q.current.1 hn * P +
            ((infectionReactionFactor a G)⁻¹ *
              (infectionTypeOneMass q.current.1 hn *
                  infectionReactionDown +
                infectionTypeTwoMass q.current.1 hn *
                  infectionReactionUp)) * P := by
    unfold infectionNonProductiveActiveMass
      infectionNotAllActiveMass
      infectionActivationMass
      infectionActivationOneMass
      infectionActivationTwoMass
      infectionTypeOneMass infectionTypeTwoMass
    dsimp only [P]
    simp
    ring
  rw [heq]
  exact hweighted

theorem expect_infectionReactionTraceStep_potential
    (n : ℕ) (h3 : 3 ≤ n)
    (a A G : ℕ)
    (ha : 4 ≤ a)
    (hG : 2 * G ≤ a)
    (q : InfectionReactionTraceState n)
    (hactive : a ≤ q.current.1.active) :
    expect (infectionReactionTraceStep n h3 A G q)
        (infectionReactionPotential a G) ≤
      infectionReactionPotential a G q := by
  by_cases hstop :
      InfectionReactionTraceStop A G q
  · unfold infectionReactionTraceStep
    rw [if_pos hstop, expect_pure]
  · exact
      expect_infectionReactionTraceStep_potential_of_live
        n h3 a A G ha hG q hstop hactive

theorem infectionReactionDown_mul_up :
    infectionReactionDown * infectionReactionUp = 1 := by
  unfold infectionReactionDown infectionReactionUp
  calc
    (3 : ℝ≥0∞) / 4 * (4 / 3) =
        ((3 : ℝ≥0∞) / 4 * 4) / 3 := by
      simp only [div_eq_mul_inv]
      ring
    _ = (3 : ℝ≥0∞) / 3 := by
      rw [ENNReal.div_mul_cancel
        (by norm_num) (by norm_num)]
    _ = 1 := ENNReal.div_self
      (by norm_num) (by norm_num)

theorem infectionReactionUp_ge_one :
    1 ≤ infectionReactionUp := by
  unfold infectionReactionUp
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (by norm_num))
    (Or.inl (by norm_num))).2
  norm_num

theorem infectionReactionDown_ne_zero :
    infectionReactionDown ≠ 0 := by
  unfold infectionReactionDown
  norm_num

theorem infectionReactionUp_ne_zero :
    infectionReactionUp ≠ 0 := by
  unfold infectionReactionUp
  norm_num

theorem infectionReactionDown_ne_top :
    infectionReactionDown ≠ ⊤ := by
  unfold infectionReactionDown
  finiteness

theorem infectionReactionUp_ne_top :
    infectionReactionUp ≠ ⊤ := by
  unfold infectionReactionUp
  finiteness

theorem infectionReactionTraceStep_active_closed
    (n : ℕ) (h3 : 3 ≤ n) (A G a : ℕ)
    (q z : InfectionReactionTraceState n)
    (hq : a ≤ q.current.1.active)
    (hz :
      infectionReactionTraceStep n h3 A G q z ≠ 0) :
    a ≤ z.current.1.active := by
  by_cases hstop :
      InfectionReactionTraceStop A G q
  · unfold infectionReactionTraceStep at hz
    rw [if_pos hstop] at hz
    have hzq : z = q := by
      by_contra hne
      simp [PMF.pure_apply, hne] at hz
    simpa [hzq] using hq
  · unfold infectionReactionTraceStep at hz
    rw [if_neg hstop] at hz
    have hzmem :
        z ∈
          ((infectionEventPMF q.current.1 (by
            have hqInv := q.current.2
            simp only [InfectionCfg.Inv] at hqInv
            omega)).map q.afterEvent).support :=
      hz
    rw [PMF.support_map] at hzmem
    rcases hzmem with ⟨e, he, rfl⟩
    exact hq.trans
      (InfectionEvent.active_le_nextState_active
        q.current e)

theorem infectionReactionPotential_threshold
    {n : ℕ} (a G H M : ℕ)
    (ha : 0 < a)
    (hG : 2 * G ≤ a)
    (q : InfectionReactionTraceState n)
    (hexposure :
      q.typeOneCount + q.typeTwoCount ≤ H)
    (hexcess :
      q.typeOneCount + M ≤ q.typeTwoCount) :
    (infectionReactionFactor a G)⁻¹ ^ H *
        infectionReactionUp ^ M ≤
      infectionReactionPotential a G q := by
  have hfactorInv :
      (infectionReactionFactor a G)⁻¹ ≤ 1 := by
    exact ENNReal.inv_le_one.mpr
      (infectionReactionFactor_ge_one
        a G ha hG)
  have hcomp :
      (infectionReactionFactor a G)⁻¹ ^ H ≤
        (infectionReactionFactor a G)⁻¹ ^
          (q.typeOneCount + q.typeTwoCount) :=
    pow_le_pow_right_of_le_one' hfactorInv hexposure
  have hup :
      infectionReactionUp ^
          (q.typeOneCount + M) ≤
        infectionReactionUp ^ q.typeTwoCount :=
    pow_le_pow_right₀ infectionReactionUp_ge_one
      hexcess
  have hcancel :
      infectionReactionDown ^ q.typeOneCount *
          infectionReactionUp ^
            (q.typeOneCount + M) =
        infectionReactionUp ^ M := by
    rw [pow_add, ← mul_assoc,
      ← mul_pow, infectionReactionDown_mul_up,
      one_pow, one_mul]
  unfold infectionReactionPotential
  calc
    (infectionReactionFactor a G)⁻¹ ^ H *
          infectionReactionUp ^ M =
        (infectionReactionFactor a G)⁻¹ ^ H *
          (infectionReactionDown ^
              q.typeOneCount *
            infectionReactionUp ^
              (q.typeOneCount + M)) := by
            rw [hcancel]
    _ ≤
        (infectionReactionFactor a G)⁻¹ ^
            (q.typeOneCount + q.typeTwoCount) *
          (infectionReactionDown ^
              q.typeOneCount *
            infectionReactionUp ^
              q.typeTwoCount) :=
      mul_le_mul hcomp
        (mul_le_mul_left' hup _) bot_le bot_le
    _ =
        (infectionReactionFactor a G)⁻¹ ^
            (q.typeOneCount + q.typeTwoCount) *
          infectionReactionDown ^ q.typeOneCount *
          infectionReactionUp ^ q.typeTwoCount := by
      ring

theorem infectionReactionTrace_tail
    (n : ℕ) (h3 : 3 ≤ n)
    (a A G : ℕ)
    (ha : 4 ≤ a)
    (hG : 2 * G ≤ a)
    (s : InfectionState n)
    (hstart : a ≤ s.1.active)
    (T H M : ℕ) :
    (∑' z,
      if z.typeOneCount + z.typeTwoCount ≤ H ∧
          z.typeOneCount + M ≤ z.typeTwoCount
      then
        iter (infectionReactionTraceStep n h3 A G) T
          ⟨s, 0, 0⟩ z
      else 0) ≤
    1 /
      ((infectionReactionFactor a G)⁻¹ ^ H *
        infectionReactionUp ^ M) := by
  let K := infectionReactionTraceStep n h3 A G
  let V : InfectionReactionTraceState n → ℝ≥0∞ :=
    infectionReactionPotential a G
  let q₀ : InfectionReactionTraceState n :=
    ⟨s, 0, 0⟩
  let theta : ℝ≥0∞ :=
    (infectionReactionFactor a G)⁻¹ ^ H *
      infectionReactionUp ^ M
  have hfactorInv0 :
      (infectionReactionFactor a G)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr
      (infectionReactionFactor_ne_top
        a G (by omega))
  have hfactorInvTop :
      (infectionReactionFactor a G)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr
      (infectionReactionFactor_ne_zero
        a G (by omega) hG)
  have htheta0 : theta ≠ 0 :=
    mul_ne_zero
      (pow_ne_zero _ hfactorInv0)
      (pow_ne_zero _ infectionReactionUp_ne_zero)
  have hthetaTop : theta ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.pow_ne_top hfactorInvTop)
      (ENNReal.pow_ne_top
        infectionReactionUp_ne_top)
  have hsub : ∀ z,
      (if z.typeOneCount + z.typeTwoCount ≤ H ∧
            z.typeOneCount + M ≤ z.typeTwoCount
        then iter K T q₀ z else 0) ≤
      (if theta ≤ V z then
          iter K T q₀ z else 0) := by
    intro z
    by_cases hz :
        z.typeOneCount + z.typeTwoCount ≤ H ∧
          z.typeOneCount + M ≤ z.typeTwoCount
    · have hV : theta ≤ V z := by
        exact infectionReactionPotential_threshold
          a G H M (by omega) hG z hz.1 hz.2
      simp [hz, hV]
    · simp [hz]
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  refine le_trans
    (markov_div
      (iter K T q₀) V theta
      htheta0 hthetaTop) ?_
  have hiter :=
    expect_iter_le_of_support_invariant
      K
      (fun q : InfectionReactionTraceState n =>
        a ≤ q.current.1.active)
      V 1
      (fun q hq z hz =>
        infectionReactionTraceStep_active_closed
          n h3 A G a q z hq hz)
      (fun q hq => by
        simpa [K, V] using
          expect_infectionReactionTraceStep_potential
            n h3 a A G ha hG q hq)
      T q₀ hstart
  apply ENNReal.div_le_div_right _ theta
  simpa [V, q₀, infectionReactionPotential]
    using hiter

end Tri

#print axioms Tri.weighted_two_mass_mono_ennreal
#print axioms Tri.infection_productive_weighted_bias
#print axioms Tri.infectionReactionFactor_ge_one
#print axioms Tri.infection_productive_weighted_compensated
#print axioms Tri.infectionReactionPotential_afterEvent
#print axioms Tri.expect_infectionReactionTraceStep_potential
#print axioms Tri.infectionReactionPotential_threshold
#print axioms Tri.infectionReactionTrace_tail
