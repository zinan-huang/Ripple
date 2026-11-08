/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Multiplicative Phase-1 far-mass drift

The one-witness argument in `Phase1FarPhiDrift` gives only a fixed strict-drop
probability.  Here both far sides are counted simultaneously.  The two ordered
rectangles

* `farHighSet × lowSet`, and
* `farLowSet × highSet`

are disjoint in their first coordinate, so their scheduler masses add.  Every
cell drops `farPhiN` by at least one, while every unit of `farPhiN` is charged
to at most two far agents.  This yields a drop probability, and hence a
weighted expected decrease, proportional to the current potential.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1FarPhiDrift
import Ripple.PopulationProtocol.ExactMajority.Probability.WeightedDriftDropSum

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase1FarPhiMultiplicative

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## The potential is controlled by the number of far agents -/

/-- Pointwise form of the fact that `farPhi` is at most two and is supported
exactly on the two far sides. -/
theorem farPhi_le_two_mul_farIndicators (v : Fin 7) :
    Phase1FarPhi.farPhi v ≤
      2 * ((if v.val ≤ 1 then 1 else 0) + (if 5 ≤ v.val then 1 else 0)) := by
  revert v
  decide

/-- Each Main contribution is at most twice its far-side indicator. -/
theorem farPhiMainN_le_two_mul_farIndicators (a : AgentState L K) :
    Phase1FarPhi.farPhiMainN a ≤
      2 * ((if AveragingRate.farLow a then 1 else 0) +
        (if AveragingRate.farHigh a then 1 else 0)) := by
  by_cases hmain : a.role = Role.main
  · simp only [Phase1FarPhi.farPhiMainN, hmain, if_pos,
      AveragingRate.farLow, AveragingRate.farHigh, true_and]
    exact farPhi_le_two_mul_farIndicators a.smallBias
  · simp [Phase1FarPhi.farPhiMainN, AveragingRate.farLow,
      AveragingRate.farHigh, hmain]

/-- Finset-count presentation of the far-low population. -/
theorem farLowSet_sum_count_eq (c : Config (AgentState L K)) :
    (AveragingRate.farLowSet L K).sum c.count =
      Multiset.countP (fun a : AgentState L K => AveragingRate.farLow a) c := by
  classical
  rw [AveragingRate.farLowSet]
  exact PartnerMargin.sum_count_filter_eq_countP
    (fun a : AgentState L K => AveragingRate.farLow a) c

/-- Finset-count presentation of the far-high population. -/
theorem farHighSet_sum_count_eq (c : Config (AgentState L K)) :
    (AveragingRate.farHighSet L K).sum c.count =
      Multiset.countP (fun a : AgentState L K => AveragingRate.farHigh a) c := by
  classical
  rw [AveragingRate.farHighSet]
  exact PartnerMargin.sum_count_filter_eq_countP
    (fun a : AgentState L K => AveragingRate.farHigh a) c

/-- The total clamped far mass is at most twice the number of far Mains. -/
theorem farPhiN_le_two_mul_farCount (c : Config (AgentState L K)) :
    Phase1FarPhi.farPhiN c ≤
      2 * ((AveragingRate.farHighSet L K).sum c.count +
        (AveragingRate.farLowSet L K).sum c.count) := by
  classical
  unfold Phase1FarPhi.farPhiN
  calc
    (c.map (fun a => Phase1FarPhi.farPhiMainN a)).sum
        ≤ (c.map (fun a =>
            2 * ((if AveragingRate.farLow a then 1 else 0) +
              (if AveragingRate.farHigh a then 1 else 0)))).sum :=
          Multiset.sum_map_le_sum_map _ _
            (fun a _ => farPhiMainN_le_two_mul_farIndicators a)
    _ = 2 * (Multiset.countP
          (fun a : AgentState L K => AveragingRate.farLow a) c +
        Multiset.countP
          (fun a : AgentState L K => AveragingRate.farHigh a) c) := by
          induction c using Multiset.induction with
          | empty => simp
          | cons a c ih =>
              rw [Multiset.map_cons, Multiset.sum_cons,
                Multiset.countP_cons, Multiset.countP_cons, ih]
              split_ifs <;> omega
    _ = 2 * ((AveragingRate.farHighSet L K).sum c.count +
        (AveragingRate.farLowSet L K).sum c.count) := by
          rw [farLowSet_sum_count_eq, farHighSet_sum_count_eq]
          omega

/-! ## One disjoint union of the two strict-drop rectangles -/

/-- The two far-side state sets are disjoint. -/
theorem farHighSet_disjoint_farLowSet :
    Disjoint (AveragingRate.farHighSet L K)
      (AveragingRate.farLowSet L K) := by
  rw [Finset.disjoint_left]
  intro a hhigh hlow
  simp only [AveragingRate.farHighSet, AveragingRate.farLowSet,
    Finset.mem_filter, AveragingRate.farHigh, AveragingRate.farLow] at hhigh hlow
  omega

/-- The union of all ordered far-by-partner rectangles. -/
def farDropRect (L K : ℕ) : Finset (AgentState L K × AgentState L K) :=
  ((AveragingRate.farHighSet L K) ×ˢ (AveragingRate.lowSet L K)) ∪
    ((AveragingRate.farLowSet L K) ×ˢ (AveragingRate.highSet L K))

/-- The two component rectangles are disjoint, so their scheduler masses add. -/
theorem farDropRect_components_disjoint :
    Disjoint
      ((AveragingRate.farHighSet L K) ×ˢ (AveragingRate.lowSet L K))
      ((AveragingRate.farLowSet L K) ×ˢ (AveragingRate.highSet L K)) := by
  exact Finset.disjoint_product.mpr
    (Or.inl (farHighSet_disjoint_farLowSet (L := L) (K := K)))

/-- Exact interaction-count mass of the disjoint rectangle union. -/
theorem sum_interactionCount_farDropRect (c : Config (AgentState L K)) :
    (∑ p ∈ farDropRect L K, c.interactionCount p.1 p.2) =
      (AveragingRate.farHighSet L K).sum c.count *
          (AveragingRate.lowSet L K).sum c.count +
        (AveragingRate.farLowSet L K).sum c.count *
          (AveragingRate.highSet L K).sum c.count := by
  classical
  unfold farDropRect
  rw [Finset.sum_union (farDropRect_components_disjoint (L := L) (K := K)),
    Phase7Convergence.sum_interactionCount_cross_disjoint7 c _ _
      AveragingRate.farHigh_low_disjoint,
    Phase7Convergence.sum_interactionCount_cross_disjoint7 c _ _
      AveragingRate.farLow_high_disjoint]

/-- Every present pair in the union is an applicable strict-drop pair. -/
theorem farDropRect_step_drop (n : ℕ) (c : Config (AgentState L K))
    (hInv : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (p : AgentState L K × AgentState L K) (hp : p ∈ farDropRect L K)
    (hp1 : 1 ≤ c.count p.1) (hp2 : 1 ≤ c.count p.2) :
    Phase1FarPhi.farPhiN
        (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) + 1
      ≤ Phase1FarPhi.farPhiN c := by
  classical
  have hm1 : p.1 ∈ c := Multiset.one_le_count_iff_mem.mp hp1
  have hm2 : p.2 ∈ c := Multiset.one_le_count_iff_mem.mp hp2
  unfold farDropRect at hp
  rw [Finset.mem_union] at hp
  rcases hp with hp | hp
  · rw [Finset.mem_product] at hp
    obtain ⟨hph, hpl⟩ := hp
    have hne := AveragingRate.farHigh_low_disjoint p.1 hph p.2 hpl
    have happ : Protocol.Applicable c p.1 p.2 :=
      Phase5Convergence.applicable_of_mem_distinct5 hm1 hm2 hne
    simp only [AveragingRate.farHighSet, Finset.mem_filter] at hph
    simp only [AveragingRate.lowSet, Finset.mem_filter] at hpl
    exact Phase1FarPhiDrift.farPhiN_stepOrSelf_drop_high
      n c hInv p.1 p.2 happ hph.2 hpl.2
  · rw [Finset.mem_product] at hp
    obtain ⟨hpl, hph⟩ := hp
    have hne := AveragingRate.farLow_high_disjoint p.1 hpl p.2 hph
    have happ : Protocol.Applicable c p.1 p.2 :=
      Phase5Convergence.applicable_of_mem_distinct5 hm1 hm2 hne
    simp only [AveragingRate.farLowSet, Finset.mem_filter] at hpl
    simp only [AveragingRate.highSet, Finset.mem_filter] at hph
    exact Phase1FarPhiDrift.farPhiN_stepOrSelf_drop_low
      n c hInv p.1 p.2 happ hpl.2 hph.2

/-- The interaction-count mass of the union is at least the partner floor times
the number of far agents. -/
theorem partnerFloor_mul_farCount_le_rectMass (n g mc : ℕ)
    (c : Config (AgentState L K))
    (hentry : Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c) :
    ((mc - g + 3) / 4) *
        ((AveragingRate.farHighSet L K).sum c.count +
          (AveragingRate.farLowSet L K).sum c.count)
      ≤ ∑ p ∈ farDropRect L K, c.interactionCount p.1 p.2 := by
  rw [sum_interactionCount_farDropRect]
  have hlow := Phase1PartnerFloor.lowSet_floor_of_phase1GapFloorEntry
    (L := L) (K := K) n g mc c hentry
  have hhigh := Phase1FarPhiDrift.highSet_floor_of_phase1GapFloorEntry
    (L := L) (K := K) n g mc c hentry
  rw [Nat.mul_add]
  exact Nat.add_le_add
    (by simpa [mul_comm] using
      Nat.mul_le_mul_left ((AveragingRate.farHighSet L K).sum c.count) hlow)
    (by simpa [mul_comm] using
      Nat.mul_le_mul_left ((AveragingRate.farLowSet L K).sum c.count) hhigh)

/-! ## Potential-proportional drop probability -/

/-- Real and `ENNReal` presentations of the uniform-scheduler rate agree. -/
theorem ofReal_scheduler_rate_eq (n N : ℕ) (hn : 2 ≤ n) :
    ENNReal.ofReal ((N : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) =
      (N : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
  have hden_pos : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by omega : 0 < n) (by omega : 0 < n - 1)
  have hdenR : ((n * (n - 1) : ℕ) : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [← hdenR, ← ENNReal.ofReal_natCast N,
    ← ENNReal.ofReal_natCast (n * (n - 1)),
    ENNReal.ofReal_div_of_pos hden_pos]

/-- The per-unit multiplicative strict-drop rate.  The factor two is exactly
the maximum contribution of one far agent to `farPhiN`. -/
noncomputable def farBeta (n g mc : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((((mc - g + 3) / 4 : ℕ) : ℝ) /
    (2 * ((n : ℝ) * ((n : ℝ) - 1))))

/-- The union rectangle gives a strict-drop probability proportional to the
current value of `farPhiN`. -/
theorem farPhiN_drop_prob_multiplicative {n g mc : ℕ} (hn : 2 ≤ n)
    (c : Config (AgentState L K))
    (hentry : Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c) :
    farBeta n g mc * (Phase1FarPhi.farPhiN c : ℝ≥0∞) ≤
      (NonuniformMajority L K).transitionKernel c
        {c' | Phase1FarPhi.farPhiN c' + 1 ≤ Phase1FarPhi.farPhiN c} := by
  classical
  let P : ℕ := (mc - g + 3) / 4
  let F : ℕ := (AveragingRate.farHighSet L K).sum c.count +
    (AveragingRate.farLowSet L K).sum c.count
  have hΦ : Phase1FarPhi.farPhiN c ≤ 2 * F := by
    simpa [F] using farPhiN_le_two_mul_farCount (L := L) (K := K) c
  have hcount : P * F ≤
      ∑ p ∈ farDropRect L K, c.interactionCount p.1 p.2 := by
    simpa [P, F] using partnerFloor_mul_farCount_le_rectMass
      (L := L) (K := K) n g mc c hentry
  have hrect := Phase7Convergence.drop_prob_of_rect
    (fun b : Config (AgentState L K) => Phase1FarPhi.farPhiN b)
    n hn c hentry.1.1 (farDropRect L K) (P * F)
    (by
      intro p hp hp1 hp2 _
      exact farDropRect_step_drop n c hentry.1 p hp hp1 hp2)
    hcount
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hΦR : (Phase1FarPhi.farPhiN c : ℝ) ≤ 2 * (F : ℝ) := by
    exact_mod_cast hΦ
  have hmul : (P : ℝ) * (Phase1FarPhi.farPhiN c : ℝ) ≤
      2 * ((P : ℝ) * (F : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hΦR (by positivity : (0 : ℝ) ≤ (P : ℝ))
    nlinarith
  have hreal :
      (((P : ℝ) / (2 * ((n : ℝ) * ((n : ℝ) - 1)))) *
          (Phase1FarPhi.farPhiN c : ℝ)) ≤
        (((P * F : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) := by
    have hden2 : (0 : ℝ) < 2 * ((n : ℝ) * ((n : ℝ) - 1)) := by
      nlinarith
    calc
      ((P : ℝ) / (2 * ((n : ℝ) * ((n : ℝ) - 1))) *
          (Phase1FarPhi.farPhiN c : ℝ))
          = ((P : ℝ) * (Phase1FarPhi.farPhiN c : ℝ)) /
              (2 * ((n : ℝ) * ((n : ℝ) - 1))) := by ring
      _ ≤ (2 * ((P : ℝ) * (F : ℝ))) /
              (2 * ((n : ℝ) * ((n : ℝ) - 1))) :=
            (div_le_div_iff_of_pos_right hden2).2 hmul
      _ = (((P * F : ℕ) : ℝ) /
              ((n : ℝ) * ((n : ℝ) - 1))) := by
            rw [Nat.cast_mul,
              mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
  refine le_trans ?_ hrect
  unfold farBeta
  change ENNReal.ofReal ((P : ℝ) /
      (2 * ((n : ℝ) * ((n : ℝ) - 1)))) *
      (Phase1FarPhi.farPhiN c : ℝ≥0∞) ≤ _
  rw [← ENNReal.ofReal_natCast (Phase1FarPhi.farPhiN c),
    ← ENNReal.ofReal_mul (by positivity :
      (0 : ℝ) ≤ (P : ℝ) / (2 * ((n : ℝ) * ((n : ℝ) - 1))))]
  exact ENNReal.ofReal_le_ofReal hreal

/-! ## Weighted drop and multiplicative expectation -/

/-- The scheduler probability mass of the union, in exact count form. -/
theorem sum_interactionProb_farDropRect (n : ℕ)
    (c : Config (AgentState L K)) (hcard : c.card = n) :
    (∑ p ∈ farDropRect L K, c.interactionProb p.1 p.2) =
      (((AveragingRate.farHighSet L K).sum c.count *
            (AveragingRate.lowSet L K).sum c.count +
          (AveragingRate.farLowSet L K).sum c.count *
            (AveragingRate.highSet L K).sum c.count : ℕ) : ℝ≥0∞) /
        ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
  classical
  simp only [Config.interactionProb, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum,
    sum_interactionCount_farDropRect, Config.totalPairs, hcard]

/-- On the union rectangle, one unit of scheduler mass is bounded by the
scheduler-weighted potential drop. -/
theorem interactionProb_le_weightedDropTerm (n : ℕ)
    (c : Config (AgentState L K))
    (hInv : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (p : AgentState L K × AgentState L K) (hp : p ∈ farDropRect L K) :
    c.interactionProb p.1 p.2 ≤
      ((Phase1FarPhi.farPhiN c : ℝ≥0∞) -
          (Phase1FarPhi.farPhiN
            (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) : ℝ≥0∞)) *
        c.interactionProb p.1 p.2 := by
  classical
  unfold farDropRect at hp
  rw [Finset.mem_union] at hp
  have hne : p.1 ≠ p.2 := by
    rcases hp with hp | hp
    · rw [Finset.mem_product] at hp
      exact AveragingRate.farHigh_low_disjoint p.1 hp.1 p.2 hp.2
    · rw [Finset.mem_product] at hp
      exact AveragingRate.farLow_high_disjoint p.1 hp.1 p.2 hp.2
  by_cases hp1 : 1 ≤ c.count p.1
  · by_cases hp2 : 1 ≤ c.count p.2
    · have hdrop := farDropRect_step_drop n c hInv p (by
          unfold farDropRect
          rw [Finset.mem_union]
          exact hp) hp1 hp2
      have hdropNat : 1 ≤ Phase1FarPhi.farPhiN c -
          Phase1FarPhi.farPhiN
            (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) := by
        omega
      have hdropE : (1 : ℝ≥0∞) ≤
          (Phase1FarPhi.farPhiN c : ℝ≥0∞) -
            (Phase1FarPhi.farPhiN
              (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) : ℝ≥0∞) := by
        simpa only [ENNReal.natCast_sub] using (show
          (1 : ℝ≥0∞) ≤ ((Phase1FarPhi.farPhiN c -
            Phase1FarPhi.farPhiN
              (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) : ℕ) : ℝ≥0∞) by
              exact_mod_cast hdropNat)
      calc
        c.interactionProb p.1 p.2 = 1 * c.interactionProb p.1 p.2 := by rw [one_mul]
        _ ≤ ((Phase1FarPhi.farPhiN c : ℝ≥0∞) -
              (Phase1FarPhi.farPhiN
                (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) : ℝ≥0∞)) *
              c.interactionProb p.1 p.2 := by gcongr
    · have hz2 : c.count p.2 = 0 := by omega
      simp [Config.interactionProb, Config.interactionCount, hne, hz2]
  · have hz1 : c.count p.1 = 0 := by omega
    simp [Config.interactionProb, Config.interactionCount, hne, hz1]

/-- The all-far rectangle lower-bounds the weighted drop sum by `farBeta` times
the current potential. -/
theorem farPhiN_weightedDropSum_floor {n g mc : ℕ} (hn : 2 ≤ n)
    (c : Config (AgentState L K))
    (hentry : Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c) :
    farBeta n g mc * (Phase1FarPhi.farPhiN c : ℝ≥0∞) ≤
      WeightedDriftDropSum.weightedDropSum (NonuniformMajority L K)
        Phase1FarPhi.farPhiN c := by
  classical
  let P : ℕ := (mc - g + 3) / 4
  let F : ℕ := (AveragingRate.farHighSet L K).sum c.count +
    (AveragingRate.farLowSet L K).sum c.count
  have hΦ : Phase1FarPhi.farPhiN c ≤ 2 * F := by
    simpa [F] using farPhiN_le_two_mul_farCount (L := L) (K := K) c
  have hcount : P * F ≤
      (AveragingRate.farHighSet L K).sum c.count *
          (AveragingRate.lowSet L K).sum c.count +
        (AveragingRate.farLowSet L K).sum c.count *
          (AveragingRate.highSet L K).sum c.count := by
    have hm := partnerFloor_mul_farCount_le_rectMass
      (L := L) (K := K) n g mc c hentry
    rw [sum_interactionCount_farDropRect] at hm
    simpa [P, F] using hm
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hΦR : (Phase1FarPhi.farPhiN c : ℝ) ≤ 2 * (F : ℝ) := by
    exact_mod_cast hΦ
  have hmul : (P : ℝ) * (Phase1FarPhi.farPhiN c : ℝ) ≤
      2 * ((P : ℝ) * (F : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hΦR (by positivity : (0 : ℝ) ≤ (P : ℝ))
    nlinarith
  have hbetaPF : farBeta n g mc * (Phase1FarPhi.farPhiN c : ℝ≥0∞) ≤
      ENNReal.ofReal (((P * F : ℕ) : ℝ) /
        ((n : ℝ) * ((n : ℝ) - 1))) := by
    have hden2 : (0 : ℝ) < 2 * ((n : ℝ) * ((n : ℝ) - 1)) := by
      nlinarith
    have hreal :
        (((P : ℝ) / (2 * ((n : ℝ) * ((n : ℝ) - 1)))) *
            (Phase1FarPhi.farPhiN c : ℝ)) ≤
          (((P * F : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) := by
      calc
        ((P : ℝ) / (2 * ((n : ℝ) * ((n : ℝ) - 1))) *
            (Phase1FarPhi.farPhiN c : ℝ))
            = ((P : ℝ) * (Phase1FarPhi.farPhiN c : ℝ)) /
                (2 * ((n : ℝ) * ((n : ℝ) - 1))) := by ring
        _ ≤ (2 * ((P : ℝ) * (F : ℝ))) /
                (2 * ((n : ℝ) * ((n : ℝ) - 1))) :=
              (div_le_div_iff_of_pos_right hden2).2 hmul
        _ = (((P * F : ℕ) : ℝ) /
                ((n : ℝ) * ((n : ℝ) - 1))) := by
              rw [Nat.cast_mul,
                mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
    unfold farBeta
    change ENNReal.ofReal ((P : ℝ) /
        (2 * ((n : ℝ) * ((n : ℝ) - 1)))) *
        (Phase1FarPhi.farPhiN c : ℝ≥0∞) ≤ _
    rw [← ENNReal.ofReal_natCast (Phase1FarPhi.farPhiN c),
      ← ENNReal.ofReal_mul (by positivity :
        (0 : ℝ) ≤ (P : ℝ) / (2 * ((n : ℝ) * ((n : ℝ) - 1))))]
    exact ENNReal.ofReal_le_ofReal hreal
  have hmass : ENNReal.ofReal (((P * F : ℕ) : ℝ) /
        ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ∑ p ∈ farDropRect L K, c.interactionProb p.1 p.2 := by
    rw [ofReal_scheduler_rate_eq n (P * F) hn,
      sum_interactionProb_farDropRect n c hentry.1.1]
    gcongr
  have hrect : (∑ p ∈ farDropRect L K, c.interactionProb p.1 p.2) ≤
      ∑ p : AgentState L K × AgentState L K,
        ((Phase1FarPhi.farPhiN c : ℝ≥0∞) -
            (Phase1FarPhi.farPhiN
              (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) : ℝ≥0∞)) *
          c.interactionProb p.1 p.2 := by
    calc
      (∑ p ∈ farDropRect L K, c.interactionProb p.1 p.2)
          ≤ ∑ p ∈ farDropRect L K,
              ((Phase1FarPhi.farPhiN c : ℝ≥0∞) -
                  (Phase1FarPhi.farPhiN
                    (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) : ℝ≥0∞)) *
                c.interactionProb p.1 p.2 :=
            Finset.sum_le_sum (fun p hp =>
              interactionProb_le_weightedDropTerm n c hentry.1 p hp)
      _ ≤ ∑ p : AgentState L K × AgentState L K,
          ((Phase1FarPhi.farPhiN c : ℝ≥0∞) -
              (Phase1FarPhi.farPhiN
                (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) : ℝ≥0∞)) *
            c.interactionProb p.1 p.2 := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => bot_le)
  exact hbetaPF.trans (hmass.trans (hrect.trans_eq rfl))

/-- The corrected one-step multiplicative expectation, in exactly the shape
consumed by `DriftSurvival`. -/
theorem farPhiN_multiplicative_drift {n g mc : ℕ} (hn : 2 ≤ n)
    (c : Config (AgentState L K))
    (hentry : Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c) :
    ∫⁻ c', (Phase1FarPhi.farPhiN c' : ℝ≥0∞)
        ∂((NonuniformMajority L K).transitionKernel c)
      ≤ (1 - farBeta n g mc) * (Phase1FarPhi.farPhiN c : ℝ≥0∞) := by
  refine WeightedDriftDropSum.weighted_dyadic_mass_drift_of_dropSum
    (NonuniformMajority L K) Phase1FarPhi.farPhiN c ?_
    (farBeta n g mc) (by simp [farBeta]) ?_ ?_
  · rw [hentry.1.1]
    exact hn
  · intro pair
    exact Phase1FarPhi.farPhiN_stepOrSelf_le_of_phase1Win
      n c hentry.1 pair.1 pair.2
  · exact farPhiN_weightedDropSum_floor hn c hentry

/-- The multiplicative rate is a valid contraction-factor input for
`DriftSurvival.driftSurvivalPhase`. -/
theorem one_sub_farBeta_le_one (n g mc : ℕ) :
    1 - farBeta n g mc ≤ (1 : ℝ≥0∞) := tsub_le_self

#print axioms farPhiN_le_two_mul_farCount
#print axioms sum_interactionCount_farDropRect
#print axioms farPhiN_drop_prob_multiplicative
#print axioms farPhiN_weightedDropSum_floor
#print axioms farPhiN_multiplicative_drift
#print axioms one_sub_farBeta_le_one

end Phase1FarPhiMultiplicative
end Ripple.PopulationProtocol.ExactMajority
