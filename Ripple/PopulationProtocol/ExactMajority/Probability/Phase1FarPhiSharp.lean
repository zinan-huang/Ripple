/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sharp multiplicative Phase-1 far-mass drift

The two-rectangle argument in `Phase1FarPhiMultiplicative` counts only one
orientation of a far-by-partner interaction and consequently loses a factor
two.  Here we add the reversed rectangles with multiplicity.  The only overlap
consists of opposite-far ordered pairs; those pairs decrease `farPhiN` by at
least two, so the overlap is paid for exactly.  This gives the sharp rate

  `P / (n (n - 1))`, where `P = (mc - g + 3) / 4`.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1FarPhiMultiplicative

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase1FarPhiSharp

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Reversed rectangles and their scheduler mass -/

/-- The orientation-reversal of `Phase1FarPhiMultiplicative.farDropRect`. -/
def farDropRectRev (L K : ℕ) :
    Finset (AgentState L K × AgentState L K) :=
  ((AveragingRate.lowSet L K) ×ˢ (AveragingRate.farHighSet L K)) ∪
    ((AveragingRate.highSet L K) ×ˢ (AveragingRate.farLowSet L K))

/-- The reversed component rectangles are disjoint in their second coordinate. -/
theorem farDropRectRev_components_disjoint :
    Disjoint
      ((AveragingRate.lowSet L K) ×ˢ (AveragingRate.farHighSet L K))
      ((AveragingRate.highSet L K) ×ˢ (AveragingRate.farLowSet L K)) := by
  exact Finset.disjoint_product.mpr
    (Or.inr (Phase1FarPhiMultiplicative.farHighSet_disjoint_farLowSet
      (L := L) (K := K)))

/-- Exact interaction-count mass of the reversed rectangle union. -/
theorem sum_interactionCount_farDropRectRev
    (c : Config (AgentState L K)) :
    (∑ p ∈ farDropRectRev L K, c.interactionCount p.1 p.2) =
      (AveragingRate.farHighSet L K).sum c.count *
          (AveragingRate.lowSet L K).sum c.count +
        (AveragingRate.farLowSet L K).sum c.count *
          (AveragingRate.highSet L K).sum c.count := by
  classical
  unfold farDropRectRev
  rw [Finset.sum_union
      (farDropRectRev_components_disjoint (L := L) (K := K)),
    Phase7Convergence.sum_interactionCount_cross_disjoint7 c _ _
      (fun a ha b hb =>
        AveragingRate.farHigh_low_disjoint b hb a ha |>.symm),
    Phase7Convergence.sum_interactionCount_cross_disjoint7 c _ _
      (fun a ha b hb =>
        AveragingRate.farLow_high_disjoint b hb a ha |>.symm)]
  ring

/-- Exact scheduler mass of the reversed rectangle union. -/
theorem sum_interactionProb_farDropRectRev (n : ℕ)
    (c : Config (AgentState L K)) (hcard : c.card = n) :
    (∑ p ∈ farDropRectRev L K, c.interactionProb p.1 p.2) =
      (((AveragingRate.farHighSet L K).sum c.count *
            (AveragingRate.lowSet L K).sum c.count +
          (AveragingRate.farLowSet L K).sum c.count *
            (AveragingRate.highSet L K).sum c.count : ℕ) : ℝ≥0∞) /
        ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
  classical
  simp only [Config.interactionProb, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum,
    sum_interactionCount_farDropRectRev, Config.totalPairs, hcard]

/-! ## Pair and configuration drops for the reversed/overlap cells -/

/-- Reversing a far-high/low cell still drops one unit. -/
theorem avgFin7_farPhi_pair_drop_high_rev (x y : Fin 7)
    (hx : x.val ≤ 3) (hy : 5 ≤ y.val) :
    Phase1FarPhi.farPhi (avgFin7 x y).1 +
        Phase1FarPhi.farPhi (avgFin7 x y).2 + 1
      ≤ Phase1FarPhi.farPhi x + Phase1FarPhi.farPhi y := by
  revert hx hy
  revert x y
  decide

/-- Reversing a far-low/high cell still drops one unit. -/
theorem avgFin7_farPhi_pair_drop_low_rev (x y : Fin 7)
    (hx : 3 ≤ x.val) (hy : y.val ≤ 1) :
    Phase1FarPhi.farPhi (avgFin7 x y).1 +
        Phase1FarPhi.farPhi (avgFin7 x y).2 + 1
      ≤ Phase1FarPhi.farPhi x + Phase1FarPhi.farPhi y := by
  revert hx hy
  revert x y
  decide

/-- Opposite far sides pay the twofold rectangle overlap. -/
theorem avgFin7_farPhi_pair_drop_two_high_low (x y : Fin 7)
    (hx : 5 ≤ x.val) (hy : y.val ≤ 1) :
    Phase1FarPhi.farPhi (avgFin7 x y).1 +
        Phase1FarPhi.farPhi (avgFin7 x y).2 + 2
      ≤ Phase1FarPhi.farPhi x + Phase1FarPhi.farPhi y := by
  revert hx hy
  revert x y
  decide

/-- Reversed opposite far sides also drop at least two. -/
theorem avgFin7_farPhi_pair_drop_two_low_high (x y : Fin 7)
    (hx : x.val ≤ 1) (hy : 5 ≤ y.val) :
    Phase1FarPhi.farPhi (avgFin7 x y).1 +
        Phase1FarPhi.farPhi (avgFin7 x y).2 + 2
      ≤ Phase1FarPhi.farPhi x + Phase1FarPhi.farPhi y := by
  revert hx hy
  revert x y
  decide

private theorem Transition_farPhi_pair_drop_of_avg
    (s t : AgentState L K)
    (hs1 : s.phase.val = 1) (ht1 : t.phase.val = 1)
    (hsM : s.role = Role.main) (htM : t.role = Role.main)
    (d : ℕ)
    (havg : Phase1FarPhi.farPhi (avgFin7 s.smallBias t.smallBias).1 +
        Phase1FarPhi.farPhi (avgFin7 s.smallBias t.smallBias).2 + d
      ≤ Phase1FarPhi.farPhi s.smallBias +
        Phase1FarPhi.farPhi t.smallBias) :
    ((({(Transition L K s t).1, (Transition L K s t).2}
        : Multiset (AgentState L K)).map
          (fun a => Phase1FarPhi.farPhiMainN a)).sum) + d
      ≤ ((({s, t} : Multiset (AgentState L K)).map
          (fun a => Phase1FarPhi.farPhiMainN a)).sum) := by
  rw [Phase1Convergence.Transition_eq_avg_of_phase1_main
    s t hs1 ht1 hsM htM]
  rw [Phase1FarPhi.farPhiMainN_pair, Phase1FarPhi.farPhiMainN_pair]
  simp only [Phase1FarPhi.farPhiMainN, hsM, htM, if_pos]
  exact havg

private theorem farPhiN_stepOrSelf_drop_of_pair
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t) (d : ℕ)
    (hpair :
      ((({(Transition L K s t).1, (Transition L K s t).2}
          : Multiset (AgentState L K)).map
            (fun a => Phase1FarPhi.farPhiMainN a)).sum) + d
        ≤ ((({s, t} : Multiset (AgentState L K)).map
            (fun a => Phase1FarPhi.farPhiMainN a)).sum)) :
    Phase1FarPhi.farPhiN
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) + d
      ≤ Phase1FarPhi.farPhiN c := by
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t
      = c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  have hsplit : c = (c - {s, t}) + ({s, t} : Multiset (AgentState L K)) := by
    rw [Multiset.sub_add_cancel hsub]
  unfold Phase1FarPhi.farPhiN
  rw [hc', Multiset.map_add, Multiset.sum_add]
  have hrhs : (c.map (fun a => Phase1FarPhi.farPhiMainN a)).sum
      = ((c - {s, t}).map (fun a => Phase1FarPhi.farPhiMainN a)).sum
        + (({s, t} : Multiset (AgentState L K)).map
            (fun a => Phase1FarPhi.farPhiMainN a)).sum := by
    conv_lhs => rw [hsplit]
    rw [Multiset.map_add, Multiset.sum_add]
  omega

private theorem farPhiN_stepOrSelf_drop_high_rev
    (n : ℕ) (c : Config (AgentState L K))
    (hInv : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (s t : AgentState L K) (happ : Protocol.Applicable c s t)
    (hsL : AveragingRate.low s) (htH : AveragingRate.farHigh t) :
    Phase1FarPhi.farPhiN
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) + 1
      ≤ Phase1FarPhi.farPhiN c := by
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hsm : s ∈ c := Multiset.mem_of_le hsub (by simp)
  have htm : t ∈ c := Multiset.mem_of_le hsub (by simp)
  exact farPhiN_stepOrSelf_drop_of_pair c s t happ 1
    (Transition_farPhi_pair_drop_of_avg s t
      (hInv.2 s hsm) (hInv.2 t htm) hsL.1 htH.1 1
      (avgFin7_farPhi_pair_drop_high_rev s.smallBias t.smallBias
        hsL.2 htH.2))

private theorem farPhiN_stepOrSelf_drop_low_rev
    (n : ℕ) (c : Config (AgentState L K))
    (hInv : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (s t : AgentState L K) (happ : Protocol.Applicable c s t)
    (hsH : AveragingRate.high s) (htL : AveragingRate.farLow t) :
    Phase1FarPhi.farPhiN
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) + 1
      ≤ Phase1FarPhi.farPhiN c := by
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hsm : s ∈ c := Multiset.mem_of_le hsub (by simp)
  have htm : t ∈ c := Multiset.mem_of_le hsub (by simp)
  exact farPhiN_stepOrSelf_drop_of_pair c s t happ 1
    (Transition_farPhi_pair_drop_of_avg s t
      (hInv.2 s hsm) (hInv.2 t htm) hsH.1 htL.1 1
      (avgFin7_farPhi_pair_drop_low_rev s.smallBias t.smallBias
        hsH.2 htL.2))

private theorem farPhiN_stepOrSelf_drop_two_high_low
    (n : ℕ) (c : Config (AgentState L K))
    (hInv : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (s t : AgentState L K) (happ : Protocol.Applicable c s t)
    (hsH : AveragingRate.farHigh s) (htL : AveragingRate.farLow t) :
    Phase1FarPhi.farPhiN
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) + 2
      ≤ Phase1FarPhi.farPhiN c := by
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hsm : s ∈ c := Multiset.mem_of_le hsub (by simp)
  have htm : t ∈ c := Multiset.mem_of_le hsub (by simp)
  exact farPhiN_stepOrSelf_drop_of_pair c s t happ 2
    (Transition_farPhi_pair_drop_of_avg s t
      (hInv.2 s hsm) (hInv.2 t htm) hsH.1 htL.1 2
      (avgFin7_farPhi_pair_drop_two_high_low s.smallBias t.smallBias
        hsH.2 htL.2))

private theorem farPhiN_stepOrSelf_drop_two_low_high
    (n : ℕ) (c : Config (AgentState L K))
    (hInv : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (s t : AgentState L K) (happ : Protocol.Applicable c s t)
    (hsL : AveragingRate.farLow s) (htH : AveragingRate.farHigh t) :
    Phase1FarPhi.farPhiN
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) + 2
      ≤ Phase1FarPhi.farPhiN c := by
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hsm : s ∈ c := Multiset.mem_of_le hsub (by simp)
  have htm : t ∈ c := Multiset.mem_of_le hsub (by simp)
  exact farPhiN_stepOrSelf_drop_of_pair c s t happ 2
    (Transition_farPhi_pair_drop_of_avg s t
      (hInv.2 s hsm) (hInv.2 t htm) hsL.1 htH.1 2
      (avgFin7_farPhi_pair_drop_two_low_high s.smallBias t.smallBias
        hsL.2 htH.2))

/-- Every present pair in the reversed union strictly drops `farPhiN`. -/
theorem farDropRectRev_step_drop (n : ℕ)
    (c : Config (AgentState L K))
    (hInv : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (p : AgentState L K × AgentState L K)
    (hp : p ∈ farDropRectRev L K)
    (hp1 : 1 ≤ c.count p.1) (hp2 : 1 ≤ c.count p.2) :
    Phase1FarPhi.farPhiN
        (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) + 1
      ≤ Phase1FarPhi.farPhiN c := by
  classical
  have hm1 : p.1 ∈ c := Multiset.one_le_count_iff_mem.mp hp1
  have hm2 : p.2 ∈ c := Multiset.one_le_count_iff_mem.mp hp2
  unfold farDropRectRev at hp
  rw [Finset.mem_union] at hp
  rcases hp with hp | hp
  · rw [Finset.mem_product] at hp
    obtain ⟨hpl, hph⟩ := hp
    have hne := AveragingRate.farHigh_low_disjoint p.2 hph p.1 hpl |>.symm
    have happ : Protocol.Applicable c p.1 p.2 :=
      Phase5Convergence.applicable_of_mem_distinct5 hm1 hm2 hne
    simp only [AveragingRate.lowSet, Finset.mem_filter] at hpl
    simp only [AveragingRate.farHighSet, Finset.mem_filter] at hph
    exact farPhiN_stepOrSelf_drop_high_rev n c hInv p.1 p.2 happ hpl.2 hph.2
  · rw [Finset.mem_product] at hp
    obtain ⟨hph, hpl⟩ := hp
    have hne := AveragingRate.farLow_high_disjoint p.2 hpl p.1 hph |>.symm
    have happ : Protocol.Applicable c p.1 p.2 :=
      Phase5Convergence.applicable_of_mem_distinct5 hm1 hm2 hne
    simp only [AveragingRate.highSet, Finset.mem_filter] at hph
    simp only [AveragingRate.farLowSet, Finset.mem_filter] at hpl
    exact farPhiN_stepOrSelf_drop_low_rev n c hInv p.1 p.2 happ hph.2 hpl.2

/-- A pair lying in both oriented unions is opposite-far and drops two units. -/
theorem farDropRect_overlap_step_drop_two (n : ℕ)
    (c : Config (AgentState L K))
    (hInv : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (p : AgentState L K × AgentState L K)
    (hp : p ∈ Phase1FarPhiMultiplicative.farDropRect L K)
    (hprev : p ∈ farDropRectRev L K)
    (hp1 : 1 ≤ c.count p.1) (hp2 : 1 ≤ c.count p.2) :
    Phase1FarPhi.farPhiN
        (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) + 2
      ≤ Phase1FarPhi.farPhiN c := by
  classical
  have hm1 : p.1 ∈ c := Multiset.one_le_count_iff_mem.mp hp1
  have hm2 : p.2 ∈ c := Multiset.one_le_count_iff_mem.mp hp2
  unfold Phase1FarPhiMultiplicative.farDropRect at hp
  unfold farDropRectRev at hprev
  rw [Finset.mem_union] at hp hprev
  rcases hp with hp | hp <;> rcases hprev with hprev | hprev
  · rw [Finset.mem_product] at hp hprev
    simp only [AveragingRate.farHighSet, AveragingRate.lowSet,
      Finset.mem_filter, AveragingRate.farHigh, AveragingRate.low] at hp hprev
    omega
  · rw [Finset.mem_product] at hp hprev
    obtain ⟨hph, hpl⟩ := hp
    obtain ⟨_, hpfl⟩ := hprev
    have hne := AveragingRate.farHigh_low_disjoint p.1 hph p.2 hpl
    have happ : Protocol.Applicable c p.1 p.2 :=
      Phase5Convergence.applicable_of_mem_distinct5 hm1 hm2 hne
    simp only [AveragingRate.farHighSet, Finset.mem_filter] at hph
    simp only [AveragingRate.farLowSet, Finset.mem_filter] at hpfl
    exact farPhiN_stepOrSelf_drop_two_high_low
      n c hInv p.1 p.2 happ hph.2 hpfl.2
  · rw [Finset.mem_product] at hp hprev
    obtain ⟨hpl, hph⟩ := hp
    obtain ⟨_, hpfh⟩ := hprev
    have hne := AveragingRate.farLow_high_disjoint p.1 hpl p.2 hph
    have happ : Protocol.Applicable c p.1 p.2 :=
      Phase5Convergence.applicable_of_mem_distinct5 hm1 hm2 hne
    simp only [AveragingRate.farLowSet, Finset.mem_filter] at hpl
    simp only [AveragingRate.farHighSet, Finset.mem_filter] at hpfh
    exact farPhiN_stepOrSelf_drop_two_low_high
      n c hInv p.1 p.2 happ hpl.2 hpfh.2
  · rw [Finset.mem_product] at hp hprev
    simp only [AveragingRate.farLowSet, AveragingRate.highSet,
      Finset.mem_filter, AveragingRate.farLow, AveragingRate.high] at hp hprev
    omega

/-! ## Multiplicity ledger -/

/-- Number (zero, one, or two) of oriented sharp rectangles containing a pair. -/
def sharpRectMultiplicity (p : AgentState L K × AgentState L K) : ℕ :=
  (if p ∈ Phase1FarPhiMultiplicative.farDropRect L K then 1 else 0) +
    (if p ∈ farDropRectRev L K then 1 else 0)

private theorem pair_ne_of_mem_farDropRect
    {p : AgentState L K × AgentState L K}
    (hp : p ∈ Phase1FarPhiMultiplicative.farDropRect L K) : p.1 ≠ p.2 := by
  unfold Phase1FarPhiMultiplicative.farDropRect at hp
  rw [Finset.mem_union] at hp
  rcases hp with hp | hp
  · rw [Finset.mem_product] at hp
    exact AveragingRate.farHigh_low_disjoint p.1 hp.1 p.2 hp.2
  · rw [Finset.mem_product] at hp
    exact AveragingRate.farLow_high_disjoint p.1 hp.1 p.2 hp.2

private theorem pair_ne_of_mem_farDropRectRev
    {p : AgentState L K × AgentState L K}
    (hp : p ∈ farDropRectRev L K) : p.1 ≠ p.2 := by
  unfold farDropRectRev at hp
  rw [Finset.mem_union] at hp
  rcases hp with hp | hp
  · rw [Finset.mem_product] at hp
    exact (AveragingRate.farHigh_low_disjoint p.2 hp.2 p.1 hp.1).symm
  · rw [Finset.mem_product] at hp
    exact (AveragingRate.farLow_high_disjoint p.2 hp.2 p.1 hp.1).symm

/-- Pointwise, rectangle multiplicity is paid by the actual potential drop. -/
theorem sharpRectMultiplicity_mul_interactionProb_le_drop
    (n : ℕ) (c : Config (AgentState L K))
    (hInv : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (p : AgentState L K × AgentState L K) :
    (sharpRectMultiplicity (L := L) (K := K) p : ℝ≥0∞) *
        c.interactionProb p.1 p.2
      ≤ ((Phase1FarPhi.farPhiN c : ℝ≥0∞) -
          (Phase1FarPhi.farPhiN
            (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) : ℝ≥0∞)) *
        c.interactionProb p.1 p.2 := by
  classical
  by_cases hp : p ∈ Phase1FarPhiMultiplicative.farDropRect L K
  · by_cases hprev : p ∈ farDropRectRev L K
    · have hne := pair_ne_of_mem_farDropRect hp
      by_cases hp1 : 1 ≤ c.count p.1
      · by_cases hp2 : 1 ≤ c.count p.2
        · have hdrop := farDropRect_overlap_step_drop_two
            n c hInv p hp hprev hp1 hp2
          have hdropNat : 2 ≤ Phase1FarPhi.farPhiN c -
              Phase1FarPhi.farPhiN
                (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) := by
            omega
          have hdropE : (2 : ℝ≥0∞) ≤
              (Phase1FarPhi.farPhiN c : ℝ≥0∞) -
                (Phase1FarPhi.farPhiN
                  (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) : ℝ≥0∞) := by
            simpa only [ENNReal.natCast_sub] using (show
              (2 : ℝ≥0∞) ≤ ((Phase1FarPhi.farPhiN c -
                Phase1FarPhi.farPhiN
                  (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) : ℕ) : ℝ≥0∞) by
                  exact_mod_cast hdropNat)
          simpa [sharpRectMultiplicity, hp, hprev] using
            (mul_le_mul_left hdropE (c.interactionProb p.1 p.2))
        · have hz2 : c.count p.2 = 0 := by omega
          simp [sharpRectMultiplicity, hp, hprev, Config.interactionProb,
            Config.interactionCount, hne, hz2]
      · have hz1 : c.count p.1 = 0 := by omega
        simp [sharpRectMultiplicity, hp, hprev, Config.interactionProb,
          Config.interactionCount, hne, hz1]
    · have hne := pair_ne_of_mem_farDropRect hp
      by_cases hp1 : 1 ≤ c.count p.1
      · by_cases hp2 : 1 ≤ c.count p.2
        · have hdrop := Phase1FarPhiMultiplicative.farDropRect_step_drop
            n c hInv p hp hp1 hp2
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
          simpa [sharpRectMultiplicity, hp, hprev] using
            (mul_le_mul_left hdropE (c.interactionProb p.1 p.2))
        · have hz2 : c.count p.2 = 0 := by omega
          simp [sharpRectMultiplicity, hp, hprev, Config.interactionProb,
            Config.interactionCount, hne, hz2]
      · have hz1 : c.count p.1 = 0 := by omega
        simp [sharpRectMultiplicity, hp, hprev, Config.interactionProb,
          Config.interactionCount, hne, hz1]
  · by_cases hprev : p ∈ farDropRectRev L K
    · have hne := pair_ne_of_mem_farDropRectRev hprev
      by_cases hp1 : 1 ≤ c.count p.1
      · by_cases hp2 : 1 ≤ c.count p.2
        · have hdrop := farDropRectRev_step_drop n c hInv p hprev hp1 hp2
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
          simpa [sharpRectMultiplicity, hp, hprev] using
            (mul_le_mul_left hdropE (c.interactionProb p.1 p.2))
        · have hz2 : c.count p.2 = 0 := by omega
          simp [sharpRectMultiplicity, hp, hprev, Config.interactionProb,
            Config.interactionCount, hne, hz2]
      · have hz1 : c.count p.1 = 0 := by omega
        simp [sharpRectMultiplicity, hp, hprev, Config.interactionProb,
          Config.interactionCount, hne, hz1]
    · simp [sharpRectMultiplicity, hp, hprev]

/-- Summing multiplicity reproduces the two oriented rectangle masses. -/
theorem sum_sharpRectMultiplicity_mul_interactionProb
    (c : Config (AgentState L K)) :
    (∑ p : AgentState L K × AgentState L K,
        (sharpRectMultiplicity (L := L) (K := K) p : ℝ≥0∞) *
          c.interactionProb p.1 p.2) =
      (∑ p ∈ Phase1FarPhiMultiplicative.farDropRect L K,
          c.interactionProb p.1 p.2) +
        ∑ p ∈ farDropRectRev L K, c.interactionProb p.1 p.2 := by
  classical
  calc
    (∑ p : AgentState L K × AgentState L K,
        (sharpRectMultiplicity (L := L) (K := K) p : ℝ≥0∞) *
          c.interactionProb p.1 p.2) =
        (∑ p : AgentState L K × AgentState L K,
          if p ∈ Phase1FarPhiMultiplicative.farDropRect L K then
            c.interactionProb p.1 p.2 else 0) +
        ∑ p : AgentState L K × AgentState L K,
          if p ∈ farDropRectRev L K then
            c.interactionProb p.1 p.2 else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro p _hp
      by_cases h₁ : p ∈ Phase1FarPhiMultiplicative.farDropRect L K <;>
        by_cases h₂ : p ∈ farDropRectRev L K <;>
        simp [sharpRectMultiplicity, h₁, h₂, two_mul]
    _ = (∑ p ∈ Phase1FarPhiMultiplicative.farDropRect L K,
          c.interactionProb p.1 p.2) +
        ∑ p ∈ farDropRectRev L K, c.interactionProb p.1 p.2 := by
      simp

/-- The two oriented rectangle masses fit under the full weighted drop sum. -/
theorem sharpRectMass_le_weightedDropSum (n : ℕ)
    (c : Config (AgentState L K))
    (hInv : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c) :
    (∑ p ∈ Phase1FarPhiMultiplicative.farDropRect L K,
        c.interactionProb p.1 p.2) +
      ∑ p ∈ farDropRectRev L K, c.interactionProb p.1 p.2
      ≤ WeightedDriftDropSum.weightedDropSum
        (NonuniformMajority L K) Phase1FarPhi.farPhiN c := by
  rw [← sum_sharpRectMultiplicity_mul_interactionProb]
  unfold WeightedDriftDropSum.weightedDropSum
  exact Finset.sum_le_sum (fun p _hp =>
    sharpRectMultiplicity_mul_interactionProb_le_drop n c hInv p)

/-! ## Sharp rate and multiplicative drift -/

/-- Sharp per-unit far-mass drop rate. -/
noncomputable def farBetaSharp (n g mc : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((((mc - g + 3) / 4 : ℕ) : ℝ)) /
    ((n : ℝ) * ((n : ℝ) - 1)))

/-- The four-rectangle multiplicity ledger gives the sharp drop-sum floor. -/
theorem farPhiN_weightedDropSum_floor_sharp
    {n g mc : ℕ} (hn : 2 ≤ n)
    (c : Config (AgentState L K))
    (hentry : Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c) :
    farBetaSharp n g mc * (Phase1FarPhi.farPhiN c : ℝ≥0∞) ≤
      WeightedDriftDropSum.weightedDropSum (NonuniformMajority L K)
        Phase1FarPhi.farPhiN c := by
  classical
  let P : ℕ := (mc - g + 3) / 4
  let F : ℕ := (AveragingRate.farHighSet L K).sum c.count +
    (AveragingRate.farLowSet L K).sum c.count
  let M : ℕ := (AveragingRate.farHighSet L K).sum c.count *
      (AveragingRate.lowSet L K).sum c.count +
    (AveragingRate.farLowSet L K).sum c.count *
      (AveragingRate.highSet L K).sum c.count
  have hΦ : Phase1FarPhi.farPhiN c ≤ 2 * F := by
    simpa [F] using
      Phase1FarPhiMultiplicative.farPhiN_le_two_mul_farCount
        (L := L) (K := K) c
  have hcount : P * F ≤ M := by
    have hm := Phase1FarPhiMultiplicative.partnerFloor_mul_farCount_le_rectMass
      (L := L) (K := K) n g mc c hentry
    rw [Phase1FarPhiMultiplicative.sum_interactionCount_farDropRect] at hm
    simpa [P, F, M] using hm
  have hbeta : farBetaSharp n g mc =
      (P : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
    unfold farBetaSharp
    simpa [P] using
      Phase1FarPhiMultiplicative.ofReal_scheduler_rate_eq n P hn
  have hrect :
      (∑ p ∈ Phase1FarPhiMultiplicative.farDropRect L K,
          c.interactionProb p.1 p.2) +
        ∑ p ∈ farDropRectRev L K, c.interactionProb p.1 p.2 =
      (M : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) +
        (M : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
    rw [Phase1FarPhiMultiplicative.sum_interactionProb_farDropRect n c hentry.1.1,
      sum_interactionProb_farDropRectRev n c hentry.1.1]
  calc
    farBetaSharp n g mc * (Phase1FarPhi.farPhiN c : ℝ≥0∞)
        = ((P : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)) *
            (Phase1FarPhi.farPhiN c : ℝ≥0∞) := by rw [hbeta]
    _ ≤ ((P : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)) *
          ((2 * F : ℕ) : ℝ≥0∞) := by
        gcongr
    _ = ((2 * (P * F) : ℕ) : ℝ≥0∞) /
          ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
        push_cast
        simp only [div_eq_mul_inv]
        ac_rfl
    _ ≤ ((2 * M : ℕ) : ℝ≥0∞) /
          ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
        gcongr
    _ = (M : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) +
          (M : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
        push_cast
        simp only [div_eq_mul_inv]
        rw [two_mul, add_mul]
    _ = (∑ p ∈ Phase1FarPhiMultiplicative.farDropRect L K,
          c.interactionProb p.1 p.2) +
        ∑ p ∈ farDropRectRev L K, c.interactionProb p.1 p.2 := hrect.symm
    _ ≤ WeightedDriftDropSum.weightedDropSum (NonuniformMajority L K)
          Phase1FarPhi.farPhiN c := sharpRectMass_le_weightedDropSum n c hentry.1

/-- Sharp one-step multiplicative expectation for Phase 1. -/
theorem farPhiN_multiplicative_drift_sharp
    {n g mc : ℕ} (hn : 2 ≤ n)
    (c : Config (AgentState L K))
    (hentry : Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c) :
    ∫⁻ c', (Phase1FarPhi.farPhiN c' : ℝ≥0∞)
        ∂((NonuniformMajority L K).transitionKernel c)
      ≤ (1 - farBetaSharp n g mc) *
          (Phase1FarPhi.farPhiN c : ℝ≥0∞) := by
  refine WeightedDriftDropSum.weighted_dyadic_mass_drift_of_dropSum
    (NonuniformMajority L K) Phase1FarPhi.farPhiN c ?_
    (farBetaSharp n g mc) (by simp [farBetaSharp]) ?_ ?_
  · rw [hentry.1.1]
    exact hn
  · intro pair
    exact Phase1FarPhi.farPhiN_stepOrSelf_le_of_phase1Win
      n c hentry.1 pair.1 pair.2
  · exact farPhiN_weightedDropSum_floor_sharp hn c hentry

/-- The sharp factor is a valid contraction-factor input. -/
theorem one_sub_farBetaSharp_le_one (n g mc : ℕ) :
    1 - farBetaSharp n g mc ≤ (1 : ℝ≥0∞) := tsub_le_self

#print axioms sum_interactionCount_farDropRectRev
#print axioms farDropRect_overlap_step_drop_two
#print axioms sharpRectMass_le_weightedDropSum
#print axioms farPhiN_weightedDropSum_floor_sharp
#print axioms farPhiN_multiplicative_drift_sharp
#print axioms one_sub_farBetaSharp_le_one

end Phase1FarPhiSharp
end Ripple.PopulationProtocol.ExactMajority
