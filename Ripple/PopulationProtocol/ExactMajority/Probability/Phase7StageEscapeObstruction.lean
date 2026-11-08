/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-7 stage-gate escape obstruction

The current exact-band stage gate asks for a fixed eliminator floor whenever
the target band is nonempty.  That floor is not one-step closed: a productive
same-band cancellation can consume the last eliminator while leaving another
target-band agent alive.  This file records the concrete four-agent
counterexample without changing the protocol or the stage definitions.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase7BandSurvival
import Ripple.PopulationProtocol.ExactMajority.Analysis.Phase0Convergence

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase7StageEscapeObstruction

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable

/-- The target exponent, index `1` in `Fin (2+1)`. -/
def j1 : Fin 3 := ⟨1, by decide⟩

/-- A positive phase-7 Main in the target band. -/
def a : AgentState 2 1 :=
  { input := .A
    output := .A
    phase := ⟨7, by decide⟩
    role := .main
    assigned := false
    bias := .dyadic .pos j1
    smallBias := ⟨3, by decide⟩
    hour := ⟨0, by decide⟩
    minute := ⟨0, by decide⟩
    full := false
    opinions := ⟨4, by decide⟩
    counter := ⟨0, by decide⟩ }

/-- The unique negative eliminator, at the same exponent. -/
def b : AgentState 2 1 :=
  { input := .B
    output := .B
    phase := ⟨7, by decide⟩
    role := .main
    assigned := false
    bias := .dyadic .neg j1
    smallBias := ⟨3, by decide⟩
    hour := ⟨0, by decide⟩
    minute := ⟨0, by decide⟩
    full := false
    opinions := ⟨1, by decide⟩
    counter := ⟨0, by decide⟩ }

/-- An unbiased phase-7 Main used only to make the population size four. -/
def d : AgentState 2 1 :=
  { input := .A
    output := .A
    phase := ⟨7, by decide⟩
    role := .main
    assigned := false
    bias := .zero
    smallBias := ⟨3, by decide⟩
    hour := ⟨0, by decide⟩
    minute := ⟨0, by decide⟩
    full := false
    opinions := ⟨2, by decide⟩
    counter := ⟨0, by decide⟩ }

/-- Two target-band agents, one eliminator, and one unbiased Main. -/
def c : Config (AgentState 2 1) := {a, a, b, d}

/-- The positive target-band count is exactly two. -/
theorem bandCount_c_j1 :
    Phase7BandDefs.bandCountN (L := 2) (K := 1) .pos j1 c = 2 := by
  rw [Phase7BandTransition.bandCountN_eq_countP]
  change Multiset.countP _ (a ::ₘ a ::ₘ b ::ₘ d ::ₘ 0) = 2
  simp only [Multiset.countP_cons, Multiset.countP_zero]
  simp [Phase7BandTransition.bandSt, a, b, d, j1]

/-- The lower positive band (index zero) is empty. -/
theorem bandCount_c_j0 :
    Phase7BandDefs.bandCountN (L := 2) (K := 1) .pos ⟨0, by decide⟩ c = 0 := by
  rw [Phase7BandTransition.bandCountN_eq_countP]
  change Multiset.countP _ (a ::ₘ a ::ₘ b ::ₘ d ::ₘ 0) = 0
  simp only [Multiset.countP_cons, Multiset.countP_zero]
  simp [Phase7BandTransition.bandSt, a, b, d, j1]

/-- The upper positive band (index two) is empty. -/
theorem bandCount_c_j2 :
    Phase7BandDefs.bandCountN (L := 2) (K := 1) .pos ⟨2, by decide⟩ c = 0 := by
  rw [Phase7BandTransition.bandCountN_eq_countP]
  change Multiset.countP _ (a ::ₘ a ::ₘ b ::ₘ d ::ₘ 0) = 0
  simp only [Multiset.countP_cons, Multiset.countP_zero]
  simp [Phase7BandTransition.bandSt, a, b, d, j1]

/-- The initial configuration satisfies the cumulative-clearance prefix. -/
theorem c_bandClear :
    Phase7BandDefs.BandClear (L := 2) (K := 1) .pos 1 c := by
  intro j hj
  fin_cases j
  · exact bandCount_c_j0
  · simp at hj
  · simp at hj

/-- The initial configuration has the uniform floor required by the current
stage gate.  The only nonempty requested band is `j=1`, and `b` supplies its
single eliminator. -/
theorem c_phase7BandPool :
    Phase7BandDefs.phase7BandPool (L := 2) (K := 1) .pos 1 1 c := by
  intro j hjlo _hjhi hpositive
  fin_cases j
  · simp at hjlo
  · have hbmem : b ∈
        Phase7BandDefs.elimWithin2 (L := 2) (K := 1) .pos ⟨1, by decide⟩ := by
      simp [Phase7BandDefs.elimWithin2, b, j1]
    have hsubset : ({b} : Finset (AgentState 2 1)) ⊆
        Phase7BandDefs.elimWithin2 (L := 2) (K := 1) .pos ⟨1, by decide⟩ := by
      simpa using hbmem
    have hsum := Finset.sum_le_sum_of_subset hsubset (f := c.count)
    simpa [c, a, b, d] using hsum
  · rw [bandCount_c_j2] at hpositive
    omega

/-- The concrete four-agent configuration is a current `Phase7StageReady`
state for `n=4`, `l=1`, `E7=1`, `sigma=pos`, `j=1`. -/
theorem c_stageReady :
    Phase7BandDefs.Phase7StageReady (L := 2) (K := 1)
      4 .pos 1 1 j1 c := by
  refine ⟨?_, c_bandClear, c_phase7BandPool⟩
  refine ⟨by simp [c], ?_⟩
  intro x hx
  simp [c] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> rfl

/-- The zeroed descendants of the cancelled ordered pair. -/
def az : AgentState 2 1 := {a with bias := .zero}
def bz : AgentState 2 1 := {b with bias := .zero}

/-- The configuration after cancelling one copy of `a` against `b`. -/
def cAfter : Config (AgentState 2 1) := {a, d, az, bz}

theorem a_ne_b : a ≠ b := by
  intro h
  have hbias := congrArg AgentState.bias h
  simp [a, b, j1] at hbias

theorem applicable_ab :
    Protocol.Applicable c a b := by
  apply Phase7BandDropSum.applicable_of_mem_distinct
  · simp [c]
  · simp [c]
  · exact a_ne_b

theorem applicable_ba :
    Protocol.Applicable c b a := by
  apply Phase7BandDropSum.applicable_of_mem_distinct
  · simp [c]
  · simp [c]
  · exact a_ne_b.symm

/-- Same-exponent opposite signs cancel in either orientation. -/
theorem transition_ab : Transition 2 1 a b = (az, bz) := by
  rw [Phase7Convergence.Transition_eq_cancelSplit_of_phase7_main]
  · rfl
  all_goals simp [a, b]

theorem transition_ba : Transition 2 1 b a = (bz, az) := by
  rw [Phase7Convergence.Transition_eq_cancelSplit_of_phase7_main]
  · rfl
  all_goals simp [a, b]

/-- Either ordered productive interaction reaches the same multiset. -/
theorem step_ab :
    Protocol.stepOrSelf (NonuniformMajority 2 1) c a b = cAfter := by
  unfold Protocol.stepOrSelf
  rw [if_pos applicable_ab]
  change c - {a, b} + {(Transition 2 1 a b).1, (Transition 2 1 a b).2} = cAfter
  rw [transition_ab]
  change ({a, a, b, d} : Multiset (AgentState 2 1)) - {a, b} + {az, bz} =
    {a, d, az, bz}
  decide

theorem step_ba :
    Protocol.stepOrSelf (NonuniformMajority 2 1) c b a = cAfter := by
  unfold Protocol.stepOrSelf
  rw [if_pos applicable_ba]
  change c - {b, a} + {(Transition 2 1 b a).1, (Transition 2 1 b a).2} = cAfter
  rw [transition_ba]
  change ({a, a, b, d} : Multiset (AgentState 2 1)) - {b, a} + {bz, az} =
    {a, d, az, bz}
  decide

/-- One positive target-band agent remains after the productive cancel. -/
theorem bandCount_after_j1 :
    Phase7BandDefs.bandCountN (L := 2) (K := 1) .pos j1 cAfter = 1 := by
  rw [Phase7BandTransition.bandCountN_eq_countP]
  change Multiset.countP _ (a ::ₘ d ::ₘ az ::ₘ bz ::ₘ 0) = 1
  simp only [Multiset.countP_cons, Multiset.countP_zero]
  simp [Phase7BandTransition.bandSt, a, b, d, az, bz, j1]

/-- No opposite-sign dyadic Main remains in the target's distance-two
eliminator set. -/
theorem elim_sum_after_zero :
    (Phase7BandDefs.elimWithin2 (L := 2) (K := 1) .pos j1).sum
        cAfter.count = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  apply Multiset.count_eq_zero.mpr
  intro hxc
  simp [cAfter] at hxc
  simp only [Phase7BandDefs.elimWithin2, Finset.mem_filter] at hx
  rcases hxc with rfl | rfl | rfl | rfl <;>
    simp [a, b, d, az, bz, j1] at hx

/-- The productive cancellation exits the current stage gate: the target band
is still nonempty but its required eliminator floor has fallen to zero. -/
theorem cAfter_not_phase7BandPool :
    ¬ Phase7BandDefs.phase7BandPool (L := 2) (K := 1) .pos 1 1 cAfter := by
  intro hpool
  have hfloor := hpool j1 (by decide) (by decide) (by rw [bandCount_after_j1])
  rw [elim_sum_after_zero] at hfloor
  omega

theorem cAfter_not_stageReady :
    ¬ Phase7BandDefs.Phase7StageReady (L := 2) (K := 1)
      4 .pos 1 1 j1 cAfter := by
  intro hready
  exact cAfter_not_phase7BandPool hready.pool

/-- Both productive orientations deterministically leave the ready gate. -/
theorem step_ab_not_stageReady :
    ¬ Phase7BandDefs.Phase7StageReady (L := 2) (K := 1)
      4 .pos 1 1 j1
        (Protocol.stepOrSelf (NonuniformMajority 2 1) c a b) := by
  rw [step_ab]
  exact cAfter_not_stageReady

theorem step_ba_not_stageReady :
    ¬ Phase7BandDefs.Phase7StageReady (L := 2) (K := 1)
      4 .pos 1 1 j1
        (Protocol.stepOrSelf (NonuniformMajority 2 1) c b a) := by
  rw [step_ba]
  exact cAfter_not_stageReady

/-- Each productive orientation has scheduler mass `2/12 = 1/6`: there are
two copies of `a`, one copy of `b`, and twelve ordered agent pairs. -/
theorem count_a : c.count a = 2 := by
  simp [Config.count, c, a, b, d, j1]

theorem count_b : c.count b = 1 := by
  simp [Config.count, c, a, b, d, j1]

theorem totalPairs_c : c.totalPairs = 12 := by
  simp [Config.totalPairs, c]

theorem interactionProb_ab :
    c.interactionProb a b = (1 / 6 : ℝ≥0∞) := by
  rw [Config.interactionProb, Config.interactionCount, if_neg a_ne_b,
    count_a, count_b, totalPairs_c]
  change (2 : ℝ≥0∞) / 12 = 1 / 6
  rw [show (12 : ℝ≥0∞) = 2 * 6 by norm_num, div_eq_mul_inv,
    ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul, one_div]

theorem interactionProb_ba :
    c.interactionProb b a = (1 / 6 : ℝ≥0∞) := by
  rw [Config.interactionProb, Config.interactionCount, if_neg a_ne_b.symm,
    count_a, count_b, totalPairs_c]
  change (2 : ℝ≥0∞) / 12 = 1 / 6
  rw [show (12 : ℝ≥0∞) = 2 * 6 by norm_num, div_eq_mul_inv,
    ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul, one_div]

theorem two_sixths_eq_one_third :
    (1 / 6 : ℝ≥0∞) + 1 / 6 = 1 / 3 := by
  rw [one_div, ← two_mul]
  rw [show (6 : ℝ≥0∞) = 2 * 3 by norm_num,
    ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  rw [one_div]

/-- The two productive orientations alone put one-step mass `1/3` outside
the current stage gate. -/
theorem transitionKernel_not_stageReady_ge_one_third :
    (NonuniformMajority 2 1).transitionKernel c
        {c' | ¬ Phase7BandDefs.Phase7StageReady (L := 2) (K := 1)
          4 .pos 1 1 j1 c'} ≥ (1 / 3 : ℝ≥0∞) := by
  let target : Set (Config (AgentState 2 1)) :=
    {c' | ¬ Phase7BandDefs.Phase7StageReady (L := 2) (K := 1)
      4 .pos 1 1 j1 c'}
  let good : Set (AgentState 2 1 × AgentState 2 1) :=
    {(a, b), (b, a)}
  have hc : 2 ≤ c.card := by simp [c]
  have hgood : ∀ pair ∈ good,
      (NonuniformMajority 2 1).scheduledStep c pair ∈ target := by
    intro pair hpair
    simp only [good, Set.mem_insert_iff, Set.mem_singleton_iff] at hpair
    rcases hpair with rfl | rfl
    · simpa [target, Protocol.scheduledStep] using step_ab_not_stageReady
    · simpa [target, Protocol.scheduledStep] using step_ba_not_stageReady
  have hlower := stepDistOrSelf_toMeasure_ge c hc target good hgood
  change ((NonuniformMajority 2 1).stepDistOrSelf c).toMeasure target ≥ _
  calc
    ((NonuniformMajority 2 1).stepDistOrSelf c).toMeasure target
        ≥ (c.interactionPMF hc).toMeasure good := hlower
    _ = (c.interactionPMF hc) (a, b) +
          (c.interactionPMF hc) (b, a) := by
      have hpairs : good = ({(a, b)} : Set _) ∪ {(b, a)} := by
        ext pair
        simp [good, or_comm]
      have hne : (a, b) ≠ (b, a) := by
        intro h
        exact a_ne_b (Prod.mk.inj h).1
      rw [hpairs, measure_union (Set.disjoint_singleton.mpr hne)
        (DiscreteMeasurableSpace.forall_measurableSet _),
        PMF.toMeasure_apply_singleton _ _
          (DiscreteMeasurableSpace.forall_measurableSet _),
        PMF.toMeasure_apply_singleton _ _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
    _ = c.interactionProb a b + c.interactionProb b a := rfl
    _ = (1 / 3 : ℝ≥0∞) := by
      rw [interactionProb_ab, interactionProb_ba, two_sixths_eq_one_third]

/-- Therefore every purported uniform stage-escape atom for this parameter
choice must spend at least `1/3` in a single step. -/
theorem phase7BandEscape_eta_ge_one_third
    {eta : ℝ≥0∞}
    (hesc : Phase7BandSurvival.Phase7BandEscapeBound
      (L := 2) (K := 1) 4 .pos 1 1 eta) :
    (1 / 3 : ℝ≥0∞) ≤ eta := by
  have hu := hesc.hesc j1 (by decide) (by decide) c c_stageReady
  exact le_trans transitionKernel_not_stageReady_ge_one_third hu

/-- The calibrated concrete stage horizon is nonzero. -/
theorem concrete_driftHorizon_pos :
    1 ≤ DriftSurvival.driftHorizon (2 : ℝ) 4 4 6 := by
  have harg :
      0 < (((4 : ℝ) * ((4 : ℝ) - 1)) / 2) *
        (Real.log (4 : ℝ) + Real.log ((6 : ℝ) * (4 : ℝ) ^ 2)) := by
    apply mul_pos
    · norm_num
    · exact add_pos (Real.log_pos (by norm_num))
        (Real.log_pos (by norm_num))
  simpa [DriftSurvival.driftHorizon] using Nat.ceil_pos.mpr harg

/-- Consequently the advertised tiny escape share cannot coexist with the
current stage gate: already one step costs at least `1/3`, whereas the proposed
per-stage sixth-share is `1/(6·4²)=1/96`. -/
theorem escape_budget_one_over_96_impossible
    {eta : ℝ≥0∞}
    (hesc : Phase7BandSurvival.Phase7BandEscapeBound
      (L := 2) (K := 1) 4 .pos 1 1 eta)
    (escapeEpsilon : ℝ≥0)
    (hescEpsilon :
      ((DriftSurvival.driftHorizon (2 : ℝ) 4 4 6 : ℕ) : ℝ≥0∞) * eta
        ≤ (escapeEpsilon : ℝ≥0∞))
    (hsmall : (escapeEpsilon : ℝ≥0∞) ≤ (1 / 96 : ℝ≥0∞)) : False := by
  have heta : (1 / 3 : ℝ≥0∞) ≤ eta := phase7BandEscape_eta_ge_one_third hesc
  have hT : (1 : ℝ≥0∞) ≤
      ((DriftSurvival.driftHorizon (2 : ℝ) 4 4 6 : ℕ) : ℝ≥0∞) := by
    exact_mod_cast concrete_driftHorizon_pos
  have hprod : (1 / 3 : ℝ≥0∞) ≤
      ((DriftSurvival.driftHorizon (2 : ℝ) 4 4 6 : ℕ) : ℝ≥0∞) * eta := by
    calc
      (1 / 3 : ℝ≥0∞) = 1 * (1 / 3 : ℝ≥0∞) := by rw [one_mul]
      _ ≤ ((DriftSurvival.driftHorizon (2 : ℝ) 4 4 6 : ℕ) : ℝ≥0∞) * eta :=
        mul_le_mul' hT heta
  have hbad : (1 / 3 : ℝ≥0∞) ≤ (1 / 96 : ℝ≥0∞) :=
    hprod.trans (hescEpsilon.trans hsmall)
  have hreal := ENNReal.toReal_mono (by norm_num : (1 / 96 : ℝ≥0∞) ≠ ⊤) hbad
  norm_num at hreal

#print axioms bandCount_c_j1
#print axioms c_stageReady
#print axioms step_ab_not_stageReady
#print axioms step_ba_not_stageReady
#print axioms interactionProb_ab
#print axioms interactionProb_ba
#print axioms transitionKernel_not_stageReady_ge_one_third
#print axioms phase7BandEscape_eta_ge_one_third
#print axioms concrete_driftHorizon_pos
#print axioms escape_budget_one_over_96_impossible

end Phase7StageEscapeObstruction
end Ripple.PopulationProtocol.ExactMajority
