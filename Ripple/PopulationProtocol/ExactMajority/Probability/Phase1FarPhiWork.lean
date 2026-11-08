/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Quantitative Phase-1 far-mass work component

This file combines the all-far-agent multiplicative drift with the truthful
clock-prefix interface.  Its `Pre` explicitly carries a future clock-prefix
budget for the current start configuration; it does not quantify a small
one-step escape bound over arbitrary `Phase1GapFloorEntry` states.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1FarPhiSharp
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1ClockLeakZero
import Ripple.PopulationProtocol.ExactMajority.Probability.DriftHorizon

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase1FarPhiWork

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Deterministic potential ceiling -/

/-- One Main contributes at most two units to `farPhiN`. -/
theorem farPhiMainN_le_two (a : AgentState L K) :
    Phase1FarPhi.farPhiMainN a ≤ 2 := by
  have hphi : ∀ v : Fin 7, Phase1FarPhi.farPhi v ≤ 2 := by decide
  unfold Phase1FarPhi.farPhiMainN
  by_cases hmain : a.role = Role.main
  · rw [if_pos hmain]
    exact hphi a.smallBias
  · rw [if_neg hmain]
    omega

/-- Hence the total Phase-1 potential is at most twice the population size. -/
theorem farPhiN_le_two_mul_card (c : Config (AgentState L K)) :
    Phase1FarPhi.farPhiN c ≤ 2 * c.card := by
  classical
  unfold Phase1FarPhi.farPhiN
  induction c using Multiset.induction with
  | empty => simp
  | cons a c ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
      have ha := farPhiMainN_le_two a
      omega

/-- The ceiling specialized to an honest Phase-1 entry of size `n`. -/
theorem farPhiN_le_two_mul_n {n g mc : ℕ}
    (c : Config (AgentState L K))
    (hentry : Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c) :
    Phase1FarPhi.farPhiN c ≤ 2 * n := by
  rw [← hentry.1.1]
  exact farPhiN_le_two_mul_card c

/-! ## Rate and horizon calibration -/

/-- The real numerator used by `DriftHorizon`.  The four-orientation ledger
recovers the full fixed partner floor. -/
noncomputable def partnerB (g mc : ℕ) : ℝ :=
  (((mc - g + 3) / 4 : ℕ) : ℝ)

/-- The sharp rate in the exact shape consumed by `drift_pow_le_budget_sub`. -/
theorem farBetaSharp_eq_ofReal_partnerB (n g mc : ℕ) :
    Phase1FarPhiSharp.farBetaSharp n g mc =
      ENNReal.ofReal (partnerB g mc /
        ((n : ℝ) * ((n : ℝ) - 1))) := by
  rfl

/-- The partner numerator is positive when the integer partner floor is. -/
theorem partnerB_pos {g mc : ℕ}
    (hP : 0 < (mc - g + 3) / 4) :
    0 < partnerB g mc := by
  unfold partnerB
  positivity

/-- The scheduler-rate cap follows from the natural calibration `mc ≤ n`. -/
theorem partnerB_le_scheduler {n g mc : ℕ}
    (hn : 2 ≤ n) (hmc : mc ≤ n) :
    partnerB g mc ≤ (n : ℝ) * ((n : ℝ) - 1) := by
  have hP : (mc - g + 3) / 4 ≤ n := by omega
  have hPR : (((mc - g + 3) / 4 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hP
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  unfold partnerB
  nlinarith

/-- The fixed half-budget horizon for Phase 1. -/
noncomputable def horizon (n g mc : ℕ) : ℕ :=
  DriftSurvival.driftHorizon (partnerB g mc) n (2 * n) 2

/-- The real-chain clock-prefix obligation attached to one work start. -/
def ClockPrefixBudget (n g mc : ℕ) (η : ℝ≥0∞)
    (c : Config (AgentState L K)) : Prop :=
  (∑ τ ∈ Finset.range (horizon n g mc),
      ((NonuniformMajority L K).transitionKernel ^ τ) c
        {x | ¬ Phase6LeakZero.ClockPos (L := L) (K := K) x}) ≤ η

/-- The honest fast-branch entry surface.  The clock tail is start-dependent,
so it is carried pointwise instead of asserted for every honest configuration. -/
def Pre (n g mc : ℕ) (η : ℝ≥0∞)
    (c : Config (AgentState L K)) : Prop :=
  Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c ∧
    ClockPrefixBudget (L := L) (K := K) n g mc η c

/-- The exact drained endpoint before reachable non-Main neutrality is added. -/
def Post (n g mc : ℕ) (c : Config (AgentState L K)) : Prop :=
  Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c ∧
    Phase1FarPhi.farPhiN c = 0

/-! ## Work component -/

/-- Phase-1 multiplicative drain with half the inverse-square budget allocated
to far-mass drift and half to the reachable clock-prefix tail. -/
noncomputable def work
    (n g mc : ℕ) (hn : 2 ≤ n) (hmc : mc ≤ n)
    (hP : 0 < (mc - g + 3) / 4)
    (ηClock : ℝ≥0∞)
    (hClock : ηClock ≤
      (DriftSurvival.driftBudgetNN 2 n : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := Pre (L := L) (K := K) n g mc ηClock
  Post := Post (L := L) (K := K) n g mc
  t := horizon n g mc
  ε := DriftSurvival.driftBudgetNN 2 n +
    DriftSurvival.driftBudgetNN 2 n
  convergence := by
    intro c₀ hpre
    let r : ℝ≥0∞ :=
      1 - Phase1FarPhiSharp.farBetaSharp n g mc
    have hdrift : ∀ c,
        Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c →
        ∫⁻ c', (Phase1FarPhi.farPhiN c' : ℝ≥0∞)
            ∂((NonuniformMajority L K).transitionKernel c)
          ≤ r * (Phase1FarPhi.farPhiN c : ℝ≥0∞) := by
      intro c hc
      exact Phase1FarPhiSharp.farPhiN_multiplicative_drift_sharp hn c hc
    have hesc : ∀ c,
        Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c →
        c ∈ {x | Phase6LeakZero.ClockPos (L := L) (K := K) x} →
        (NonuniformMajority L K).transitionKernel c
          {x | ¬ Phase1PartnerFloor.Phase1GapFloorEntry
            (L := L) (K := K) n g mc x} ≤ (0 : ℝ≥0∞) := by
      intro c hc hpos
      have hz := Phase1ClockLeakZero.phase1GapFloorEntry_leak_zero_on_clockPos
        n g mc c hc hpos
      have heq :
          {x | ¬ Phase1PartnerFloor.Phase1GapFloorEntry
            (L := L) (K := K) n g mc x} =
            (Phase1FarPhiSurvival.phase1GapFloorEntryGate
              (L := L) (K := K) n g mc)ᶜ := by
        ext x
        simp [Phase1FarPhiSurvival.phase1GapFloorEntryGate]
      rw [heq, hz]
    have htail := DriftSurvival.real_tail_le_drift_plus_side_prefix
      (NonuniformMajority L K).transitionKernel
      (Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc)
      Phase1FarPhi.farPhiN r hdrift
      {x | Phase6LeakZero.ClockPos (L := L) (K := K) x}
      0 hesc (horizon n g mc) c₀ hpre.1
    have hB0 : 0 < partnerB g mc := partnerB_pos hP
    have hBle : partnerB g mc ≤ (n : ℝ) * ((n : ℝ) - 1) :=
      partnerB_le_scheduler hn hmc
    have hdrain : r ^ (horizon n g mc) * ((2 * n : ℕ) : ℝ≥0∞) ≤
        (DriftSurvival.driftBudgetNN 2 n : ℝ≥0∞) := by
      dsimp [r, horizon]
      rw [farBetaSharp_eq_ofReal_partnerB]
      exact DriftSurvival.drift_pow_le_budget_sub hn (by omega) (by omega)
        hB0 hBle
    calc
      ((NonuniformMajority L K).transitionKernel ^ horizon n g mc) c₀
          {c | ¬ Post (L := L) (K := K) n g mc c}
          ≤ r ^ horizon n g mc *
                (Phase1FarPhi.farPhiN c₀ : ℝ≥0∞) +
              ((horizon n g mc : ℕ) : ℝ≥0∞) * 0 +
                (∑ τ ∈ Finset.range (horizon n g mc),
                  ((NonuniformMajority L K).transitionKernel ^ τ) c₀
                    {x | ¬ Phase6LeakZero.ClockPos
                      (L := L) (K := K) x}) := by
            simpa [Post, add_assoc] using htail
      _ ≤ r ^ horizon n g mc * ((2 * n : ℕ) : ℝ≥0∞) + ηClock := by
            simp only [mul_zero, add_zero]
            exact add_le_add
              (mul_le_mul_right (by
                exact_mod_cast farPhiN_le_two_mul_n c₀ hpre.1) _)
              hpre.2
      _ ≤ (DriftSurvival.driftBudgetNN 2 n : ℝ≥0∞) +
            (DriftSurvival.driftBudgetNN 2 n : ℝ≥0∞) :=
          add_le_add hdrain hClock
      _ = ((DriftSurvival.driftBudgetNN 2 n +
            DriftSurvival.driftBudgetNN 2 n : ℝ≥0) : ℝ≥0∞) := by
          rw [ENNReal.coe_add]

/-- The work component spends at most the full inverse-square phase budget. -/
theorem work_epsilon_le_inv_sq
    (n g mc : ℕ) (hn : 2 ≤ n) (hmc : mc ≤ n)
    (hP : 0 < (mc - g + 3) / 4)
    (ηClock : ℝ≥0∞)
    (hClock : ηClock ≤
      (DriftSurvival.driftBudgetNN 2 n : ℝ≥0∞)) :
    ((work (L := L) (K := K) n g mc hn hmc hP ηClock hClock).ε : ℝ≥0∞)
      ≤ 1 / (n : ℝ≥0∞) ^ 2 := by
  change (DriftSurvival.driftBudgetNN 2 n : ℝ≥0∞) +
      (DriftSurvival.driftBudgetNN 2 n : ℝ≥0∞) ≤ _
  rw [← two_mul]
  exact le_of_eq (DriftSurvival.natCast_mul_driftBudgetNN_eq_inv_sq
    (D := 2) (n := n) (by omega) (by omega))

/-- Forgetting the conserved gap and Main-count fields gives the minimal
reachable endpoint used by the Phase-1-to-2 bridge. -/
theorem post_to_phase1Drained
    (n g mc : ℕ) (c : Config (AgentState L K))
    (h : Post (L := L) (K := K) n g mc c) :
    Phase1GapFloorEntryClosure.Phase1Drained (L := L) (K := K) n c :=
  ⟨h.1.1, h.2⟩

#print axioms farPhiN_le_two_mul_card
#print axioms farPhiN_le_two_mul_n
#print axioms farBetaSharp_eq_ofReal_partnerB
#print axioms partnerB_le_scheduler
#print axioms work
#print axioms work_epsilon_le_inv_sq
#print axioms post_to_phase1Drained

end Phase1FarPhiWork
end Ripple.PopulationProtocol.ExactMajority
