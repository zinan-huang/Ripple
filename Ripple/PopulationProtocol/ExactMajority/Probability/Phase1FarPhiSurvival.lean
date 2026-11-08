/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Contracting survival for the honest Phase-1 far-mass gate

This is the gate-level composition for `Phase1FarPhiDrift`.  The gate is the
truthful `Phase1PartnerFloor.Phase1GapFloorEntry`, not the historical all-Main predicate.
The remaining inputs are explicitly the counter/window escape tail and scalar
budget; no structural premise is manufactured from a bare phase-only window.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1FarPhiDrift

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical

namespace Phase1FarPhiSurvival

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- The satisfiable stopped-drift gate. -/
def phase1GapFloorEntryGate (n g mc : ℕ) : Set (Config (AgentState L K)) :=
  {c | Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c}

/-- The fixed honest partner-pool floor. -/
def partnerFloor (g mc : ℕ) : ℕ := (mc - g + 3) / 4

/-- Per-interaction strict-drop probability floor. -/
noncomputable def dropRate (n g mc : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((partnerFloor g mc : ℕ) : ℝ) /
    ((n : ℝ) * ((n : ℝ) - 1)))

/-- Contracting stopped-MGF rate. -/
noncomputable def farRate (n g mc : ℕ) (s : ℝ) : ℝ≥0∞ :=
  contractRate (dropRate n g mc) s

/-- The rate is strictly contracting whenever the partner floor is positive. -/
theorem farRate_lt_one {n g mc : ℕ} (hn : 2 ≤ n)
    (hPpos : 0 < partnerFloor g mc)
    (hPle : ((partnerFloor g mc : ℕ) : ℝ)
      ≤ (n : ℝ) * ((n : ℝ) - 1))
    (s : ℝ) (hs : 0 < s) :
    farRate n g mc s < 1 := by
  unfold farRate dropRate partnerFloor
  exact Phase1SurvivalContracting.phase1_contractRate_lt_one
    s hs hn hPpos hPle

/-- The stopped-MGF high event is exactly failure of Main-bias safety. -/
theorem unsafe_eq_stopped_high (s : ℝ) (hs : 0 < s) :
    {c : Config (AgentState L K) | ¬ Phase1FarPhi.MainBiasSafe c}
      = {c | ENNReal.ofReal (Real.exp s) ≤
          Phase1FarPhiDrift.stoppedFarPot (L := L) (K := K) s c} := by
  ext c
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hunsafe
    apply (Phase1FarPhiDrift.stoppedFarPot_threshold_iff s hs c).2
    by_contra hnot
    have hz : Phase1FarPhi.farPhiN c = 0 := by omega
    exact hunsafe ((Phase1FarPhi.farPhiN_eq_zero_iff_mainBiasSafe c).1 hz)
  · intro hhigh hsafe
    have hge := (Phase1FarPhiDrift.stoppedFarPot_threshold_iff s hs c).1 hhigh
    have hz := (Phase1FarPhi.farPhiN_eq_zero_iff_mainBiasSafe c).2 hsafe
    omega

/--
Contracting survival to the exact Main-safe endpoint.

`S` is the clock-safe subset used by the killed-kernel prefix decomposition.
`hLeak` controls one-step gate exit while both the gate and `S` hold; `hClock`
controls cumulative failure of `S`.  These are the only non-drift probability
inputs.  In particular, no universal `Phase1Win → Phase1GapFloorEntry` premise occurs.
-/
theorem mainBiasSafe_tail {n g mc : ℕ} (hn : 2 ≤ n)
    (hPpos : 0 < partnerFloor g mc)
    (hPle : ((partnerFloor g mc : ℕ) : ℝ)
      ≤ (n : ℝ) * ((n : ℝ) - 1))
    (s : ℝ) (hs : 0 < s)
    (S : Set (Config (AgentState L K))) (qLeak : ℝ≥0∞)
    (hLeak : ∀ x ∈ phase1GapFloorEntryGate (L := L) (K := K) n g mc, x ∈ S →
      (NonuniformMajority L K).transitionKernel x
        (phase1GapFloorEntryGate (L := L) (K := K) n g mc)ᶜ ≤ qLeak)
    (T : ℕ) (c₀ : Config (AgentState L K))
    (hEntry₀ : Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c₀)
    (εDrain : ℝ≥0)
    (hBudget : ((T : ℝ≥0∞) * qLeak +
        (farRate n g mc s) ^ T *
          Phase1FarPhiDrift.stoppedFarPot (L := L) (K := K) s c₀ /
            ENNReal.ofReal (Real.exp s) : ℝ≥0∞) ≤ (εDrain : ℝ≥0∞))
    (ηClock : ℝ≥0∞)
    (hClock : (∑ τ ∈ Finset.range T,
      ((NonuniformMajority L K).transitionKernel ^ τ) c₀ Sᶜ) ≤ ηClock) :
    farRate n g mc s < 1 ∧
      ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ Phase1FarPhi.MainBiasSafe c}
          ≤ (εDrain : ℝ≥0∞) + ηClock := by
  classical
  have hrlt := farRate_lt_one hn hPpos hPle s hs
  have hDrift : ∀ x ∈ phase1GapFloorEntryGate (L := L) (K := K) n g mc,
      ∫⁻ y, Phase1FarPhiDrift.stoppedFarPot (L := L) (K := K) s y
          ∂((NonuniformMajority L K).transitionKernel x)
        ≤ farRate n g mc s *
          Phase1FarPhiDrift.stoppedFarPot (L := L) (K := K) s x := by
    intro x hx
    simp only [phase1GapFloorEntryGate, Set.mem_setOf_eq] at hx
    simpa [farRate, dropRate, partnerFloor] using
      (Phase1FarPhiDrift.stoppedFarPot_drift_of_phase1GapFloorEntry
        (L := L) (K := K) hn s hs.le x hx)
  have hθ0 : ENNReal.ofReal (Real.exp s) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos s))
  have hθtop : ENNReal.ofReal (Real.exp s) ≠ ∞ := ENNReal.ofReal_ne_top
  have hTail := GatedDrift.gated_real_tail_anyr
    (K := (NonuniformMajority L K).transitionKernel)
    (G := phase1GapFloorEntryGate (L := L) (K := K) n g mc)
    (Phase1FarPhiDrift.stoppedFarPot (L := L) (K := K) s)
    (farRate n g mc s) hDrift T c₀ (ENNReal.ofReal (Real.exp s)) hθ0 hθtop
  have hEscape := GatedDrift.kill_escape_le_prefix_union
    (K := (NonuniformMajority L K).transitionKernel)
    (G := phase1GapFloorEntryGate (L := L) (K := K) n g mc)
    S qLeak hLeak T c₀ hEntry₀
  refine ⟨hrlt, ?_⟩
  rw [unsafe_eq_stopped_high s hs]
  refine hTail.trans ?_
  calc
    (GatedDrift.killK (NonuniformMajority L K).transitionKernel
          (phase1GapFloorEntryGate (L := L) (K := K) n g mc) ^ T)
          (some c₀) {(none : Option (Config (AgentState L K)))} +
        (farRate n g mc s) ^ T *
          Phase1FarPhiDrift.stoppedFarPot (L := L) (K := K) s c₀ /
            ENNReal.ofReal (Real.exp s)
      ≤ ((T : ℝ≥0∞) * qLeak +
          ∑ τ ∈ Finset.range T,
            ((NonuniformMajority L K).transitionKernel ^ τ) c₀ Sᶜ) +
        (farRate n g mc s) ^ T *
          Phase1FarPhiDrift.stoppedFarPot (L := L) (K := K) s c₀ /
            ENNReal.ofReal (Real.exp s) := add_le_add hEscape le_rfl
    _ = ((T : ℝ≥0∞) * qLeak +
          (farRate n g mc s) ^ T *
            Phase1FarPhiDrift.stoppedFarPot (L := L) (K := K) s c₀ /
              ENNReal.ofReal (Real.exp s)) +
        ∑ τ ∈ Finset.range T,
          ((NonuniformMajority L K).transitionKernel ^ τ) c₀ Sᶜ := by ring
    _ ≤ (εDrain : ℝ≥0∞) + ηClock := add_le_add hBudget hClock

#print axioms farRate_lt_one
#print axioms unsafe_eq_stopped_high
#print axioms mainBiasSafe_tail

end Phase1FarPhiSurvival
end Ripple.PopulationProtocol.ExactMajority
