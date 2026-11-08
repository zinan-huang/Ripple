/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Weighted multiplicative drift from scheduler-weighted drop sums

This file restores only the generic, protocol-faithful engine.  The historical
Phase-7 specialization is intentionally omitted: its old terminal predicate is
not reachable from all paper-relevant deep-minority states and must not be used.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase0Window

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

namespace DyadicMassDrainTight

variable {L K : ℕ}

/-- One-step multiplicative drift for a natural-valued potential on an invariant. -/
def WeightedDyadicMassDrift
    (Inv : Config (AgentState L K) → Prop)
    (Φ : Config (AgentState L K) → ℕ)
    (r : ℝ≥0∞) : Prop :=
  ∀ b : Config (AgentState L K), Inv b →
    ∫⁻ c, (Φ c : ℝ≥0∞) ∂((NonuniformMajority L K).transitionKernel b)
      ≤ r * (Φ b : ℝ≥0∞)

end DyadicMassDrainTight

namespace WeightedDriftDropSum

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

attribute [local instance] Classical.propDecidable

section Generic

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- The scheduler-weighted one-step drop of a natural potential. -/
noncomputable def weightedDropSum (P : Protocol Λ) (Φ : Config Λ → ℕ)
    (c : Config Λ) : ℝ≥0∞ :=
  ∑ pair : Λ × Λ,
    ((Φ c : ℝ≥0∞) -
        (Φ (Protocol.stepOrSelf P c pair.1 pair.2) : ℝ≥0∞))
      * c.interactionProb pair.1 pair.2

/-- If `Φ` is pointwise non-increasing under every scheduled update, then the
one-step expectation plus the scheduler-weighted drop sum equals the current
potential. -/
theorem lintegral_add_weightedDropSum_eq_current (P : Protocol Λ) (Φ : Config Λ → ℕ)
    (c : Config Λ) (hc : 2 ≤ c.card)
    (hmono : ∀ pair : Λ × Λ,
      Φ (Protocol.stepOrSelf P c pair.1 pair.2) ≤ Φ c) :
    (∫⁻ c', (Φ c' : ℝ≥0∞) ∂(P.transitionKernel c)) + weightedDropSum P Φ c
      = (Φ c : ℝ≥0∞) := by
  classical
  rw [Phase0Window.lintegral_transitionKernel_eq_sum P c hc]
  unfold weightedDropSum
  calc
    (∑ pair : Λ × Λ,
          (Φ (Protocol.stepOrSelf P c pair.1 pair.2) : ℝ≥0∞)
            * c.interactionProb pair.1 pair.2)
        + ∑ pair : Λ × Λ,
          ((Φ c : ℝ≥0∞) -
              (Φ (Protocol.stepOrSelf P c pair.1 pair.2) : ℝ≥0∞))
            * c.interactionProb pair.1 pair.2
        = ∑ pair : Λ × Λ,
            ((Φ (Protocol.stepOrSelf P c pair.1 pair.2) : ℝ≥0∞)
                * c.interactionProb pair.1 pair.2
              + ((Φ c : ℝ≥0∞) -
                  (Φ (Protocol.stepOrSelf P c pair.1 pair.2) : ℝ≥0∞))
                * c.interactionProb pair.1 pair.2) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ pair : Λ × Λ, (Φ c : ℝ≥0∞) * c.interactionProb pair.1 pair.2 := by
          refine Finset.sum_congr rfl ?_
          intro pair _
          have hle :
              (Φ (Protocol.stepOrSelf P c pair.1 pair.2) : ℝ≥0∞)
                ≤ (Φ c : ℝ≥0∞) := by
            exact_mod_cast hmono pair
          rw [← add_mul]
          have hsum :
              (Φ (Protocol.stepOrSelf P c pair.1 pair.2) : ℝ≥0∞)
                  + ((Φ c : ℝ≥0∞) -
                    (Φ (Protocol.stepOrSelf P c pair.1 pair.2) : ℝ≥0∞))
                = (Φ c : ℝ≥0∞) := by
            rw [add_comm]
            exact tsub_add_cancel_of_le hle
          rw [hsum]
    _ = (Φ c : ℝ≥0∞) * ∑ pair : Λ × Λ, c.interactionProb pair.1 pair.2 := by
          rw [Finset.mul_sum]
    _ = (Φ c : ℝ≥0∞) := by
          have hsumprob : (∑ pair : Λ × Λ, c.interactionProb pair.1 pair.2) = 1 := by
            have h := (c.interactionPMF hc).tsum_coe
            rw [tsum_eq_sum (s := Finset.univ)
              (by intro x hx; exact absurd (Finset.mem_univ x) hx)] at h
            convert h using 1
          rw [hsumprob, mul_one]

/-- Scheduler-level weighted multiplicative drift.  The parameter `β` is the
per-step multiplicative drop fraction, e.g. `β = c₀ / n`. -/
theorem weighted_dyadic_mass_drift_of_dropSum (P : Protocol Λ) (Φ : Config Λ → ℕ)
    (c : Config Λ) (hc : 2 ≤ c.card) (β : ℝ≥0∞) (hβtop : β ≠ ∞)
    (hmono : ∀ pair : Λ × Λ,
      Φ (Protocol.stepOrSelf P c pair.1 pair.2) ≤ Φ c)
    (hdrop : β * (Φ c : ℝ≥0∞) ≤ weightedDropSum P Φ c) :
    ∫⁻ c', (Φ c' : ℝ≥0∞) ∂(P.transitionKernel c)
      ≤ (1 - β) * (Φ c : ℝ≥0∞) := by
  classical
  set X : ℝ≥0∞ := (Φ c : ℝ≥0∞)
  set I : ℝ≥0∞ := ∫⁻ c', (Φ c' : ℝ≥0∞) ∂(P.transitionKernel c)
  set D : ℝ≥0∞ := weightedDropSum P Φ c
  have hID : I + D = X := by
    simpa [I, D, X] using lintegral_add_weightedDropSum_eq_current P Φ c hc hmono
  have hIX : I + β * X ≤ X := by
    calc
      I + β * X ≤ I + D := by gcongr
      _ = X := hID
  have hβXtop : β * X ≠ ∞ := by
    simpa [X] using ENNReal.mul_ne_top hβtop (ENNReal.natCast_ne_top (Φ c))
  have hIle : I ≤ X - β * X :=
    ENNReal.le_sub_of_add_le_right hβXtop hIX
  have hsubmul : (1 - β) * X = X - β * X := by
    calc
      (1 - β) * X = 1 * X - β * X := by
        exact ENNReal.sub_mul (a := 1) (b := β) (c := X) (by
          intro _hβpos _hβlt
          simp [X])
      _ = X - β * X := by rw [one_mul]
  simpa [I, X, hsubmul]
    using hIle

end Generic

section AgentStateGeneric

variable {L K : ℕ}

/-- In the exact-majority protocol, a uniform weighted-drop-sum lower bound on an
invariant gives the named `WeightedDyadicMassDrift` shape. -/
theorem weighted_dyadic_mass_drift_on_of_dropSum
    (Inv : Config (AgentState L K) → Prop) (Φ : Config (AgentState L K) → ℕ)
    (β : ℝ≥0∞) (hβtop : β ≠ ∞)
    (hcard : ∀ b, Inv b → 2 ≤ b.card)
    (hmono : ∀ b, Inv b → ∀ pair : AgentState L K × AgentState L K,
      Φ (Protocol.stepOrSelf (NonuniformMajority L K) b pair.1 pair.2) ≤ Φ b)
    (hdrop : ∀ b, Inv b →
      β * (Φ b : ℝ≥0∞) ≤ weightedDropSum (NonuniformMajority L K) Φ b) :
    DyadicMassDrainTight.WeightedDyadicMassDrift (L := L) (K := K)
      Inv Φ (1 - β) := by
  intro b hb
  exact weighted_dyadic_mass_drift_of_dropSum
    (NonuniformMajority L K) Φ b (hcard b hb) β hβtop (hmono b hb) (hdrop b hb)

end AgentStateGeneric

#print axioms lintegral_add_weightedDropSum_eq_current
#print axioms weighted_dyadic_mass_drift_of_dropSum
#print axioms weighted_dyadic_mass_drift_on_of_dropSum

end WeightedDriftDropSum
end Ripple.PopulationProtocol.ExactMajority
