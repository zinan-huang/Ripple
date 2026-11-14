-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockMarkedCompensator.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMarkedWindow
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockTwoPeriodIndicators
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockOpportunityProcess

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMarkedCompensator

open TimeTheorem PairLog PhaseThreeScalar PhaseThreeClockPrefixTails
  PhaseThreeClockThinning PhaseThreeClockMarkedWindow
  PhaseThreeClockTwoPeriodIndicators PhaseThreeClockOpportunityProcess

variable {L K : ℕ}

def rawSet (init : Cfg L K) (s u N t : ℕ) : Set (Ω L K) :=
  {ω | rawFlag init s u N t ω}

def lateSet (init : Cfg L K) (s ℓ u N t : ℕ) : Set (Ω L K) :=
  {ω | lateFlag init s ℓ u N t ω}

def markedOpportunity (init : Cfg L K) (C : Finset (Fin init.card))
    (s ℓ u N t : ℕ) : Ω L K → ℝ :=
  periodOpportunity (rawSet init s u N t) (lateSet init s ℓ u N t)
    (maskTickIndicator init C (u + t))

def markedRate (init : Cfg L K) (s u N : ℕ) (r k : ℝ) (t : ℕ) : Ω L K → ℝ :=
  periodRate (rawSet init s u N t) r k

def markedCharge (init : Cfg L K) (C : Finset (Fin init.card))
    (s ℓ u N : ℕ) (r k : ℝ) (v : ℕ) (ω : Ω L K) : ℝ :=
  opportunityCompensator (markedRate init s u N r k)
    (markedOpportunity init C s ℓ u N) v ω

theorem rawSet_measurable (init : Cfg L K) (s u N t : ℕ) :
    MeasurableSet[shiftedFiltration (pairLogFiltration L K) u t]
      (rawSet init s u N t) := by
  simpa only [rawSet, shiftedFiltration_apply] using rawFlag_measurable init s u N t

theorem lateSet_measurable (init : Cfg L K) (s ℓ u N t : ℕ) :
    MeasurableSet[shiftedFiltration (pairLogFiltration L K) u t]
      (lateSet init s ℓ u N t) := by
  simpa only [lateSet, shiftedFiltration_apply] using lateFlag_measurable init s ℓ u N t

theorem rawSet_lateSet_disjoint (init : Cfg L K) (s ℓ u N t : ℕ) :
    Disjoint (rawSet init s u N t) (lateSet init s ℓ u N t) := by
  apply Set.disjoint_left.mpr
  intro ω hr hl
  exact raw_late_disjoint init s ℓ u N t ω hr hl

theorem markedOpportunity_zero_one (init : Cfg L K)
    (C : Finset (Fin init.card)) (s ℓ u N t : ℕ) :
    ∀ ω, markedOpportunity init C s ℓ u N t ω = 0 ∨
      markedOpportunity init C s ℓ u N t ω = 1 :=
  periodOpportunity_zero_one _ _ _
    (rawSet_lateSet_disjoint init s ℓ u N t)
    (maskTickIndicator_zero_one init C (u + t))

theorem markedOpportunity_stronglyMeasurable (init : Cfg L K)
    (C : Finset (Fin init.card)) (s ℓ u N t : ℕ) :
    StronglyMeasurable[shiftedFiltration (pairLogFiltration L K) u (t + 1)]
      (markedOpportunity init C s ℓ u N t) := by
  apply periodOpportunity_stronglyMeasurable
    (ℱ := shiftedFiltration (pairLogFiltration L K) u) t
    (rawSet init s u N t) (lateSet init s ℓ u N t)
    (rawSet_measurable init s u N t) (lateSet_measurable init s ℓ u N t)
    (maskTickIndicator init C (u + t))
  simpa only [shiftedFiltration_apply, Nat.add_assoc] using
    maskTickIndicator_stronglyMeasurable init C (u + t)

theorem markedRate_stronglyMeasurable (init : Cfg L K) (s u N : ℕ)
    (r k : ℝ) (t : ℕ) :
    StronglyMeasurable[shiftedFiltration (pairLogFiltration L K) u t]
      (markedRate init s u N r k t) :=
  periodRate_stronglyMeasurable
    (ℱ := shiftedFiltration (pairLogFiltration L K) u) t
    (rawSet init s u N t) (rawSet_measurable init s u N t) r k

theorem markedRate_nonneg (init : Cfg L K) (s u N : ℕ)
    (r k : ℝ) (hr : 0 ≤ r) (hk : 0 ≤ k) (t : ℕ) :
    ∀ ω, 0 ≤ markedRate init s u N r k t ω :=
  periodRate_nonneg _ r k hr hk

theorem charge_split (init : Cfg L K) (C : Finset (Fin init.card))
    (s ℓ u N : ℕ) (r k : ℝ) (v : ℕ) (ω : Ω L K) :
    markedCharge init C s ℓ u N r k v ω =
      r * (rawSlotCount init s u N v ω : ℝ) +
        k * laterClockCount init C s ℓ u N v ω := by
  classical
  unfold markedCharge markedRate markedOpportunity opportunityCompensator
  rw [period_compensator_split (rawSet init s u N) (lateSet init s ℓ u N)
    (fun t => maskTickIndicator init C (u + t)) r k
    (fun t => rawSet_lateSet_disjoint init s ℓ u N t) v ω,
    rawSlotCount_cast_eq_sum]
  simp only [rawSet, lateSet, Set.indicator_apply, Set.mem_setOf_eq,
    laterClockCount, laterTickIndicator, bernoulliCount]

theorem charge_le (init : Cfg L K) (C : Finset (Fin init.card))
    (s ℓ u N D : ℕ) (r k : ℝ) (hr : 0 ≤ r) (hk : 0 ≤ k)
    (v : ℕ) (ω : Ω L K)
    (hD : laterClockCount init C s ℓ u N v ω ≤ (D : ℝ)) :
    markedCharge init C s ℓ u N r k v ω ≤ r * (N : ℝ) + k * (D : ℝ) := by
  rw [charge_split]
  have hraw : (rawSlotCount init s u N v ω : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast rawSlotCount_le_budget init s u N v ω
  exact add_le_add (mul_le_mul_of_nonneg_left hraw hr)
    (mul_le_mul_of_nonneg_left hD hk)

theorem scaled_charge_le (init : Cfg L K) (C : Finset (Fin init.card))
    (s ℓ u N D : ℕ) (a r k : ℝ) (ha : 0 ≤ a) (hr : 0 ≤ r) (hk : 0 ≤ k)
    (v : ℕ) (ω : Ω L K)
    (hD : laterClockCount init C s ℓ u N v ω ≤ (D : ℝ)) :
    opportunityCompensator (fun t ω => a * markedRate init s u N r k t ω)
      (markedOpportunity init C s ℓ u N) v ω ≤
        a * (r * (N : ℝ) + k * (D : ℝ)) := by
  calc
    _ = a * markedCharge init C s ℓ u N r k v ω := by
      simp only [markedCharge, opportunityCompensator, Finset.mul_sum, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (charge_le init C s ℓ u N D r k hr hk v ω hD) ha

theorem markedCharge_stronglyMeasurable (init : Cfg L K)
    (C : Finset (Fin init.card)) (s ℓ u N : ℕ) (r k : ℝ) (v : ℕ) :
    StronglyMeasurable[shiftedFiltration (pairLogFiltration L K) u v]
      (markedCharge init C s ℓ u N r k v) :=
  opportunityCompensator_stronglyMeasurable _ _
    (fun t => markedRate_stronglyMeasurable init s u N r k t)
    (fun t => markedOpportunity_stronglyMeasurable init C s ℓ u N t) v

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMarkedCompensator

end
