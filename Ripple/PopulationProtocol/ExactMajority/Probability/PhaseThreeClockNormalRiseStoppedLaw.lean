-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockNormalRiseStoppedLaw.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockNormalRise
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3Scalar

/-!
# Original-law upper rate of a next-safe normal rise

The next-state phase cap is part of the counted event. Conditional
expectation monotonicity compares that event to the observed candidate
pair event, so no law is conditioned on future safety.

This supplies the upper-rate half of a pre-breach freeze construction.
It does not construct the frozen front processes or supply their lower
front rate at a possible breach.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockNormalRiseStoppedLaw

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockEmbeddingBridge
  PhaseThreeClockPredictablePairs PhaseThreeClockEarlyMarks
  PhaseThreeClockEarlyMarkEmbedding PhaseThreeClockNormalRise
  PhaseThreeClockActivationSeed PhaseThreeClockSeedTails

variable {L K : ℕ}

def CurrentMarkedGuard (init : Cfg L K) (C : Finset (Fin init.card))
    (ℓ cutoff s t : ℕ) (ω : Ω L K) : Prop :=
  ClockEnvironment (virtualLabels init ω t) ∧
    C = clockSet (virtualLabels init ω t) ∧
    markedAt init C ℓ cutoff s ω t ⊆ aboveSet (virtualLabels init ω t) (ℓ + 1)

open Classical in
def nextSafeNormalIndicator (init : Cfg L K) (C : Finset (Fin init.card))
    (ℓ cutoff s t : ℕ) (ω : Ω L K) : ℝ :=
  if CurrentMarkedGuard init C ℓ cutoff s t ω ∧
      (∀ k, (virtualLabels init ω (t + 1) k).phase.val ≤ 3) ∧
      normalCount (virtualLabels init ω (t + 1)) (markedAt init C ℓ cutoff s ω (t + 1)) ℓ =
        normalCount (virtualLabels init ω t) (markedAt init C ℓ cutoff s ω t) ℓ + 1
    then 1 else 0

theorem nextSafeNormalIndicator_stronglyMeasurable (init : Cfg L K)
    (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ) :
    StronglyMeasurable[pairLogFiltration L K (t + 1)]
      (nextSafeNormalIndicator init C ℓ cutoff s t) := by
  classical
  let trunc : (Finset.Iic (t + 1) → Draw L K) → (Finset.Iic t → Draw L K) :=
    fun p k => p ⟨k.val, Finset.mem_Iic.mpr
      (le_trans (Finset.mem_Iic.mp k.property) (Nat.le_succ t))⟩
  let H : (Finset.Iic (t + 1) → Draw L K) → ℝ := fun p =>
    let f := auxPrefix init virtualRule t (trunc p)
    let g := auxPrefix init virtualRule (t + 1) p
    let M := markedPrefix init C ℓ cutoff s t (trunc p)
    let N := markedPrefix init C ℓ cutoff s (t + 1) p
    if (ClockEnvironment f ∧ C = clockSet f ∧ M ⊆ aboveSet f (ℓ + 1)) ∧
        (∀ k, (g k).phase.val ≤ 3) ∧ normalCount g N ℓ = normalCount f M ℓ + 1
      then 1 else 0
  have hH : StronglyMeasurable[pairLogFiltration L K (t + 1)]
      (fun ω => H (frestrictLe (t + 1) ω)) :=
    ((measurable_of_countable H).comp
      (measurable_pairLog_prefix L K (t + 1))).stronglyMeasurable
  convert hH using 1
  funext ω
  by_cases hcnd : CurrentMarkedGuard init C ℓ cutoff s t ω ∧
      (∀ k, (virtualLabels init ω (t + 1) k).phase.val ≤ 3) ∧
      normalCount (virtualLabels init ω (t + 1)) (markedAt init C ℓ cutoff s ω (t + 1)) ℓ =
        normalCount (virtualLabels init ω t) (markedAt init C ℓ cutoff s ω t) ℓ + 1
  · rw [nextSafeNormalIndicator, if_pos hcnd]
    exact (if_pos (show _ from ⟨hcnd.1, hcnd.2⟩)).symm
  · rw [nextSafeNormalIndicator, if_neg hcnd]
    exact (if_neg (fun h => hcnd ⟨h.1, h.2⟩)).symm

theorem nextSafeNormalIndicator_zero_one (init : Cfg L K)
    (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ) (ω : Ω L K) :
    nextSafeNormalIndicator init C ℓ cutoff s t ω = 0 ∨
      nextSafeNormalIndicator init C ℓ cutoff s t ω = 1 := by
  classical
  unfold nextSafeNormalIndicator
  split_ifs <;> simp

theorem normalRiseIndicator_stronglyMeasurable (init : Cfg L K)
    (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ) :
    StronglyMeasurable[pairLogFiltration L K (t + 1)]
      (normalRiseIndicator init C ℓ cutoff s t) := by
  simpa only [normalRiseIndicator, virtualLabels, auxLabels, markedAt] using
    prefix_pair_indicator_stronglyMeasurable init t
      (fun p => NormalRisePair (auxPrefix init virtualRule t p)
        (markedPrefix init C ℓ cutoff s t p) ℓ)

theorem normalRiseIndicator_zero_one (init : Cfg L K)
    (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ) (ω : Ω L K) :
    normalRiseIndicator init C ℓ cutoff s t ω = 0 ∨
      normalRiseIndicator init C ℓ cutoff s t ω = 1 := by
  classical
  unfold normalRiseIndicator
  split_ifs <;> simp

theorem nextSafeNormalIndicator_le_candidate (init : Cfg L 256)
    (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ)
    (hst : s ≤ t) (hℓ : 1 ≤ ℓ) (hcap : ℓ + 1 ≤ 256 * (L + 1))
    (ω : Ω L 256) :
    nextSafeNormalIndicator init C ℓ cutoff s t ω ≤
      normalRiseIndicator init C ℓ cutoff s t ω := by
  classical
  unfold nextSafeNormalIndicator
  split_ifs with h
  · have heq := h.2.2
    have hrise : (normalCount (virtualLabels init ω (t + 1))
        (markedAt init C ℓ cutoff s ω (t + 1)) ℓ : ℝ) -
        (normalCount (virtualLabels init ω t) (markedAt init C ℓ cutoff s ω t) ℓ : ℝ) = 1 := by
      rw [heq, Nat.cast_add, Nat.cast_one]
      ring
    have hle := normal_increment_indicator_le_candidate init C ℓ cutoff s t ω
      hst hℓ hcap h.1.1 h.1.2.1 h.1.2.2 h.2.1
    simpa only [if_pos hrise] using hle
  · rcases normalRiseIndicator_zero_one init C ℓ cutoff s t ω with h | h <;>
      simp only [h] <;> norm_num

/-- Conditional monotonicity counts only the next-safe event; it never
conditions the law on the next phase cap. -/
theorem nextSafeNormalIndicator_conditional_upper (init : Cfg L 256)
    (hc : 2 ≤ init.card) (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ)
    (hst : s ≤ t) (hℓ : 1 ≤ ℓ) (hcap : ℓ + 1 ≤ 256 * (L + 1)) :
    ∀ᵐ ω ∂law init, CurrentMarkedGuard init C ℓ cutoff s t ω →
      ((law init)[nextSafeNormalIndicator init C ℓ cutoff s t | pairLogFiltration L 256 t]) ω ≤
        ((frontCount (virtualLabels init ω t) ℓ : ℝ) ^ 2 +
          2 * (C.card : ℝ) *
            (normalCount (virtualLabels init ω t) (markedAt init C ℓ cutoff s ω t) ℓ : ℝ)) /
          ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
  have hsafe : Integrable (nextSafeNormalIndicator init C ℓ cutoff s t) (law init) :=
    PhaseThreeScalar.bernoulli_integrable
      (nextSafeNormalIndicator_stronglyMeasurable init C ℓ cutoff s)
      (fun k => ae_of_all _ (nextSafeNormalIndicator_zero_one init C ℓ cutoff s k)) t
  have hcand : Integrable (normalRiseIndicator init C ℓ cutoff s t) (law init) :=
    PhaseThreeScalar.bernoulli_integrable
      (normalRiseIndicator_stronglyMeasurable init C ℓ cutoff s)
      (fun k => ae_of_all _ (normalRiseIndicator_zero_one init C ℓ cutoff s k)) t
  have hmono := condExp_mono (m := pairLogFiltration L 256 t) hsafe hcand
    (ae_of_all _ (nextSafeNormalIndicator_le_candidate init C ℓ cutoff s t hst hℓ hcap))
  filter_upwards [hmono, normalRiseIndicator_conditional_upper init hc C ℓ cutoff s t]
    with ω hle hupper
  intro hguard
  have hcount : clockCount (virtualLabels init ω t) = C.card := by
    change (clockSet (virtualLabels init ω t)).card = C.card
    rw [← hguard.2.1]
  exact hle.trans (by simpa only [hcount] using hupper hguard.2.2)

variable {n : ℕ}

theorem currentMarkedGuard_of_seedPrefix (init : InputCfg n) (ω : InputLog n)
    (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hst : s ≤ t) (hℓ : 1 ≤ ℓ)
    (hmask : C = clockSet (labelsAt init ω s))
    (hcap : ∀ k, (virtualLabels init ω t k).phase.val ≤ 3) :
    CurrentMarkedGuard init C ℓ cutoff s t ω := by
  refine ⟨⟨?_, virtual_carrier_from_seedPrefix init ω s hseed t hst⟩, ?_, ?_⟩
  · intro k
    exact ⟨virtual_phase_floor_from_seedPrefix init ω s t hseed hst k, hcap k⟩
  · exact hmask.trans
      (virtual_clockSet_eq_seed_of_current_phase_cap init ω s t hseed hst hcap).symm
  · exact markedAt_subset_above_of_seedPrefix init ω C ℓ cutoff s t hseed hst hℓ hmask hcap

theorem nextSafeNormalIndicator_conditional_upper_from_seed (init : InputCfg n)
    (hc : 2 ≤ init.card) (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ)
    (hst : s ≤ t) (hℓ : 1 ≤ ℓ)
    (hlevel : ℓ + 1 ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    ∀ᵐ ω ∂law init, ω ∈ seedPrefix init s →
      C = clockSet (labelsAt init ω s) →
      (∀ k, (virtualLabels init ω t k).phase.val ≤ 3) →
      ((law init)[nextSafeNormalIndicator init C ℓ cutoff s t | pairLogFiltration _ _ t]) ω ≤
        ((frontCount (virtualLabels init ω t) ℓ : ℝ) ^ 2 +
          2 * (C.card : ℝ) *
            (normalCount (virtualLabels init ω t) (markedAt init C ℓ cutoff s ω t) ℓ : ℝ)) /
          ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
  filter_upwards [nextSafeNormalIndicator_conditional_upper init hc C ℓ cutoff s t
    hst hℓ hlevel] with ω hω
  intro hseed hmask hcap
  exact hω (currentMarkedGuard_of_seedPrefix init ω C ℓ cutoff s t hseed hst hℓ hmask hcap)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockNormalRiseStoppedLaw

end
