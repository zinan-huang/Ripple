import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoThresholds
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoProvenance
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase2OutcomeWork

/-!
# Actual-law dispatch from an observed pure Phase-2 boundary

The producer uses the pinned outcome work, including output cleanup in the
A/B/T branches. Its target is stable completion or a phase above two.
The inverse-square budget below is the budget of that existing work; it
does not assert the sharper PHASE02 dispatcher budget or AsyncEntry.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseTwoDispatch

open TimeTheorem PairLog PhaseOneDrain PhaseTwoThresholds

variable {L K : ℕ}

theorem pure_dispatch_from_prefix
    (init : Cfg L K) (n : ℕ) (hn : 2 ≤ n)
    (s : ℕ) (A : Set ((k : Finset.Iic s) → Draw L K))
    (hA : ∀ p ∈ A,
      Phase2EntryDispatcher.PurePhase2Provenance init n (prefixCfg init s p)) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        ¬ Phase2OutcomeWork.Target init n
          (trace init ω (s + Phase2OutcomeWork.commonHorizon init n hn))} ≤
      (1 / (n : ℝ≥0∞) ^ 2) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
  apply recorded_prefix_endpoint_bound init s
    (Phase2OutcomeWork.commonHorizon init n hn) A
    {c | ¬ Phase2OutcomeWork.Target init n c} (1 / (n : ℝ≥0∞) ^ 2)
  intro p hp
  have hdispatch := Phase2EntryDispatcher.outcome_dispatch init n
    (prefixCfg init s p) (hA p hp)
  have htail := (Phase2OutcomeWork.outcomeWork init n hn).convergence
    (prefixCfg init s p) hdispatch
  exact htail.trans (Phase2OutcomeWork.outcomeWork_epsilon_le_inv_sq init n hn)

def pureDispatchFailure
    (init : Cfg L K) (n : ℕ) (hn : 2 ≤ n)
    (σ : Ω L K → WithTop ℕ) : Set (Ω L K) :=
  {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
    Phase2EntryDispatcher.PurePhase2Provenance init n (trace init ω s) ∧
    ¬ Phase2OutcomeWork.Target init n
      (trace init ω (s + Phase2OutcomeWork.commonHorizon init n hn))}

theorem pureDispatchFailure_measurable
    (init : Cfg L K) (n : ℕ) (hn : 2 ≤ n)
    (σ : Ω L K → WithTop ℕ) (hσ : PairLogPastTime σ) :
    MeasurableSet (pureDispatchFailure init n hn σ) := by
  have heq : pureDispatchFailure init n hn σ =
      ⋃ s : ℕ, {ω | σ ω = (s : WithTop ℕ)} ∩
        {ω | Phase2EntryDispatcher.PurePhase2Provenance init n (trace init ω s)} ∩
        {ω | ¬ Phase2OutcomeWork.Target init n
          (trace init ω (s + Phase2OutcomeWork.commonHorizon init n hn))} := by
    ext ω
    simp only [pureDispatchFailure, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨s, hs, hp, hb⟩
      exact ⟨s, ⟨⟨hs, hp⟩, hb⟩⟩
    · rintro ⟨s, ⟨⟨hs, hp⟩, hb⟩⟩
      exact ⟨s, hs, hp, hb⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro s
  have ht : MeasurableSet {ω | σ ω = (s : WithTop ℕ)} :=
    (pairLogFiltration L K).le s _ (hσ s)
  have hp : MeasurableSet
      {ω | Phase2EntryDispatcher.PurePhase2Provenance init n (trace init ω s)} :=
    (Set.to_countable
      {c : Cfg L K | Phase2EntryDispatcher.PurePhase2Provenance init n c}).measurableSet.preimage
        ((measurable_pi_apply s).comp (measurable_trace init))
  have hb : MeasurableSet {ω | ¬ Phase2OutcomeWork.Target init n
      (trace init ω (s + Phase2OutcomeWork.commonHorizon init n hn))} :=
    (Set.to_countable {c : Cfg L K | ¬ Phase2OutcomeWork.Target init n c}).measurableSet.preimage
      ((measurable_pi_apply (s + Phase2OutcomeWork.commonHorizon init n hn)).comp
        (measurable_trace init))
  exact (ht.inter hp).inter hb

theorem pure_dispatch_at_past_time
    (init : Cfg L K) (n : ℕ) (hn : 2 ≤ n)
    (σ : Ω L K → WithTop ℕ) (hσ : PairLogPastTime σ) :
    law init (pureDispatchFailure init n hn σ) ≤ 1 / (n : ℝ≥0∞) ^ 2 := by
  refine genuine_seed_splice (law init) σ
    (pureDispatchFailure init n hn σ) (1 / (n : ℝ≥0∞) ^ 2)
    (pureDispatchFailure_measurable init n hn σ hσ)
    (fun s => (pairLogFiltration L K).le s _ (hσ s)) ?_ ?_
  · rintro ω ⟨s, hs, _⟩
    rw [hs]
    exact WithTop.coe_ne_top
  · intro s
    have hσs := hσ s
    rw [pairLogFiltration_eq_comap] at hσs
    obtain ⟨Aσ, _, hAσ⟩ := hσs
    let A : Set ((k : Finset.Iic s) → Draw L K) :=
      {p | p ∈ Aσ ∧
        Phase2EntryDispatcher.PurePhase2Provenance init n (prefixCfg init s p)}
    have hmem (ω : Ω L K) :
        frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ Aσ ↔
          σ ω = (s : WithTop ℕ) := by
      change ω ∈ (frestrictLe (π := fun _ : ℕ => Draw L K) s) ⁻¹' Aσ ↔
        ω ∈ {ω | σ ω = (s : WithTop ℕ)}
      rw [hAσ]
    calc
      law init (pureDispatchFailure init n hn σ ∩
          {ω | σ ω = (s : WithTop ℕ)}) ≤
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
          ¬ Phase2OutcomeWork.Target init n
            (trace init ω (s + Phase2OutcomeWork.commonHorizon init n hn))} := by
        apply measure_mono
        rintro ω ⟨⟨r, hr, hp, hb⟩, hs⟩
        have hrs : r = s := WithTop.coe_injective (hr.symm.trans hs)
        subst r
        exact ⟨⟨(hmem ω).mpr hs, hp⟩, hb⟩
      _ ≤ (1 / (n : ℝ≥0∞) ^ 2) *
          law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} :=
        pure_dispatch_from_prefix init n hn s A (fun p hp => hp.2)
      _ ≤ (1 / (n : ℝ≥0∞) ^ 2) *
          law init {ω | σ ω = (s : WithTop ℕ)} :=
        mul_le_mul_left' (measure_mono fun ω hω => (hmem ω).mp hω.1) _

/-- The provenance precondition above is obtained from a recorded mixed history,
rather than postulated as a sign-origin or initializer-image condition. -/
theorem pure_history_dispatch_at_past_time
    {n : ℕ} (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (hn : 2 ≤ n)
    (σ : InputLog n → WithTop ℕ) (hσ : PairLogPastTime σ) :
    law init {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
        (∃ u : ℕ, u ≤ s ∧
          (∀ a ∈ trace init ω u, a.phase.val = 1) ∧
          (∀ k, u ≤ k → k ≤ s → ∀ a ∈ trace init ω k,
            1 ≤ a.phase.val ∧ a.phase.val ≤ 2)) ∧
        (∀ a ∈ trace init ω s, a.phase.val = 2) ∧
        ¬ Phase2OutcomeWork.Target init n
          (trace init ω (s + Phase2OutcomeWork.commonHorizon init n hn))} ≤
      1 / (n : ℝ≥0∞) ^ 2 := by
  refine (measure_mono ?_).trans (pure_dispatch_at_past_time init n hn σ hσ)
  rintro ω ⟨s, hs, ⟨u, hus, hstart, hwindow⟩, hpure, hbad⟩
  have hreach : (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
      init (trace init ω s) := by
    simpa only [TraceDrain.trace_zero] using
      (trace_reachable init ω (s := 0) (t := s) (Nat.zero_le s))
  have hcard : (trace init ω s).card = n :=
    (Protocol.reachable_card_eq hreach).trans hinput.2.2
  exact ⟨s, hs,
    PhaseTwoProvenance.pure_phase_two_provenance_from_history init ω n u s
      hinput.2.1 hus hstart hwindow hcard hpure, hbad⟩

end Ripple.PopulationProtocol.ExactMajority.PhaseTwoDispatch

end
