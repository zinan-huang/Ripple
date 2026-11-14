import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoDispatch
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoPersistence

/-!
# Two observed dispatch blocks

The existing outcome work has an inverse-square bound. On its failure,
a reachable successor of a pure Phase-2 configuration is again pure
Phase 2 with the same provenance. Consequently two blocks cost an
inverse-fourth probability, without conditioning on the future success
of either block and without a union over the dispatcher branches.

The historical conclusion is stable completion or a phase-at-least-three
seed. An exact Phase-3 seed profile still requires the absence of backup
at that genuine first crossing.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseTwoDispatchAmplification

open TimeTheorem PairLog PhaseOneDrain PhaseTwoDispatch

variable {L K : ℕ}

theorem provenance_of_not_target_reachable
    (init c c' : Cfg L K) (n : ℕ)
    (h : Phase2EntryDispatcher.PurePhase2Provenance init n c)
    (hreach : (NonuniformMajority L K).Reachable c c')
    (hnot : ¬ Phase2OutcomeWork.Target init n c') :
    Phase2EntryDispatcher.PurePhase2Provenance init n c' := by
  rcases PhaseTwoPersistence.pure_or_threshold_seed_reachable
    init c c' n h hreach with hpure | hseed
  · exact hpure
  · exfalso
    apply hnot
    right
    refine ⟨⟨(Protocol.reachable_card_eq hreach).trans h.card_eq, ?_⟩, ?_⟩
    · exact PhaseOneDrainStopping.phase_lower_reachable 2 c c' hreach
        (fun a ha => (h.phase_eq a ha).symm.le)
    · change 1 ≤ c'.countP (fun a => 3 ≤ a.phase.val)
      exact Multiset.countP_pos.mpr hseed

def dispatchHorizon (init : Cfg L K) (n : ℕ) (hn : 2 ≤ n) : ℕ :=
  2 * Phase2OutcomeWork.commonHorizon init n hn

def ObservedOutcome (init c : Cfg L K) : Prop :=
  c ∈ StableDone L K init ∨ ∃ a ∈ c, 3 ≤ a.phase.val

theorem target_implies_observed (init c : Cfg L K) (n : ℕ)
    (h : Phase2OutcomeWork.Target init n c) : ObservedOutcome init c := by
  rcases h with hdone | hadv
  · exact Or.inl hdone
  · right
    have hcount : 1 ≤ c.countP (fun a => 3 ≤ a.phase.val) := hadv.2
    exact Multiset.countP_pos.mp hcount

theorem double_dispatch_from_prefix
    (init : Cfg L K) (n : ℕ) (hn : 2 ≤ n)
    (s : ℕ) (A : Set ((k : Finset.Iic s) → Draw L K))
    (hA : ∀ p ∈ A,
      Phase2EntryDispatcher.PurePhase2Provenance init n (prefixCfg init s p)) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        ¬ Phase2OutcomeWork.Target init n
          (trace init ω (s + Phase2OutcomeWork.commonHorizon init n hn)) ∧
        ¬ Phase2OutcomeWork.Target init n
          (trace init ω (s + dispatchHorizon init n hn))} ≤
      (1 / (n : ℝ≥0∞) ^ 4) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
  let H := Phase2OutcomeWork.commonHorizon init n hn
  let t := s + H
  have hst : s ≤ t := Nat.le_add_right s H
  have hfinal : t + H = s + dispatchHorizon init n hn := by
    dsimp [t, dispatchHorizon, H]
    omega
  let B : Set ((k : Finset.Iic t) → Draw L K) :=
    {p | TraceDrain.restrictPrefix hst p ∈ A ∧
      Phase2EntryDispatcher.PurePhase2Provenance init n (prefixCfg init t p) ∧
      ¬ Phase2OutcomeWork.Target init n (prefixCfg init t p)}
  let q : ℝ≥0∞ := 1 / (n : ℝ≥0∞) ^ 2
  let PA := law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A}
  have hfirst :
      law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        ¬ Phase2OutcomeWork.Target init n (trace init ω t)} ≤ q * PA :=
    pure_dispatch_from_prefix init n hn s A hA
  have hBmass :
      law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) t ω ∈ B} ≤
        q * PA := by
    refine (measure_mono ?_).trans hfirst
    intro ω hω
    exact ⟨hω.1, hω.2.2⟩
  have hsecond :
      law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) t ω ∈ B ∧
        ¬ Phase2OutcomeWork.Target init n (trace init ω (t + H))} ≤
      q * law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) t ω ∈ B} :=
    pure_dispatch_from_prefix init n hn t B (fun p hp => hp.2.1)
  have hsub :
      {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        ¬ Phase2OutcomeWork.Target init n (trace init ω (s + H)) ∧
        ¬ Phase2OutcomeWork.Target init n
          (trace init ω (s + dispatchHorizon init n hn))} ⊆
      {ω | frestrictLe (π := fun _ : ℕ => Draw L K) t ω ∈ B ∧
        ¬ Phase2OutcomeWork.Target init n (trace init ω (t + H))} := by
    rintro ω ⟨hp, hmid, hend⟩
    have hprov := provenance_of_not_target_reachable init
      (trace init ω s) (trace init ω t) n (hA _ hp)
      (TimeTheorem.trace_reachable init ω hst) hmid
    refine ⟨⟨hp, hprov, hmid⟩, ?_⟩
    simpa only [hfinal] using hend
  have hq : q * q = 1 / (n : ℝ≥0∞) ^ 4 := by
    dsimp [q]
    simp only [one_div, ENNReal.inv_pow]
    ring
  calc
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        ¬ Phase2OutcomeWork.Target init n
          (trace init ω (s + Phase2OutcomeWork.commonHorizon init n hn)) ∧
        ¬ Phase2OutcomeWork.Target init n
          (trace init ω (s + dispatchHorizon init n hn))} ≤
      law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) t ω ∈ B ∧
        ¬ Phase2OutcomeWork.Target init n (trace init ω (t + H))} :=
      measure_mono hsub
    _ ≤ q * law init
        {ω | frestrictLe (π := fun _ : ℕ => Draw L K) t ω ∈ B} := hsecond
    _ ≤ q * (q * PA) := mul_le_mul_left' hBmass _
    _ = (1 / (n : ℝ≥0∞) ^ 4) * PA := by rw [← mul_assoc, hq]

/-- The conditioning event is precisely the prefix set A. The no-hit clause
is the bad event whose probability is bounded. -/
theorem pure_no_outcome_tail_from_prefix
    (init : Cfg L K) (n : ℕ) (hn : 2 ≤ n)
    (s : ℕ) (A : Set ((k : Finset.Iic s) → Draw L K))
    (hA : ∀ p ∈ A,
      Phase2EntryDispatcher.PurePhase2Provenance init n (prefixCfg init s p)) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        ∀ k ≤ dispatchHorizon init n hn,
          ¬ ObservedOutcome init (trace init ω (s + k))} ≤
      (1 / (n : ℝ≥0∞) ^ 4) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
  refine (measure_mono ?_).trans (double_dispatch_from_prefix init n hn s A hA)
  rintro ω ⟨hp, hno⟩
  refine ⟨hp, ?_, ?_⟩
  · intro htarget
    apply hno (Phase2OutcomeWork.commonHorizon init n hn)
      (by unfold dispatchHorizon; omega)
    exact target_implies_observed init _ n htarget
  · intro htarget
    exact hno (dispatchHorizon init n hn) le_rfl
      (target_implies_observed init _ n htarget)

def doubleDispatchFailure
    (init : Cfg L K) (n : ℕ) (hn : 2 ≤ n)
    (σ : Ω L K → WithTop ℕ) : Set (Ω L K) :=
  {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
    Phase2EntryDispatcher.PurePhase2Provenance init n (trace init ω s) ∧
    ¬ Phase2OutcomeWork.Target init n
      (trace init ω (s + Phase2OutcomeWork.commonHorizon init n hn)) ∧
    ¬ Phase2OutcomeWork.Target init n
      (trace init ω (s + dispatchHorizon init n hn))}

theorem doubleDispatchFailure_measurable
    (init : Cfg L K) (n : ℕ) (hn : 2 ≤ n)
    (σ : Ω L K → WithTop ℕ) (hσ : PairLogPastTime σ) :
    MeasurableSet (doubleDispatchFailure init n hn σ) := by
  have ht (s : ℕ) : MeasurableSet {ω | σ ω = (s : WithTop ℕ)} :=
    (pairLogFiltration L K).le s _ (hσ s)
  have hp (s : ℕ) : MeasurableSet
      {ω | Phase2EntryDispatcher.PurePhase2Provenance init n (trace init ω s)} :=
    (Set.to_countable
      {c : Cfg L K | Phase2EntryDispatcher.PurePhase2Provenance init n c}).measurableSet.preimage
        ((measurable_pi_apply s).comp (measurable_trace init))
  have hb (s : ℕ) : MeasurableSet
      {ω | ¬ Phase2OutcomeWork.Target init n (trace init ω s)} :=
    (Set.to_countable
      {c : Cfg L K | ¬ Phase2OutcomeWork.Target init n c}).measurableSet.preimage
        ((measurable_pi_apply s).comp (measurable_trace init))
  have heq : doubleDispatchFailure init n hn σ =
      ⋃ s : ℕ, {ω | σ ω = (s : WithTop ℕ)} ∩
        ({ω | Phase2EntryDispatcher.PurePhase2Provenance init n (trace init ω s)} ∩
          ({ω | ¬ Phase2OutcomeWork.Target init n
            (trace init ω (s + Phase2OutcomeWork.commonHorizon init n hn))} ∩
           {ω | ¬ Phase2OutcomeWork.Target init n
            (trace init ω (s + dispatchHorizon init n hn))})) := by
    ext ω
    simp only [doubleDispatchFailure, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
  rw [heq]
  exact MeasurableSet.iUnion fun s =>
    (ht s).inter ((hp s).inter ((hb _).inter (hb _)))

theorem double_dispatch_at_past_time
    (init : Cfg L K) (n : ℕ) (hn : 2 ≤ n)
    (σ : Ω L K → WithTop ℕ) (hσ : PairLogPastTime σ) :
    law init (doubleDispatchFailure init n hn σ) ≤
      1 / (n : ℝ≥0∞) ^ 4 := by
  refine genuine_seed_splice (law init) σ (doubleDispatchFailure init n hn σ)
    (1 / (n : ℝ≥0∞) ^ 4)
    (doubleDispatchFailure_measurable init n hn σ hσ)
    (fun s => (pairLogFiltration L K).le s _ (hσ s))
    (fun ω hω => ?_) (fun s => ?_)
  · obtain ⟨s, hs, -, -, -⟩ := hω
    rw [hs]
    exact WithTop.coe_ne_top
  · have hσs := hσ s
    rw [pairLogFiltration_eq_comap] at hσs
    obtain ⟨Aσ, -, hAσ⟩ := hσs
    let A : Set ((k : Finset.Iic s) → Draw L K) :=
      {p | p ∈ Aσ ∧
        Phase2EntryDispatcher.PurePhase2Provenance init n (prefixCfg init s p)}
    have hmem (ω : Ω L K) :
        frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ Aσ ↔
          σ ω = (s : WithTop ℕ) := by
      change ω ∈ (frestrictLe (π := fun _ : ℕ => Draw L K) s) ⁻¹' Aσ ↔
        ω ∈ {ω | σ ω = (s : WithTop ℕ)}
      rw [hAσ]
    have htail := double_dispatch_from_prefix init n hn s A (fun p hp => hp.2)
    calc
      law init (doubleDispatchFailure init n hn σ ∩ {ω | σ ω = (s : WithTop ℕ)}) ≤
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
          ¬ Phase2OutcomeWork.Target init n
            (trace init ω (s + Phase2OutcomeWork.commonHorizon init n hn)) ∧
          ¬ Phase2OutcomeWork.Target init n
            (trace init ω (s + dispatchHorizon init n hn))} := by
        apply measure_mono
        rintro ω ⟨⟨r, hr, hp, hm, he⟩, hs⟩
        have hrs : r = s := WithTop.coe_injective (hr.symm.trans hs)
        subst r
        exact ⟨⟨(hmem ω).mpr hs, hp⟩, hm, he⟩
      _ ≤ (1 / (n : ℝ≥0∞) ^ 4) *
          law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := htail
      _ ≤ (1 / (n : ℝ≥0∞) ^ 4) *
          law init {ω | σ ω = (s : WithTop ℕ)} :=
        mul_le_mul_left' (measure_mono fun ω hω => (hmem ω).mp hω.1) _

theorem pure_no_outcome_tail_at_past_time
    (init : Cfg L K) (n : ℕ) (hn : 2 ≤ n)
    (σ : Ω L K → WithTop ℕ) (hσ : PairLogPastTime σ) :
    law init {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
        Phase2EntryDispatcher.PurePhase2Provenance init n (trace init ω s) ∧
        ∀ k ≤ dispatchHorizon init n hn,
          ¬ ObservedOutcome init (trace init ω (s + k))} ≤
      1 / (n : ℝ≥0∞) ^ 4 := by
  refine (measure_mono ?_).trans (double_dispatch_at_past_time init n hn σ hσ)
  rintro ω ⟨s, hs, hp, hno⟩
  refine ⟨s, hs, hp, ?_, ?_⟩
  · intro ht
    apply hno (Phase2OutcomeWork.commonHorizon init n hn)
      (by unfold dispatchHorizon; omega)
    exact target_implies_observed init _ n ht
  · intro ht
    exact hno (dispatchHorizon init n hn) le_rfl
      (target_implies_observed init _ n ht)

theorem dispatchHorizon_le_thirty_eight
    (init : Cfg L K) (n L' : ℕ) (hn : 2 ≤ n)
    (hlogp1 : Real.log (n : ℝ) + 1 ≤ (L' + 1 : ℝ))
    (hnL : n ≤ 2 ^ L') :
    dispatchHorizon init n hn ≤ 38 * n * (L' + 1) := by
  have h := Phase2OutcomeWork.commonHorizon_le_nineteen
    init n L' hn hlogp1 hnL
  unfold dispatchHorizon
  nlinarith [h]

end Ripple.PopulationProtocol.ExactMajority.PhaseTwoDispatchAmplification

end
