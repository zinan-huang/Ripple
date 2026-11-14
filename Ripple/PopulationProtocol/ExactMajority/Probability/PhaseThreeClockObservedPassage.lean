-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockObservedPassage.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockReciprocalPassage

/-!
# Calibrated passage from an observed positive front

The measurable event EnvironmentSpan records the virtual clock environment
through the end of a finite observed interval. On that event, physical Clock
roles are fixed and every positive front is nondecreasing.

Consequently, if an observed positive front has not reached its bulk target
at the endpoint, the concrete PassageWindow has survived throughout. The
calibrated killed tail therefore bounds this actual target-passage failure.
AsyncEntry supplies EnvironmentSpan pathwise; it is never used as a future
conditioning event in the probability proof.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockObservedPassage

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne
  PhaseThreeClockEmbeddingBridge PhaseThreeClockStoppedPassage
  PhaseThreeClockReciprocalAlgebra PhaseThreeClockReciprocalPassage

variable {L : ℕ}

def EnvironmentSpan (init : Cfg L 256) (s N : ℕ) (ω : Ω L 256) : Prop :=
  ∀ t ≤ N, ClockEnvironment (virtualLabels init ω (s + t))

def observedPassageFailure (init : Cfg L 256) (ℓ C s N : ℕ) : Set (Ω L 256) :=
  {ω | EnvironmentSpan init s N ω ∧
    frontCount (virtualLabels init ω (s + N)) ℓ < StageEventSpec.bulkThreshold C}

theorem environmentSpan_measurable (init : Cfg L 256) (s N : ℕ) :
    MeasurableSet[pairLogFiltration L 256 (s + N)]
      {ω | EnvironmentSpan init s N ω} := by
  have heq : {ω | EnvironmentSpan init s N ω} =
      ⋂ t : ℕ, {ω | t ≤ N →
        ClockEnvironment (virtualLabels init ω (s + t))} := by
    ext ω
    simp only [EnvironmentSpan, Set.mem_setOf_eq, Set.mem_iInter]
  rw [heq]
  refine MeasurableSet.iInter fun t => ?_
  by_cases ht : t ≤ N
  · have hstate : MeasurableSet[pairLogFiltration L 256 (s + t)]
        {ω | ClockEnvironment (virtualLabels init ω (s + t))} :=
      (show MeasurableSet {f : Fin init.card → AgentState L 256 |
          ClockEnvironment f} from
        (Set.to_countable _).measurableSet).preimage
          (measurable_virtualLabels init (s + t))
    have hlift : MeasurableSet[pairLogFiltration L 256 (s + N)]
        {ω | ClockEnvironment (virtualLabels init ω (s + t))} :=
      ((pairLogFiltration L 256).mono (by omega : s + t ≤ s + N)) _ hstate
    simpa only [ht, true_implies] using hlift
  · simp only [ht, false_implies, Set.setOf_true]
    exact MeasurableSet.univ

theorem observedPassageFailure_measurable (init : Cfg L 256) (ℓ C s N : ℕ) :
    MeasurableSet[pairLogFiltration L 256 (s + N)]
      (observedPassageFailure init ℓ C s N) := by
  have hfront : MeasurableSet[pairLogFiltration L 256 (s + N)]
      {ω | frontCount (virtualLabels init ω (s + N)) ℓ <
        StageEventSpec.bulkThreshold C} :=
    (show MeasurableSet {f : Fin init.card → AgentState L 256 |
        frontCount f ℓ < StageEventSpec.bulkThreshold C} from
      (Set.to_countable _).measurableSet).preimage
        (measurable_virtualLabels init (s + N))
  exact (environmentSpan_measurable init s N).inter hfront

theorem clockCount_step_of_environment (init : Cfg L 256) (ω : Ω L 256) (t : ℕ)
    (hcur : ClockEnvironment (virtualLabels init ω t))
    (hnext : ClockEnvironment (virtualLabels init ω (t + 1))) :
    clockCount (virtualLabels init ω (t + 1)) =
      clockCount (virtualLabels init ω t) := by
  have hroles := virtualLabels_roles_step_of_phase_range init ω t
    hcur.phase_range (fun k => (hnext.phase_range k).2)
  simp only [clockCount, clockSet, hroles]

theorem frontCount_step_mono_of_environment (init : Cfg L 256) (ω : Ω L 256)
    (t ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ 256 * (L + 1))
    (hcur : ClockEnvironment (virtualLabels init ω t))
    (hnext : ClockEnvironment (virtualLabels init ω (t + 1))) :
    frontCount (virtualLabels init ω t) ℓ ≤
      frontCount (virtualLabels init ω (t + 1)) ℓ := by
  classical
  cases hd : drawLabels init ω (t + 1) with
  | none =>
      exact (frontCount_virtualLabels_succ_of_none init ω t hd ℓ).ge
  | some ij =>
      rcases ij with ⟨i, j⟩
      have hstep := frontCount_virtualLabels_succ_of_phase_range init ω t i j hd
        hcur.phase_range
        (fun k hk => hcur.carrier k (Or.inr (Or.inr hk)))
        (fun k => (hnext.phase_range k).2) ℓ hℓ hcap
      rw [hstep]
      exact Nat.le_add_right _ _

theorem clockCount_eq_of_environmentSpan (init : Cfg L 256)
    (ω : Ω L 256) (s N : ℕ) (hspan : EnvironmentSpan init s N ω) :
    ∀ t ≤ N, clockCount (virtualLabels init ω (s + t)) =
      clockCount (virtualLabels init ω s) := by
  intro t
  induction t with
  | zero =>
      intro ht
      simp only [Nat.add_zero]
  | succ t ih =>
      intro ht
      have hstep := clockCount_step_of_environment init ω (s + t)
        (hspan t (by omega))
        (by simpa only [Nat.add_assoc] using hspan (t + 1) ht)
      calc
        clockCount (virtualLabels init ω (s + (t + 1))) =
            clockCount (virtualLabels init ω (s + t)) := by
          simpa only [Nat.add_assoc] using hstep
        _ = clockCount (virtualLabels init ω s) := ih (by omega)

theorem frontCount_mono_of_environmentSpan (init : Cfg L 256)
    (ω : Ω L 256) (s N ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (hcap : ℓ ≤ 256 * (L + 1)) (hspan : EnvironmentSpan init s N ω)
    (u v : ℕ) (huv : u ≤ v) (hvN : v ≤ N) :
    frontCount (virtualLabels init ω (s + u)) ℓ ≤
      frontCount (virtualLabels init ω (s + v)) ℓ := by
  revert hvN
  induction v, huv using Nat.le_induction with
  | base =>
      intro hvN
      exact le_rfl
  | succ v huv ih =>
      intro hvN
      have hstep := frontCount_step_mono_of_environment init ω (s + v) ℓ hℓ hcap
        (hspan v (by omega))
        (by simpa only [Nat.add_assoc] using hspan (v + 1) hvN)
      exact (ih (by omega)).trans (by simpa only [Nat.add_assoc] using hstep)

/-- On the environment event, endpoint failure to reach the bulk threshold
forces every explicit guard of PassageWindow to have survived. -/
theorem below_bulk_implies_survival (init : Cfg L 256) (ω : Ω L 256)
    (ℓ C s N : ℕ) (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ 256 * (L + 1))
    (hspan : EnvironmentSpan init s N ω)
    (hdensity : 6 * init.card ≤ 25 * C)
    (hcount : clockCount (virtualLabels init ω s) = C)
    (hpositive : 1 ≤ frontCount (virtualLabels init ω s) ℓ)
    (hbelow : frontCount (virtualLabels init ω (s + N)) ℓ <
      StageEventSpec.bulkThreshold C) :
    (N : WithTop ℕ) < passageStop init ℓ (StageEventSpec.bulkThreshold C) s ω := by
  apply lt_of_not_ge
  intro hstop
  obtain ⟨u, hu, hfail⟩ :=
    (passageStop_le_iff init ℓ (StageEventSpec.bulkThreshold C) s N ω).mp hstop
  apply hfail
  have hCu : clockCount (virtualLabels init ω (s + u)) = C :=
    (clockCount_eq_of_environmentSpan init ω s N hspan u hu).trans hcount
  have hlow : frontCount (virtualLabels init ω s) ℓ ≤
      frontCount (virtualLabels init ω (s + u)) ℓ := by
    simpa only [Nat.add_zero] using
      frontCount_mono_of_environmentSpan init ω s N ℓ hℓ hcap hspan
        0 u (Nat.zero_le u) hu
  have hupper : frontCount (virtualLabels init ω (s + u)) ℓ <
      StageEventSpec.bulkThreshold C :=
    (frontCount_mono_of_environmentSpan init ω s N ℓ hℓ hcap hspan
      u N hu le_rfl).trans_lt hbelow
  refine ⟨(hspan u hu).phase_range, ?_, ?_, hpositive.trans hlow, hupper, ?_⟩
  · intro k hk
    exact (hspan u hu).carrier k (Or.inr (Or.inr hk))
  · rw [hCu]
    exact hdensity
  · rw [hCu]
    exact below_bulk_is_sparse _ C hupper

/-- The observed endpoint failure has a calibrated original-law tail.
The prefix contains its initial positivity and Clock-count facts. -/
theorem observed_bulk_passage_prefix_tail (init : Cfg L 256)
    (hm : 20 ≤ init.card) (C ℓ s : ℕ)
    (hC : C ≤ init.card) (hdensity : 6 * init.card ≤ 25 * C)
    (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ 256 * (L + 1))
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 s] E)
    (hstart : ∀ ω ∈ E,
      1 ≤ frontCount (virtualLabels init ω s) ℓ ∧
        clockCount (virtualLabels init ω s) = C) :
    law init
        (E ∩ observedPassageFailure init ℓ C s
          (PhaseThreeModel.Numeric.firstHitHorizon init.card)) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 9) * law init E := by
  apply (measure_mono ?_).trans
    (bulk_passage_prefix_tail init hm C ℓ s hC hℓ hcap E hE)
  rintro ω ⟨he, hspan, hbelow⟩
  exact ⟨he, below_bulk_implies_survival init ω ℓ C s _
    hℓ hcap hspan hdensity (hstart ω he).2 (hstart ω he).1 hbelow⟩

theorem observed_bulk_passage_prefix_measurable (init : Cfg L 256)
    (C ℓ s : ℕ) (E : Set (Ω L 256))
    (hE : MeasurableSet[pairLogFiltration L 256 s] E) :
    MeasurableSet[pairLogFiltration L 256
        (s + PhaseThreeModel.Numeric.firstHitHorizon init.card)]
      (E ∩ observedPassageFailure init ℓ C s
        (PhaseThreeModel.Numeric.firstHitHorizon init.card)) := by
  have hEend : MeasurableSet[pairLogFiltration L 256
      (s + PhaseThreeModel.Numeric.firstHitHorizon init.card)] E :=
    ((pairLogFiltration L 256).mono (by omega :
      s ≤ s + PhaseThreeModel.Numeric.firstHitHorizon init.card)) _ hE
  exact hEend.inter (observedPassageFailure_measurable init ℓ C s _)


/-- On an all-time environment path, never reaching the bulk target keeps
the concrete window alive forever. This is a pathwise implication, not a
conditioning assertion about the future environment. -/
theorem never_bulk_implies_infinite_stop (init : Cfg L 256) (ω : Ω L 256)
    (ℓ C s : ℕ) (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ 256 * (L + 1))
    (henv : ∀ t, ClockEnvironment (virtualLabels init ω (s + t)))
    (hdensity : 6 * init.card ≤ 25 * C)
    (hcount : clockCount (virtualLabels init ω s) = C)
    (hpositive : 1 ≤ frontCount (virtualLabels init ω s) ℓ)
    (hbelow : ∀ t, frontCount (virtualLabels init ω (s + t)) ℓ <
      StageEventSpec.bulkThreshold C) :
    passageStop init ℓ (StageEventSpec.bulkThreshold C) s ω = ⊤ := by
  by_contra htop
  obtain ⟨N, hN⟩ := WithTop.ne_top_iff_exists.mp htop
  have hsur := below_bulk_implies_survival init ω ℓ C s N hℓ hcap
    (fun t _ => henv t) hdensity hcount hpositive (hbelow N)
  have hcontra : (N : WithTop ℕ) < (N : WithTop ℕ) := by
    simpa only [← hN] using hsur
  exact (lt_irrefl _) hcontra

/-- A genuinely positive observed front reaches its bulk target in finite
time almost surely on the intersection with the all-time environment.
No measurability of that future intersection is assumed. -/
theorem observed_bulk_never_hit_null (init : Cfg L 256)
    (hc : 2 ≤ init.card) (C ℓ s : ℕ)
    (hdensity : 6 * init.card ≤ 25 * C)
    (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ 256 * (L + 1))
    (E : Set (Ω L 256))
    (hstart : ∀ ω ∈ E,
      1 ≤ frontCount (virtualLabels init ω s) ℓ ∧
        clockCount (virtualLabels init ω s) = C) :
    law init (E ∩ {ω |
      (∀ t, ClockEnvironment (virtualLabels init ω (s + t))) ∧
        ¬ ∃ t, StageEventSpec.bulkThreshold C ≤
          frontCount (virtualLabels init ω (s + t)) ℓ}) = 0 := by
  apply le_antisymm ?_ zero_le
  calc
    law init (E ∩ {ω |
      (∀ t, ClockEnvironment (virtualLabels init ω (s + t))) ∧
        ¬ ∃ t, StageEventSpec.bulkThreshold C ≤
          frontCount (virtualLabels init ω (s + t)) ℓ}) ≤
        law init {ω |
          passageStop init ℓ (StageEventSpec.bulkThreshold C) s ω = ⊤} := by
      apply measure_mono
      rintro ω ⟨he, henv, hnever⟩
      exact never_bulk_implies_infinite_stop init ω ℓ C s hℓ hcap henv hdensity
        (hstart ω he).2 (hstart ω he).1
        (fun t => lt_of_not_ge (fun hhit => hnever ⟨t, hhit⟩))
    _ = 0 := passageStop_eq_top_null init hc ℓ (StageEventSpec.bulkThreshold C) s hℓ hcap

/-- The existing entry history supplies the environment pathwise.
No measurability of a future AsyncEntry event is asserted or used. -/
theorem environmentSpan_of_asyncEntry {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (S T s N : ℕ)
    (hentry : StageEventSpec.AsyncEntry init ω S T) (hSs : S ≤ s) :
    EnvironmentSpan init s N ω := by
  intro t ht
  exact virtualLabels_clockEnvironment_of_asyncEntry init ω S T hentry (s + t) (by omega)

theorem asyncEntry_below_bulk_subset {n : ℕ} (init : InputCfg n)
    (S s N ℓ C : ℕ) (hSs : S ≤ s) :
    {ω | (∃ T, StageEventSpec.AsyncEntry init ω S T) ∧
      frontCount (virtualLabels init ω (s + N)) ℓ < StageEventSpec.bulkThreshold C} ⊆
        observedPassageFailure init ℓ C s N := by
  rintro ω ⟨⟨T, hentry⟩, hbelow⟩
  exact ⟨environmentSpan_of_asyncEntry init ω S T s N hentry hSs, hbelow⟩

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockObservedPassage

end
