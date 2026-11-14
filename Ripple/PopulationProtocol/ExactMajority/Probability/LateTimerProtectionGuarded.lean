-- Ripple/PopulationProtocol/ExactMajority/Probability/LateTimerProtectionGuarded.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateTimerProtectionOriginalLaw
import Ripple.PopulationProtocol.ExactMajority.Probability.LateF6OriginalLaw

/-!
# Guarded form of the late-timer protection

The unguarded route (all logs from `init`, deleted from `LateTimerProtectionOriginalLaw`) was false: the first phase-`p+1` agent need not come
from a Clock timer.  If some agent of the valid initial configuration is still an
unassigned `mcr` at phase `0` when the first phase-`p` agent exists, the next
interaction between them drags it through `phaseInit 1`, which errors it (and the
partner) to phase `10`.  That is an agent at phase `>= p+1` one step after the seed
with no timer participation.

This file states the route and the failure set only on logs where every agent is at
phase `>= 3` by the seed time (`allThreeStart < s`).  On that part of the log space
the configuration is reachable, has phases in `[3, 9]`, hence is `Wf`
(`LateMixedFiveSixReachableWf`), and the Phase-10 error track is closed.  The
complementary event `seed_p <= allThreeStart` is charged separately.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal NNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateTimerProtectionGuarded

open TimeTheorem PairLog PhaseOneDrain PhaseOneDrainStopping
open StageEventSpec LateF6OriginalLaw
open LateTimerPrefixScalar LateTimerProtectionOriginalLaw

variable {n : ℕ}

/-- Early next seed on logs whose first phase-`p` seed happens after all agents
reached phase `3`. -/
def timerProtectionFailureGuarded
    (init : InputCfg n) (p : ℕ) : Set (InputLog n) :=
  {omega | ∃ s : ℕ,
    phaseSeedTime init p omega = (s : WithTop ℕ) ∧
      allThreeStart init omega < (s : WithTop ℕ) ∧
      phaseSeedTime init (p + 1) omega ≤
        ((s + protectionHorizon n : ℕ) : WithTop ℕ)}

/-- The phase-`p` seed occurs while some agent is still below phase `3`. -/
def earlySeedBeforeAllThree
    (init : InputCfg n) (p : ℕ) : Set (InputLog n) :=
  {omega | ∃ s : ℕ,
    phaseSeedTime init p omega = (s : WithTop ℕ) ∧
      allThreeStart init omega ≥ (s : WithTop ℕ)}

/-- The corrected deterministic route: only logs on which all agents are at
phase `>= 3` at the seed time are asked to produce a fast label.  The statement
quantifies over fewer logs than the (false) all-logs route; the excluded logs are exactly
those on which the Phase-10 error track can create the next seed by a
Phase-0/1 laggard. -/
structure LateCounterRouteGuarded (init : InputCfg n) (p : ℕ) : Prop where
  route :
    ∀ (omega : InputLog n) (s : ℕ),
      phaseSeedTime init p omega = (s : WithTop ℕ) →
      allThreeStart init omega < (s : WithTop ℕ) →
      phaseSeedTime init (p + 1) omega ≤
        ((s + protectionHorizon n : ℕ) : WithTop ℕ) →
      ∃ i : Fin init.card, omega ∈ labelFastEvent init i s

/-- Every early next seed is in the guarded failure set or in the early-seed
event. -/
theorem timerProtectionFailure_subset_guarded_union
    (init : InputCfg n) (p : ℕ) :
    timerProtectionFailure init p ⊆
      timerProtectionFailureGuarded init p ∪ earlySeedBeforeAllThree init p := by
  rintro omega ⟨s, hs, hnext⟩
  by_cases hguard : allThreeStart init omega < (s : WithTop ℕ)
  · exact Or.inl ⟨s, hs, hguard, hnext⟩
  · exact Or.inr ⟨s, hs, not_lt.mp hguard⟩

/-- Seed-fibre tail for the guarded failure set. -/
theorem timerProtectionFailureGuarded_seedFibre_tail
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (p : ℕ) (hroute : LateCounterRouteGuarded init p) (s : ℕ) :
    law init
        (timerProtectionFailureGuarded init p ∩ phaseSeedFibre init p s) ≤
      timerProtectionBudget n * law init (phaseSeedFibre init p s) := by
  have hnpos : 0 < n := by
    have hlarge :=
      (TimeTheorem.time_population_bounds hinput.1).2
    omega
  have hcover :
      timerProtectionFailureGuarded init p ∩ phaseSeedFibre init p s ⊆
        ⋃ i : Fin init.card,
          phaseSeedFibre init p s ∩ labelFastEvent init i s := by
    rintro omega ⟨hbad, hfibre⟩
    change phaseSeedTime init p omega = (s : WithTop ℕ) at hfibre
    rcases hbad with ⟨r, hr, hguard, hnext⟩
    have hrs : r = s :=
      WithTop.coe_injective (hr.symm.trans hfibre)
    subst r
    rcases hroute.route omega s hfibre hguard hnext with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hfibre, hi⟩
  calc
    law init
        (timerProtectionFailureGuarded init p ∩ phaseSeedFibre init p s) ≤
      law init
        (⋃ i : Fin init.card,
          phaseSeedFibre init p s ∩ labelFastEvent init i s) :=
      measure_mono hcover
    _ ≤ ∑' i : Fin init.card,
        law init (phaseSeedFibre init p s ∩ labelFastEvent init i s) :=
      measure_iUnion_le _
    _ ≤ ∑' _i : Fin init.card,
        perLabelTimerBudget n * law init (phaseSeedFibre init p s) :=
      ENNReal.tsum_le_tsum fun i =>
        labelFastEvent_seedFibre_tail init hinput p s i
    _ = (init.card : ℝ≥0∞) *
        (perLabelTimerBudget n * law init (phaseSeedFibre init p s)) := by
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    _ = ((n : ℝ≥0∞) * perLabelTimerBudget n) *
        law init (phaseSeedFibre init p s) := by
      rw [hinput.2.2]
      ring
    _ = timerProtectionBudget n *
        law init (phaseSeedFibre init p s) := by
      rw [population_mul_perLabelTimerBudget hnpos]

/-- Original-law `n^(-2.06)` bound on the guarded failure set. -/
theorem law_timerProtectionFailureGuarded_tail
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (p : ℕ) (_hp : LateTimedPhase p)
    (hroute : LateCounterRouteGuarded init p) :
    law init (timerProtectionFailureGuarded init p) ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-(103 / 50 : ℝ))) := by
  have htail :=
    PhaseThreeClockProducer.splice_of_local
      (law init) (phaseSeedTime init p)
      (timerProtectionFailureGuarded init p) (timerProtectionBudget n)
      (fun s =>
        (PairLog.pairLogFiltration
          (PhaseThreeModel.Numeric.hourIndex n) 256).le s _
            ((phaseSeedTime_past init p) s))
      (by
        intro omega hbad
        rcases hbad with ⟨s, hs, _⟩
        rw [hs]
        exact WithTop.coe_ne_top)
      (fun s =>
        timerProtectionFailureGuarded_seedFibre_tail
          init hinput p hroute s)
  simpa [timerProtectionBudget] using htail

/-- The unguarded failure is charged by the guarded tail plus the separate
early-seed event. -/
theorem law_timerProtectionFailure_le_guarded_add_early
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (p : ℕ) (hp : LateTimedPhase p)
    (hroute : LateCounterRouteGuarded init p) :
    law init (timerProtectionFailure init p) ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-(103 / 50 : ℝ))) +
        law init (earlySeedBeforeAllThree init p) :=
  ((measure_mono (timerProtectionFailure_subset_guarded_union init p)).trans
    (measure_union_le _ _)).trans
      (add_le_add (law_timerProtectionFailureGuarded_tail init hinput p hp hroute) le_rfl)

end Ripple.PopulationProtocol.ExactMajority.LateTimerProtectionGuarded

end
