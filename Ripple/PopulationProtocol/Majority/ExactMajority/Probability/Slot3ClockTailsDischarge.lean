import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot3ResidualsDischarge

/-!
# Slot-3 clock-tail providers

This file isolates the non-circular slot-3 clock-tail discharge surface.
The Ionescu-Tulcea trace law already has the correct finite-prefix marginals;
the remaining probabilistic input must be an actual `GoodClockUpTo` (or stronger)
bad-event bound under `ProtocolTraceLaw.μ`.
-/

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open Finset Preorder
open scoped ENNReal NNReal BigOperators Real

namespace ProtocolTraceLaw

variable {L K : ℕ}

/-- Public finite-prefix marginal of the protocol Ionescu-Tulcea trajectory law. -/
theorem map_frestrictLe_μ (entry : Config (AgentState L K)) (T : ℕ) :
    Measure.map
        (frestrictLe T : (Π n, St L K n) → (Π i : Finset.Iic T, St L K i))
        (μ (L := L) (K := K) entry) =
      Kernel.partialTraj (kfamily (L := L) (K := K)) 0 T
        ((fun _ => entry) : Π i : Finset.Iic 0, St L K i) := by
  unfold μ traj0
  rw [Kernel.traj_map_frestrictLe_apply]

/-- Cylinder-event form of `map_frestrictLe_μ`. -/
theorem cylinder_eq_partialTraj
    (entry : Config (AgentState L K)) (T : ℕ)
    (A : Set (Π i : Finset.Iic T, St L K i))
    (hA : MeasurableSet A) :
    μ (L := L) (K := K) entry
        {tr |
          (frestrictLe T : (Π n, St L K n) → (Π i : Finset.Iic T, St L K i)) tr ∈ A} =
      Kernel.partialTraj (kfamily (L := L) (K := K)) 0 T
        ((fun _ => entry) : Π i : Finset.Iic 0, St L K i) A := by
  rw [← map_frestrictLe_μ (L := L) (K := K) entry T]
  rw [Measure.map_apply (measurable_frestrictLe T) hA]
  rfl

end ProtocolTraceLaw

namespace Phase3GoodClockRegime

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

theorem clockFrontQuantile_bad_subset_goodClock_bad
    {M : ℕ} {θ : Phase3GoodClock.ClockTimingParams} {lastHour : ℕ} :
    {tr : Phase3GoodClock.Trace L K |
      ¬ ClockFrontQuantileRegime (L := L) (K := K) θ tr lastHour} ⊆
      {tr |
        ¬ GoodClockUpTo (L := L) (K := K) M θ tr lastHour} := by
  intro tr hbad G
  exact hbad G.quantile

theorem hdomFailure_subset_goodClock_bad
    {M : ℕ} {θ : Phase3GoodClock.ClockTimingParams} {lastHour : ℕ} :
    {tr : Phase3GoodClock.Trace L K |
      HDomFailureUpTo (L := L) (K := K) M θ tr lastHour} ⊆
      {tr |
        ¬ GoodClockUpTo (L := L) (K := K) M θ tr lastHour} := by
  intro tr hbad G
  exact hbad G.quantile G.hdom_stopped

/-- A genuine good-clock bad-event tail implies the quantile-tail residual. -/
theorem clockFrontQuantileTail_of_goodClock_tail
    {μ : Measure (Phase3GoodClock.Trace L K)}
    {M : ℕ} {θ : Phase3GoodClock.ClockTimingParams}
    {lastHour : ℕ} {ε : ℝ≥0∞}
    (hgood :
      μ {tr |
        ¬ GoodClockUpTo (L := L) (K := K) M θ tr lastHour} ≤ ε) :
    ClockFrontQuantileTail (L := L) (K := K) μ θ lastHour ε := by
  exact le_trans
    (measure_mono
      (clockFrontQuantile_bad_subset_goodClock_bad
        (L := L) (K := K) (M := M) (θ := θ) (lastHour := lastHour)))
    hgood

/-- A genuine good-clock bad-event tail implies the hdom-failure residual. -/
theorem hdomFailure_tail_of_goodClock_tail
    {μ : Measure (Phase3GoodClock.Trace L K)}
    {M : ℕ} {θ : Phase3GoodClock.ClockTimingParams}
    {lastHour : ℕ} {ε : ℝ≥0∞}
    (hgood :
      μ {tr |
        ¬ GoodClockUpTo (L := L) (K := K) M θ tr lastHour} ≤ ε) :
    μ {tr | HDomFailureUpTo (L := L) (K := K) M θ tr lastHour} ≤ ε := by
  exact le_trans
    (measure_mono
      (hdomFailure_subset_goodClock_bad
        (L := L) (K := K) (M := M) (θ := θ) (lastHour := lastHour)))
    hgood

theorem protocol_clockFrontQuantileTail_of_goodClock_tail
    {M : ℕ} {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)} {lastHour : ℕ} {ε : ℝ≥0∞}
    (hgood :
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr | ¬ GoodClockUpTo (L := L) (K := K) M θ tr lastHour} ≤ ε) :
    ClockFrontQuantileTail (L := L) (K := K)
      (ProtocolTraceLaw.μ (L := L) (K := K) entry) θ lastHour ε :=
  clockFrontQuantileTail_of_goodClock_tail
    (L := L) (K := K) (M := M) hgood

theorem protocol_hdomFailure_tail_of_goodClock_tail
    {M : ℕ} {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)} {lastHour : ℕ} {ε : ℝ≥0∞}
    (hgood :
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr | ¬ GoodClockUpTo (L := L) (K := K) M θ tr lastHour} ≤ ε) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr | HDomFailureUpTo (L := L) (K := K) M θ tr lastHour} ≤ ε :=
  hdomFailure_tail_of_goodClock_tail
    (L := L) (K := K) (M := M) hgood

end Phase3GoodClockRegime

namespace Phase3Assembly

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

namespace Slot3ClockRegimeTails

/-- Provider from a direct quantile tail and a genuine protocol-trace good-clock tail. -/
noncomputable def ofQuantileAndGoodClockTail
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    {εq εh εclock : ℝ≥0∞}
    (hquant :
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr |
          ¬ Phase3GoodClockRegime.ClockFrontQuantileRegime
            (L := L) (K := K) θ tr D.lastCoreHour} ≤ εq)
    (hgood :
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr |
          ¬ Phase3GoodClockRegime.GoodClockUpTo
            (L := L) (K := K) D.M θ tr D.lastCoreHour} ≤ εh)
    (hbudget : εq + εh ≤ εclock) :
    Slot3ClockRegimeTails (L := L) (K := K) D θ entry where
  εq := εq
  εh := εh
  εclock := εclock
  clock_quantile_tail := hquant
  hdom_tail :=
    Phase3GoodClockRegime.protocol_hdomFailure_tail_of_goodClock_tail
      (L := L) (K := K) hgood
  budget := hbudget

/-- Provider from two genuine protocol-trace good-clock tails. -/
noncomputable def ofGoodClockTails
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    {εq εh εclock : ℝ≥0∞}
    (hquantGood :
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr |
          ¬ Phase3GoodClockRegime.GoodClockUpTo
            (L := L) (K := K) D.M θ tr D.lastCoreHour} ≤ εq)
    (hhdomGood :
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr |
          ¬ Phase3GoodClockRegime.GoodClockUpTo
            (L := L) (K := K) D.M θ tr D.lastCoreHour} ≤ εh)
    (hbudget : εq + εh ≤ εclock) :
    Slot3ClockRegimeTails (L := L) (K := K) D θ entry where
  εq := εq
  εh := εh
  εclock := εclock
  clock_quantile_tail :=
    Phase3GoodClockRegime.protocol_clockFrontQuantileTail_of_goodClock_tail
      (L := L) (K := K) hquantGood
  hdom_tail :=
    Phase3GoodClockRegime.protocol_hdomFailure_tail_of_goodClock_tail
      (L := L) (K := K) hhdomGood
  budget := hbudget

/-- Single-tail convenience wrapper, charging the same good-clock tail twice. -/
noncomputable def ofGoodClockTail
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    {εgood εclock : ℝ≥0∞}
    (hgood :
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr |
          ¬ Phase3GoodClockRegime.GoodClockUpTo
            (L := L) (K := K) D.M θ tr D.lastCoreHour} ≤ εgood)
    (hbudget : εgood + εgood ≤ εclock) :
    Slot3ClockRegimeTails (L := L) (K := K) D θ entry :=
  ofGoodClockTails (L := L) (K := K) hgood hgood hbudget

end Slot3ClockRegimeTails

end Phase3Assembly

#print axioms ProtocolTraceLaw.map_frestrictLe_μ
#print axioms ProtocolTraceLaw.cylinder_eq_partialTraj
#print axioms Phase3GoodClockRegime.clockFrontQuantileTail_of_goodClock_tail
#print axioms Phase3GoodClockRegime.hdomFailure_tail_of_goodClock_tail
#print axioms Phase3Assembly.Slot3ClockRegimeTails.ofQuantileAndGoodClockTail
#print axioms Phase3Assembly.Slot3ClockRegimeTails.ofGoodClockTails
#print axioms Phase3Assembly.Slot3ClockRegimeTails.ofGoodClockTail

end ExactMajority
