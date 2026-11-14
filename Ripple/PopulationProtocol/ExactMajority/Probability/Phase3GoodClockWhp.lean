import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3ClockTails

/-!
# Slot-3 GoodClock tail under the protocol trace law

This file gives the non-circular assembly surface for the slot-3 GoodClock tail.
The clock-front part is decomposed into per-hour first-passage timing events and
assembled by a finite union bound.  The remaining inputs are the two genuine Doty et al.
ingredients at their natural interfaces:

* Doty et al. Lemmas 6.3--6.9: per-hour clock-front quantile timing tails.
* Doty et al. Lemma 6.10: stopped hour-domain transfer to `HDomStoppedUpTo`.
-/

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Phase3GoodClockRegime

open Phase3GoodClock

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- One hour of the clock-front first-passage timing regime.

The inequalities are quantified over the existence witnesses.  This makes the
event independent of which witness is later used to build the global
`ClockFrontQuantileRegime`; `start_h` and `end_h` are first-passage times of the
underlying predicates. -/
structure ClockFrontQuantileHourRegime
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) (lastHour : ℕ)
    (i : Fin (lastHour + 1)) : Prop where
  start_exists :
    ∃ τ, Phase3GoodClock.StartHit (L := L) (K := K) θ i.val (tr τ)
  end_exists :
    ∃ τ, Phase3GoodClock.EndHit (L := L) (K := K) θ i.val (tr τ)
  twoOverC_le_end :
    ∀ (hs : ∃ τ, Phase3GoodClock.StartHit (L := L) (K := K) θ i.val (tr τ))
      (he : ∃ τ, Phase3GoodClock.EndHit (L := L) (K := K) θ i.val (tr τ)),
      Phase3GoodClock.start_h (L := L) (K := K) θ tr i.val hs + θ.twoOverC ≤
        Phase3GoodClock.end_h (L := L) (K := K) θ tr i.val he
  fortyOne_le_end :
    ∀ (hs : ∃ τ, Phase3GoodClock.StartHit (L := L) (K := K) θ i.val (tr τ))
      (he : ∃ τ, Phase3GoodClock.EndHit (L := L) (K := K) θ i.val (tr τ)),
      Phase3GoodClock.start_h (L := L) (K := K) θ tr i.val hs +
          θ.twoOverC + θ.fortyOneOverM ≤
        Phase3GoodClock.end_h (L := L) (K := K) θ tr i.val he
  fortySeven_le_end :
    ∀ (hs : ∃ τ, Phase3GoodClock.StartHit (L := L) (K := K) θ i.val (tr τ))
      (he : ∃ τ, Phase3GoodClock.EndHit (L := L) (K := K) θ i.val (tr τ)),
      Phase3GoodClock.start_h (L := L) (K := K) θ tr i.val hs +
          θ.twoOverC + θ.fortySevenOverM ≤
        Phase3GoodClock.end_h (L := L) (K := K) θ tr i.val he
  fortySeven_slack :
    ∀ (hs : ∃ τ, Phase3GoodClock.StartHit (L := L) (K := K) θ i.val (tr τ))
      (he : ∃ τ, Phase3GoodClock.EndHit (L := L) (K := K) θ i.val (tr τ)),
      Phase3GoodClock.start_h (L := L) (K := K) θ tr i.val hs +
          θ.twoOverC + θ.fortySevenOverM + 1 ≤
        Phase3GoodClock.end_h (L := L) (K := K) θ tr i.val he
  prev_end_lt_start :
    0 < i.val →
    ∀ (hs : ∃ τ, Phase3GoodClock.StartHit (L := L) (K := K) θ i.val (tr τ))
      (hePrev :
        ∃ τ, Phase3GoodClock.EndHit (L := L) (K := K) θ (i.val - 1) (tr τ)),
      Phase3GoodClock.end_h (L := L) (K := K) θ tr (i.val - 1) hePrev <
        Phase3GoodClock.start_h (L := L) (K := K) θ tr i.val hs

/-- All per-hour timing events imply the global clock-front quantile regime. -/
theorem clockFrontQuantileRegime_of_hourRegimes
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K} {lastHour : ℕ}
    (H : ∀ i : Fin (lastHour + 1),
      ClockFrontQuantileHourRegime (L := L) (K := K) θ tr lastHour i) :
    ClockFrontQuantileRegime (L := L) (K := K) θ tr lastHour := by
  classical
  let hs : ∀ h, h ≤ lastHour →
      ∃ τ, Phase3GoodClock.StartHit (L := L) (K := K) θ h (tr τ) :=
    fun h hh => (H ⟨h, Nat.lt_succ_of_le hh⟩).start_exists
  let he : ∀ h, h ≤ lastHour →
      ∃ τ, Phase3GoodClock.EndHit (L := L) (K := K) θ h (tr τ) :=
    fun h hh => (H ⟨h, Nat.lt_succ_of_le hh⟩).end_exists
  refine
    { start_exists := hs
      end_exists := he
      twoOverC_le_end := ?_
      fortyOne_le_end := ?_
      fortySeven_le_end := ?_
      fortySeven_slack := ?_
      prev_end_lt_start := ?_ }
  · intro h hh
    simpa [hs, he] using
      (H ⟨h, Nat.lt_succ_of_le hh⟩).twoOverC_le_end (hs h hh) (he h hh)
  · intro h hh
    simpa [hs, he] using
      (H ⟨h, Nat.lt_succ_of_le hh⟩).fortyOne_le_end (hs h hh) (he h hh)
  · intro h hh
    simpa [hs, he] using
      (H ⟨h, Nat.lt_succ_of_le hh⟩).fortySeven_le_end (hs h hh) (he h hh)
  · intro h hh
    simpa [hs, he] using
      (H ⟨h, Nat.lt_succ_of_le hh⟩).fortySeven_slack (hs h hh) (he h hh)
  · intro h hh hp
    have hprev : h - 1 ≤ lastHour := by omega
    simpa [hs, he] using
      (H ⟨h, Nat.lt_succ_of_le hh⟩).prev_end_lt_start hp (hs h hh) (he (h - 1) hprev)

/-- The bad global quantile event is covered by the finite union of per-hour
bad first-passage timing events. -/
theorem clockFrontQuantile_bad_subset_hour_bad_iUnion
    {θ : Phase3GoodClock.ClockTimingParams} {lastHour : ℕ} :
    {tr : Phase3GoodClock.Trace L K |
      ¬ ClockFrontQuantileRegime (L := L) (K := K) θ tr lastHour} ⊆
      ⋃ i : Fin (lastHour + 1),
        {tr |
          ¬ ClockFrontQuantileHourRegime (L := L) (K := K) θ tr lastHour i} := by
  classical
  intro tr hbad
  by_cases hall :
      ∀ i : Fin (lastHour + 1),
        ClockFrontQuantileHourRegime (L := L) (K := K) θ tr lastHour i
  · exact False.elim (hbad (clockFrontQuantileRegime_of_hourRegimes
      (L := L) (K := K) hall))
  · push Not at hall
    rcases hall with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hi⟩

/-- Doty et al. Lemmas 6.3--6.9 residual, stated at the per-hour level:
the clock-front first-passage timing bad event for each hour has the supplied
tail under the Ionescu-Tulcea protocol trace law. -/
def ClockFrontHourTails63_69
    (entry : Config (AgentState L K))
    (θ : Phase3GoodClock.ClockTimingParams) (lastHour : ℕ)
    (εHour : Fin (lastHour + 1) → ℝ≥0∞) : Prop :=
  ∀ i : Fin (lastHour + 1),
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr |
        ¬ ClockFrontQuantileHourRegime (L := L) (K := K) θ tr lastHour i} ≤
      εHour i

/-- Assemble Doty et al. Lemmas 6.3--6.9 per-hour tails into the global
`ClockFrontQuantileRegime` tail by the finite union bound over hours. -/
theorem clockFrontQuantileTail_of_hourTails
    {entry : Config (AgentState L K)}
    {θ : Phase3GoodClock.ClockTimingParams} {lastHour : ℕ}
    {εHour : Fin (lastHour + 1) → ℝ≥0∞} {εq : ℝ≥0∞}
    (hHour :
      ClockFrontHourTails63_69 (L := L) (K := K) entry θ lastHour εHour)
    (hBudget : (∑ i : Fin (lastHour + 1), εHour i) ≤ εq) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr | ¬ ClockFrontQuantileRegime (L := L) (K := K) θ tr lastHour} ≤ εq := by
  classical
  calc
    ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr | ¬ ClockFrontQuantileRegime (L := L) (K := K) θ tr lastHour}
        ≤ ProtocolTraceLaw.μ (L := L) (K := K) entry
            (⋃ i : Fin (lastHour + 1),
              {tr |
                ¬ ClockFrontQuantileHourRegime (L := L) (K := K) θ tr lastHour i}) :=
          measure_mono
            (clockFrontQuantile_bad_subset_hour_bad_iUnion
              (L := L) (K := K) (θ := θ) (lastHour := lastHour))
    _ ≤ ∑ i : Fin (lastHour + 1),
          ProtocolTraceLaw.μ (L := L) (K := K) entry
            {tr |
              ¬ ClockFrontQuantileHourRegime (L := L) (K := K) θ tr lastHour i} := by
          simpa using
            (measure_biUnion_finset_le
              (μ := ProtocolTraceLaw.μ (L := L) (K := K) entry)
              (I := (Finset.univ : Finset (Fin (lastHour + 1))))
              (s := fun i : Fin (lastHour + 1) =>
                {tr |
                  ¬ ClockFrontQuantileHourRegime (L := L) (K := K) θ tr lastHour i}))
    _ ≤ ∑ i : Fin (lastHour + 1), εHour i := by
          exact Finset.sum_le_sum (fun i _ => hHour i)
    _ ≤ εq := hBudget

/-- Doty et al. Lemma 6.10 residual at the trace-law level.

This is the precise transfer still needed beyond `lemma610_mAbove_frac_tail`: stop the
protocol on the hour gate, transfer the stopped-kernel Azuma tail back to the
Ionescu-Tulcea trace up to the first exit, and union over all time points in the
clock-certified hour intervals. -/
def HDomStoppedTraceTail610
    (entry : Config (AgentState L K)) (M : ℕ)
    (θ : Phase3GoodClock.ClockTimingParams) (lastHour : ℕ)
    (εh : ℝ≥0∞) : Prop :=
  ProtocolTraceLaw.μ (L := L) (K := K) entry
    {tr | HDomFailureUpTo (L := L) (K := K) M θ tr lastHour} ≤ εh

/-- The non-circular slot-3 GoodClock tail: per-hour clock-front quantile tails
plus the Lemma-6.10 stopped hdom transfer imply the desired `GoodClockUpTo`
bad-event bound under the protocol Ionescu-Tulcea trace law. -/
theorem protocol_goodClockUpTo_tail_of_frontHours_and_hdom
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    {εHour : Fin (D.lastCoreHour + 1) → ℝ≥0∞}
    {εq εh ε : ℝ≥0∞}
    (hHour :
      ClockFrontHourTails63_69
        (L := L) (K := K) entry θ D.lastCoreHour εHour)
    (hHourBudget : (∑ i : Fin (D.lastCoreHour + 1), εHour i) ≤ εq)
    (hhdom :
      HDomStoppedTraceTail610
        (L := L) (K := K) entry D.M θ D.lastCoreHour εh)
    (hBudget : εq + εh ≤ ε) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr |
        ¬ GoodClockUpTo (L := L) (K := K) D.M θ tr D.lastCoreHour} ≤ ε := by
  exact goodClock_regime_whp (L := L) (K := K)
    (clockFrontQuantileTail_of_hourTails
      (L := L) (K := K) hHour hHourBudget)
    hhdom hBudget

end Phase3GoodClockRegime

namespace Phase3Assembly

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- Pack the new GoodClock tail producer into the slot-3 clock-tail provider used
by `Slot3ClockTailsDischarge`, charging the same GoodClock tail twice as in the
existing single-tail convenience wrapper. -/
noncomputable def Phase3ClockRegimeTails.ofGoodClockWhp
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    {εHour : Fin (D.lastCoreHour + 1) → ℝ≥0∞}
    {εq εh εgood εclock : ℝ≥0∞}
    (hHour :
      Phase3GoodClockRegime.ClockFrontHourTails63_69
        (L := L) (K := K) entry θ D.lastCoreHour εHour)
    (hHourBudget : (∑ i : Fin (D.lastCoreHour + 1), εHour i) ≤ εq)
    (hhdom :
      Phase3GoodClockRegime.HDomStoppedTraceTail610
        (L := L) (K := K) entry D.M θ D.lastCoreHour εh)
    (hGoodBudget : εq + εh ≤ εgood)
    (hClockBudget : εgood + εgood ≤ εclock) :
    Phase3ClockRegimeTails (L := L) (K := K) D θ entry :=
  Phase3ClockRegimeTails.ofGoodClockTail (L := L) (K := K)
    (Phase3GoodClockRegime.protocol_goodClockUpTo_tail_of_frontHours_and_hdom
      (L := L) (K := K) hHour hHourBudget hhdom hGoodBudget)
    hClockBudget

end Phase3Assembly

#print axioms Phase3GoodClockRegime.clockFrontQuantileRegime_of_hourRegimes
#print axioms Phase3GoodClockRegime.clockFrontQuantileTail_of_hourTails
#print axioms Phase3GoodClockRegime.protocol_goodClockUpTo_tail_of_frontHours_and_hdom
#print axioms Phase3Assembly.Phase3ClockRegimeTails.ofGoodClockWhp

end Ripple.PopulationProtocol.ExactMajority
