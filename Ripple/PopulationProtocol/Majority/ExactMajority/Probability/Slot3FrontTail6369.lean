import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot3GoodClockWhp
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WidthPrefixConcrete
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockFrontWidth

/-!
# Slot-3 Doty 6.3--6.9 clock-front tail

This file reduces the per-hour clock-front quantile tail needed by
`Slot3GoodClockWhp` to the trace-level first-passage consequences of Doty
6.3--6.9.

The front-decay files already provide the kernel/front pieces: the squaring
mechanism, windowed front profile, climb bound, good-width glue, and prefix
width tails.  What is still a genuine bridge at this surface is the trace
first-passage conversion: under the Ionescu-Tulcea law, the Doty 6.3--6.8
front behavior must imply the per-hour `start_h`/`end_h` hits and length
inequalities of Theorem 6.9.  We keep those sub-tails as precisely named
inputs and prove the measure assembly to `ClockFrontHourTails63_69`.
-/

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Phase3GoodClockRegime

open Phase3GoodClock

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

private theorem firstPassage_congr
    {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ t, P t ↔ Q t)
    (hP : ∃ t, P t) (hQ : ∃ t, Q t) :
    Phase3GoodClock.firstPassage P hP =
      Phase3GoodClock.firstPassage Q hQ := by
  apply le_antisymm
  · have hhit :
        P (Phase3GoodClock.firstPassage Q hQ) :=
      (hPQ _).2
        (Phase3GoodClock.firstPassage_firstHit (P := Q) hQ).hit
    exact Phase3GoodClock.firstPassage_le_of_hit (P := P) hP hhit
  · have hhit :
        Q (Phase3GoodClock.firstPassage P hP) :=
      (hPQ _).1
        (Phase3GoodClock.firstPassage_firstHit (P := P) hP).hit
    exact Phase3GoodClock.firstPassage_le_of_hit (P := Q) hQ hhit

/-- The two first-passage hit existences for one Doty 6.9 synchronous hour. -/
def HourHits6369
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) (h : ℕ) : Prop :=
  (∃ τ, Phase3GoodClock.StartHit (L := L) (K := K) θ h (tr τ)) ∧
    ∃ τ, Phase3GoodClock.EndHit (L := L) (K := K) θ h (tr τ)

/-- The three lower-length inequalities for one Doty 6.9 synchronous hour. -/
def HourLengthBounds6369
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) (h : ℕ) : Prop :=
  ∀ (hs : ∃ τ, Phase3GoodClock.StartHit (L := L) (K := K) θ h (tr τ))
    (he : ∃ τ, Phase3GoodClock.EndHit (L := L) (K := K) θ h (tr τ)),
    Phase3GoodClock.start_h (L := L) (K := K) θ tr h hs + θ.twoOverC ≤
      Phase3GoodClock.end_h (L := L) (K := K) θ tr h he ∧
    Phase3GoodClock.start_h (L := L) (K := K) θ tr h hs +
        θ.twoOverC + θ.fortyOneOverM ≤
      Phase3GoodClock.end_h (L := L) (K := K) θ tr h he ∧
    Phase3GoodClock.start_h (L := L) (K := K) θ tr h hs +
        θ.twoOverC + θ.fortySevenOverM ≤
      Phase3GoodClock.end_h (L := L) (K := K) θ tr h he ∧
    Phase3GoodClock.start_h (L := L) (K := K) θ tr h hs +
        θ.twoOverC + θ.fortySevenOverM + 1 ≤
      Phase3GoodClock.end_h (L := L) (K := K) θ tr h he

/-- Pathwise inputs sufficient for the previous-hour ordering in Doty 6.9.

For hour `h`, the previous end is the first small hit of the same cumulative
hour-front process that later reaches the bulk threshold at `start_h`. -/
def PrevHourOrderInputs6369
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) (h : ℕ) : Prop :=
  θ.small < θ.bulk ∧
    (∀ τ,
      Phase3GoodClock.hourFront (L := L) (K := K) h (tr τ) ≤
        Phase3GoodClock.hourFront (L := L) (K := K) h (tr (τ + 1))) ∧
    (∀ τ,
      Phase3GoodClock.hourFront (L := L) (K := K) h (tr (τ + 1)) ≤
        Phase3GoodClock.hourFront (L := L) (K := K) h (tr τ) + 1) ∧
    Phase3GoodClock.hourFront (L := L) (K := K) h (tr 0) < θ.small

/-- The trace-level Doty 6.3--6.9 front-tail pieces for one hour. -/
def HourFrontTailPieces6369
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) (h : ℕ) : Prop :=
  HourHits6369 (L := L) (K := K) θ tr h ∧
    HourLengthBounds6369 (L := L) (K := K) θ tr h ∧
    PrevHourOrderInputs6369 (L := L) (K := K) θ tr h

/-- The previous-hour order follows from monotone unit first-passage arithmetic. -/
theorem prevHourOrder6369_of_inputs
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K} {h : ℕ}
    (H : PrevHourOrderInputs6369 (L := L) (K := K) θ tr h)
    (hp : 0 < h)
    (hs : ∃ τ, Phase3GoodClock.StartHit (L := L) (K := K) θ h (tr τ))
    (hePrev :
      ∃ τ, Phase3GoodClock.EndHit (L := L) (K := K) θ (h - 1) (tr τ)) :
    Phase3GoodClock.end_h (L := L) (K := K) θ tr (h - 1) hePrev <
      Phase3GoodClock.start_h (L := L) (K := K) θ tr h hs := by
  classical
  obtain ⟨hsmall, hmono, hunit, hstartSmall⟩ := H
  let X : ℕ → ℕ := fun τ =>
    Phase3GoodClock.hourFront (L := L) (K := K) h (tr τ)
  have heSmall : ∃ τ, θ.small ≤ X τ := by
    rcases hePrev with ⟨τ, hτ⟩
    refine ⟨τ, ?_⟩
    have heq :
        Phase3GoodClock.hourFront (L := L) (K := K) h (tr τ) =
          Phase3GoodClock.beyondHour (L := L) (K := K) (h - 1) (tr τ) := by
      simpa [Nat.sub_add_cancel hp] using
        Phase3GoodClock.hourFront_succ_eq_beyondHour
          (L := L) (K := K) (h - 1) (tr τ)
    have hτ' :
        θ.small ≤
          Phase3GoodClock.beyondHour (L := L) (K := K) (h - 1) (tr τ) := by
      simpa [Phase3GoodClock.EndHit] using hτ
    simpa [X, heq] using hτ'
  have hsBulk : ∃ τ, θ.bulk ≤ X τ := by
    simpa [Phase3GoodClock.StartHit, X] using hs
  have hmain :=
    firstHit_small_lt_bulk_of_mono_unit
      (X := X) (small := θ.small) (bulk := θ.bulk)
      hsmall hmono hunit hstartSmall heSmall hsBulk
  have hend :
      Phase3GoodClock.end_h (L := L) (K := K) θ tr (h - 1) hePrev =
        Phase3GoodClock.firstPassage (fun τ => θ.small ≤ X τ) heSmall := by
    unfold Phase3GoodClock.end_h
    exact firstPassage_congr
      (P := fun τ =>
        Phase3GoodClock.EndHit (L := L) (K := K) θ (h - 1) (tr τ))
      (Q := fun τ => θ.small ≤ X τ)
      (by
        intro τ
        have heq :
            Phase3GoodClock.hourFront (L := L) (K := K) h (tr τ) =
              Phase3GoodClock.beyondHour (L := L) (K := K) (h - 1) (tr τ) := by
          simpa [Nat.sub_add_cancel hp] using
            Phase3GoodClock.hourFront_succ_eq_beyondHour
              (L := L) (K := K) (h - 1) (tr τ)
        constructor
        · intro hτ
          have hτ' :
              θ.small ≤
                Phase3GoodClock.beyondHour (L := L) (K := K) (h - 1) (tr τ) := by
            simpa [Phase3GoodClock.EndHit] using hτ
          simpa [X, heq] using hτ'
        · intro hτ
          have hτ' :
              θ.small ≤
                Phase3GoodClock.beyondHour (L := L) (K := K) (h - 1) (tr τ) := by
            simpa [X, heq] using hτ
          simpa [Phase3GoodClock.EndHit] using hτ')
      hePrev heSmall
  have hstart :
      Phase3GoodClock.start_h (L := L) (K := K) θ tr h hs =
        Phase3GoodClock.firstPassage (fun τ => θ.bulk ≤ X τ) hsBulk := by
    unfold Phase3GoodClock.start_h
    exact firstPassage_congr
      (P := fun τ =>
        Phase3GoodClock.StartHit (L := L) (K := K) θ h (tr τ))
      (Q := fun τ => θ.bulk ≤ X τ)
      (by
        intro τ
        simp [Phase3GoodClock.StartHit, X])
      hs hsBulk
  calc
    Phase3GoodClock.end_h (L := L) (K := K) θ tr (h - 1) hePrev =
        Phase3GoodClock.firstPassage (fun τ => θ.small ≤ X τ) heSmall := hend
    _ < Phase3GoodClock.firstPassage (fun τ => θ.bulk ≤ X τ) hsBulk := hmain
    _ = Phase3GoodClock.start_h (L := L) (K := K) θ tr h hs := hstart.symm

/-- Doty 6.3--6.9 trace pieces imply the per-hour quantile regime. -/
theorem clockFrontQuantileHourRegime_of_section6369_pieces
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K} {lastHour : ℕ}
    {i : Fin (lastHour + 1)}
    (H : HourFrontTailPieces6369 (L := L) (K := K) θ tr i.val) :
    ClockFrontQuantileHourRegime (L := L) (K := K) θ tr lastHour i := by
  classical
  obtain ⟨hhits, hlen, hprev⟩ := H
  refine
    { start_exists := hhits.1
      end_exists := hhits.2
      twoOverC_le_end := ?_
      fortyOne_le_end := ?_
      fortySeven_le_end := ?_
      fortySeven_slack := ?_
      prev_end_lt_start := ?_ }
  · intro hs he
    exact (hlen hs he).1
  · intro hs he
    exact (hlen hs he).2.1
  · intro hs he
    exact (hlen hs he).2.2.1
  · intro hs he
    exact (hlen hs he).2.2.2
  · intro hp hs hePrev
    exact prevHourOrder6369_of_inputs
      (L := L) (K := K) hprev hp hs hePrev

/-- The bad per-hour quantile event is covered by the failure of one Doty
6.3--6.9 front-tail piece. -/
theorem clockFrontQuantileHour_bad_subset_section6369_piece_bad
    {θ : Phase3GoodClock.ClockTimingParams} {lastHour : ℕ}
    {i : Fin (lastHour + 1)} :
    {tr : Phase3GoodClock.Trace L K |
      ¬ ClockFrontQuantileHourRegime (L := L) (K := K) θ tr lastHour i} ⊆
      {tr |
        ¬ HourFrontTailPieces6369 (L := L) (K := K) θ tr i.val} := by
  intro tr hbad hgood
  exact hbad
    (clockFrontQuantileHourRegime_of_section6369_pieces
      (L := L) (K := K) hgood)

/-- The failure of the combined Doty 6.3--6.9 piece is covered by hit,
length, or previous-order failure. -/
theorem piece6369_bad_subset_three_bad
    {θ : Phase3GoodClock.ClockTimingParams} {h : ℕ} :
    {tr : Phase3GoodClock.Trace L K |
      ¬ HourFrontTailPieces6369 (L := L) (K := K) θ tr h} ⊆
      {tr | ¬ HourHits6369 (L := L) (K := K) θ tr h} ∪
        {tr | ¬ HourLengthBounds6369 (L := L) (K := K) θ tr h} ∪
        {tr | ¬ PrevHourOrderInputs6369 (L := L) (K := K) θ tr h} := by
  intro tr hbad
  by_cases hhits : HourHits6369 (L := L) (K := K) θ tr h
  · by_cases hlen : HourLengthBounds6369 (L := L) (K := K) θ tr h
    · by_cases hprev : PrevHourOrderInputs6369 (L := L) (K := K) θ tr h
      · exact False.elim (hbad ⟨hhits, hlen, hprev⟩)
      · right
        exact hprev
    · left
      right
      exact hlen
  · left
    left
    exact hhits

/-- The named trace-level Doty 6.3--6.9 sub-tails.

The intended producers are:
* hits: Doty 6.4, 6.8, 6.9 first-passage existence;
* length: Doty 6.3--6.8 front-decay timing, assembled in 6.9;
* order: the previous-hour small-hit before current bulk-hit ordering. -/
structure TraceFirstPassageTails6369
    (entry : Config (AgentState L K))
    (θ : Phase3GoodClock.ClockTimingParams) (lastHour : ℕ) where
  εHits : Fin (lastHour + 1) → ℝ≥0∞
  εLength : Fin (lastHour + 1) → ℝ≥0∞
  εPrev : Fin (lastHour + 1) → ℝ≥0∞
  hits64_68 :
    ∀ i : Fin (lastHour + 1),
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr |
          ¬ HourHits6369 (L := L) (K := K) θ tr i.val} ≤
        εHits i
  length63_68 :
    ∀ i : Fin (lastHour + 1),
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr |
          ¬ HourLengthBounds6369 (L := L) (K := K) θ tr i.val} ≤
        εLength i
  prevOrder69 :
    ∀ i : Fin (lastHour + 1),
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr |
          ¬ PrevHourOrderInputs6369 (L := L) (K := K) θ tr i.val} ≤
        εPrev i

/-- Per-hour tail for the combined Doty 6.3--6.9 piece by a three-way union. -/
theorem piece6369_tail
    {entry : Config (AgentState L K)}
    {θ : Phase3GoodClock.ClockTimingParams} {lastHour : ℕ}
    (R : TraceFirstPassageTails6369 (L := L) (K := K) entry θ lastHour)
    (i : Fin (lastHour + 1)) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr |
        ¬ HourFrontTailPieces6369 (L := L) (K := K) θ tr i.val} ≤
      R.εHits i + R.εLength i + R.εPrev i := by
  classical
  let μ : Measure (Phase3GoodClock.Trace L K) :=
    ProtocolTraceLaw.μ (L := L) (K := K) entry
  let A : Set (Phase3GoodClock.Trace L K) :=
    {tr | ¬ HourHits6369 (L := L) (K := K) θ tr i.val}
  let B : Set (Phase3GoodClock.Trace L K) :=
    {tr | ¬ HourLengthBounds6369 (L := L) (K := K) θ tr i.val}
  let C : Set (Phase3GoodClock.Trace L K) :=
    {tr | ¬ PrevHourOrderInputs6369 (L := L) (K := K) θ tr i.val}
  calc
    μ {tr |
        ¬ HourFrontTailPieces6369 (L := L) (K := K) θ tr i.val}
        ≤ μ (A ∪ B ∪ C) :=
          measure_mono
            (by
              simpa [A, B, C] using
                (piece6369_bad_subset_three_bad
                  (L := L) (K := K) (θ := θ) (h := i.val)))
    _ ≤ μ (A ∪ B) + μ C := measure_union_le (μ := μ) (A ∪ B) C
    _ ≤ (μ A + μ B) + μ C := by
          have hAB : μ (A ∪ B) ≤ μ A + μ B :=
            measure_union_le (μ := μ) A B
          exact add_le_add_left hAB (μ C)
    _ ≤ R.εHits i + R.εLength i + R.εPrev i := by
          exact add_le_add (add_le_add (R.hits64_68 i) (R.length63_68 i))
            (R.prevOrder69 i)

/-- Main reduction: the trace-level Doty 6.3--6.9 sub-tails discharge the
`Slot3GoodClockWhp` per-hour residual. -/
theorem clockFrontHourTails63_69_of_trace_firstPassage_tails
    {entry : Config (AgentState L K)}
    {θ : Phase3GoodClock.ClockTimingParams} {lastHour : ℕ}
    {εHour : Fin (lastHour + 1) → ℝ≥0∞}
    (R : TraceFirstPassageTails6369 (L := L) (K := K) entry θ lastHour)
    (hBudget : ∀ i : Fin (lastHour + 1),
      R.εHits i + R.εLength i + R.εPrev i ≤ εHour i) :
    ClockFrontHourTails63_69 (L := L) (K := K) entry θ lastHour εHour := by
  intro i
  calc
    ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr |
          ¬ ClockFrontQuantileHourRegime (L := L) (K := K) θ tr lastHour i}
        ≤ ProtocolTraceLaw.μ (L := L) (K := K) entry
            {tr |
              ¬ HourFrontTailPieces6369 (L := L) (K := K) θ tr i.val} :=
          measure_mono
            (clockFrontQuantileHour_bad_subset_section6369_piece_bad
              (L := L) (K := K) (θ := θ) (lastHour := lastHour) (i := i))
    _ ≤ R.εHits i + R.εLength i + R.εPrev i :=
          piece6369_tail (L := L) (K := K) R i
    _ ≤ εHour i := hBudget i

#print axioms prevHourOrder6369_of_inputs
#print axioms clockFrontQuantileHourRegime_of_section6369_pieces
#print axioms piece6369_tail
#print axioms clockFrontHourTails63_69_of_trace_firstPassage_tails

end Phase3GoodClockRegime

end ExactMajority
