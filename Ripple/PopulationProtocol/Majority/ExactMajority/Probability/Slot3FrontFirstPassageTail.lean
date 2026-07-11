import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot3FrontTail6369
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockFrontIter

/-!
# Slot-3 front first-passage tails for Doty 6.3--6.9

`Slot3FrontTail6369.lean` reduced the clock-front part of the slot-3
GoodClock tail to per-hour trace first-passage tails.  This file gives the
next assembly layer: a single per-hour front-width first-passage good event
implies the already-committed `ClockFrontQuantileHourRegime`, and a trace-law
tail for failure of that good event discharges `ClockFrontHourTails63_69`.

The genuine front machinery is already present upstream:

* `ClockFrontWidth.rBeyond_seed_le_rBeyondSq` proves the real-kernel empty-seed
  squaring;
* `FrontAllLevels.frontAll_empty_concentration` iterates the squaring over the
  whole front by the threshold-antitone collapse;
* `ClockFrontIter.envelope_collapsed_at_width` is the doubly-exponential
  `frontWidthBound n = O(log log n)` collapse.

The remaining irreducible producer is therefore named here at the trace-law
surface as `FrontWidthFirstPassageTailResidual6369`: it is exactly the
per-hour probability that the Doty 6.3--6.9 front-width first-passage package
fails.  At the kernel/front-shape surface this corresponds to the existing
`ClockFrontIter.JointClockFront` boundary-feeder/joint clock-front induction
residual; this file does not assert that residual.
-/

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace Phase3GoodClockRegime

open Phase3GoodClock

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Existing front-width machinery, exposed at this surface. -/

/-- The doubly-exponential envelope has collapsed below `1/n` past the
`frontWidthBound n` front width.  This is the deterministic width-decay content
used by the first-passage producer. -/
theorem envelope6369_collapsed_at_width (f0 : ℝ)
    (hf0 : 0 ≤ f0) (hsub : f0 ≤ 1 / 2)
    (n : ℕ) (hn2 : 2 ≤ n) (i : ℕ)
    (hi : FrontTail.frontWidthBound n ≤ i) :
    FrontTailKernel.envelope f0 i < 1 / (n : ℝ) :=
  ClockFrontIter.envelope_collapsed_at_width
    f0 hf0 hsub n hn2 i hi

/-- At a collapsed front level, being within the doubly-exponential envelope is
equivalent to the real front count being empty. -/
theorem withinEnvelope6369_iff_empty_at_width (f0 : ℝ)
    (hf0 : 0 ≤ f0) (hsub : f0 ≤ 1 / 2)
    (n : ℕ) (hn2 : 2 ≤ n) (i : ℕ)
    (hi : FrontTail.frontWidthBound n ≤ i)
    (c : Config (AgentState L K)) (hcard : c.card = n) :
    ClockFrontWidth.RWithinEnvelope (L := L) (K := K) f0 i c ↔
      ClockRealKernel.rBeyond (L := L) (K := K) i c = 0 :=
  ClockFrontIter.base_case_within_iff_empty
    (L := L) (K := K) f0 hf0 hsub n hn2 i hi c hcard

/-- Kernel-level name for the remaining joint front-width decay obstruction:
the boundary feeder and the clock-front advance have to be maintained together.
This is a `Prop` alias only; it is not asserted here. -/
abbrev IrreducibleFrontWidthDecay6369
    (n mC Bbd H : ℕ) (ε : ℝ≥0∞) : Prop :=
  ClockFrontIter.JointClockFront (L := L) (K := K) n mC Bbd H ε

/-! ## Per-hour first-passage package. -/

/-- The per-hour pathwise front-width first-passage package supplied by Doty
6.3--6.9: first hits exist, the synchronous-hour length bounds hold, and the
previous-hour ordering follows from the front's monotone unit motion. -/
structure FrontWidthFirstPassageGood6369
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) (h : ℕ) : Prop where
  hits : HourHits6369 (L := L) (K := K) θ tr h
  length : HourLengthBounds6369 (L := L) (K := K) θ tr h
  prevOrder : PrevHourOrderInputs6369 (L := L) (K := K) θ tr h

/-- Convert the named front-width first-passage package to the already-committed
Doty 6.3--6.9 pieces. -/
theorem FrontWidthFirstPassageGood6369.toPieces
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K} {h : ℕ}
    (G : FrontWidthFirstPassageGood6369 (L := L) (K := K) θ tr h) :
    HourFrontTailPieces6369 (L := L) (K := K) θ tr h :=
  ⟨G.hits, G.length, G.prevOrder⟩

/-- Convert the committed Doty 6.3--6.9 pieces back to the named front-width
first-passage package. -/
theorem FrontWidthFirstPassageGood6369.ofPieces
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K} {h : ℕ}
    (H : HourFrontTailPieces6369 (L := L) (K := K) θ tr h) :
    FrontWidthFirstPassageGood6369 (L := L) (K := K) θ tr h :=
  ⟨H.1, H.2.1, H.2.2⟩

/-- The front-width first-passage package implies the per-hour quantile regime. -/
theorem clockFrontQuantileHourRegime_of_frontWidthFirstPassage
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K} {lastHour : ℕ}
    {i : Fin (lastHour + 1)}
    (G : FrontWidthFirstPassageGood6369 (L := L) (K := K) θ tr i.val) :
    ClockFrontQuantileHourRegime (L := L) (K := K) θ tr lastHour i :=
  clockFrontQuantileHourRegime_of_section6369_pieces
    (L := L) (K := K) G.toPieces

/-- The bad per-hour quantile event is covered by failure of the front-width
first-passage package. -/
theorem clockFrontQuantileHour_bad_subset_frontWidthFirstPassage_bad
    {θ : Phase3GoodClock.ClockTimingParams} {lastHour : ℕ}
    {i : Fin (lastHour + 1)} :
    {tr : Phase3GoodClock.Trace L K |
      ¬ ClockFrontQuantileHourRegime (L := L) (K := K) θ tr lastHour i} ⊆
      {tr |
        ¬ FrontWidthFirstPassageGood6369
          (L := L) (K := K) θ tr i.val} := by
  intro tr hbad hgood
  exact hbad
    (clockFrontQuantileHourRegime_of_frontWidthFirstPassage
      (L := L) (K := K) hgood)

/-! ## Tiny-before-end readout from the first-hit interface. -/

/-- The first-hit readout: strictly before `end_h`, the beyond-hour front is
still below the small threshold. -/
def TinyBeforeEndUntilEnd6369
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) (h : ℕ) : Prop :=
  ∀ (he : ∃ τ, Phase3GoodClock.EndHit (L := L) (K := K) θ h (tr τ))
    (τ : ℕ),
    τ < Phase3GoodClock.end_h (L := L) (K := K) θ tr h he →
      Phase3GoodClock.TinyBeforeEnd (L := L) (K := K) θ h (tr τ)

/-- The tiny-before-end readout is deterministic once the `EndHit` witness is
chosen; it is exactly the `end_h` first-hit property. -/
theorem tinyBeforeEnd6369_until_end
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) (h : ℕ) :
    TinyBeforeEndUntilEnd6369 (L := L) (K := K) θ tr h := by
  intro he τ hτ
  have hnot : ¬ Phase3GoodClock.EndHit (L := L) (K := K) θ h (tr τ) :=
    (Phase3GoodClock.end_h_firstHit
      (L := L) (K := K) θ tr h he).first τ hτ
  exact Nat.lt_of_not_ge hnot

/-- The useful per-hour readout: first hits exist and every strict pre-`end_h`
time is `TinyBeforeEnd`. -/
def TinyBeforeEndReadout6369
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) (h : ℕ) : Prop :=
  HourHits6369 (L := L) (K := K) θ tr h ∧
    TinyBeforeEndUntilEnd6369 (L := L) (K := K) θ tr h

/-- A front-width first-passage good hour gives the `TinyBeforeEnd` readout. -/
theorem tinyBeforeEndReadout6369_of_frontWidthFirstPassage
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K} {h : ℕ}
    (G : FrontWidthFirstPassageGood6369 (L := L) (K := K) θ tr h) :
    TinyBeforeEndReadout6369 (L := L) (K := K) θ tr h :=
  ⟨G.hits, tinyBeforeEnd6369_until_end (L := L) (K := K) θ tr h⟩

/-- Failure of the tiny-before-end readout is covered by failure of the
front-width first-passage good event. -/
theorem tinyBeforeEndReadout_bad_subset_frontWidthFirstPassage_bad
    {θ : Phase3GoodClock.ClockTimingParams} {h : ℕ} :
    {tr : Phase3GoodClock.Trace L K |
      ¬ TinyBeforeEndReadout6369 (L := L) (K := K) θ tr h} ⊆
      {tr |
        ¬ FrontWidthFirstPassageGood6369
          (L := L) (K := K) θ tr h} := by
  intro tr hbad hgood
  exact hbad
    (tinyBeforeEndReadout6369_of_frontWidthFirstPassage
      (L := L) (K := K) hgood)

/-! ## The trace-law front-width first-passage tail residual. -/

/-- The precise trace-law residual for Doty 6.3--6.9 at this surface.

For each hour, the probability that the front-width first-passage package fails
is bounded by `εFront i`.  This is the honest residual left if the full
doubly-exponential front-width/joint clock-front argument is not closed in this
file. -/
structure FrontWidthFirstPassageTailResidual6369
    (entry : Config (AgentState L K))
    (θ : Phase3GoodClock.ClockTimingParams) (lastHour : ℕ) where
  εFront : Fin (lastHour + 1) → ℝ≥0∞
  frontWidthDecay63_69 :
    ∀ i : Fin (lastHour + 1),
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr |
          ¬ FrontWidthFirstPassageGood6369
            (L := L) (K := K) θ tr i.val} ≤
        εFront i

namespace FrontWidthFirstPassageTailResidual6369

variable {entry : Config (AgentState L K)}
variable {θ : Phase3GoodClock.ClockTimingParams} {lastHour : ℕ}

/-- The hits-bad event is covered by the front-width first-passage bad event. -/
theorem hits_bad_subset
    (i : Fin (lastHour + 1)) :
    {tr : Phase3GoodClock.Trace L K |
      ¬ HourHits6369 (L := L) (K := K) θ tr i.val} ⊆
      {tr |
        ¬ FrontWidthFirstPassageGood6369
          (L := L) (K := K) θ tr i.val} := by
  intro tr hbad hgood
  exact hbad hgood.hits

/-- The length-bad event is covered by the front-width first-passage bad event. -/
theorem length_bad_subset
    (i : Fin (lastHour + 1)) :
    {tr : Phase3GoodClock.Trace L K |
      ¬ HourLengthBounds6369 (L := L) (K := K) θ tr i.val} ⊆
      {tr |
        ¬ FrontWidthFirstPassageGood6369
          (L := L) (K := K) θ tr i.val} := by
  intro tr hbad hgood
  exact hbad hgood.length

/-- The previous-order-bad event is covered by the front-width first-passage
bad event. -/
theorem prev_bad_subset
    (i : Fin (lastHour + 1)) :
    {tr : Phase3GoodClock.Trace L K |
      ¬ PrevHourOrderInputs6369 (L := L) (K := K) θ tr i.val} ⊆
      {tr |
        ¬ FrontWidthFirstPassageGood6369
          (L := L) (K := K) θ tr i.val} := by
  intro tr hbad hgood
  exact hbad hgood.prevOrder

/-- Compatibility wrapper for the older three-tail reduction.  Each of the
three sub-tail budgets is charged to the same front-width first-passage tail. -/
def toTraceFirstPassageTails
    (R : FrontWidthFirstPassageTailResidual6369
      (L := L) (K := K) entry θ lastHour) :
    TraceFirstPassageTails6369 (L := L) (K := K) entry θ lastHour where
  εHits := R.εFront
  εLength := R.εFront
  εPrev := R.εFront
  hits64_68 := by
    intro i
    exact le_trans
      (measure_mono
        (hits_bad_subset (L := L) (K := K) (θ := θ) (lastHour := lastHour) i))
      (R.frontWidthDecay63_69 i)
  length63_68 := by
    intro i
    exact le_trans
      (measure_mono
        (length_bad_subset (L := L) (K := K) (θ := θ) (lastHour := lastHour) i))
      (R.frontWidthDecay63_69 i)
  prevOrder69 := by
    intro i
    exact le_trans
      (measure_mono
        (prev_bad_subset (L := L) (K := K) (θ := θ) (lastHour := lastHour) i))
      (R.frontWidthDecay63_69 i)

end FrontWidthFirstPassageTailResidual6369

/-! ## Tail assembly. -/

/-- Direct assembly: a per-hour front-width first-passage tail discharges the
committed `ClockFrontHourTails63_69` residual without paying the three-way
union used by the compatibility wrapper. -/
theorem clockFrontHourTails63_69_of_frontWidthFirstPassageTail
    {entry : Config (AgentState L K)}
    {θ : Phase3GoodClock.ClockTimingParams} {lastHour : ℕ}
    {εHour : Fin (lastHour + 1) → ℝ≥0∞}
    (R : FrontWidthFirstPassageTailResidual6369
      (L := L) (K := K) entry θ lastHour)
    (hBudget : ∀ i : Fin (lastHour + 1), R.εFront i ≤ εHour i) :
    ClockFrontHourTails63_69 (L := L) (K := K) entry θ lastHour εHour := by
  intro i
  calc
    ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr |
          ¬ ClockFrontQuantileHourRegime
            (L := L) (K := K) θ tr lastHour i}
        ≤ ProtocolTraceLaw.μ (L := L) (K := K) entry
            {tr |
              ¬ FrontWidthFirstPassageGood6369
                (L := L) (K := K) θ tr i.val} :=
          measure_mono
            (clockFrontQuantileHour_bad_subset_frontWidthFirstPassage_bad
              (L := L) (K := K) (θ := θ) (lastHour := lastHour) (i := i))
    _ ≤ R.εFront i := R.frontWidthDecay63_69 i
    _ ≤ εHour i := hBudget i

/-- Assembly through the already-committed three-tail reduction.  This is useful
for callers that still consume `TraceFirstPassageTails6369`; it pays three
copies of the same per-hour front-width budget. -/
theorem clockFrontHourTails63_69_of_frontWidthFirstPassageTail_via_trace_tails
    {entry : Config (AgentState L K)}
    {θ : Phase3GoodClock.ClockTimingParams} {lastHour : ℕ}
    {εHour : Fin (lastHour + 1) → ℝ≥0∞}
    (R : FrontWidthFirstPassageTailResidual6369
      (L := L) (K := K) entry θ lastHour)
    (hBudget : ∀ i : Fin (lastHour + 1),
      R.εFront i + R.εFront i + R.εFront i ≤ εHour i) :
    ClockFrontHourTails63_69 (L := L) (K := K) entry θ lastHour εHour :=
  clockFrontHourTails63_69_of_trace_firstPassage_tails
    (L := L) (K := K)
    (R.toTraceFirstPassageTails (L := L) (K := K)) hBudget

/-- The same front-width residual also bounds the first-hit `TinyBeforeEnd`
readout failure for each hour. -/
theorem tinyBeforeEndReadout_tail_of_frontWidthFirstPassageTail
    {entry : Config (AgentState L K)}
    {θ : Phase3GoodClock.ClockTimingParams} {lastHour : ℕ}
    (R : FrontWidthFirstPassageTailResidual6369
      (L := L) (K := K) entry θ lastHour)
    (i : Fin (lastHour + 1)) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr |
        ¬ TinyBeforeEndReadout6369
          (L := L) (K := K) θ tr i.val} ≤
      R.εFront i :=
  le_trans
    (measure_mono
      (tinyBeforeEndReadout_bad_subset_frontWidthFirstPassage_bad
        (L := L) (K := K) (θ := θ) (h := i.val)))
    (R.frontWidthDecay63_69 i)

#print axioms envelope6369_collapsed_at_width
#print axioms withinEnvelope6369_iff_empty_at_width
#print axioms clockFrontQuantileHourRegime_of_frontWidthFirstPassage
#print axioms tinyBeforeEnd6369_until_end
#print axioms FrontWidthFirstPassageTailResidual6369.toTraceFirstPassageTails
#print axioms clockFrontHourTails63_69_of_frontWidthFirstPassageTail
#print axioms clockFrontHourTails63_69_of_frontWidthFirstPassageTail_via_trace_tails
#print axioms tinyBeforeEndReadout_tail_of_frontWidthFirstPassageTail

end Phase3GoodClockRegime

end ExactMajority
