import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase3Pre3
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockFrontSnapshots
import Mathlib.Tactic

namespace ExactMajority

open scoped BigOperators ENNReal

namespace Phase3GoodClock

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-!
Slot-3 piece 4: the stopped GoodClock/hour-domain interface.

This file deliberately only packages first-passage clock facts and the hour-local
snapshot consumed by the later Core(h) row.  The later clock-front Regime proof
is responsible for producing this bundle with high probability.
-/

/-- A discrete trajectory, separated from any particular kernel proof. -/
abbrev Trace (L K : ℕ) := ℕ → Config (AgentState L K)

/-! ## First-passage times -/

/-- The generic first-passage time of a nonempty event. -/
noncomputable def firstPassage (P : ℕ → Prop) [DecidablePred P] (hex : ∃ t, P t) : ℕ :=
  Nat.find hex

/-- A first-passage certificate: the event holds at `t`, and never strictly before `t`. -/
structure FirstHit (P : ℕ → Prop) (t : ℕ) : Prop where
  hit : P t
  first : ∀ τ, τ < t → ¬ P τ

theorem firstPassage_firstHit {P : ℕ → Prop} [DecidablePred P] (hex : ∃ t, P t) :
    FirstHit P (firstPassage P hex) := by
  constructor
  · simpa [firstPassage] using Nat.find_spec hex
  · intro τ hτ
    simpa [firstPassage] using Nat.find_min hex hτ

theorem firstPassage_le_of_hit {P : ℕ → Prop} [DecidablePred P] (hex : ∃ t, P t)
    {τ : ℕ} (hτ : P τ) :
    firstPassage P hex ≤ τ := by
  simpa [firstPassage] using Nat.find_min' hex hτ

/-! ## Clock-front thresholds -/

/-- Discrete timing and front-threshold parameters for one Phase-3 proof run. -/
structure ClockTimingParams where
  /-- Small beyond-hour threshold. `end_h` is the first hit of this event. -/
  small : ℕ
  /-- Bulk threshold for clocks at hour `h` or beyond. `start_h` is the first hit of this event. -/
  bulk : ℕ
  /-- Discrete interaction budget for `2/c`. -/
  twoOverC : ℕ
  /-- Discrete interaction budget for `41/m`. -/
  fortyOneOverM : ℕ
  /-- Discrete interaction budget for `47/m`. -/
  fortySevenOverM : ℕ
  /-- The small threshold is below the bulk threshold, matching the paper's quantiles. -/
  small_le_bulk : small ≤ bulk
  /-- The `41/m` checkpoint occurs no later than the `47/m` checkpoint. -/
  fortyOne_le_fortySeven : fortyOneOverM ≤ fortySevenOverM

/-- Clocks at hour `h` or beyond, i.e. clocks with minute at least `h*K`. -/
def clockAtOrBeyondHourP (h : ℕ) (a : AgentState L K) : Prop :=
  a.role = Role.clock ∧ h * K ≤ a.minute.val

instance (h : ℕ) (a : AgentState L K) : Decidable (clockAtOrBeyondHourP (L := L) (K := K) h a) := by
  unfold clockAtOrBeyondHourP
  infer_instance

/-- Count of clocks at hour `h` or beyond. -/
def hourFront (h : ℕ) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => clockAtOrBeyondHourP (L := L) (K := K) h a) c

/-- Count of clocks beyond hour `h`, i.e. at hour `h+1` or beyond. -/
def beyondHour (h : ℕ) (c : Config (AgentState L K)) : ℕ :=
  HourCoupling.cAbove (L := L) (K := K) h c

theorem hourFront_succ_eq_beyondHour (h : ℕ) (c : Config (AgentState L K)) :
    hourFront (L := L) (K := K) (h + 1) c =
      beyondHour (L := L) (K := K) h c := by
  rfl

/-- Start event: the hour-`h` front has reached the bulk threshold. -/
def StartHit (θ : ClockTimingParams) (h : ℕ) (c : Config (AgentState L K)) : Prop :=
  θ.bulk ≤ hourFront (L := L) (K := K) h c

/-- End event: the beyond-`h` front has reached the small threshold. -/
def EndHit (θ : ClockTimingParams) (h : ℕ) (c : Config (AgentState L K)) : Prop :=
  θ.small ≤ beyondHour (L := L) (K := K) h c

/-- The useful strict-before-end readout. -/
def TinyBeforeEnd (θ : ClockTimingParams) (h : ℕ) (c : Config (AgentState L K)) : Prop :=
  beyondHour (L := L) (K := K) h c < θ.small

/-- Anti-pattern marker: using this as the `end_h` predicate makes the first hit
often occur at time zero.  The real `end_h` predicate is `EndHit`. -/
def WrongEndPredicate (θ : ClockTimingParams) (h : ℕ) (c : Config (AgentState L K)) : Prop :=
  beyondHour (L := L) (K := K) h c ≤ θ.small

/-- First time the hour-`h` front reaches the bulk threshold. -/
noncomputable def start_h (θ : ClockTimingParams) (tr : Trace L K) (h : ℕ)
    (hex : ∃ τ, StartHit (L := L) (K := K) θ h (tr τ)) : ℕ :=
  firstPassage (fun τ => StartHit (L := L) (K := K) θ h (tr τ)) hex

/-- First time the beyond-`h` front reaches the small threshold. -/
noncomputable def end_h (θ : ClockTimingParams) (tr : Trace L K) (h : ℕ)
    (hex : ∃ τ, EndHit (L := L) (K := K) θ h (tr τ)) : ℕ :=
  firstPassage (fun τ => EndHit (L := L) (K := K) θ h (tr τ)) hex

theorem start_h_firstHit (θ : ClockTimingParams) (tr : Trace L K) (h : ℕ)
    (hex : ∃ τ, StartHit (L := L) (K := K) θ h (tr τ)) :
    FirstHit (fun τ => StartHit (L := L) (K := K) θ h (tr τ))
      (start_h (L := L) (K := K) θ tr h hex) := by
  simpa [start_h] using
    firstPassage_firstHit
      (P := fun τ => StartHit (L := L) (K := K) θ h (tr τ)) hex

theorem end_h_firstHit (θ : ClockTimingParams) (tr : Trace L K) (h : ℕ)
    (hex : ∃ τ, EndHit (L := L) (K := K) θ h (tr τ)) :
    FirstHit (fun τ => EndHit (L := L) (K := K) θ h (tr τ))
      (end_h (L := L) (K := K) θ tr h hex) := by
  simpa [end_h] using
    firstPassage_firstHit
      (P := fun τ => EndHit (L := L) (K := K) θ h (tr τ)) hex

/-! ## Hour-domain snapshot -/

/-- The per-config hour-domain snapshot consumed inside a stopped synchronous hour. -/
structure HDomAt (top : ℕ) (c : Config (AgentState L K)) : Prop where
  hIdx : WindowReconciliation.BiasedMainIndexLeHour (L := L) (K := K) c
  hMainHour : WindowReconciliation.MainHourBelow (L := L) (K := K) top c
  hAllBiasedBelow : DoublingEdges.AllBiasedMainBelow (L := L) (K := K) top c

/-- Legacy lowercase name for the old over-strong hour-domain snapshot.  This
legacy alias is kept only for already-landed snapshot bridges that explicitly
prove the old leaves. -/
def legacyHdom (top : ℕ) (c : Config (AgentState L K)) : Prop :=
  HDomAt (L := L) (K := K) top c

namespace HDomAt

theorem allBiasedBelow {top : ℕ} {c : Config (AgentState L K)}
    (H : HDomAt (L := L) (K := K) top c) :
    DoublingEdges.AllBiasedMainBelow (L := L) (K := K) top c :=
  H.hAllBiasedBelow

/-- Build the snapshot from the two deterministic clock-front leaves. -/
def ofSnapshots {top : ℕ} {c : Config (AgentState L K)}
    (hIdx : WindowReconciliation.BiasedMainIndexLeHour (L := L) (K := K) c)
    (hMainHour : WindowReconciliation.MainHourBelow (L := L) (K := K) top c) :
    HDomAt (L := L) (K := K) top c where
  hIdx := hIdx
  hMainHour := hMainHour
  hAllBiasedBelow :=
    Phase3ActiveBand.allBiasedMainBelow_of_clockFrontSnapshots
      (L := L) (K := K) (top := top) hIdx hMainHour

end HDomAt

/-- The active-band hour-domain snapshot the Regime/Core path may carry at
good checkpoints.

The old pointwise leaves `BiasedMainIndexLeHour` and `MainHourBelow` are not part
of this interface: the former is false as a phase-3 step invariant, while the
stopped Lemma 6.10 route gives only a small Main-ahead tail, not a zero tail. -/
structure HDomAt' (top M : ℕ) (c : Config (AgentState L K)) : Prop where
  hAllBiasedBelow : DoublingEdges.AllBiasedMainBelow (L := L) (K := K) top c
  hMainTailSmall :
    (HourCoupling.mAbove (L := L) (K := K) top c : ℝ) ≤
      (12 / 10000 : ℝ) * (M : ℝ)

/-- Lowercase consumer name for the Lemma-6.10 hour-domain tail.

The probabilistic hdom kernel controls only the Main-ahead tail.  Active-band
index ceilings live on the good-event/Core side and are not part of the bad
event covered by Lemma 6.10. -/
def hdom (top M : ℕ) (c : Config (AgentState L K)) : Prop :=
  (HourCoupling.mAbove (L := L) (K := K) top c : ℝ) ≤
    (12 / 10000 : ℝ) * (M : ℝ)

namespace HDomAt'

theorem allBiasedBelow {top M : ℕ} {c : Config (AgentState L K)}
    (H : HDomAt' (L := L) (K := K) top M c) :
    DoublingEdges.AllBiasedMainBelow (L := L) (K := K) top c :=
  H.hAllBiasedBelow

theorem mainTailSmall {top M : ℕ} {c : Config (AgentState L K)}
    (H : HDomAt' (L := L) (K := K) top M c) :
    (HourCoupling.mAbove (L := L) (K := K) top c : ℝ) ≤
      (12 / 10000 : ℝ) * (M : ℝ) :=
  H.hMainTailSmall

end HDomAt'

/-- `hdom` as a stopped interval event. -/
def HDomStopped (top M lo hi : ℕ) (tr : Trace L K) : Prop :=
  ∀ τ, lo ≤ τ → τ ≤ hi → hdom (L := L) (K := K) top M (tr τ)

/-! ## Field provenance markers -/

/-- Provenance marker for this interface. -/
inductive FieldSource where
  | pureInterface
  | abstractClockProto
  deriving DecidableEq, Repr

/-- First-hit existence and timing fields are intentionally assumed at this layer. -/
def source_start_h : FieldSource := FieldSource.pureInterface

/-- `end_h` is also an assumed first-hit interface field; the direction is fixed by `EndHit`. -/
def source_end_h : FieldSource := FieldSource.pureInterface

/-- Interval length fields are assumed until the later synchronous-hour Regime proof. -/
def source_interval_lengths : FieldSource := FieldSource.pureInterface

/-- The stopped `hdom` snapshot is assumed here and later populated by the clock-front proof. -/
def source_hdom : FieldSource := FieldSource.pureInterface

/-- The abstract clock protocol already supplies monotone/front-shape inputs
for the later producer. -/
def source_clockProto_front_tools : FieldSource := FieldSource.abstractClockProto

/-! ## GoodClock bundle -/

/-- The stopped GoodClock event for one trace.

All fields are local to the stopped trace.  In particular, the `hdom_stopped`
field is not a global invariant over arbitrary configurations.
-/
structure GoodClock (M : ℕ) (θ : ClockTimingParams) (tr : Trace L K) where
  start_exists : ∀ h, ∃ τ, StartHit (L := L) (K := K) θ h (tr τ)
  end_exists : ∀ h, ∃ τ, EndHit (L := L) (K := K) θ h (tr τ)
  twoOverC_le_end : ∀ h,
    start_h (L := L) (K := K) θ tr h (start_exists h) + θ.twoOverC ≤
      end_h (L := L) (K := K) θ tr h (end_exists h)
  fortyOne_le_end : ∀ h,
    start_h (L := L) (K := K) θ tr h (start_exists h) + θ.twoOverC +
        θ.fortyOneOverM ≤
      end_h (L := L) (K := K) θ tr h (end_exists h)
  fortySeven_le_end : ∀ h,
    start_h (L := L) (K := K) θ tr h (start_exists h) + θ.twoOverC +
        θ.fortySevenOverM ≤
      end_h (L := L) (K := K) θ tr h (end_exists h)
  prev_end_lt_start : ∀ h, 0 < h →
    end_h (L := L) (K := K) θ tr (h - 1) (end_exists (h - 1)) <
      start_h (L := L) (K := K) θ tr h (start_exists h)
  hdom_stopped : ∀ h,
    HDomStopped (L := L) (K := K) (h + 1) M
      (start_h (L := L) (K := K) θ tr h (start_exists h) + θ.twoOverC)
      (end_h (L := L) (K := K) θ tr h (end_exists h)) tr

namespace GoodClock

variable {M : ℕ} {θ : ClockTimingParams} {tr : Trace L K}

noncomputable def start (G : GoodClock (L := L) (K := K) M θ tr) (h : ℕ) : ℕ :=
  start_h (L := L) (K := K) θ tr h (G.start_exists h)

noncomputable def finish (G : GoodClock (L := L) (K := K) M θ tr) (h : ℕ) : ℕ :=
  end_h (L := L) (K := K) θ tr h (G.end_exists h)

theorem start_first (G : GoodClock (L := L) (K := K) M θ tr) (h : ℕ) :
    FirstHit (fun τ => StartHit (L := L) (K := K) θ h (tr τ)) (G.start h) :=
  start_h_firstHit (L := L) (K := K) θ tr h (G.start_exists h)

theorem finish_first (G : GoodClock (L := L) (K := K) M θ tr) (h : ℕ) :
    FirstHit (fun τ => EndHit (L := L) (K := K) θ h (tr τ)) (G.finish h) :=
  end_h_firstHit (L := L) (K := K) θ tr h (G.end_exists h)

theorem start_bulk_hit (G : GoodClock (L := L) (K := K) M θ tr) (h : ℕ) :
    StartHit (L := L) (K := K) θ h (tr (G.start h)) :=
  (G.start_first h).hit

theorem finish_small_hit (G : GoodClock (L := L) (K := K) M θ tr) (h : ℕ) :
    EndHit (L := L) (K := K) θ h (tr (G.finish h)) :=
  (G.finish_first h).hit

/-- Strictly before `end_h`, the beyond-`h` clock front is still below the small threshold. -/
theorem tiny_before_finish (G : GoodClock (L := L) (K := K) M θ tr)
    (h τ : ℕ) (hτ : τ < G.finish h) :
    TinyBeforeEnd (L := L) (K := K) θ h (tr τ) := by
  have hnot : ¬ EndHit (L := L) (K := K) θ h (tr τ) :=
    (G.finish_first h).first τ hτ
  exact Nat.lt_of_not_ge hnot

theorem hdom_at_work_start (G : GoodClock (L := L) (K := K) M θ tr) (h : ℕ) :
    hdom (L := L) (K := K) (h + 1) M (tr (G.start h + θ.twoOverC)) :=
  G.hdom_stopped h (G.start h + θ.twoOverC) (le_refl _) (G.twoOverC_le_end h)

theorem hdom_at_41 (G : GoodClock (L := L) (K := K) M θ tr) (h : ℕ) :
    hdom (L := L) (K := K) (h + 1) M
      (tr (G.start h + θ.twoOverC + θ.fortyOneOverM)) :=
  G.hdom_stopped h (G.start h + θ.twoOverC + θ.fortyOneOverM)
    (by simp [start]) (G.fortyOne_le_end h)

theorem hdom_at_47 (G : GoodClock (L := L) (K := K) M θ tr) (h : ℕ) :
    hdom (L := L) (K := K) (h + 1) M
      (tr (G.start h + θ.twoOverC + θ.fortySevenOverM)) :=
  G.hdom_stopped h (G.start h + θ.twoOverC + θ.fortySevenOverM)
    (by simp [start]) (G.fortySeven_le_end h)

theorem previous_hour_finished (G : GoodClock (L := L) (K := K) M θ tr)
    (h : ℕ) (hh : 0 < h) :
    G.finish (h - 1) < G.start h :=
  G.prev_end_lt_start h hh

end GoodClock

/-! ## Projection to the Core(h) scaffold -/

/-- The GoodClock facts one Core(h) row consumes. -/
structure CoreClockInputs (θ : ClockTimingParams) (tr : Trace L K) (h : ℕ) where
  /-- Main-population scale used by the corrected active-band hdom snapshot. -/
  M : ℕ
  /-- First passage of the hour-`h` bulk front. -/
  start : ℕ
  /-- First passage of the beyond-`h` small front. -/
  finish : ℕ
  /-- The previous hour's finish, used only when `0 < h`. -/
  prevFinish : ℕ
  /-- H13 / Lemma 6.13: clock catalyst floor at `start_h`. -/
  h13_start_bulk : StartHit (L := L) (K := K) θ h (tr start)
  /-- H13 and H14: before `end_h`, the beyond-`h` front remains tiny. -/
  tiny_until_finish : ∀ τ, τ < finish →
    TinyBeforeEnd (L := L) (K := K) θ h (tr τ)
  /-- H13 active-band / hour-domain snapshot after the `2/c` warm-up. -/
  h13_hdom_start :
    hdom (L := L) (K := K) (h + 1) M (tr (start + θ.twoOverC))
  /-- H15: the `41/m` checkpoint lies inside the stopped hour and has the snapshot. -/
  h15_hdom_41 :
    hdom (L := L) (K := K) (h + 1) M
      (tr (start + θ.twoOverC + θ.fortyOneOverM))
  /-- H16: the `47/m` checkpoint lies inside the stopped hour and has the snapshot. -/
  h16_hdom_47 :
    hdom (L := L) (K := K) (h + 1) M
      (tr (start + θ.twoOverC + θ.fortySevenOverM))
  /-- H15 timing input. -/
  fortyOne_inside : start + θ.twoOverC + θ.fortyOneOverM ≤ finish
  /-- H16 timing input. -/
  fortySeven_inside : start + θ.twoOverC + θ.fortySevenOverM ≤ finish
  /-- H13 handoff from the previous H16 row. -/
  previous_hour_finished : 0 < h → prevFinish < start

namespace CoreClockInputs

noncomputable def ofGoodClock {θ : ClockTimingParams} {tr : Trace L K} (M h : ℕ)
    (G : GoodClock (L := L) (K := K) M θ tr) :
    CoreClockInputs (L := L) (K := K) θ tr h where
  M := M
  start := G.start h
  finish := G.finish h
  prevFinish := G.finish (h - 1)
  h13_start_bulk := G.start_bulk_hit h
  tiny_until_finish := fun τ hτ => G.tiny_before_finish h τ hτ
  h13_hdom_start := G.hdom_at_work_start h
  h15_hdom_41 := G.hdom_at_41 h
  h16_hdom_47 := G.hdom_at_47 h
  fortyOne_inside := G.fortyOne_le_end h
  fortySeven_inside := G.fortySeven_le_end h
  previous_hour_finished := fun hh => G.previous_hour_finished h hh

end CoreClockInputs

#print axioms firstPassage_firstHit
#print axioms start_h_firstHit
#print axioms end_h_firstHit
#print axioms HDomAt.ofSnapshots
#print axioms GoodClock.tiny_before_finish
#print axioms GoodClock.hdom_at_47
#print axioms CoreClockInputs.ofGoodClock

end Phase3GoodClock

end ExactMajority
