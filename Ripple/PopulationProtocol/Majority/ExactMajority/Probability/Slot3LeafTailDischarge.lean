import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot3ClosureBuild
import Mathlib.Tactic

/-!
# Slot-3 leaf-tail discharge surface.

This file isolates the honest slot-3 `leaf_tail` reduction.

The deterministic part is closed here:

* static invariants plus the hour `Window` imply membership in the stopped
  Lemma-6.10 regime;
* strict cut placement implies the `TinyBeforeEnd` leaves;
* these facts build `Slot3LeafGood`;
* hence the target leaf-failure event is covered by deterministic-cut failure
  plus the true Window-failure event.

The probabilistic Window tail is carried through a named `negPhi` residual.  This
keeps the orientation explicit: Window failure is a lower deviation of `Phi`, so
the tail event is stated for `negPhi = -Phi`, not for the existing upper tail of
`Phi`.
-/

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Real

namespace Phase3Assembly
namespace Slot3LeafTailDischarge

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- The lower-tail orientation used for Window failure. -/
noncomputable def negPhi (M C : ℝ) (h : ℕ) (c : Config (AgentState L K)) : ℝ :=
  - HourCouplingAzuma.Phi (L := L) (K := K) M C h c

/-- Static part of the stopped Lemma-6.10 regime: the phase-3 hour window and
the fixed role counts.  The only missing conjunct is the hour `Window`. -/
def StaticInv (D : Phase3Core.Phase3ModeDomain L) (C : ℝ)
    (c : Config (AgentState L K)) : Prop :=
  HourCoupling.HourWindow (L := L) (K := K) c ∧
    (HourCouplingAzuma.mainCount (L := L) (K := K) c : ℝ) = (D.M : ℝ) ∧
    (HourCouplingAzuma.clockCount (L := L) (K := K) c : ℝ) = C ∧
    1 ≤ HourCouplingAzuma.mainCount (L := L) (K := K) c ∧
    1 ≤ HourCouplingAzuma.clockCount (L := L) (K := K) c

theorem regime_of_staticInv_window
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {h : ℕ} {c : Config (AgentState L K)}
    (hs : StaticInv (L := L) (K := K) D C c)
    (hw : HourCouplingAzuma.Window (L := L) (K := K) h c) :
    c ∈ Lemma610StoppedAzuma.regimeSet
      (L := L) (K := K) (D.M : ℝ) C h := by
  exact ⟨hs.1, hw, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2⟩

theorem not_window_of_staticInv_not_regime
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {h : ℕ} {c : Config (AgentState L K)}
    (hs : StaticInv (L := L) (K := K) D C c)
    (hr :
      c ∉ Lemma610StoppedAzuma.regimeSet
        (L := L) (K := K) (D.M : ℝ) C h) :
    ¬ HourCouplingAzuma.Window (L := L) (K := K) h c := by
  intro hw
  exact hr (regime_of_staticInv_window (L := L) (K := K) hs hw)

noncomputable def coreInput
    (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K)
    (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
    (h : ℕ) :
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h :=
  Phase3GoodClock.CoreClockInputs.ofGoodClock (L := L) (K := K) D.M h G

noncomputable def afterOState
    (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K)
    (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
    (h : ℕ) : Config (AgentState L K) :=
  tr ((coreInput (L := L) (K := K) D θ tr G h).start + θ.twoOverC)

noncomputable def afterPhiState
    (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K)
    (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
    (h : ℕ) : Config (AgentState L K) :=
  tr ((coreInput (L := L) (K := K) D θ tr G h).start +
    θ.twoOverC + θ.fortyOneOverM)

noncomputable def afterMassState
    (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K)
    (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
    (h : ℕ) : Config (AgentState L K) :=
  tr ((coreInput (L := L) (K := K) D θ tr G h).start +
    θ.twoOverC + θ.fortySevenOverM)

structure LeafStaticInvGood
    (D : Phase3Core.Phase3ModeDomain L) (C : ℝ)
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) : Prop where
  afterO :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      StaticInv (L := L) (K := K) D C
        (afterOState (L := L) (K := K) D θ tr G h)
  afterPhi :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      StaticInv (L := L) (K := K) D C
        (afterPhiState (L := L) (K := K) D θ tr G h)
  afterMass :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      StaticInv (L := L) (K := K) D C
        (afterMassState (L := L) (K := K) D θ tr G h)

structure LeafWindowGood
    (D : Phase3Core.Phase3ModeDomain L) (C : ℝ)
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) : Prop where
  afterO :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      HourCouplingAzuma.Window (L := L) (K := K) h
        (afterOState (L := L) (K := K) D θ tr G h)
  afterPhi :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      HourCouplingAzuma.Window (L := L) (K := K) h
        (afterPhiState (L := L) (K := K) D θ tr G h)
  afterMass :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      HourCouplingAzuma.Window (L := L) (K := K) h
        (afterMassState (L := L) (K := K) D θ tr G h)

structure LeafRegimeGood
    (D : Phase3Core.Phase3ModeDomain L) (C : ℝ)
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) : Prop where
  afterO :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      afterOState (L := L) (K := K) D θ tr G h ∈
        Lemma610StoppedAzuma.regimeSet (L := L) (K := K) (D.M : ℝ) C h
  afterPhi :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      afterPhiState (L := L) (K := K) D θ tr G h ∈
        Lemma610StoppedAzuma.regimeSet (L := L) (K := K) (D.M : ℝ) C h
  afterMass :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      afterMassState (L := L) (K := K) D θ tr G h ∈
        Lemma610StoppedAzuma.regimeSet (L := L) (K := K) (D.M : ℝ) C h

theorem leafRegimeGood_of_static_window
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (hs : LeafStaticInvGood (L := L) (K := K) D C θ tr)
    (hw : LeafWindowGood (L := L) (K := K) D C θ tr) :
    LeafRegimeGood (L := L) (K := K) D C θ tr where
  afterO := by
    intro G h hh
    exact regime_of_staticInv_window
      (L := L) (K := K) (hs.afterO G h hh) (hw.afterO G h hh)
  afterPhi := by
    intro G h hh
    exact regime_of_staticInv_window
      (L := L) (K := K) (hs.afterPhi G h hh) (hw.afterPhi G h hh)
  afterMass := by
    intro G h hh
    exact regime_of_staticInv_window
      (L := L) (K := K) (hs.afterMass G h hh) (hw.afterMass G h hh)

/-- The current `GoodClock` interface gives `≤ finish`; this residual asks for
the strict form needed to read `TinyBeforeEnd` at the three leaf cuts. -/
structure LeafStrictCutInside
    (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) : Prop where
  afterMass_lt_finish :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      (coreInput (L := L) (K := K) D θ tr G h).start +
          θ.twoOverC + θ.fortySevenOverM <
        (coreInput (L := L) (K := K) D θ tr G h).finish

structure LeafTinyGood
    (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) : Prop where
  afterO :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      Phase3GoodClock.TinyBeforeEnd (L := L) (K := K) θ h
        (afterOState (L := L) (K := K) D θ tr G h)
  afterPhi :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      Phase3GoodClock.TinyBeforeEnd (L := L) (K := K) θ h
        (afterPhiState (L := L) (K := K) D θ tr G h)
  afterMass :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      Phase3GoodClock.TinyBeforeEnd (L := L) (K := K) θ h
        (afterMassState (L := L) (K := K) D θ tr G h)

theorem leafTinyGood_of_strictCutInside
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (hs : LeafStrictCutInside (L := L) (K := K) D θ tr) :
    LeafTinyGood (L := L) (K := K) D θ tr where
  afterO := by
    intro G h hh
    have hlt := hs.afterMass_lt_finish G h hh
    dsimp [afterOState]
    exact (coreInput (L := L) (K := K) D θ tr G h).tiny_until_finish
      ((coreInput (L := L) (K := K) D θ tr G h).start + θ.twoOverC) (by
        omega)
  afterPhi := by
    intro G h hh
    have hlt := hs.afterMass_lt_finish G h hh
    dsimp [afterPhiState]
    exact (coreInput (L := L) (K := K) D θ tr G h).tiny_until_finish
      ((coreInput (L := L) (K := K) D θ tr G h).start +
        θ.twoOverC + θ.fortyOneOverM) (by
        have h41 := θ.fortyOne_le_fortySeven
        omega)
  afterMass := by
    intro G h hh
    have hlt := hs.afterMass_lt_finish G h hh
    dsimp [afterMassState]
    exact (coreInput (L := L) (K := K) D θ tr G h).tiny_until_finish
      ((coreInput (L := L) (K := K) D θ tr G h).start +
        θ.twoOverC + θ.fortySevenOverM) hlt

structure LeafNumericFacts
    (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams) (C : ℝ) : Prop where
  leakageC_pos : 0 < C
  leakageK_pos : 0 < K
  clock_tiny_frac :
    ∀ h c,
      Phase3GoodClock.TinyBeforeEnd (L := L) (K := K) θ h c →
        (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) / C ≤
          (1 / 1000 : ℝ)

noncomputable def coreSurfaceSixLeaf_of_facts
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (hn : LeafNumericFacts (L := L) (K := K) D θ C)
    (hr : LeafRegimeGood (L := L) (K := K) D C θ tr)
    (ht : LeafTinyGood (L := L) (K := K) D θ tr) :
    CoreSurfaceSixLeaf (L := L) (K := K) D θ tr where
  leakageC := C
  leakageC_pos := hn.leakageC_pos
  leakageK_pos := hn.leakageK_pos
  regime_afterO := by
    intro G h hh
    simpa [afterOState, coreInput] using hr.afterO G h hh
  regime_afterPhi := by
    intro G h hh
    simpa [afterPhiState, coreInput] using hr.afterPhi G h hh
  regime_afterMass := by
    intro G h hh
    simpa [afterMassState, coreInput] using hr.afterMass G h hh
  tiny_afterO := by
    intro G h hh
    simpa [afterOState, coreInput] using ht.afterO G h hh
  tiny_afterPhi := by
    intro G h hh
    simpa [afterPhiState, coreInput] using ht.afterPhi G h hh
  tiny_afterMass := by
    intro G h hh
    simpa [afterMassState, coreInput] using ht.afterMass G h hh
  spanGate := fun _ _ => Set.univ
  clock_tiny_frac := hn.clock_tiny_frac
  eps13 := fun _ => 0
  eps14 := fun _ => 0
  eps15 := fun _ => 0
  eps16 := fun _ => 0

theorem slot3LeafGood_of_static_window_strict
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (hn : LeafNumericFacts (L := L) (K := K) D θ C)
    (hs : LeafStaticInvGood (L := L) (K := K) D C θ tr)
    (hw : LeafWindowGood (L := L) (K := K) D C θ tr)
    (hi : LeafStrictCutInside (L := L) (K := K) D θ tr) :
    Slot3LeafGood (L := L) (K := K) D θ tr := by
  exact ⟨coreSurfaceSixLeaf_of_facts (L := L) (K := K) hn
    (leafRegimeGood_of_static_window (L := L) (K := K) hs hw)
    (leafTinyGood_of_strictCutInside (L := L) (K := K) hi), trivial⟩

def deterministicCutFailure
    (D : Phase3Core.Phase3ModeDomain L) (C : ℝ)
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) : Prop :=
  ¬ LeafStaticInvGood (L := L) (K := K) D C θ tr ∨
    ¬ LeafStrictCutInside (L := L) (K := K) D θ tr

def windowFailure
    (D : Phase3Core.Phase3ModeDomain L) (C : ℝ)
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) : Prop :=
  LeafStaticInvGood (L := L) (K := K) D C θ tr ∧
    LeafStrictCutInside (L := L) (K := K) D θ tr ∧
    ¬ LeafWindowGood (L := L) (K := K) D C θ tr

theorem leaf_failure_subset_det_or_window
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {θ : Phase3GoodClock.ClockTimingParams}
    (hn : LeafNumericFacts (L := L) (K := K) D θ C) :
    {tr : Phase3GoodClock.Trace L K |
      Phase3GoodClockRegime.GoodClockUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
      ¬ Slot3LeafGood (L := L) (K := K) D θ tr} ⊆
      {tr |
        Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
        deterministicCutFailure (L := L) (K := K) D C θ tr} ∪
      {tr |
        Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
        windowFailure (L := L) (K := K) D C θ tr} := by
  intro tr htr
  rcases htr with ⟨hg, hleaf⟩
  by_cases hs : LeafStaticInvGood (L := L) (K := K) D C θ tr
  · by_cases hi : LeafStrictCutInside (L := L) (K := K) D θ tr
    · by_cases hw : LeafWindowGood (L := L) (K := K) D C θ tr
      · exact False.elim (hleaf
          (slot3LeafGood_of_static_window_strict (L := L) (K := K) hn hs hw hi))
      · right
        exact ⟨hg, hs, hi, hw⟩
    · left
      exact ⟨hg, Or.inr hi⟩
  · left
    exact ⟨hg, Or.inl hs⟩

/-- Tail bound after the deterministic leaf reduction: deterministic-cut failure
plus the Window-failure tail pays for the original slot-3 leaf event. -/
theorem leaf_tail_of_det_and_window_tails
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    {εdet εwindow εleaf : ℝ≥0∞}
    (hn : LeafNumericFacts (L := L) (K := K) D θ C)
    (hdet :
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr |
          Phase3GoodClockRegime.GoodClockUpTo
            (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
          deterministicCutFailure (L := L) (K := K) D C θ tr} ≤ εdet)
    (hwindow :
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr |
          Phase3GoodClockRegime.GoodClockUpTo
            (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
          windowFailure (L := L) (K := K) D C θ tr} ≤ εwindow)
    (hbudget : εdet + εwindow ≤ εleaf) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr |
        Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
        ¬ Slot3LeafGood (L := L) (K := K) D θ tr} ≤ εleaf := by
  calc
    ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr |
          Phase3GoodClockRegime.GoodClockUpTo
            (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
          ¬ Slot3LeafGood (L := L) (K := K) D θ tr}
        ≤
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        ({tr |
          Phase3GoodClockRegime.GoodClockUpTo
            (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
          deterministicCutFailure (L := L) (K := K) D C θ tr} ∪
        {tr |
          Phase3GoodClockRegime.GoodClockUpTo
            (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
          windowFailure (L := L) (K := K) D C θ tr}) :=
      measure_mono (leaf_failure_subset_det_or_window (L := L) (K := K) hn)
    _ ≤
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr |
          Phase3GoodClockRegime.GoodClockUpTo
            (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
          deterministicCutFailure (L := L) (K := K) D C θ tr} +
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr |
          Phase3GoodClockRegime.GoodClockUpTo
            (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
          windowFailure (L := L) (K := K) D C θ tr} :=
      measure_union_le _ _
    _ ≤ εdet + εwindow := add_le_add hdet hwindow
    _ ≤ εleaf := hbudget

/-- The correctly-oriented deviation event for the probabilistic Window tail. -/
def negPhiDeviation
    (D : Phase3Core.Phase3ModeDomain L) (C : ℝ)
    (θ : Phase3GoodClock.ClockTimingParams) (lam : ℝ)
    (tr : Phase3GoodClock.Trace L K) : Prop :=
  ∃ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
    (h : ℕ), h ≤ D.lastCoreHour ∧
      (lam ≤ negPhi (L := L) (K := K) (D.M : ℝ) C h
          (afterOState (L := L) (K := K) D θ tr G h) ∨
       lam ≤ negPhi (L := L) (K := K) (D.M : ℝ) C h
          (afterPhiState (L := L) (K := K) D θ tr G h) ∨
       lam ≤ negPhi (L := L) (K := K) (D.M : ℝ) C h
          (afterMassState (L := L) (K := K) D θ tr G h))

structure Slot3LeafWindowTailResiduals
    (D : Phase3Core.Phase3ModeDomain L) (C : ℝ)
    (θ : Phase3GoodClock.ClockTimingParams)
    (entry : Config (AgentState L K)) (εwindow : ℝ≥0∞) where
  lam : ℝ
  lam_pos : 0 < lam
  window_failure_to_negPhi_deviation :
    {tr : Phase3GoodClock.Trace L K |
      Phase3GoodClockRegime.GoodClockUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
      windowFailure (L := L) (K := K) D C θ tr} ⊆
    {tr | negPhiDeviation (L := L) (K := K) D C θ lam tr}
  negPhi_deviation_tail :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr | negPhiDeviation (L := L) (K := K) D C θ lam tr} ≤ εwindow

namespace Slot3LeafWindowTailResiduals

theorem window_tail
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)} {εwindow : ℝ≥0∞}
    (R : Slot3LeafWindowTailResiduals
      (L := L) (K := K) D C θ entry εwindow) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr |
        Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
        windowFailure (L := L) (K := K) D C θ tr} ≤ εwindow :=
  le_trans (measure_mono R.window_failure_to_negPhi_deviation) R.negPhi_deviation_tail

end Slot3LeafWindowTailResiduals

structure Slot3LeafTailInputs
    (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (entry : Config (AgentState L K)) (εleaf : ℝ≥0∞) where
  leakageC : ℝ
  numeric : LeafNumericFacts (L := L) (K := K) D θ leakageC
  εdet : ℝ≥0∞
  εwindow : ℝ≥0∞
  staticInv_strictCut_failure_tail :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr |
        Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
        deterministicCutFailure (L := L) (K := K) D leakageC θ tr} ≤ εdet
  window_tail :
    Slot3LeafWindowTailResiduals (L := L) (K := K) D leakageC θ entry εwindow
  budget : εdet + εwindow ≤ εleaf

namespace Slot3LeafTailInputs

theorem leaf_tail
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)} {εleaf : ℝ≥0∞}
    (I : Slot3LeafTailInputs (L := L) (K := K) D θ entry εleaf) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr |
        Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
        ¬ Slot3LeafGood (L := L) (K := K) D θ tr} ≤ εleaf :=
  leaf_tail_of_det_and_window_tails
    (L := L) (K := K) I.numeric I.staticInv_strictCut_failure_tail
    I.window_tail.window_tail I.budget

end Slot3LeafTailInputs

/-! ## Generic stopped-exit bridge contract. -/

namespace StoppedExitBridge

variable {α : Type*} [MeasurableSpace α]

abbrev Trace (α : Type*) := ℕ → α

def exitBy (S : Set α) (t : ℕ) (tr : Trace α) : Prop :=
  ∃ s, s ≤ t ∧ tr s ∉ S

def prob_exitBy_eq_stopped_bad
    (μ : Measure (Trace α)) (Kstar : Kernel α α) (entry : α)
    (S : Set α) (t : ℕ) : Prop :=
  μ {tr | exitBy S t tr} = (Kstar ^ t) entry Sᶜ

theorem prob_exitBy_le_stopped_bad
    {μ : Measure (Trace α)} {Kstar : Kernel α α} {entry : α}
    {S : Set α} {t : ℕ} {ε : ℝ≥0∞}
    (hbridge : prob_exitBy_eq_stopped_bad μ Kstar entry S t)
    (hstopped : (Kstar ^ t) entry Sᶜ ≤ ε) :
    μ {tr | exitBy S t tr} ≤ ε := by
  rw [hbridge]
  exact hstopped

theorem stopped_bad_le_of_dev_tail
    {Kstar : Kernel α α} {entry : α}
    {S Dev : Set α} {t : ℕ} {ε : ℝ≥0∞}
    (hsub : Sᶜ ⊆ Dev)
    (hdev : (Kstar ^ t) entry Dev ≤ ε) :
    (Kstar ^ t) entry Sᶜ ≤ ε :=
  le_trans (measure_mono hsub) hdev

theorem exitBy_le_dev_tail_of_bridge
    {μ : Measure (Trace α)} {Kstar : Kernel α α} {entry : α}
    {S Dev : Set α} {t : ℕ} {ε : ℝ≥0∞}
    (hbridge : prob_exitBy_eq_stopped_bad μ Kstar entry S t)
    (hsub : Sᶜ ⊆ Dev)
    (hdev : (Kstar ^ t) entry Dev ≤ ε) :
    μ {tr | exitBy S t tr} ≤ ε :=
  prob_exitBy_le_stopped_bad hbridge
    (stopped_bad_le_of_dev_tail hsub hdev)

end StoppedExitBridge

#print axioms regime_of_staticInv_window
#print axioms not_window_of_staticInv_not_regime
#print axioms leafRegimeGood_of_static_window
#print axioms leafTinyGood_of_strictCutInside
#print axioms coreSurfaceSixLeaf_of_facts
#print axioms slot3LeafGood_of_static_window_strict
#print axioms leaf_failure_subset_det_or_window
#print axioms leaf_tail_of_det_and_window_tails
#print axioms Slot3LeafWindowTailResiduals.window_tail
#print axioms Slot3LeafTailInputs.leaf_tail
#print axioms StoppedExitBridge.prob_exitBy_le_stopped_bad
#print axioms StoppedExitBridge.stopped_bad_le_of_dev_tail
#print axioms StoppedExitBridge.exitBy_le_dev_tail_of_bridge

end Slot3LeafTailDischarge
end Phase3Assembly
end ExactMajority
