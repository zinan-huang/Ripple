import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot3LeafTailDischarge
import Mathlib.Tactic

/-!
# Slot-3 Window/negPhi tail discharge

`Slot3LeafTailDischarge` exposed the Window-failure branch in the `negPhi = -Phi`
orientation.  Under the already-carried leaf hypotheses, that branch is actually
empty: strict cut placement gives `TinyBeforeEnd` at the three leaf checkpoints,
and the numeric leaf facts turn `TinyBeforeEnd` into
`cAbove / C <= 1/1000`.  Together with the static role-count identity
`clockCount = C`, this implies the Lemma-6.10 synchronous window
`11 * cAbove <= clockCount`.

Thus the leaf Window tail is discharged without a new probabilistic residual.
-/

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Real

namespace Phase3Assembly
namespace Slot3WindowNegPhiTail

open Slot3LeafTailDischarge

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- The leaf numeric clock-smallness fact is stronger than the Lemma-6.10
Window threshold `cAbove / C <= 1/11`. -/
theorem window_of_static_tiny_numeric
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {θ : Phase3GoodClock.ClockTimingParams} {h : ℕ}
    {c : Config (AgentState L K)}
    (hn : LeafNumericFacts (L := L) (K := K) D θ C)
    (hs : StaticInv (L := L) (K := K) D C c)
    (htiny : Phase3GoodClock.TinyBeforeEnd (L := L) (K := K) θ h c) :
    HourCouplingAzuma.Window (L := L) (K := K) h c := by
  have hfrac := hn.clock_tiny_frac h c htiny
  have hCpos : 0 < C := hn.leakageC_pos
  have hcAbove_le :
      (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) ≤ C / 1000 := by
    calc
      (HourCoupling.cAbove (L := L) (K := K) h c : ℝ)
          = ((HourCoupling.cAbove (L := L) (K := K) h c : ℝ) / C) * C := by
              field_simp [ne_of_gt hCpos]
      _ ≤ (1 / 1000 : ℝ) * C :=
              mul_le_mul_of_nonneg_right hfrac hCpos.le
      _ = C / 1000 := by ring
  have h11c_le_C :
      11 * (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) ≤ C := by
    have hscale :
        11 * (HourCoupling.cAbove (L := L) (K := K) h c : ℝ)
          ≤ 11 * (C / 1000) :=
      mul_le_mul_of_nonneg_left hcAbove_le (by norm_num : (0 : ℝ) ≤ 11)
    have hsmall : 11 * (C / 1000) ≤ C := by
      nlinarith [hCpos]
    exact hscale.trans hsmall
  have hclock : (HourCouplingAzuma.clockCount (L := L) (K := K) c : ℝ) = C :=
    hs.2.2.1
  unfold HourCouplingAzuma.Window
  have hreal :
      (11 * HourCoupling.cAbove (L := L) (K := K) h c : ℝ) ≤
        (HourCouplingAzuma.clockCount (L := L) (K := K) c : ℝ) := by
    simpa [hclock] using h11c_le_C
  exact_mod_cast hreal

/-- Static invariants plus the strict leaf cuts already imply all three Window
checks.  This is the deterministic discharge of the `negPhi` branch. -/
theorem leafWindowGood_of_static_strict_numeric
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (hn : LeafNumericFacts (L := L) (K := K) D θ C)
    (hs : LeafStaticInvGood (L := L) (K := K) D C θ tr)
    (hi : LeafStrictCutInside (L := L) (K := K) D θ tr) :
    LeafWindowGood (L := L) (K := K) D C θ tr := by
  let ht : LeafTinyGood (L := L) (K := K) D θ tr :=
    leafTinyGood_of_strictCutInside (L := L) (K := K) hi
  exact
    { afterO := by
        intro G h hh
        exact window_of_static_tiny_numeric
          (L := L) (K := K) hn (hs.afterO G h hh) (ht.afterO G h hh)
      afterPhi := by
        intro G h hh
        exact window_of_static_tiny_numeric
          (L := L) (K := K) hn (hs.afterPhi G h hh) (ht.afterPhi G h hh)
      afterMass := by
        intro G h hh
        exact window_of_static_tiny_numeric
          (L := L) (K := K) hn (hs.afterMass G h hh) (ht.afterMass G h hh) }

/-- The Window-failure branch from `Slot3LeafTailDischarge` is empty under the
same numeric facts needed by the leaf readout. -/
theorem not_windowFailure_of_numeric
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (hn : LeafNumericFacts (L := L) (K := K) D θ C) :
    ¬ windowFailure (L := L) (K := K) D C θ tr := by
  intro hwf
  exact hwf.2.2 (leafWindowGood_of_static_strict_numeric
    (L := L) (K := K) hn hwf.1 hwf.2.1)

/-- The trace-level Window-failure tail is zero.  This replaces the earlier
`negPhiDeviation` probabilistic residual for the leaf-tail branch. -/
theorem window_tail_zero
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    (hn : LeafNumericFacts (L := L) (K := K) D θ C) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr |
        Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
        windowFailure (L := L) (K := K) D C θ tr} ≤ 0 := by
  let S : Set (Phase3GoodClock.Trace L K) :=
    {tr |
      Phase3GoodClockRegime.GoodClockUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
      windowFailure (L := L) (K := K) D C θ tr}
  have hsub : S ⊆ (∅ : Set (Phase3GoodClock.Trace L K)) := by
    intro tr htr
    exact False.elim (not_windowFailure_of_numeric (L := L) (K := K) hn htr.2)
  calc
    ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr |
          Phase3GoodClockRegime.GoodClockUpTo
            (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
          windowFailure (L := L) (K := K) D C θ tr}
        = ProtocolTraceLaw.μ (L := L) (K := K) entry S := by rfl
    _ ≤ ProtocolTraceLaw.μ (L := L) (K := K) entry
          (∅ : Set (Phase3GoodClock.Trace L K)) :=
      measure_mono hsub
    _ = 0 := by simp

/-- Leaf-tail wrapper with the Window/`negPhi` branch discharged to zero. -/
theorem leaf_tail_of_det_tail
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    {C : ℝ} {εdet εleaf : ℝ≥0∞}
    (hn : LeafNumericFacts (L := L) (K := K) D θ C)
    (hdet :
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr |
          Phase3GoodClockRegime.GoodClockUpTo
            (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
          deterministicCutFailure (L := L) (K := K) D C θ tr} ≤ εdet)
    (hbudget : εdet ≤ εleaf) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr |
        Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
        ¬ Slot3LeafGood (L := L) (K := K) D θ tr} ≤ εleaf := by
  refine leaf_tail_of_det_and_window_tails
    (L := L) (K := K) hn hdet (window_tail_zero (L := L) (K := K) hn) ?_
  simpa using hbudget

#print axioms window_of_static_tiny_numeric
#print axioms leafWindowGood_of_static_strict_numeric
#print axioms not_windowFailure_of_numeric
#print axioms window_tail_zero
#print axioms leaf_tail_of_det_tail

end Slot3WindowNegPhiTail
end Phase3Assembly
end ExactMajority
