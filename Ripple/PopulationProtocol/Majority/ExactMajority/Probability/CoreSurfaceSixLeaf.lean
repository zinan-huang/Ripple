import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase3Assembly

/-!
# `CoreSurfaceSixLeaf` — the irreducible Doty-§6 facts behind the Core surface.

`Phase3Assembly.CoreSurfacePredicateFacts` is the residual that `mkSurface` turns
into a concrete `CoreRunSurface`.  Most of its ~15 fields are plumbing (the gate /
trace-cut sets and the checkpoint design).  This file isolates the genuine §6
content into a small leaf and discharges all the plumbing concretely:

* `gatePred h := { c | TinyBeforeEnd θ h c }`  — so `hourGate_clock_tiny` is the
  second projection of `predicateHourGate` membership.
* `traceCut _ _ := Set.univ`  — so every `trace_*_mem_traceCut` is `Set.mem_univ`.
  (The checkpoint's trace arm becomes `True`; the floor arm `coreCutInvariant`
  still distinguishes the cuts, used by the existing `mem_after*_of_gate_of_floors`
  chain helpers.)

What is left in the leaf are exactly the irreducible §6 obligations:
`regime_after{O,Phi,Mass}` (the trace point sits in the stopped Main regime at the
cut time — Lemma 6.10 / HourWindow preservation, for good traces), `tiny_after*`
(clock-front tininess at the cut time — from the GoodClock front data), and the
clock-side constant-arithmetic fact `clock_tiny_frac`.  The Main-side fraction
fact is the definitional theorem `Phase3Core.main_not_tiny_frac` from the
M-scale threshold.

No `sorry` / `admit` / `axiom` / `native_decide`.
-/

namespace ExactMajority
namespace Phase3Assembly

open Phase3Core Phase3GoodClock
open scoped ENNReal NNReal BigOperators Real

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- The irreducible §6 facts the Core predicate surface needs, separated from the
gate / checkpoint plumbing. -/
structure CoreSurfaceSixLeaf
    (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) where
  leakageC : ℝ
  leakageC_pos : 0 < leakageC
  leakageK_pos : 0 < K
  /-- Main structural concentration at the `afterO` cut (Lemma 6.10 + HourWindow). -/
  regime_afterO :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      let I := Phase3GoodClock.CoreClockInputs.ofGoodClock
        (L := L) (K := K) D.M h G
      tr (I.start + θ.twoOverC) ∈
        Lemma610StoppedAzuma.regimeSet (L := L) (K := K) (D.M : ℝ) leakageC h
  regime_afterPhi :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      let I := Phase3GoodClock.CoreClockInputs.ofGoodClock
        (L := L) (K := K) D.M h G
      tr (I.start + θ.twoOverC + θ.fortyOneOverM) ∈
        Lemma610StoppedAzuma.regimeSet (L := L) (K := K) (D.M : ℝ) leakageC h
  regime_afterMass :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      let I := Phase3GoodClock.CoreClockInputs.ofGoodClock
        (L := L) (K := K) D.M h G
      tr (I.start + θ.twoOverC + θ.fortySevenOverM) ∈
        Lemma610StoppedAzuma.regimeSet (L := L) (K := K) (D.M : ℝ) leakageC h
  /-- Clock-front tininess at the `afterO` cut. -/
  tiny_afterO :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      let I := Phase3GoodClock.CoreClockInputs.ofGoodClock
        (L := L) (K := K) D.M h G
      Phase3GoodClock.TinyBeforeEnd (L := L) (K := K) θ h
        (tr (I.start + θ.twoOverC))
  tiny_afterPhi :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      let I := Phase3GoodClock.CoreClockInputs.ofGoodClock
        (L := L) (K := K) D.M h G
      Phase3GoodClock.TinyBeforeEnd (L := L) (K := K) θ h
        (tr (I.start + θ.twoOverC + θ.fortyOneOverM))
  tiny_afterMass :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      let I := Phase3GoodClock.CoreClockInputs.ofGoodClock
        (L := L) (K := K) D.M h G
      Phase3GoodClock.TinyBeforeEnd (L := L) (K := K) θ h
        (tr (I.start + θ.twoOverC + θ.fortySevenOverM))
  spanGate : ℕ → ℕ → Set (Phase3Core.Omega L K)
  clock_tiny_frac : ∀ h c,
    Phase3GoodClock.TinyBeforeEnd (L := L) (K := K) θ h c →
      (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) / leakageC ≤
        (1 / 1000 : ℝ)
  eps13 : ℕ → ℝ≥0∞
  eps14 : ℕ → ℝ≥0∞
  eps15 : ℕ → ℝ≥0∞
  eps16 : ℕ → ℝ≥0∞

namespace CoreSurfaceSixLeaf

/-- The concrete gate predicate: clock-front tininess. -/
def gatePred
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (_S : CoreSurfaceSixLeaf (L := L) (K := K) D θ tr)
    (h : ℕ) : Set (Phase3Core.Omega L K) :=
  {c | Phase3GoodClock.TinyBeforeEnd (L := L) (K := K) θ h c}

/-- Assemble the §6 leaf into the full predicate-facts surface, discharging all
the gate / trace-cut plumbing. -/
noncomputable def toFacts
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (S : CoreSurfaceSixLeaf (L := L) (K := K) D θ tr) :
    CoreSurfacePredicateFacts (L := L) (K := K) D θ tr where
  leakageC := S.leakageC
  leakageC_pos := S.leakageC_pos
  leakageK_pos := S.leakageK_pos
  gatePred := S.gatePred
  spanGate := S.spanGate
  traceCut := fun _ _ => Set.univ
  trace_afterO_mem_gate := by
    intro G h hh
    exact ⟨S.regime_afterO G h hh, S.tiny_afterO G h hh⟩
  trace_afterO_mem_traceCut := by
    intro G h hh; exact Set.mem_univ _
  trace_afterPhi_mem_gate := by
    intro G h hh
    exact ⟨S.regime_afterPhi G h hh, S.tiny_afterPhi G h hh⟩
  trace_afterPhi_mem_traceCut := by
    intro G h hh; exact Set.mem_univ _
  trace_afterMass_mem_gate := by
    intro G h hh
    exact ⟨S.regime_afterMass G h hh, S.tiny_afterMass G h hh⟩
  trace_afterMass_mem_traceCut := by
    intro G h hh; exact Set.mem_univ _
  hourGate_clock_tiny := by
    intro h _hh c hc
    exact hc.2
  clockTiny_frac := S.clock_tiny_frac
  eps13 := S.eps13
  eps14 := S.eps14
  eps15 := S.eps15
  eps16 := S.eps16

/-- End-to-end surface supply: a §6 leaf plus a `GoodClockUpTo` witness yields a
concrete `CoreRunSurface`.  This is the surface half of the slot-3 closure: once
the leaf is paid (its facts are the §6 good-trace event), `surfaceOf` is the
`CoreRunSurface` consumed by the Core producers / chain. -/
noncomputable def surfaceOf
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (S : CoreSurfaceSixLeaf (L := L) (K := K) D θ tr)
    (G : Phase3GoodClockRegime.GoodClockUpTo
      (L := L) (K := K) D.M θ tr D.lastCoreHour) :
    Phase3Core.CoreRunSurface (L := L) (K := K) D θ tr :=
  CoreSurfacePredicateFacts.mkSurface (L := L) (K := K) G S.toFacts

/-- The §6 good-event leaf plus a `GoodClockUpTo` witness the range-local
`GoodCoreThreadTrace` event — the event whose complement the slot-3 trace
residual bounds.  Contrapositive: `¬ GoodCoreThreadTrace → ¬(GoodClockUpTo ∧
leaf)`, i.e. the bad-trace set is covered by the clock-tail set together with the
§6 leaf-failure set (paid by Lemma 6.10 + the clock front whp). -/
theorem goodCoreThreadTrace_of
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (S : CoreSurfaceSixLeaf (L := L) (K := K) D θ tr)
    (G : Phase3GoodClockRegime.GoodClockUpTo
      (L := L) (K := K) D.M θ tr D.lastCoreHour) :
    GoodCoreThreadTrace (L := L) (K := K) D θ tr :=
  ⟨{ good := G, surface := S.surfaceOf G }, trivial⟩

end CoreSurfaceSixLeaf

end Phase3Assembly
end ExactMajority

#print axioms ExactMajority.Phase3Assembly.CoreSurfaceSixLeaf.toFacts
#print axioms ExactMajority.Phase3Assembly.CoreSurfaceSixLeaf.surfaceOf
#print axioms ExactMajority.Phase3Assembly.CoreSurfaceSixLeaf.goodCoreThreadTrace_of
