import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase3Bridges
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Lemma615MassAboveDefs
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Lemma616TotalMass
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Lemma617Minority
import Mathlib.Tactic

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Real

namespace Phase3Engines

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

local instance instOptionMSPhase3Engines :
    MeasurableSpace (Option (Phase3Core.Omega L K)) := ⊤

local instance instOptionDMSPhase3Engines :
    DiscreteMeasurableSpace (Option (Phase3Core.Omega L K)) :=
  ⟨fun _ => trivial⟩

/-!
Slot-3 piece 7: engine-to-Core producer layer.

The landed 6.15/6.16/6.17 engines are kernel-level engines.  The Core scaffold
uses the GoodClock/hour killed-kernel shape from `Phase3Core.stoppedTail`.
This file therefore keeps the remaining hour-support transfer obligations as
explicit fields and only wires them into `mkH15`/`mkH16`.

Inventory of the consumed engines:

* 6.15:
  this producer layer consumes the already-transported `muAbove` real-tail
  directly, keeping the numerical Azuma discharge outside the Core import
  closure.
* 6.16:
  `Lemma616TotalMass.perRow_totalMass_tail`
  (`Probability/Lemma616TotalMass.lean:80`) plus the same-exponent row variants
  and `Lemma616TotalMass.totalMass_le`
  (`Probability/Lemma616TotalMass.lean:179`).
* 6.17:
  `Lemma617Minority.perRow_cancelClock_tail`
  (`Probability/Lemma617Minority.lean:43`),
  `Lemma617Minority.perRow_minorityBad_tail`
  (`Probability/Lemma617Minority.lean:106`),
  `Lemma617Minority.perRow_minorityBad_tail_of_coeff_readout`
  (`Probability/Lemma617Minority.lean:161`), and
  `Lemma617Minority.minorityMass_le`
  (`Probability/Lemma617Minority.lean:275`).
* cancellation clock:
  `CancelClockConcentration.stoppedKernel`
  (`Probability/CancelClockConcentration.lean:51`) and
  `CancelClockConcentration.cancelClock_concentration_stoppedKernel_canonicalL`
  (`Probability/CancelClockConcentration.lean:623`), usually entered through
  `Phase3SameExpRect.perRow_cancelClock_tail_sameExp`
  (`Probability/Phase3SameExpRect.lean:311`).
-/

/-! ## Direct wrappers around landed engines -/

/-- 6.17 same-exponent per-row minority engine with an explicit majority
orientation `σ`.  This avoids the false WLOG-A orientation: the caller chooses
`σ = sign(g)` (or another explicit majority sign) and supplies row floors for
that orientation. -/
theorem h17_perRow_minorityBad_tail_sameExp_of_coeff_readout
    (σ : Sign) (idx : Fin (L + 1))
    (βminus : Config (AgentState L K) → ℝ)
    (C : Config (AgentState L K) → ℕ)
    (A0 B0 n D T h : ℕ) (b d leak ξ M : ℝ)
    (x0 : Config (AgentState L K))
    (hC0 : C x0 = 0)
    (hn : 2 ≤ n) (hD : D < B0) (hBA : B0 ≤ A0)
    (hqle :
      ∀ i : Fin D, CancelClockConcentration.twoSidedQ A0 B0 n D i ≤ 1)
    (hcard : ∀ x, C x < D → x.card = n)
    (hstep :
      ∀ x, C x < D →
        ∀ᵐ y ∂((NonuniformMajority L K).transitionKernel x),
          C y = C x ∨ C y = C x + 1)
    (hAfloor :
      ∀ x (_ : C x < D),
        ((A0 - C x : ℕ) : ℝ) ≤
          Phase3SameExpRect.majorityCount (L := L) (K := K) σ idx x)
    (hBfloor :
      ∀ x (_ : C x < D),
        ((B0 - C x : ℕ) : ℝ) ≤
          Phase3SameExpRect.minorityCount (L := L) (K := K) σ idx x)
    (hCinc :
      ∀ x (_ : C x < D),
        ∀ p ∈ Phase3SameExpRect.sameExpCancelPairs (L := L) (K := K) x σ idx,
          C ((NonuniformMajority L K).scheduledStep x p) = C x + 1)
    (hT :
      CancelClockConcentration.integratedInvRateClock D
        (CancelClockConcentration.twoSidedQ A0 B0 n D) D ≤ (T : ℝ))
    (hM : 0 ≤ M)
    (hcoeff : b - d + leak ≤ ξ)
    (hreadout :
      ∀ x, D ≤ C x →
        βminus x ≤ (b - d + leak) * M * (2 : ℝ) ^ (-(h : ℤ))) :
    (CancelClockConcentration.stoppedKernel
        (NonuniformMajority L K).transitionKernel C D ^ T) x0
        (Lemma617Minority.minorityBad βminus h ξ M)
      ≤ ENNReal.ofReal (Real.exp
          (-(((T : ℝ) -
              CancelClockConcentration.integratedInvRateClock D
                (CancelClockConcentration.twoSidedQ A0 B0 n D) D) ^ 2)
            / (2 * (T : ℝ) *
                (CancelClockConcentration.invRateSlack D
                  (CancelClockConcentration.twoSidedQ A0 B0 n D)) ^ 2))) := by
  refine Lemma617Minority.perRow_minorityBad_tail_of_coeff_readout
    (K := (NonuniformMajority L K).transitionKernel)
    (βminus := βminus) (C := C)
    (A := Phase3SameExpRect.majorityCount (L := L) (K := K) σ idx)
    (B := Phase3SameExpRect.minorityCount (L := L) (K := K) σ idx)
    (A0 := A0) (B0 := B0) (n := n) (D := D) (T := T) (h := h)
    (b := b) (d := d) (leak := leak) (ξ := ξ) (M := M) (x0 := x0)
    hC0 hn hD hBA hqle hstep hAfloor hBfloor ?_ hT hM hcoeff hreadout
  intro x hx
  exact Phase3SameExpRect.phase3_sameExp_cancelCount_step_ge
    (L := L) (K := K) σ idx C n x (hcard x hx) hn (hCinc x hx)

/-! ## Generic stopped-tail six-row union -/

theorem stoppedTail_sixUnion
    {G : Set (Phase3Core.Omega L K)} {t : ℕ}
    {x : Phase3Core.Omega L K}
    {Bad Row0 Row1 Row2 Row3 Row4 Row5 : Phase3Core.Omega L K → Prop}
    {ε0 ε1 ε2 ε3 ε4 ε5 ε : ℝ≥0∞}
    (hcover : ∀ c, Bad c →
      Lemma617Minority.sixUnion Row0 Row1 Row2 Row3 Row4 Row5 c)
    (h0 : Phase3Core.stoppedTail (L := L) (K := K) G t x Row0 ε0)
    (h1 : Phase3Core.stoppedTail (L := L) (K := K) G t x Row1 ε1)
    (h2 : Phase3Core.stoppedTail (L := L) (K := K) G t x Row2 ε2)
    (h3 : Phase3Core.stoppedTail (L := L) (K := K) G t x Row3 ε3)
    (h4 : Phase3Core.stoppedTail (L := L) (K := K) G t x Row4 ε4)
    (h5 : Phase3Core.stoppedTail (L := L) (K := K) G t x Row5 ε5)
    (hbudget : Lemma617Minority.sixSum ε0 ε1 ε2 ε3 ε4 ε5 ≤ ε) :
    Phase3Core.stoppedTail (L := L) (K := K) G t x Bad ε := by
  unfold Phase3Core.stoppedTail at h0 h1 h2 h3 h4 h5 ⊢
  have hsub :
      Phase3Core.killedBad Bad ⊆
        Lemma617Minority.sixUnion
          (Phase3Core.killedBad Row0) (Phase3Core.killedBad Row1)
          (Phase3Core.killedBad Row2) (Phase3Core.killedBad Row3)
          (Phase3Core.killedBad Row4) (Phase3Core.killedBad Row5) := by
    intro o ho
    rcases ho with hnone | ⟨c, rfl, hbad⟩
    · unfold Lemma617Minority.sixUnion
      exact Or.inl (Or.inl hnone)
    · have hc := hcover c hbad
      unfold Lemma617Minority.sixUnion at hc ⊢
      rcases hc with h0c | hrest
      · exact Or.inl (Or.inr ⟨c, rfl, h0c⟩)
      · rcases hrest with h1c | hrest
        · exact Or.inr (Or.inl (Or.inr ⟨c, rfl, h1c⟩))
        · rcases hrest with h2c | hrest
          · exact Or.inr (Or.inr (Or.inl (Or.inr ⟨c, rfl, h2c⟩)))
          · rcases hrest with h3c | hrest
            · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨c, rfl, h3c⟩))))
            · rcases hrest with h4c | h5c
              · exact Or.inr
                  (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨c, rfl, h4c⟩)))))
              · exact Or.inr
                  (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨c, rfl, h5c⟩)))))
  calc
    (GatedDrift.killK_now (Phase3Core.phase3Kernel L K) G ^ t) (some x)
        (Phase3Core.killedBad Bad)
        ≤ (GatedDrift.killK_now (Phase3Core.phase3Kernel L K) G ^ t) (some x)
            (Lemma617Minority.sixUnion
              (Phase3Core.killedBad Row0) (Phase3Core.killedBad Row1)
              (Phase3Core.killedBad Row2) (Phase3Core.killedBad Row3)
              (Phase3Core.killedBad Row4) (Phase3Core.killedBad Row5)) :=
          measure_mono hsub
    _ ≤ Lemma617Minority.sixSum
          ((GatedDrift.killK_now (Phase3Core.phase3Kernel L K) G ^ t) (some x)
            (Phase3Core.killedBad Row0))
          ((GatedDrift.killK_now (Phase3Core.phase3Kernel L K) G ^ t) (some x)
            (Phase3Core.killedBad Row1))
          ((GatedDrift.killK_now (Phase3Core.phase3Kernel L K) G ^ t) (some x)
            (Phase3Core.killedBad Row2))
          ((GatedDrift.killK_now (Phase3Core.phase3Kernel L K) G ^ t) (some x)
            (Phase3Core.killedBad Row3))
          ((GatedDrift.killK_now (Phase3Core.phase3Kernel L K) G ^ t) (some x)
            (Phase3Core.killedBad Row4))
          ((GatedDrift.killK_now (Phase3Core.phase3Kernel L K) G ^ t) (some x)
            (Phase3Core.killedBad Row5)) :=
          Lemma617Minority.measure_sixUnion_le _ _ _ _ _ _ _
    _ ≤ Lemma617Minority.sixSum ε0 ε1 ε2 ε3 ε4 ε5 := by
          unfold Lemma617Minority.sixSum
          exact add_le_add h0
            (add_le_add h1
              (add_le_add h2
                (add_le_add h3 (add_le_add h4 h5))))
    _ ≤ ε := hbudget

/-! ## H15 engine producer -/

/-- With the Core H15 surface aligned to Doty's mass-above readout, failure of
`PhiPotentialDrop` is exactly contained in the landed engine's bad event. -/
theorem Phi15CoreReadout
    (D : Phase3Core.Phase3ModeDomain L) (h : ℕ) (c : Phase3Core.Omega L K) :
    ¬ Phase3Core.PhiPotentialDrop (L := L) (K := K) D h c →
      Lemma615MassAbove.muAbove (L := L) (K := K) h c
        > Phase3Core.H15MassThreshold (L := L) D h := by
  intro hbad
  by_contra hnot
  have hle :
      Lemma615MassAbove.muAbove (L := L) (K := K) h c
        ≤ Phase3Core.H15MassThreshold (L := L) D h :=
    le_of_not_gt hnot
  exact hbad (by
    unfold Phase3Core.PhiPotentialDrop Phase3Core.PhiSmall Phase3Core.MassAboveSmall
    exact ⟨hle, hle⟩)

/-- Stopped H15 tails after the landed 6.15 engine has been transported to the
GoodClock hour gate.  The real-kernel Azuma tail controls alive bad states, while
`exit_tail` pays for the cemetery mass created by leaving the hour gate. -/
structure H15Engine {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3Core.Phase3ModeDomain L)
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr) where
  steps : ℕ → ℕ
  epsExit : ℕ → ℝ≥0∞
  epsMu : ℕ → ℝ≥0∞
  steps_eq : ∀ h, h ≤ D.lastCoreHour → 5 ≤ h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
      steps h =
        Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterO (L := L) (K := K) (T.clockInput h)
  eps_budget : ∀ h, h ≤ D.lastCoreHour → 5 ≤ h →
    epsExit h + epsMu h ≤ T.surface.eps15 h
  real_tail : ∀ h, h ≤ D.lastCoreHour → 5 ≤ h →
    Phase3Core.PrevCore (L := L) (K := K) D T h →
    Phase3Core.H13 (L := L) (K := K) D T h →
    Phase3Core.H14 (L := L) (K := K) D T h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    ∀ cO, cO ∈ T.surface.checkpoint .afterO h →
      (Phase3Core.phase3Kernel L K ^ steps h) cO
        {x | Lemma615MassAbove.muAbove (L := L) (K := K) h x
          > Phase3Core.H15MassThreshold (L := L) D h} ≤ epsMu h
  exit_tail : ∀ h, h ≤ D.lastCoreHour → 5 ≤ h →
    Phase3Core.PrevCore (L := L) (K := K) D T h →
    Phase3Core.H13 (L := L) (K := K) D T h →
    Phase3Core.H14 (L := L) (K := K) D T h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    ∀ cO, cO ∈ T.surface.checkpoint .afterO h →
      (GatedDrift.killK_now (Phase3Core.phase3Kernel L K) (T.surface.hourGate h) ^
          steps h)
        (some cO) {(none : Option (Phase3Core.Omega L K))} ≤ epsExit h

namespace H15Engine

noncomputable def mkH15 {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    (E : H15Engine (L := L) (K := K) D T) :
    ∀ h, h ≤ D.lastCoreHour → 5 ≤ h →
      Phase3Core.PrevCore (L := L) (K := K) D T h →
      Phase3Core.H13 (L := L) (K := K) D T h →
      Phase3Core.H14 (L := L) (K := K) D T h →
      Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
      Phase3Core.H15 (L := L) (K := K) D T h := by
  intro h hle h5 prev h13 h14 I
  refine ⟨hle, ?_⟩
  intro cO hcO
  let BadMu : Phase3Core.Omega L K → Prop := fun c =>
    Lemma615MassAbove.muAbove (L := L) (K := K) h c
      > Phase3Core.H15MassThreshold (L := L) D h
  have hreal :
      (Phase3Core.phase3Kernel L K ^ E.steps h) cO {y | BadMu y}
        ≤ E.epsMu h := by
    exact E.real_tail h hle h5 prev h13 h14 I cO hcO
  have hmu_steps :
      Phase3Core.stoppedTail (L := L) (K := K) (T.surface.hourGate h)
        (E.steps h) cO BadMu (E.epsExit h + E.epsMu h) := by
    exact Phase3Bridges.stoppedTail_of_real_tail_add_exit
      (L := L) (K := K)
      (G := T.surface.hourGate h) (t := E.steps h) (x := cO)
      (Bad := BadMu)
      (hexit := E.exit_tail h hle h5 prev h13 h14 I cO hcO)
      (hreal := hreal)
      (hbudget := le_rfl)
  have hmu :
      Phase3Core.stoppedTail (L := L) (K := K) (T.surface.hourGate h)
        (Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterO (L := L) (K := K) (T.clockInput h))
        cO BadMu (E.epsExit h + E.epsMu h) := by
    simpa [BadMu, E.steps_eq h hle h5 I] using hmu_steps
  have hcore :
      Phase3Core.stoppedTail (L := L) (K := K) (T.surface.hourGate h)
        (Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterO (L := L) (K := K) (T.clockInput h))
        cO
        (fun c => ¬ Phase3Core.PhiPotentialDrop (L := L) (K := K) D h c)
        (E.epsExit h + E.epsMu h) := by
    exact Phase3Bridges.stoppedTail_mono (L := L) (K := K)
      (Bad := fun c => ¬ Phase3Core.PhiPotentialDrop (L := L) (K := K) D h c)
      (Bad' := BadMu)
      (fun c hc => Phi15CoreReadout (L := L) (K := K) D h c hc)
      hmu
  exact hcore.trans (E.eps_budget h hle h5)

end H15Engine

/-! ## H16 engine producer -/

/-- Six stopped row tails for H16 after the 6.16 row clocks have been transported
to the GoodClock hour gate.

The row tails are deliberately not stated as global invariants.  They are the
remaining stopped-support obligations: same-exponent row floors, counter
support, cancellation readout, and hour-kill transfer from
`CancelClockConcentration.stoppedKernel` to the Core killed kernel. -/
structure H16Engine {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3Core.Phase3ModeDomain L)
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr) where
  Row0 : ℕ → Set (Phase3Core.Omega L K)
  Row1 : ℕ → Set (Phase3Core.Omega L K)
  Row2 : ℕ → Set (Phase3Core.Omega L K)
  Row3 : ℕ → Set (Phase3Core.Omega L K)
  Row4 : ℕ → Set (Phase3Core.Omega L K)
  Row5 : ℕ → Set (Phase3Core.Omega L K)
  eps0 : ℕ → ℝ≥0∞
  eps1 : ℕ → ℝ≥0∞
  eps2 : ℕ → ℝ≥0∞
  eps3 : ℕ → ℝ≥0∞
  eps4 : ℕ → ℝ≥0∞
  eps5 : ℕ → ℝ≥0∞
  cover : ∀ h, h ≤ D.lastCoreHour → 0 < h →
    Phase3Core.PrevCore (L := L) (K := K) D T h →
    Phase3Core.H15 (L := L) (K := K) D T h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    ∀ c, ¬ Phase3Core.TotalMassBound (L := L) (K := K) D h c →
      Lemma617Minority.sixUnion (Row0 h) (Row1 h) (Row2 h)
        (Row3 h) (Row4 h) (Row5 h) c
  eps_budget : ∀ h, h ≤ D.lastCoreHour → 0 < h →
    Lemma617Minority.sixSum
      (eps0 h) (eps1 h) (eps2 h) (eps3 h) (eps4 h) (eps5 h) ≤
        T.surface.eps16 h
  tail0 : ∀ h, h ≤ D.lastCoreHour → 0 < h →
    Phase3Core.PrevCore (L := L) (K := K) D T h →
    Phase3Core.H15 (L := L) (K := K) D T h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    ∀ cPhi, cPhi ∈ T.surface.checkpoint .afterPhi h →
    ∀ dt,
      Phase3Core.ClockCut.afterMass (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) ≤ dt →
      dt ≤
          Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput h) -
            Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) →
      Phase3Core.stoppedTail (L := L) (K := K) (T.surface.hourGate h) dt cPhi
        (Row0 h) (eps0 h)
  tail1 : ∀ h, h ≤ D.lastCoreHour → 0 < h →
    Phase3Core.PrevCore (L := L) (K := K) D T h →
    Phase3Core.H15 (L := L) (K := K) D T h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    ∀ cPhi, cPhi ∈ T.surface.checkpoint .afterPhi h →
    ∀ dt,
      Phase3Core.ClockCut.afterMass (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) ≤ dt →
      dt ≤
          Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput h) -
            Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) →
      Phase3Core.stoppedTail (L := L) (K := K) (T.surface.hourGate h) dt cPhi
        (Row1 h) (eps1 h)
  tail2 : ∀ h, h ≤ D.lastCoreHour → 0 < h →
    Phase3Core.PrevCore (L := L) (K := K) D T h →
    Phase3Core.H15 (L := L) (K := K) D T h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    ∀ cPhi, cPhi ∈ T.surface.checkpoint .afterPhi h →
    ∀ dt,
      Phase3Core.ClockCut.afterMass (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) ≤ dt →
      dt ≤
          Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput h) -
            Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) →
      Phase3Core.stoppedTail (L := L) (K := K) (T.surface.hourGate h) dt cPhi
        (Row2 h) (eps2 h)
  tail3 : ∀ h, h ≤ D.lastCoreHour → 0 < h →
    Phase3Core.PrevCore (L := L) (K := K) D T h →
    Phase3Core.H15 (L := L) (K := K) D T h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    ∀ cPhi, cPhi ∈ T.surface.checkpoint .afterPhi h →
    ∀ dt,
      Phase3Core.ClockCut.afterMass (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) ≤ dt →
      dt ≤
          Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput h) -
            Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) →
      Phase3Core.stoppedTail (L := L) (K := K) (T.surface.hourGate h) dt cPhi
        (Row3 h) (eps3 h)
  tail4 : ∀ h, h ≤ D.lastCoreHour → 0 < h →
    Phase3Core.PrevCore (L := L) (K := K) D T h →
    Phase3Core.H15 (L := L) (K := K) D T h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    ∀ cPhi, cPhi ∈ T.surface.checkpoint .afterPhi h →
    ∀ dt,
      Phase3Core.ClockCut.afterMass (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) ≤ dt →
      dt ≤
          Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput h) -
            Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) →
      Phase3Core.stoppedTail (L := L) (K := K) (T.surface.hourGate h) dt cPhi
        (Row4 h) (eps4 h)
  tail5 : ∀ h, h ≤ D.lastCoreHour → 0 < h →
    Phase3Core.PrevCore (L := L) (K := K) D T h →
    Phase3Core.H15 (L := L) (K := K) D T h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    ∀ cPhi, cPhi ∈ T.surface.checkpoint .afterPhi h →
    ∀ dt,
      Phase3Core.ClockCut.afterMass (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) ≤ dt →
      dt ≤
          Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput h) -
            Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) →
      Phase3Core.stoppedTail (L := L) (K := K) (T.surface.hourGate h) dt cPhi
        (Row5 h) (eps5 h)

namespace H16Engine

noncomputable def mkH16 {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    (E : H16Engine (L := L) (K := K) D T) :
    ∀ h, h ≤ D.lastCoreHour → 0 < h →
      Phase3Core.PrevCore (L := L) (K := K) D T h →
      Phase3Core.H15 (L := L) (K := K) D T h →
      Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
      Phase3Core.H16 (L := L) (K := K) D T h := by
  intro h hle hpos prev h15 I
  refine ⟨hle, ?_⟩
  intro cPhi hcPhi dt hdtlo hdthi
  exact stoppedTail_sixUnion (L := L) (K := K)
    (Bad := fun c => ¬ Phase3Core.TotalMassBound (L := L) (K := K) D h c)
    (Row0 := E.Row0 h) (Row1 := E.Row1 h) (Row2 := E.Row2 h)
    (Row3 := E.Row3 h) (Row4 := E.Row4 h) (Row5 := E.Row5 h)
    (hcover := E.cover h hle hpos prev h15 I)
    (h0 := E.tail0 h hle hpos prev h15 I cPhi hcPhi dt hdtlo hdthi)
    (h1 := E.tail1 h hle hpos prev h15 I cPhi hcPhi dt hdtlo hdthi)
    (h2 := E.tail2 h hle hpos prev h15 I cPhi hcPhi dt hdtlo hdthi)
    (h3 := E.tail3 h hle hpos prev h15 I cPhi hcPhi dt hdtlo hdthi)
    (h4 := E.tail4 h hle hpos prev h15 I cPhi hcPhi dt hdtlo hdthi)
    (h5 := E.tail5 h hle hpos prev h15 I cPhi hcPhi dt hdtlo hdthi)
    (hbudget := E.eps_budget h hle hpos)

end H16Engine

/-! ## Core producer package -/

/-- Core producers with H13/H14 supplied by the bridge layer and H15/H16
supplied by the stopped engine layer above. -/
structure CoreEngineProducers {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3Core.Phase3ModeDomain L)
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr) where
  pre3 : Phase3Core.Pre3Seed (L := L) (K := K) D T
  h13 : Phase3Bridges.H13Bridge (L := L) (K := K) D T
  h14 : Phase3Bridges.H14Bridge (L := L) (K := K) D T
  h15 : H15Engine (L := L) (K := K) D T
  h16 : H16Engine (L := L) (K := K) D T

namespace CoreEngineProducers

noncomputable def toCoreBridgeProducers {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    (P : CoreEngineProducers (L := L) (K := K) D T) :
    Phase3Bridges.CoreBridgeProducers (L := L) (K := K) D T where
  pre3 := P.pre3
  h13 := P.h13
  h14 := P.h14
  mkH15 := P.h15.mkH15
  mkH16 := P.h16.mkH16

noncomputable def toCoreProducers {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    (P : CoreEngineProducers (L := L) (K := K) D T) :
    Phase3Core.CoreProducers (L := L) (K := K) D T :=
  P.toCoreBridgeProducers.toCoreProducers

end CoreEngineProducers

#print axioms Phi15CoreReadout
#print axioms h17_perRow_minorityBad_tail_sameExp_of_coeff_readout
#print axioms stoppedTail_sixUnion
#print axioms H15Engine.mkH15
#print axioms H16Engine.mkH16
#print axioms CoreEngineProducers.toCoreProducers

end Phase3Engines

end ExactMajority
