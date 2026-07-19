import Ripple.BoundedUniversality.BGP.SelectorFaithfulCapstone
import Ripple.BoundedUniversality.BGP.FlagHmixConstant
import Ripple.BoundedUniversality.BGP.SelectorReplicatorSettledResidual
import Ripple.BoundedUniversality.BGP.EventualTracking
import Ripple.BoundedUniversality.BGP.HeadlineUnconditional

/-!
# Faithful-tube to headline wire

This file keeps the new route separate from the analytic producers in
`HeadlineUnconditional`.  The main bridge is intentionally thin: once the
faithful tube has supplied a generic settled concentration rate, an honest
`hoff` field cap, and the hold-frozen next-start residual, the existing
rate-shaped settled residual interface constructs late-start facts, which are
then weakened to the eventual interface consumed by the headline.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Filter Set MachineInstance UniversalMachine
open scoped BigOperators Topology

/-- Halt-coordinate mix accuracy at the faithful gate-hold sample from the
one-hot concentration shape exposed by the faithful tube. -/
theorem selectorMixTarget_halt_at_gateHold_of_concentration
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38
      selectorSchedule branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (cfg : ℕ → UConf) (epsLam : ℕ → ℝ)
    (hcfg_step : ∀ j, cfg (j + 1) = M_U.step (cfg j))
    (hepsLam_nonneg : ∀ j, 0 ≤ epsLam j)
    (hsum_hold : ∀ j,
      (∑ v : UniversalLocalView, sol.lam v (selectorGateMixHold j)) = 1)
    (hlam_nonneg_hold : ∀ j, ∀ v : UniversalLocalView,
      0 ≤ sol.lam v (selectorGateMixHold j))
    (hwrong_hold : ∀ j, ∀ v : UniversalLocalView,
      v ≠ localViewU (cfg j) → sol.lam v (selectorGateMixHold j) ≤ epsLam j) :
    ∀ j,
      |selectorMixTarget branchU sol.u sol.lam (selectorGateMixHold j) haltCoordU -
        stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU| ≤
          (Fintype.card UniversalLocalView : ℝ) * epsLam j := by
  intro j
  have hmix :=
    selectorMixTarget_halt_to_next_of_concentration
      sol.u sol.lam (selectorGateMixHold j) (cfg j)
      (hepsLam_nonneg j) (hsum_hold j) (hlam_nonneg_hold j)
      (hwrong_hold j)
  simpa [hcfg_step j] using hmix

namespace EventualLateStartHaltFactsAt

/-- All-word late-start halt facts, restricted to one input, imply the weaker
tail-only eventual interface with threshold `0`. -/
def ofLateStartHaltFacts
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (late : MUReplicatorLateStartHaltFacts sol) (w : ℕ) :
    EventualLateStartHaltFactsAt sol w where
  cfg := late.cfg w
  hcfg := late.hcfg w
  N := 0
  Bz_read := late.readStart.Bz_read w
  hz_read_start := by
    intro j _hj
    have hread := late.readStart.hz_read_start w j
    simpa [selectorMUInterReadStart, selectorMUWriteReadTime, late.hcfg w (j + 1)]
      using hread
  hBz_read_tendsto := late.readStart.hBz_read_tendsto w
  hBz_read_nonneg := late.readStart.hBz_read_nonneg w
  δnext := late.δnext w
  hδnext := late.hδnext w
  hδnext_nonneg := late.hδnext_nonneg w
  hoff := by
    intro j _hj henc t ht
    exact late.hoff w j henc t ht
  hnextWrite := by
    intro j _hj t ht
    exact late.hnextWrite w j t ht

end EventualLateStartHaltFactsAt

/-- The residual bundle expected from the faithful tube route for one warm-gain
headline family.  Its concentration-rate field is the point where the
faithful self-consistent tube is meant to enter the settled/read-start
pipeline. -/
abbrev FaithfulHeadlineResidual (wg : ℕ) :=
  MUReplicatorSettledHaltThinRateFieldCapHoldStableStartResiduals
    (bgpHeadlineSolFam wg)

/-- Convert faithful-route residuals into the eventual late-start facts consumed
by `bgp_headline_unconditional_of_eventual_late_start`. -/
def bgpHeadlineEventualLateStartFromFaithfulResidual
    (res : ∀ wg, FaithfulHeadlineResidual wg) :
    ∀ wg, EventualLateStartHaltFactsAt (bgpHeadlineSolFam wg) wg := by
  intro wg
  exact
    EventualLateStartHaltFactsAt.ofLateStartHaltFacts
      ((res wg).toLateStartHaltFacts (bgpHeadlineBoxInputs wg)) wg

/-- Headline wire for the faithful-tube route, after the faithful residual
producer has supplied the rate-shaped settled residual bundle. -/
theorem bgp_headline_via_faithful_tube
    (res : ∀ wg, FaithfulHeadlineResidual wg) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P undecidableMachine) :=
  bgp_headline_unconditional_of_eventual_late_start
    (bgpHeadlineEventualLateStartFromFaithfulResidual res)

end Ripple.BoundedUniversality.BGP
