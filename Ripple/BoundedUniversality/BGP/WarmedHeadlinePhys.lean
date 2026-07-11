/-
Ripple.BoundedUniversality.BGP.WarmedHeadlinePhys
-----------------------------
The warmed de-axiom headline RETARGETED onto the REAL off-phase phase schedule
`bgpSchedulePhys` (= the `selectorSchedule` geometry), replacing the PLACEHOLDER
`bgpSchedule` (`FinalAssembly.lean:19`: `cycleStart j = j`, `zActiveWindow = univ`).

WHY THIS MATTERS (verified against the code, not a cosmetic swap):
Over the placeholder `bgpSchedule` the per-cycle window-hold premises
`hwindow_hold` / `hz_window_hold` (and `hflag_domain`) inside
`ContractTrackingInputs` are PROVABLY FALSE — `zActiveWindow = Set.univ` is not an
off-phase window, so `bGateU` / `bGateZ` are NOT suppressed on it (concrete
refutation: `j = 0`, `τ = 3π/2 ∈ univ`, gate `= 1`, `α τ > 1`, but the cycle-0
budget `K = exp 0 = 1`).  The retargeted schedule supplies a genuine off-phase
read band `[2πj + 5π/6, 2πj + 7π/6]` that STRADDLES the gate-zero midpoint
`2πj + π` (`sin` changes sign there): on `[5π/6, π]` `sin ≥ 0` (the U-off
sub-segment for `bGateU_le_offphase`), on `[π, 7π/6]` `sin ≤ 0` (the Z-off
sub-segment for `bGateZ_le_offphase`).  This turns the window-hold premises from
FALSE into SATISFIABLE — the prerequisite for discharging them via the banked
`hleak_of_pointwise_dynChi_cycle` (`DynChiLeak.lean`) + `contract_window_hold_of_ode`
(`InactiveLeakage.lean`).

The supply (`contract_raw_supply_of_polynomial_field_finitetime`) and the whole
assembly `main_assembled_dyn_contract_windexed_raw` are GENERIC in `sched`, so
the retarget is mechanically sound: the producer bundle is simply re-stated over
`bgpSchedulePhys` (and is now over a window on which it can be discharged, unlike
the placeholder).  Discharging the (now two-regime) window-hold producers is the
genuine remaining analytic work — see `WarmedProducerDischarge`.
-/

import Ripple.BoundedUniversality.BGP.WarmedHeadline

namespace Ripple.BoundedUniversality.BGP

open Ripple.BoundedUniversality.Core
open scoped BigOperators

noncomputable section

open MachineInstance

/-- The REAL off-phase phase schedule for the warmed contract route: `2π`-periodic
cycles aligned with the `sin`/`cos` gate clock, with the satisfiable stable read
band `[2πj + 5π/6, 2πj + 7π/6]` (NOT `Set.univ`).  Geometry identical to
`SelectorField.selectorSchedule`; copied here as a lightweight leaf so the warmed
contract route does not import the heavy selector machinery. -/
def bgpSchedulePhys : PhaseSchedule where
  domain := Set.Ici 0
  cycleStart := fun j => 2 * Real.pi * (j : ℝ)
  cycleMid := fun j => 2 * Real.pi * (j : ℝ) + Real.pi
  cycleEnd := fun j => 2 * Real.pi * ((j : ℝ) + 1)
  zActiveWindow := fun j => Set.Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
    (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6)
  stableWindow_subset_zActiveWindow := fun _ => subset_refl _
  cycleEnd_start_next := fun j => by push_cast; ring

/-- `bgpSchedulePhys.domain = Set.Ici 0`, so membership is just `0 ≤ t`. -/
theorem bgpSchedulePhys_domain_nonneg :
    ∀ t : ℝ, t ∈ bgpSchedulePhys.domain → 0 ≤ t := fun _ ht => ht

/-- The U-off sub-segment of cycle `j`'s read band: `sin ≥ 0` on
`[2πj + 5π/6, 2πj + π]` (the first half, where `bGateU` is suppressed). -/
theorem bgpSchedulePhys_Uoff (j : ℕ) {t : ℝ}
    (h1 : 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6 ≤ t)
    (h2 : t ≤ 2 * Real.pi * (j : ℝ) + Real.pi) :
    0 ≤ Real.sin t :=
  sin_window_nonneg j (by have := Real.pi_pos; linarith) (by linarith)

/-- The Z-off sub-segment of cycle `j`'s read band: `sin ≤ 0` on
`[2πj + π, 2πj + 7π/6]` (the second half, where `bGateZ` is suppressed). -/
theorem bgpSchedulePhys_Zoff (j : ℕ) {t : ℝ}
    (h1 : 2 * Real.pi * (j : ℝ) + Real.pi ≤ t)
    (h2 : t ≤ 2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6) :
    Real.sin t ≤ 0 :=
  sin_window_nonpos j (by linarith) (by have := Real.pi_pos; linarith)

/-- **Warmed de-axiom headline over the REAL off-phase schedule.**  Identical to
`bgp_unconditional_warmed` but instantiated at `bgpSchedulePhys` instead of the
placeholder `bgpSchedule`, so the carried window-hold / flag-domain producers are
stated over the genuine off-phase read band and are therefore SATISFIABLE. -/
theorem bgp_unconditional_warmed_phys
    (S : RobustStepContract
      UniversalMachine.undecidableMachine.toDiscreteMachine stackMachineEncodingU)
    {K : ℝ} {R : ℕ} (hK : 0 < K)
    (κ χ : ℕ → ℕ → ℝ) (rLE : Fin d_U → ℝ) (amp : ℕ → ℕ → Fin d_U → ℝ)
    (η : ℕ →
      DynContractIteratorSol (Fin d_U) bgpParams38 bgpSchedulePhys S.F →
      ℕ → Fin d_U → ℝ)
    (W : ℕ → ℕ → Fin d_U → ℝ) (depth : ℕ → ℕ → Fin d_U → ℤ)
    (hsupply :
      ∀ w : ℕ, ∃ _sol :
        DynContractIteratorSol (Fin d_U) bgpParams38 bgpSchedulePhys S.F, True)
    (htracking_inputs :
      ∀ (w : ℕ)
        (sol : DynContractIteratorSol (Fin d_U) bgpParams38 bgpSchedulePhys S.F),
        ContractTrackingInputs S bgpParams38 bgpSchedulePhys sol
          (fun j => UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
            (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
          (κ w) (χ w) rLE (amp w) (η w sol) (W w) (depth w)
          (trueMovingBox (d := d_U)) haltCoordU)
    (hlatch :
      ∀ sol : DynContractIteratorSol (Fin d_U) bgpParams38 bgpSchedulePhys S.F,
        ∃ La : ContractHaltLatchSol sol contractFlagIndicatorPackageU_ramp.Hval K R,
          ContractLatchConvergenceKernel sol haltCoordU contractFlagIndicatorPackageU_ramp La)
    (hflag_margin_all :
      ∀ w sol j, η w sol j haltCoordU ≤ haltFlagPackageU.flagMargin)
    (hflag_margin_indicator : haltFlagPackageU.flagMargin ≤ 1 / 4)
    (hflag_domain :
      ∀ (w : ℕ)
        (sol : DynContractIteratorSol (Fin d_U) bgpParams38 bgpSchedulePhys S.F),
        ∀ j t, t ∈ bgpSchedulePhys.zActiveWindow j →
          sol.z t haltCoordU ∈ Set.Icc (0 : ℝ) 1)
    (fieldPkg :
      ContractPolynomialFieldPackage UniversalMachine.undecidableMachine
        stackMachineEncodingU S
        bgpParams38 bgpSchedulePhys haltCoordU contractFlagIndicatorPackageU_ramp K R) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  main_assembled_dyn_contract_windexed_raw
    UniversalMachine.undecidableMachine stackMachineEncodingU S
    bgpParams38 bgpSchedulePhys haltCoordU haltFlagPackageU
    contractFlagIndicatorPackageU_ramp hK
    κ χ rLE amp η W depth hsupply htracking_inputs hlatch
    hflag_margin_all hflag_margin_indicator hflag_domain fieldPkg

/-- **Warmed physical headline with rich, solution-specific producer data.**

For each input, the supplied ODE solution carries the tracking inputs, latch
kernel, flag-margin bound, and flag-domain invariant.  This is the satisfiable
interface for finite-horizon ODE producers; it avoids asking those facts for
arbitrary solutions of the same field.
-/
theorem bgp_unconditional_warmed_phys_rich_supply
    (S : RobustStepContract
      UniversalMachine.undecidableMachine.toDiscreteMachine stackMachineEncodingU)
    {K : ℝ} {R : ℕ} (hK : 0 < K)
    (κ χ : ℕ → ℕ → ℝ) (rLE : Fin d_U → ℝ) (amp : ℕ → ℕ → Fin d_U → ℝ)
    (η : ℕ →
      DynContractIteratorSol (Fin d_U) bgpParams38 bgpSchedulePhys S.F →
      ℕ → Fin d_U → ℝ)
    (W : ℕ → ℕ → Fin d_U → ℝ) (depth : ℕ → ℕ → Fin d_U → ℤ)
    (hsupply_rich :
      ∀ w : ℕ,
        ∃ sol : DynContractIteratorSol (Fin d_U) bgpParams38 bgpSchedulePhys S.F,
          ContractTrackingInputs S bgpParams38 bgpSchedulePhys sol
            (fun j => UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
              (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
            (κ w) (χ w) rLE (amp w) (η w sol) (W w) (depth w)
            (trueMovingBox (d := d_U)) haltCoordU ∧
          (∃ La : ContractHaltLatchSol sol contractFlagIndicatorPackageU_ramp.Hval K R,
            ContractLatchConvergenceKernel sol haltCoordU contractFlagIndicatorPackageU_ramp La) ∧
          (∀ j, η w sol j haltCoordU ≤ haltFlagPackageU.flagMargin) ∧
          (∀ j t, t ∈ bgpSchedulePhys.zActiveWindow j →
            sol.z t haltCoordU ∈ Set.Icc (0 : ℝ) 1))
    (hflag_margin_indicator : haltFlagPackageU.flagMargin ≤ 1 / 4)
    (fieldPkg :
      ContractPolynomialFieldPackage UniversalMachine.undecidableMachine
        stackMachineEncodingU S
        bgpParams38 bgpSchedulePhys haltCoordU contractFlagIndicatorPackageU_ramp K R) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  main_assembled_dyn_contract_windexed_raw_rich_supply
    UniversalMachine.undecidableMachine stackMachineEncodingU S
    bgpParams38 bgpSchedulePhys haltCoordU haltFlagPackageU
    contractFlagIndicatorPackageU_ramp hK
    κ χ rLE amp η W depth hsupply_rich hflag_margin_indicator fieldPkg

#print axioms bgp_unconditional_warmed_phys_rich_supply

end

end Ripple.BoundedUniversality.BGP
