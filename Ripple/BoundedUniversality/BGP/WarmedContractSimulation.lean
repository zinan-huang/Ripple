/-
Ripple.BoundedUniversality.BGP.WarmedContractSimulation
-------------------------
The warmed de-axiom headline (capstone): the box-free windexed assembly
`main_assembled_dyn_contract_windexed_noBox` instantiated for the universal machine
M_U with the continuous polynomial halt indicator (`contractFlagIndicatorPackageU_ramp`)
and the strict-cascade clock parameters `bgpParamsBase` (cα = 3/8, off the κ wall).

This reduces
  `∃ P : PIVP ℚ, Nonempty (EventualThresholdSimulation P undecidableMachine)`
to exactly the banked producer bundle (raw supply, the warmed tracking inputs,
the latch, the flag domain, and the contract field package) — NO axiom, NO
`ContractPerCycleBox`.  Each carried hypothesis has a banked discharge:
- `hsupply` ← `contract_noBox_supply_of_polynomial_field_finitetime` (+ `contract_finiteHorizonBound_MU_N`),
- `htracking_inputs` ← `contract_tracking_hypotheses_assemble_with_schedules_noBox` (+ the field producers / WarmWeightedStepWiring),
- `hlatch` ← `contract_latch_high/low` + `contractFlagIndicatorPackageU_ramp_Hcont`,
- `fieldPkg` ← `contractPolynomialFieldPackage` with `FP_MU_N` + `haltFlagIndicatorPolyU_ramp`.

Stated generically in the contract step `S` (the M_U step
`bgpStepContractExp_N_assembled` is plugged in at the final application).
-/

import Ripple.BoundedUniversality.BGP.ContractMainWindexedNoBox
import Ripple.BoundedUniversality.BGP.ContractSimulation
import Ripple.BoundedUniversality.BGP.FlagIndicatorPolyMU
import Ripple.BoundedUniversality.BGP.WarmHoldMU

namespace Ripple.BoundedUniversality.BGP

open Ripple.BoundedUniversality.Core
open scoped BigOperators

noncomputable section

open MachineInstance

/-- **Warmed de-axiom headline (conditional on the banked producer bundle).**
Plugs M_U + the polynomial halt indicator + the strict-cascade params into the
box-free windexed assembly. -/
theorem bgp_simulates_undecidable_of_warmed_contract_data
    (S : RobustStepContract
      UniversalMachine.undecidableMachine.toDiscreteMachine stackMachineEncodingU)
    {K : ℝ} {R : ℕ} (hK : 0 < K)
    (κ χ : ℕ → ℕ → ℝ) (rLE : Fin d_U → ℝ) (amp : ℕ → ℕ → Fin d_U → ℝ)
    (η : ℕ →
      DynContractIteratorSol (Fin d_U) bgpParamsBase bgpSchedule S.F →
      ℕ → Fin d_U → ℝ)
    (W : ℕ → ℕ → Fin d_U → ℝ) (depth : ℕ → ℕ → Fin d_U → ℤ)
    (hsupply :
      ∀ w : ℕ, ∃ _sol :
        DynContractIteratorSol (Fin d_U) bgpParamsBase bgpSchedule S.F, True)
    (htracking_inputs :
      ∀ (w : ℕ)
        (sol : DynContractIteratorSol (Fin d_U) bgpParamsBase bgpSchedule S.F),
        ContractTrackingHypotheses S bgpParamsBase bgpSchedule sol
          (fun j => UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
            (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
          (κ w) (χ w) rLE (amp w) (η w sol) (W w) (depth w)
          (trueMovingBox (d := d_U)) haltCoordU)
    (hlatch :
      ∀ sol : DynContractIteratorSol (Fin d_U) bgpParamsBase bgpSchedule S.F,
        ∃ La : ContractHaltLatchSol sol contractFlagIndicatorPackageU_ramp.Hval K R,
          ContractLatchConvergenceKernel sol haltCoordU contractFlagIndicatorPackageU_ramp La)
    (hflag_margin_all :
      ∀ w sol j, η w sol j haltCoordU ≤ haltFlagPackageU.flagMargin)
    (hflag_margin_indicator : haltFlagPackageU.flagMargin ≤ 1 / 4)
    (hflag_domain :
      ∀ (w : ℕ)
        (sol : DynContractIteratorSol (Fin d_U) bgpParamsBase bgpSchedule S.F),
        ∀ j t, t ∈ bgpSchedule.zActiveWindow j →
          sol.z t haltCoordU ∈ Set.Icc (0 : ℝ) 1)
    (fieldPkg :
      ContractPolynomialFieldPackage UniversalMachine.undecidableMachine
        stackMachineEncodingU S
        bgpParamsBase bgpSchedule haltCoordU contractFlagIndicatorPackageU_ramp K R) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  main_assembled_dyn_contract_windexed_noBox
    UniversalMachine.undecidableMachine stackMachineEncodingU S
    bgpParamsBase bgpSchedule haltCoordU haltFlagPackageU
    contractFlagIndicatorPackageU_ramp hK
    κ χ rLE amp η W depth hsupply htracking_inputs hlatch
    hflag_margin_all hflag_margin_indicator hflag_domain fieldPkg

end

end Ripple.BoundedUniversality.BGP
