/-
Ripple.BoundedUniversality.BGP.ContractWindexedRaw
------------------------------
The WINDEXED + RAW contract Euclidean assembly: per-input (w-indexed) phase
schedules (needed for the warm shift `m(|w|)+j`) AND box-free (`movingBox :=
trueMovingBox`, no `ContractPerCycleBox` input) — the combination of
`ContractWindexed` and `ContractNoBoxRefactor`.

This is the Euclidean assembly the warmed de-axiom headline actually uses:
supply provides only a raw `DynContractIteratorSol`, `contract_all_time_tracking`
establishes the z/u tubes, and the moving box is never required a-priori.
-/

import Ripple.BoundedUniversality.BGP.ContractWindexed
import Ripple.BoundedUniversality.BGP.ContractNoBoxRefactor

namespace Ripple.BoundedUniversality.BGP

open Ripple.BoundedUniversality.Core
open scoped BigOperators

noncomputable section

private lemma step_orbit_step_wraw
    {Conf : Type} [Primcodable Conf] (M : DiscreteMachine Conf) (w j : ℕ) :
    M.step^[j + 1] (M.init w) = M.step (M.step^[j] (M.init w)) := by
  rw [Function.iterate_succ_apply']

private lemma haltsOn_iff_orbit_halted_wraw
    {Conf : Type} [Primcodable Conf] (M : DiscreteMachine Conf) (w : ℕ) :
    M.haltsOn w ↔ ∃ N : ℕ, M.halted (M.step^[N] (M.init w)) = true := by
  rfl

/-- Windexed + box-free contract Euclidean simulation assembly. -/
theorem contract_dyn_assembled_euclidean_simulation_windexed_raw
    {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    (M : DiscreteMachine Conf) (E : StackMachineEncoding d nS M)
    (S : RobustStepContract M E) (p : DynGateParams) (sched : PhaseSchedule)
    (flagCoord : Fin d) (flagPkg : HaltFlagPackage E flagCoord)
    (I : ContractFlagIndicatorPackage flagCoord) {K : ℝ} {R : ℕ} (hK : 0 < K)
    (κ χ : ℕ → ℕ → ℝ) (rLE : Fin d → ℝ) (amp : ℕ → ℕ → Fin d → ℝ)
    (η : ℕ → DynContractIteratorSol (Fin d) p sched S.F → ℕ → Fin d → ℝ)
    (W : ℕ → ℕ → Fin d → ℝ) (depth : ℕ → ℕ → Fin d → ℤ)
    (hsupply :
      ∀ w : ℕ, ∃ _sol : DynContractIteratorSol (Fin d) p sched S.F, True)
    (htracking_inputs :
      ∀ (w : ℕ) (sol : DynContractIteratorSol (Fin d) p sched S.F),
        ContractTrackingInputs S p sched sol
          (fun j => M.step^[j] (M.init w))
          (κ w) (χ w) rLE (amp w) (η w sol) (W w) (depth w)
          (trueMovingBox (d := d)) flagCoord)
    (hlatch :
      ∀ sol : DynContractIteratorSol (Fin d) p sched S.F,
        ∃ La : ContractHaltLatchSol sol I.Hval K R,
          ContractLatchConvergenceKernel sol flagCoord I La)
    (hflag_margin_all : ∀ w sol j, η w sol j flagCoord ≤ flagPkg.flagMargin)
    (hflag_margin_indicator : flagPkg.flagMargin ≤ 1 / 4)
    (hflag_domain :
      ∀ (w : ℕ) (sol : DynContractIteratorSol (Fin d) p sched S.F),
        ∀ j t, t ∈ sched.zActiveWindow j →
          sol.z t flagCoord ∈ Set.Icc (0 : ℝ) 1) :
    ContractDynAssembledEuclideanSimulation M E S p sched flagCoord I K R := by
  classical
  refine { K_pos := hK, per_input := ?_ }
  intro w
  obtain ⟨sol, _⟩ := hsupply w
  let c : ℕ → Conf := fun j => M.step^[j] (M.init w)
  have hc_step : ∀ j, c (j + 1) = M.step (c j) := by
    intro j; dsimp [c]; exact step_orbit_step_wraw M w j
  have inputs := htracking_inputs w sol
  have track :
      ContractTrackingResult (E := E) S sol c rLE (amp w) (η w sol) (W w)
        (depth w) (trueMovingBox (d := d)) flagCoord :=
    contract_all_time_tracking
      (S := S) p sched sol c hc_step (κ w) (χ w) rLE (amp w) (η w sol) (W w)
        (depth w) (trueMovingBox (d := d)) flagCoord
      inputs.hamp_stack inputs.hamp_reset flagPkg.flag_reset
      inputs.hmu_large inputs.heps_mono inputs.hinit_weighted inputs.hchiD_nonneg
      inputs.hhold_slack inputs.hwindow_hold inputs.hz_window_hold
      inputs.hflag_z_read_window_bridge inputs.hbranch_of_window
      inputs.hrecurrence_of_branch inputs.hweighted_step inputs.hmoving_box
  obtain ⟨La, kernel⟩ := hlatch sol
  have readout :
      ContractFlagReadout (fun j => M.halted (c j) = true) La.a :=
    contract_halt_flag_readout
      (S := S) sol c hc_step flagCoord track flagPkg I La kernel
      (hflag_margin_all w sol) hflag_margin_indicator (hflag_domain w sol)
  refine ⟨sol, La, ?_, ?_⟩
  · intro hw
    exact readout.correct_halt ((haltsOn_iff_orbit_halted_wraw M w).mp hw)
  · intro hw
    apply readout.correct_nonhalt
    intro N hN
    exact hw ((haltsOn_iff_orbit_halted_wraw M w).mpr ⟨N, hN⟩)

/--
Windexed + box-free Euclidean assembly with solution-specific data.

For each input, the supplied solution itself carries the raw tracking inputs,
latch kernel, margin bound, and flag-domain invariant.  This avoids requiring
those facts for arbitrary solutions of the same ODE field.
-/
theorem contract_dyn_assembled_euclidean_simulation_windexed_raw_rich_supply
    {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    (M : DiscreteMachine Conf) (E : StackMachineEncoding d nS M)
    (S : RobustStepContract M E) (p : DynGateParams) (sched : PhaseSchedule)
    (flagCoord : Fin d) (flagPkg : HaltFlagPackage E flagCoord)
    (I : ContractFlagIndicatorPackage flagCoord) {K : ℝ} {R : ℕ} (hK : 0 < K)
    (κ χ : ℕ → ℕ → ℝ) (rLE : Fin d → ℝ) (amp : ℕ → ℕ → Fin d → ℝ)
    (η : ℕ → DynContractIteratorSol (Fin d) p sched S.F → ℕ → Fin d → ℝ)
    (W : ℕ → ℕ → Fin d → ℝ) (depth : ℕ → ℕ → Fin d → ℤ)
    (hsupply_rich :
      ∀ w : ℕ,
        ∃ sol : DynContractIteratorSol (Fin d) p sched S.F,
          ContractTrackingInputs S p sched sol
            (fun j => M.step^[j] (M.init w))
            (κ w) (χ w) rLE (amp w) (η w sol) (W w) (depth w)
            (trueMovingBox (d := d)) flagCoord ∧
          (∃ La : ContractHaltLatchSol sol I.Hval K R,
            ContractLatchConvergenceKernel sol flagCoord I La) ∧
          (∀ j, η w sol j flagCoord ≤ flagPkg.flagMargin) ∧
          (∀ j t, t ∈ sched.zActiveWindow j →
            sol.z t flagCoord ∈ Set.Icc (0 : ℝ) 1))
    (hflag_margin_indicator : flagPkg.flagMargin ≤ 1 / 4) :
    ContractDynAssembledEuclideanSimulation M E S p sched flagCoord I K R := by
  classical
  refine { K_pos := hK, per_input := ?_ }
  intro w
  obtain ⟨sol, inputs, hlatch, hflag_margin_all, hflag_domain⟩ := hsupply_rich w
  let c : ℕ → Conf := fun j => M.step^[j] (M.init w)
  have hc_step : ∀ j, c (j + 1) = M.step (c j) := by
    intro j; dsimp [c]; exact step_orbit_step_wraw M w j
  have track :
      ContractTrackingResult (E := E) S sol c rLE (amp w) (η w sol) (W w)
        (depth w) (trueMovingBox (d := d)) flagCoord :=
    contract_all_time_tracking
      (S := S) p sched sol c hc_step (κ w) (χ w) rLE (amp w) (η w sol) (W w)
        (depth w) (trueMovingBox (d := d)) flagCoord
      inputs.hamp_stack inputs.hamp_reset flagPkg.flag_reset
      inputs.hmu_large inputs.heps_mono inputs.hinit_weighted inputs.hchiD_nonneg
      inputs.hhold_slack inputs.hwindow_hold inputs.hz_window_hold
      inputs.hflag_z_read_window_bridge inputs.hbranch_of_window
      inputs.hrecurrence_of_branch inputs.hweighted_step inputs.hmoving_box
  obtain ⟨La, kernel⟩ := hlatch
  have readout :
      ContractFlagReadout (fun j => M.halted (c j) = true) La.a :=
    contract_halt_flag_readout
      (S := S) sol c hc_step flagCoord track flagPkg I La kernel
      hflag_margin_all hflag_margin_indicator hflag_domain
  refine ⟨sol, La, ?_, ?_⟩
  · intro hw
    exact readout.correct_halt ((haltsOn_iff_orbit_halted_wraw M w).mp hw)
  · intro hw
    apply readout.correct_nonhalt
    intro N hN
    exact hw ((haltsOn_iff_orbit_halted_wraw M w).mpr ⟨N, hN⟩)

end

end Ripple.BoundedUniversality.BGP
