import Ripple.BoundedUniversality.BGP.ContractMain

/-!
Ripple.BoundedUniversality.BGP.ContractWindexed
---------------------------
Per-input (w-indexed) version of the contract Euclidean-assembly theorem.

The original `contract_dyn_assembled_euclidean_simulation` (in
`Ripple.BoundedUniversality.BGP.ContractMain`) hard-codes a single phase schedule
(`κ`, `χ`, `η sol`, `hflag_margin_all sol`) shared by all inputs.  The
"warmed variant" route to the axiom-free headline needs *per-input*
schedules `κ w`, `χ w`, `η w sol` so that the input-length warm-up
`m(|w|)+j` can be installed separately for each input `w`.

This file is a faithful per-input copy of the original proof: after
`intro w`, every use of the per-cycle schedule `κ` / `χ` / `η sol` /
`hflag_margin_all sol` is replaced by its w-indexed counterpart
`κ w` / `χ w` / `η w sol` / `hflag_margin_all w sol`.  The internal
lemmas (`contract_all_time_tracking`, `contract_halt_flag_readout`) are
reused exactly as in the original.

This file is intentionally additive.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Ripple.BoundedUniversality.Core
open scoped BigOperators

-- The original `contract_dyn_assembled_euclidean_simulation` proof calls two
-- helper lemmas (`step_orbit_step`, `haltsOn_iff_orbit_halted`) that are
-- declared `private` in `ContractMain.lean` and so are not visible here.
-- We reproduce them locally (same proofs) for the per-input copy.

private lemma step_orbit_step_windexed
    {Conf : Type} [Primcodable Conf] (M : DiscreteMachine Conf) (w j : ℕ) :
    M.step^[j + 1] (M.init w) = M.step (M.step^[j] (M.init w)) := by
  rw [Function.iterate_succ_apply']

private lemma haltsOn_iff_orbit_halted_windexed
    {Conf : Type} [Primcodable Conf] (M : DiscreteMachine Conf) (w : ℕ) :
    M.haltsOn w ↔ ∃ N : ℕ, M.halted (M.step^[N] (M.init w)) = true := by
  rfl

/--
H2'. Per-input (w-indexed) contract Euclidean simulation assembly.

Identical to `contract_dyn_assembled_euclidean_simulation`, except the
phase schedule is supplied per input: `κ`, `χ` become `ℕ → ℕ → ℝ`
(applied as `κ w`, `χ w`), `η` becomes
`ℕ → DynContractIteratorSol ... → ℕ → Fin d → ℝ` (applied as `η w sol`),
and `hflag_margin_all` becomes `∀ w sol j, ...`.
-/
theorem contract_dyn_assembled_euclidean_simulation_windexed
    {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    (M : DiscreteMachine Conf) (E : StackMachineEncoding d nS M)
    (S : RobustStepContract M E) (p : DynGateParams) (sched : PhaseSchedule)
    (flagCoord : Fin d) (flagPkg : HaltFlagPackage E flagCoord)
    (I : ContractFlagIndicatorPackage flagCoord) {K : ℝ} {R : ℕ} (hK : 0 < K)
    (κ χ : ℕ → ℕ → ℝ) (rLE : Fin d → ℝ) (amp : ℕ → ℕ → Fin d → ℝ)
    (η : ℕ → DynContractIteratorSol (Fin d) p sched S.F → ℕ → Fin d → ℝ)
    (W : ℕ → ℕ → Fin d → ℝ) (depth : ℕ → ℕ → Fin d → ℤ)
    (movingBox : ℕ → ℝ → (Fin d → ℝ) → (Fin d → ℝ) → Prop) (D : ℝ)
    (hsupply :
      ∀ w : ℕ,
        ∃ sol : DynContractIteratorSol (Fin d) p sched S.F,
          ContractPerCycleBox E sol w D)
    (htracking_inputs :
      ∀ (w : ℕ) (sol : DynContractIteratorSol (Fin d) p sched S.F),
        ContractPerCycleBox E sol w D →
          ContractTrackingInputs S p sched sol
            (fun j => M.step^[j] (M.init w))
            (κ w) (χ w) rLE (amp w) (η w sol) (W w) (depth w) (movingBox w)
            flagCoord)
    (hlatch :
      ∀ sol : DynContractIteratorSol (Fin d) p sched S.F,
        ∃ La : ContractHaltLatchSol sol I.Hval K R,
          ContractLatchConvergenceKernel sol flagCoord I La)
    (hflag_margin_all : ∀ w sol j, η w sol j flagCoord ≤ flagPkg.flagMargin)
    (hflag_margin_indicator : flagPkg.flagMargin ≤ 1 / 4)
    (hflag_domain :
      ∀ (w : ℕ) (sol : DynContractIteratorSol (Fin d) p sched S.F)
        (_box : ContractPerCycleBox E sol w D),
        ∀ j t, t ∈ sched.zActiveWindow j →
          sol.z t flagCoord ∈ Set.Icc (0 : ℝ) 1) :
    ContractDynAssembledEuclideanSimulation M E S p sched flagCoord I K R := by
  classical
  refine
    { K_pos := hK
      per_input := ?_ }
  intro w
  obtain ⟨sol, box⟩ := hsupply w
  let c : ℕ → Conf := fun j => M.step^[j] (M.init w)
  have hc_step : ∀ j, c (j + 1) = M.step (c j) := by
    intro j
    dsimp [c]
    exact step_orbit_step_windexed M w j
  have inputs := htracking_inputs w sol box
  have track :
      ContractTrackingResult (E := E) S sol c rLE (amp w) (η w sol) (W w)
        (depth w) (movingBox w) flagCoord :=
    contract_all_time_tracking
      (S := S) p sched sol c hc_step (κ w) (χ w) rLE (amp w) (η w sol) (W w)
        (depth w) (movingBox w) flagCoord
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
      (hflag_margin_all w sol) hflag_margin_indicator (hflag_domain w sol box)
  refine ⟨sol, La, ?_, ?_⟩
  · intro hw
    exact readout.correct_halt ((haltsOn_iff_orbit_halted_windexed M w).mp hw)
  · intro hw
    apply readout.correct_nonhalt
    intro N hN
    exact hw ((haltsOn_iff_orbit_halted_windexed M w).mpr ⟨N, hN⟩)

end Ripple.BoundedUniversality.BGP
