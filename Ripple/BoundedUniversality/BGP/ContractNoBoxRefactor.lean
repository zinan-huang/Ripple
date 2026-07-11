/-
Ripple.BoundedUniversality.BGP.ContractNoBoxRefactor
--------------------------------
R-REFACTOR (pbook): break the supply↔box circularity (Option B).

The supplier's `ContractPerCycleBox` input was NOT an a-priori analytic fact — it
was the same z/u tracking invariant `contract_all_time_tracking` proves.  So:

* supply produces only a raw `DynContractIteratorSol` (no box);
* the tracking-input assembler carries `movingBox := trueMovingBox` (the field is
  unused by the halt readout), so no `ContractPerCycleBox` is needed;
* `contract_all_time_tracking` then establishes the real z/u tubes;
* a `ContractPerCycleBoxBounds` certificate, if wanted, is an OUTPUT *after*
  tracking (not part of the headline path).

This is the box-free Euclidean assembly the warmed headline uses.
-/

import Ripple.BoundedUniversality.BGP.ContractSupply
import Ripple.BoundedUniversality.BGP.ContractSchedulesWarm
import Ripple.BoundedUniversality.BGP.EncBoxCore

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open MvPolynomial

noncomputable section

/-- Trivial moving-box predicate (the field is carried but unused by the readout). -/
def trueMovingBox {d : ℕ} : ℝ → (Fin d → ℝ) → (Fin d → ℝ) → Prop :=
  fun _ _ _ => True

/-! ## 1. Raw polynomial-field supply: NO `ContractPerCycleBox` input -/

/-- `contract_supply_of_polynomial_field_finitetime` with the circular `hbox`
removed: constructs only the dynamic contract iterator solution. -/
theorem contract_raw_supply_of_polynomial_field_finitetime
    {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    (E : StackMachineEncoding d nS M)
    (S : RobustStepContract M E)
    (p : DynGateParams) (sched : PhaseSchedule)
    (FP : Fin d → MvPolynomial (Fin (contractDim d)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    {Aq Kq cμq cαq : ℚ} {L R : ℕ}
    (hA : p.A = (Aq : ℝ)) (hcμ : p.cμ = (cμq : ℝ)) (hcα : p.cα = (cαq : ℝ))
    (hL : p.L = L)
    (hdomain_nonneg : ∀ t : ℝ, t ∈ sched.domain → 0 ≤ t)
    (y₀ : ℕ → Fin (contractDim d) → ℝ)
    (hfin :
      ∀ w : ℕ,
        Ripple.FiniteHorizonBound
          (fun x i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x
            (contractAssembledField d FP HP Aq Kq cμq cαq L R i))
          (y₀ w))
    (hgateZ :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim d) → ℝ), ∀ t : ℝ, 0 ≤ t →
        y t (contractGateZ d) = bGateZ L (y t (contractMu d)) t)
    (hgateU :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim d) → ℝ), ∀ t : ℝ, 0 ≤ t →
        y t (contractGateU d) = bGateU L (y t (contractMu d)) t)
    (field_eval_identity :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim d) → ℝ), ∀ t : ℝ, 0 ≤ t →
        ∀ i : Fin d,
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) (FP i) =
            S.F (y t (contractMu d)) (fun k => y t (contractU k)) i) :
    ∀ w : ℕ, ∃ _sol : DynContractIteratorSol (Fin d) p sched S.F, True := by
  intro w
  obtain ⟨y, _hy0, hyode, hycont⟩ :=
    contractAssembledField_global_solution_exists_finitetime
      FP HP Aq Kq cμq cαq L R (y₀ w) (hfin w)
  exact
    ⟨dynContractIteratorSol_of_contractAssembledField_solution
      (E := E) (S := S) (p := p) (sched := sched)
      FP HP hA hcμ hcα hL hdomain_nonneg y hyode hycont
      (hgateZ w y) (hgateU w y) (field_eval_identity w y), trivial⟩

/-! ## 2. Raw warmed tracking-input assembler: `movingBox := trueMovingBox` -/

/-- The schedule-parametric assembler with the only circular field removed: the
`hmoving_box` field is trivially `True`, so no `ContractPerCycleBox` is needed. -/
theorem contract_tracking_inputs_assemble_with_schedules_raw
    {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    {M : DiscreteMachine Conf} (E : StackMachineEncoding d nS M)
    (S : RobustStepContract M E)
    (p : DynGateParams) (sched : PhaseSchedule)
    (w : ℕ) (sol : DynContractIteratorSol (Fin d) p sched S.F)
    (κ χ : ℕ → ℝ)
    (rLE : Fin d → ℝ)
    (amp η W : ℕ → Fin d → ℝ)
    (depth : ℕ → Fin d → ℤ)
    (flagCoord : Fin d)
    (hamp_stack :
      ∀ j s, amp j (E.stackCoord s) =
          (E.k : ℝ) ^ E.stackDelta ((fun j => M.step^[j] (M.init w)) j) s)
    (hamp_reset : ∀ j i, E.coordStackIndex i = none → amp j i = 0)
    (hmu_large : ∀ j t, t ∈ sched.zActiveWindow j → S.mu_min ≤ sol.μ t)
    (heps_mono : ∀ i {mu0 mu1 : ℝ}, mu0 ≤ mu1 → S.epsF mu1 i ≤ S.epsF mu0 i)
    (hinit_weighted :
      ContractWeightedBound (E := E) sol (fun j => M.step^[j] (M.init w)) depth W 0)
    (hchiD_nonneg : ∀ j, 0 ≤ χ j * S.D)
    (hhold_slack :
      ∀ j, ContractWeightedBound (E := E) sol (fun j => M.step^[j] (M.init w)) depth W j →
          ∀ i, contractBoundaryError (E := E) sol (fun j => M.step^[j] (M.init w)) j i +
              χ j * S.D ≤ rLE i)
    (hwindow_hold :
      ∀ j t, t ∈ sched.zActiveWindow j → ∀ i,
        |sol.u t i - E.enc ((fun j => M.step^[j] (M.init w)) j) i| ≤
          contractBoundaryError (E := E) sol (fun j => M.step^[j] (M.init w)) j i + χ j * S.D)
    (hz_window_hold :
      ∀ j t, t ∈ sched.zActiveWindow j → ∀ i,
        |sol.z t i - E.enc ((fun j => M.step^[j] (M.init w)) j) i| ≤
          contractBoundaryError (E := E) sol (fun j => M.step^[j] (M.init w)) j i + χ j * S.D)
    (hflag_z_read_window_bridge :
      ∀ j t, t ∈ sched.zActiveWindow j →
        |sol.z t flagCoord - E.enc ((fun j => M.step^[j] (M.init w)) j) flagCoord| ≤
          contractBoundaryError (E := E) sol (fun j => M.step^[j] (M.init w)) (j + 1) flagCoord)
    (hrLE_radius :
      ∀ j t, t ∈ sched.zActiveWindow j → ∀ i, rLE i ≤ S.radius (sol.μ t))
    (hrecurrence_of_branch :
      ∀ j, ContractWeightedBound (E := E) sol (fun j => M.step^[j] (M.init w)) depth W j →
        ContractWindowTube (E := E) sol (fun j => M.step^[j] (M.init w)) rLE j →
        ContractBranchLocked (E := E) S sol (fun j => M.step^[j] (M.init w)) j →
        ContractRecurrenceAt (E := E) sol (fun j => M.step^[j] (M.init w)) amp η j)
    (hweighted_step :
      ∀ j, ContractWeightedBound (E := E) sol (fun j => M.step^[j] (M.init w)) depth W j →
        ContractRecurrenceAt (E := E) sol (fun j => M.step^[j] (M.init w)) amp η j →
        ContractWeightedBound (E := E) sol (fun j => M.step^[j] (M.init w)) depth W (j + 1)) :
    ContractTrackingInputs S p sched sol
      (fun j => M.step^[j] (M.init w))
      κ χ rLE amp η W depth (trueMovingBox (d := d)) flagCoord := by
  refine
    { hamp_stack := hamp_stack
      hamp_reset := hamp_reset
      hmu_large := hmu_large
      heps_mono := heps_mono
      hinit_weighted := hinit_weighted
      hchiD_nonneg := hchiD_nonneg
      hhold_slack := hhold_slack
      hwindow_hold := hwindow_hold
      hz_window_hold := hz_window_hold
      hflag_z_read_window_bridge := hflag_z_read_window_bridge
      hbranch_of_window := ?_
      hrecurrence_of_branch := hrecurrence_of_branch
      hweighted_step := hweighted_step
      hmoving_box := ?_ }
  · exact contract_branch_of_window_from_radius S hmu_large hrLE_radius
  · intro t _ht; trivial

/-! ## 3. Raw box-free Euclidean assembly -/

private lemma step_orbit_step_raw
    {Conf : Type} [Primcodable Conf] (M : DiscreteMachine Conf) (w j : ℕ) :
    M.step^[j + 1] (M.init w) = M.step (M.step^[j] (M.init w)) := by
  rw [Function.iterate_succ_apply']

private lemma haltsOn_iff_orbit_halted_raw
    {Conf : Type} [Primcodable Conf] (M : DiscreteMachine Conf) (w : ℕ) :
    M.haltsOn w ↔ ∃ N : ℕ, M.halted (M.step^[N] (M.init w)) = true := by
  rfl

/-- Raw version of `contract_dyn_assembled_euclidean_simulation`: NO supplied
`ContractPerCycleBox`.  Tracking runs from raw `ContractTrackingInputs` with
`movingBox := trueMovingBox`. -/
theorem contract_dyn_assembled_euclidean_simulation_raw
    {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    (M : DiscreteMachine Conf) (E : StackMachineEncoding d nS M)
    (S : RobustStepContract M E)
    (p : DynGateParams) (sched : PhaseSchedule)
    (flagCoord : Fin d)
    (flagPkg : HaltFlagPackage E flagCoord)
    (I : ContractFlagIndicatorPackage flagCoord)
    {K : ℝ} {R : ℕ}
    (hK : 0 < K)
    (κ χ : ℕ → ℝ)
    (rLE : Fin d → ℝ)
    (amp : ℕ → ℕ → Fin d → ℝ)
    (η : DynContractIteratorSol (Fin d) p sched S.F → ℕ → Fin d → ℝ)
    (W : ℕ → ℕ → Fin d → ℝ)
    (depth : ℕ → ℕ → Fin d → ℤ)
    (hsupply :
      ∀ w : ℕ, ∃ _sol : DynContractIteratorSol (Fin d) p sched S.F, True)
    (htracking_inputs :
      ∀ (w : ℕ) (sol : DynContractIteratorSol (Fin d) p sched S.F),
        ContractTrackingInputs S p sched sol
          (fun j => M.step^[j] (M.init w))
          κ χ rLE (amp w) (η sol) (W w) (depth w)
          (trueMovingBox (d := d)) flagCoord)
    (hlatch :
      ∀ sol : DynContractIteratorSol (Fin d) p sched S.F,
        ∃ La : ContractHaltLatchSol sol I.Hval K R,
          ContractLatchConvergenceKernel sol flagCoord I La)
    (hflag_margin_all : ∀ sol j, η sol j flagCoord ≤ flagPkg.flagMargin)
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
    intro j; dsimp [c]; exact step_orbit_step_raw M w j
  have inputs := htracking_inputs w sol
  have track :
      ContractTrackingResult (E := E) S sol c rLE (amp w) (η sol) (W w) (depth w)
        (trueMovingBox (d := d)) flagCoord :=
    contract_all_time_tracking
      (S := S) p sched sol c hc_step κ χ rLE (amp w) (η sol) (W w) (depth w)
        (trueMovingBox (d := d)) flagCoord
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
      (hflag_margin_all sol) hflag_margin_indicator (hflag_domain w sol)
  refine ⟨sol, La, ?_, ?_⟩
  · intro hw
    exact readout.correct_halt ((haltsOn_iff_orbit_halted_raw M w).mp hw)
  · intro hw
    apply readout.correct_nonhalt
    intro N hN
    exact hw ((haltsOn_iff_orbit_halted_raw M w).mpr ⟨N, hN⟩)

end

end Ripple.BoundedUniversality.BGP
