/-
Ripple.BoundedUniversality.BGP.ContractSchedulesWarm
--------------------------------
Schedule-parametric clone of `contract_tracking_inputs_assemble`
(`ContractSchedules.lean`).  The existing assembler hard-codes the conclusion's
schedules to `kappaSchedule p` / `chiSchedule p` / `contractEtaSchedule S p sched sol`;
the warmed (pre-cycle-shifted) route needs the per-input schedules `κ w` / `χ w` /
`η w sol` instead.  The proof body is identical record-filling — only the type
changes: `κ χ η` are exposed as parameters, and `hchiD_nonneg` is taken as a
hypothesis (the warmed `χ` is not `chiSchedule`, so it cannot be derived from
`chiSchedule_nonneg`; correspondingly `hA`/`hr` are dropped).
-/

import Ripple.BoundedUniversality.BGP.ContractSchedules

namespace Ripple.BoundedUniversality.BGP

noncomputable section

/-- **Schedule-parametric tracking-inputs assembler.**  Identical to
`contract_tracking_inputs_assemble` but with the clock/eta schedules `κ χ η`
exposed (so the warmed schedules can be plugged in).  `hchiD_nonneg` replaces the
`chiSchedule_nonneg` derivation. -/
theorem contract_tracking_inputs_assemble_with_schedules
    {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    {M : DiscreteMachine Conf} (E : StackMachineEncoding d nS M)
    (S : RobustStepContract M E)
    (p : DynGateParams) (sched : PhaseSchedule)
    (w : ℕ) (sol : DynContractIteratorSol (Fin d) p sched S.F)
    (Dbox : ℝ) (box : ContractPerCycleBox E sol w Dbox)
    (κ χ : ℕ → ℝ)
    (rLE : Fin d → ℝ)
    (amp η W : ℕ → Fin d → ℝ)
    (depth : ℕ → Fin d → ℤ)
    (flagCoord : Fin d)
    (hamp_stack :
      ∀ j s,
        amp j (E.stackCoord s) =
          (E.k : ℝ) ^ E.stackDelta ((fun j => M.step^[j] (M.init w)) j) s)
    (hamp_reset :
      ∀ j i, E.coordStackIndex i = none → amp j i = 0)
    (hmu_large :
      ∀ j t, t ∈ sched.zActiveWindow j → S.mu_min ≤ sol.μ t)
    (heps_mono :
      ∀ i {mu0 mu1 : ℝ}, mu0 ≤ mu1 → S.epsF mu1 i ≤ S.epsF mu0 i)
    (hinit_weighted :
      ContractWeightedBound (E := E) sol
        (fun j => M.step^[j] (M.init w)) depth W 0)
    (hchiD_nonneg : ∀ j, 0 ≤ χ j * S.D)
    (hhold_slack :
      ∀ j,
        ContractWeightedBound (E := E) sol
          (fun j => M.step^[j] (M.init w)) depth W j →
          ∀ i,
            contractBoundaryError (E := E) sol
                (fun j => M.step^[j] (M.init w)) j i +
              χ j * S.D ≤ rLE i)
    (hwindow_hold :
      ∀ j t, t ∈ sched.zActiveWindow j → ∀ i,
        |sol.u t i - E.enc ((fun j => M.step^[j] (M.init w)) j) i| ≤
          contractBoundaryError (E := E) sol
              (fun j => M.step^[j] (M.init w)) j i +
            χ j * S.D)
    (hz_window_hold :
      ∀ j t, t ∈ sched.zActiveWindow j → ∀ i,
        |sol.z t i - E.enc ((fun j => M.step^[j] (M.init w)) j) i| ≤
          contractBoundaryError (E := E) sol
              (fun j => M.step^[j] (M.init w)) j i +
            χ j * S.D)
    (hflag_z_read_window_bridge :
      ∀ j t, t ∈ sched.zActiveWindow j →
        |sol.z t flagCoord -
            E.enc ((fun j => M.step^[j] (M.init w)) j) flagCoord| ≤
          contractBoundaryError (E := E) sol
            (fun j => M.step^[j] (M.init w)) (j + 1) flagCoord)
    (hrLE_radius :
      ∀ j t, t ∈ sched.zActiveWindow j → ∀ i,
        rLE i ≤ S.radius (sol.μ t))
    (hrecurrence_of_branch :
      ∀ j,
        ContractWeightedBound (E := E) sol
          (fun j => M.step^[j] (M.init w)) depth W j →
        ContractWindowTube (E := E) sol
          (fun j => M.step^[j] (M.init w)) rLE j →
        ContractBranchLocked (E := E) S sol
          (fun j => M.step^[j] (M.init w)) j →
        ContractRecurrenceAt (E := E) sol
          (fun j => M.step^[j] (M.init w)) amp η j)
    (hweighted_step :
      ∀ j,
        ContractWeightedBound (E := E) sol
          (fun j => M.step^[j] (M.init w)) depth W j →
        ContractRecurrenceAt (E := E) sol
          (fun j => M.step^[j] (M.init w)) amp η j →
        ContractWeightedBound (E := E) sol
          (fun j => M.step^[j] (M.init w)) depth W (j + 1))
    (hbox_domain_cover :
      ∀ t ∈ sched.domain, ∃ j, t ∈ sched.zActiveWindow j) :
    ContractTrackingInputs S p sched sol
      (fun j => M.step^[j] (M.init w))
      κ χ rLE amp η W depth
      (contractMovingBox (contractOrbit E w) Dbox sched) flagCoord := by
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
  · exact contractMovingBox_of_perCycleBox_domain box hbox_domain_cover

end

end Ripple.BoundedUniversality.BGP
