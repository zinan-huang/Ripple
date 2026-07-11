import Ripple.BoundedUniversality.BGP.ContractTracking
import Ripple.BoundedUniversality.BGP.DynamicGate
import Ripple.BoundedUniversality.BGP.ContractMain

/-!
Ripple.BoundedUniversality.BGP.ContractSchedules
----------------------------
Schedule-level glue for the contract tracking input package.

This file is intentionally parametric over the machine-instance amp/depth
bookkeeping and over the final weighted-budget margins.  The current checkout
defines `ContractTrackingInputs` in `ContractMain.lean`, not in
`ContractTracking.lean`; the extra import is therefore required to state the
assembler theorem.
-/

namespace Ripple.BoundedUniversality.BGP

open Ripple.BoundedUniversality.Core

noncomputable section

/-! ## Dynamic-gate schedules -/

/-- Contract-facing contraction schedule, directly backed by `dynKappa`. -/
def kappaU (A : ℝ) (L : ℕ) (c0 c1 : ℝ) (j : ℕ) : ℝ :=
  dynKappa A L c0 c1 j

/-- Contract-facing leak schedule, directly backed by `dynChi`. -/
def chiU (A : ℝ) (L : ℕ) (c0 c1 : ℝ) (j : ℕ) : ℝ :=
  dynChi A L c0 c1 j

/-- The `DynGateParams` specialization of `kappaU`. -/
def kappaSchedule (p : DynGateParams) (j : ℕ) : ℝ :=
  kappaU p.A p.L p.cμ p.cα j

/-- The `DynGateParams` specialization of `chiU`. -/
def chiSchedule (p : DynGateParams) (j : ℕ) : ℝ :=
  chiU p.A p.L p.cμ p.cα j

theorem kappaU_pos (A : ℝ) (L : ℕ) (c0 c1 : ℝ) (j : ℕ) :
    0 < kappaU A L c0 c1 j := by
  unfold kappaU dynKappa
  exact Real.exp_pos _

theorem kappaU_nonneg (A : ℝ) (L : ℕ) (c0 c1 : ℝ) (j : ℕ) :
    0 ≤ kappaU A L c0 c1 j :=
  (kappaU_pos A L c0 c1 j).le

theorem kappaU_le_one_of_nonneg
    {A : ℝ} {L : ℕ} {c0 c1 : ℝ} (hA : 0 ≤ A) (j : ℕ) :
    kappaU A L c0 c1 j ≤ 1 := by
  unfold kappaU dynKappa
  rw [Real.exp_le_one_iff]
  exact neg_nonpos.mpr
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg hA (Real.exp_pos _).le)
        (Real.exp_pos _).le)
      (by positivity))

theorem chiU_nonneg
    {A : ℝ} {L : ℕ} {c0 c1 : ℝ}
    (hA : 0 ≤ A) (hr : 0 < c0 * (1 / 2) ^ L - c1) (j : ℕ) :
    0 ≤ chiU A L c0 c1 j := by
  unfold chiU dynChi
  exact div_nonneg
    (mul_nonneg hA (Real.exp_pos _).le)
    hr.le

theorem chiSchedule_nonneg
    {p : DynGateParams}
    (hA : 0 ≤ p.A) (hr : 0 < p.cμ * (1 / 2) ^ p.L - p.cα) (j : ℕ) :
    0 ≤ chiSchedule p j := by
  exact chiU_nonneg hA hr j

/-- Summability of the concrete leak schedule, inherited from `DynamicGate`. -/
theorem chiU_summable
    (A : ℝ) (L : ℕ) (c0 c1 : ℝ)
    (hr : 0 < c0 * (1 / 2) ^ L - c1) :
    Summable (fun j : ℕ => chiU A L c0 c1 j) := by
  simpa [chiU] using dynChi_summable A L c0 c1 hr

/-- Summability of the parameter-record leak schedule. -/
theorem chiSchedule_summable
    (p : DynGateParams)
    (hr : 0 < p.cμ * (1 / 2) ^ p.L - p.cα) :
    Summable (fun j : ℕ => chiSchedule p j) := by
  simpa [chiSchedule] using chiU_summable p.A p.L p.cμ p.cα hr

/-! ## Eta, weighted, and depth schedules -/

/--
The recurrence-driven additive envelope:
`eps_j + 2 * kappa_j * D + (base + 1) * chi_j * D`.
-/
def etaU {d : ℕ}
    (eps : ℕ → Fin d → ℝ) (base D : ℝ)
    (kappa chi : ℕ → ℝ) (j : ℕ) (i : Fin d) : ℝ :=
  eps j i + 2 * kappa j * D + ((base + 1) * chi j * D)

/-- Contract specialization of `etaU` using the live cycle-start precision. -/
def contractEtaSchedule
    {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    {M : DiscreteMachine Conf} {E : StackMachineEncoding d nS M}
    (S : RobustStepContract M E)
    (p : DynGateParams) (sched : PhaseSchedule)
    (sol : DynContractIteratorSol (Fin d) p sched S.F)
    (j : ℕ) (i : Fin d) : ℝ :=
  etaU
    (fun j i => S.epsF (sol.μ (sched.cycleStart j)) i)
    (E.k : ℝ) S.D (kappaSchedule p) (chiSchedule p) j i

theorem contractEtaSchedule_def
    {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    {M : DiscreteMachine Conf} {E : StackMachineEncoding d nS M}
    (S : RobustStepContract M E)
    (p : DynGateParams) (sched : PhaseSchedule)
    (sol : DynContractIteratorSol (Fin d) p sched S.F)
    (j : ℕ) (i : Fin d) :
    contractEtaSchedule S p sched sol j i =
      S.epsF (sol.μ (sched.cycleStart j)) i +
        2 * kappaSchedule p j * S.D +
          (((E.k : ℝ) + 1) * chiSchedule p j * S.D) := by
  rfl

/-- Coordinatewise weighted form from `DepthBudget`. -/
def WU {d : ℕ}
    (base : ℝ) (depth : ℕ → Fin d → ℤ) (err : ℕ → Fin d → ℝ)
    (j : ℕ) (i : Fin d) : ℝ :=
  DepthBudget.W base (fun n => depth n i) (fun n => err n i) j

/-- Contract weighted form for the boundary error. -/
def contractWeightedSchedule
    {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    {M : DiscreteMachine Conf} {E : StackMachineEncoding d nS M}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (c : ℕ → Conf) (depth : ℕ → Fin d → ℤ)
    (j : ℕ) (i : Fin d) : ℝ :=
  WU (E.k : ℝ) depth (fun j i => contractBoundaryError (E := E) sol c j i) j i

theorem contractWeightedSchedule_bound
    {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    {M : DiscreteMachine Conf} {E : StackMachineEncoding d nS M}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (c : ℕ → Conf) (depth : ℕ → Fin d → ℤ) :
    ∀ j,
      ContractWeightedBound (E := E) sol c depth
        (contractWeightedSchedule (E := E) sol c depth) j := by
  intro j i
  rfl

/-- Depth schedule generated by an initial depth and per-cycle deltas. -/
def depthU {d : ℕ} (d0 : Fin d → ℤ) (delta : ℕ → Fin d → ℤ) :
    ℕ → Fin d → ℤ
  | 0, i => d0 i
  | j + 1, i => depthU d0 delta j i - delta j i

theorem depthU_step {d : ℕ}
    (d0 : Fin d → ℤ) (delta : ℕ → Fin d → ℤ) (j : ℕ) (i : Fin d) :
    depthU d0 delta (j + 1) i = depthU d0 delta j i - delta j i := by
  rfl

/-- Contract depth recurrence driven by `coordDelta`. -/
def contractDepthU
    {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    {M : DiscreteMachine Conf} (E : StackMachineEncoding d nS M)
    (c : ℕ → Conf) (d0 : Fin d → ℤ) : ℕ → Fin d → ℤ :=
  depthU d0 (fun j i => E.coordDelta (c j) i)

theorem contractDepthU_step
    {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    {M : DiscreteMachine Conf} (E : StackMachineEncoding d nS M)
    (c : ℕ → Conf) (d0 : Fin d → ℤ) (j : ℕ) (i : Fin d) :
    contractDepthU E c d0 (j + 1) i =
      contractDepthU E c d0 j i - E.coordDelta (c j) i := by
  rfl

/-- Coordinatewise geometric margin wrapper around `DepthBudget.T3`. -/
theorem WU_geometric_margin
    {d : ℕ} (base : ℝ) (depth delta : ℕ → Fin d → ℤ)
    (err eps : ℕ → Fin d → ℝ) (i : Fin d)
    {d0 beta eta C : ℝ}
    (hbase : 1 < base)
    (hrec :
      ∀ j, err (j + 1) i ≤ base ^ delta j i * err j i + eps j i)
    (hdepth : ∀ j, depth (j + 1) i = depth j i - delta j i)
    (herr : ∀ j, 0 ≤ err j i)
    (hdepth_nonneg : ∀ j, 0 ≤ depth j i)
    (hgrow : ∀ j, (depth j i : ℝ) ≤ d0 + beta * j)
    (hdecay : ∀ j, eps j i ≤ C * Real.exp (-(eta) * j))
    (heta : beta * Real.log base < eta)
    (hC : 0 ≤ C)
    (hbeta : 0 ≤ beta) :
    ∀ j,
      err j i ≤
        WU base depth err 0 i +
          DepthBudget.geometricBudgetConstant base d0 beta eta C := by
  simpa [WU] using
    DepthBudget.T3
      (e := fun j => err j i)
      (d := fun j => depth j i)
      (delta := fun j => delta j i)
      (eps := fun j => eps j i)
      (k := base) (d0 := d0) (beta := beta) (eta := eta) (C := C)
      hbase hrec hdepth herr hdepth_nonneg hgrow hdecay heta hC hbeta

/-! ## Moving box -/

/--
Moving box predicate around a cycle-indexed orbit.  This is the predicate
stored by `ContractTrackingInputs`; the domain-to-window cover below connects
it to `ContractPerCycleBox`.
-/
def contractMovingBox {d : ℕ}
    (orbit : ℕ → Fin d → ℝ) (D : ℝ) (sched : PhaseSchedule)
    (t : ℝ) (z u : Fin d → ℝ) : Prop :=
  ∃ j : ℕ, t ∈ sched.zActiveWindow j ∧
    (∀ i, |z i - orbit j i| ≤ D) ∧
      (∀ i, |u i - orbit j i| ≤ D)

theorem contractMovingBox_of_perCycleBox_window
    {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    {M : DiscreteMachine Conf} {E : StackMachineEncoding d nS M}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {sol : DynContractIteratorSol (Fin d) p sched F}
    {w : ℕ} {D : ℝ}
    (box : ContractPerCycleBox E sol w D)
    {j : ℕ} {t : ℝ} (ht : t ∈ sched.zActiveWindow j) :
    contractMovingBox (contractOrbit E w) D sched t (sol.z t) (sol.u t) := by
  refine ⟨j, ht, ?_, ?_⟩
  · exact (box.box j t ht).2.1
  · exact (box.box j t ht).2.2.1

theorem contractMovingBox_of_perCycleBox_domain
    {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    {M : DiscreteMachine Conf} {E : StackMachineEncoding d nS M}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {sol : DynContractIteratorSol (Fin d) p sched F}
    {w : ℕ} {D : ℝ}
    (box : ContractPerCycleBox E sol w D)
    (hcover : ∀ t ∈ sched.domain, ∃ j, t ∈ sched.zActiveWindow j) :
    ∀ t ∈ sched.domain,
      contractMovingBox (contractOrbit E w) D sched t (sol.z t) (sol.u t) := by
  intro t ht
  obtain ⟨j, hj⟩ := hcover t ht
  exact contractMovingBox_of_perCycleBox_window box hj

/-! ## ContractTrackingInputs assembly -/

theorem contract_branch_of_window_from_radius
    {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    {M : DiscreteMachine Conf} {E : StackMachineEncoding d nS M}
    (S : RobustStepContract M E)
    {p : DynGateParams} {sched : PhaseSchedule}
    {sol : DynContractIteratorSol (Fin d) p sched S.F}
    {c : ℕ → Conf} {rLE : Fin d → ℝ}
    (hmu_large :
      ∀ j t, t ∈ sched.zActiveWindow j → S.mu_min ≤ sol.μ t)
    (hrLE_radius :
      ∀ j t, t ∈ sched.zActiveWindow j → ∀ i, rLE i ≤ S.radius (sol.μ t)) :
    ∀ j, ContractWindowTube (E := E) sol c rLE j →
      ContractBranchLocked (E := E) S sol c j := by
  intro j hwindow t ht
  exact S.local_extract_correct (hmu_large j t ht) (by
    intro i
    exact (hwindow t ht i).trans (hrLE_radius j t ht i))

/--
Assembler for the contract tracking input package.

The concrete schedules are `kappaSchedule p`, `chiSchedule p`, and
`contractEtaSchedule S p sched sol`.  The amp/depth schedule and the global
weighted budget are left parametric, with exactly the compatibility and margin
hypotheses needed by `ContractTrackingInputs`.
-/
theorem contract_tracking_inputs_assemble
    {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    {M : DiscreteMachine Conf} (E : StackMachineEncoding d nS M)
    (S : RobustStepContract M E)
    (p : DynGateParams) (sched : PhaseSchedule)
    (w : ℕ) (sol : DynContractIteratorSol (Fin d) p sched S.F)
    (Dbox : ℝ) (box : ContractPerCycleBox E sol w Dbox)
    (rLE : Fin d → ℝ)
    (amp W : ℕ → Fin d → ℝ)
    (depth : ℕ → Fin d → ℤ)
    (flagCoord : Fin d)
    (hA : 0 ≤ p.A)
    (hr : 0 < p.cμ * (1 / 2) ^ p.L - p.cα)
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
    (hhold_slack :
      ∀ j,
        ContractWeightedBound (E := E) sol
          (fun j => M.step^[j] (M.init w)) depth W j →
          ∀ i,
            contractBoundaryError (E := E) sol
                (fun j => M.step^[j] (M.init w)) j i +
              chiSchedule p j * S.D ≤ rLE i)
    (hwindow_hold :
      ∀ j t, t ∈ sched.zActiveWindow j → ∀ i,
        |sol.u t i - E.enc ((fun j => M.step^[j] (M.init w)) j) i| ≤
          contractBoundaryError (E := E) sol
              (fun j => M.step^[j] (M.init w)) j i +
            chiSchedule p j * S.D)
    (hz_window_hold :
      ∀ j t, t ∈ sched.zActiveWindow j → ∀ i,
        |sol.z t i - E.enc ((fun j => M.step^[j] (M.init w)) j) i| ≤
          contractBoundaryError (E := E) sol
              (fun j => M.step^[j] (M.init w)) j i +
            chiSchedule p j * S.D)
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
          (fun j => M.step^[j] (M.init w)) amp
            (contractEtaSchedule S p sched sol) j)
    (hweighted_step :
      ∀ j,
        ContractWeightedBound (E := E) sol
          (fun j => M.step^[j] (M.init w)) depth W j →
        ContractRecurrenceAt (E := E) sol
          (fun j => M.step^[j] (M.init w)) amp
            (contractEtaSchedule S p sched sol) j →
        ContractWeightedBound (E := E) sol
          (fun j => M.step^[j] (M.init w)) depth W (j + 1))
    (hbox_domain_cover :
      ∀ t ∈ sched.domain, ∃ j, t ∈ sched.zActiveWindow j) :
    ContractTrackingInputs S p sched sol
      (fun j => M.step^[j] (M.init w))
      (kappaSchedule p) (chiSchedule p) rLE amp
      (contractEtaSchedule S p sched sol) W depth
      (contractMovingBox (contractOrbit E w) Dbox sched) flagCoord := by
  refine
    { hamp_stack := hamp_stack
      hamp_reset := hamp_reset
      hmu_large := hmu_large
      heps_mono := heps_mono
      hinit_weighted := hinit_weighted
      hchiD_nonneg := ?_
      hhold_slack := hhold_slack
      hwindow_hold := hwindow_hold
      hz_window_hold := hz_window_hold
      hflag_z_read_window_bridge := hflag_z_read_window_bridge
      hbranch_of_window := ?_
      hrecurrence_of_branch := hrecurrence_of_branch
      hweighted_step := hweighted_step
      hmoving_box := ?_ }
  · intro j
    exact mul_nonneg (chiSchedule_nonneg hA hr j) S.D_nonneg
  · exact contract_branch_of_window_from_radius S hmu_large hrLE_radius
  · exact contractMovingBox_of_perCycleBox_domain box hbox_domain_cover

end

end Ripple.BoundedUniversality.BGP
