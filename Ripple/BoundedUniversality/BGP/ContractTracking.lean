/-
Ripple.BoundedUniversality.BGP.ContractTracking
---------------------------
Contract-version dynamic iterator and all-time tracking heart.

Design source read end-to-end before this file was added:
* notes/gpt-life2-contract-main.md

Documented deviations forced by the current checkout:
* `DynGateParams`, `PhaseSchedule`, `IsRationalFamily`, and the contract
  all-time result package are introduced here because the checkout only has the
  concrete `DynamicGate.DynIteratorSol` API, not the note's generic records.
* The current `DepthBudget` file exposes scalar unrolled lemmas rather than the
  note's full coordinatewise feasible-budget structure with hold slack.  The
  theorem `contract_all_time_tracking` therefore takes the budget step, hold
  slack, window-hold, and recurrence constructors as explicit hypotheses, then
  proves the simultaneous induction in the order required by the note:
  weighted tube -> hold/window tube -> branch lock -> recurrence -> next
  weighted tube.
* Reset coordinates use amplifier zero through `hamp_reset`; the exported
  `flag_reset_bound` is derived from that zero-amplifier recurrence.
-/

import Ripple.BoundedUniversality.BGP.CycleTracking
import Ripple.BoundedUniversality.BGP.DynamicGate

namespace Ripple.BoundedUniversality.BGP

open Real intervalIntegral
open Ripple.BoundedUniversality.Core

noncomputable section

/-! ## Generic dynamic-gate schedule and moving-target solutions -/

/-- Minimal parameter record for the generic dynamic-gate iterator. -/
structure DynGateParams where
  A : ℝ
  L : ℕ
  cμ : ℝ
  cα : ℝ

/-- Minimal phase schedule used by the contract tracking layer. -/
structure PhaseSchedule where
  domain : Set ℝ
  cycleStart : ℕ → ℝ
  cycleMid : ℕ → ℝ
  cycleEnd : ℕ → ℝ
  zActiveWindow : ℕ → Set ℝ
  stableWindow_subset_zActiveWindow :
    ∀ j : ℕ,
      Set.Icc
        (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6) ⊆
        zActiveWindow j
  cycleEnd_start_next : ∀ j, cycleEnd j = cycleStart (j + 1)

/--
Placeholder rational-family predicate for the proof-level contract wrapper.
The final PIVP packaging phase is responsible for replacing this with concrete
rational expression data.
-/
def IsRationalFamily (Coord : Type*) [Fintype Coord]
    (_F : ℝ → (Coord → ℝ) → Coord → ℝ) : Prop :=
  True

/--
Moving-target dynamic iterator.  The target path `w` is abstract, as required
by `CycleTracking.moving_target_bound`; contract specialization only rewrites
`w` to `F (μ t) (u t)`.
-/
structure DynMovingTargetIteratorSol
    (Coord : Type*) [Fintype Coord]
    (p : DynGateParams)
    (sched : PhaseSchedule) where
  z : ℝ → Coord → ℝ
  u : ℝ → Coord → ℝ
  w : ℝ → Coord → ℝ
  μ : ℝ → ℝ
  α : ℝ → ℝ
  init_z : Coord → ℝ
  init_u : Coord → ℝ
  init_μ : ℝ
  init_α : ℝ
  z_at_zero : z 0 = init_z
  u_at_zero : u 0 = init_u
  μ_at_zero : μ 0 = init_μ
  α_at_zero : α 0 = init_α
  cont_z : ∀ s : Coord, Continuous fun t => z t s
  cont_u : ∀ s : Coord, Continuous fun t => u t s
  cont_w : ∀ s : Coord, Continuous fun t => w t s
  z_hasDeriv :
    ∀ t ∈ sched.domain, ∀ s : Coord,
      HasDerivAt (fun τ => z τ s)
        (p.A * α t * bGateZ p.L (μ t) t * (w t s - z t s)) t
  u_hasDeriv :
    ∀ t ∈ sched.domain, ∀ s : Coord,
      HasDerivAt (fun τ => u τ s)
        (p.A * α t * bGateU p.L (μ t) t * (z t s - u t s)) t
  μ_hasDeriv :
    ∀ t ∈ sched.domain, HasDerivAt μ p.cμ t
  α_hasDeriv :
    ∀ t ∈ sched.domain, HasDerivAt α (p.cα * α t) t

/-- Contract specialization of the abstract moving-target solution. -/
structure DynContractIteratorSol
    (Coord : Type*) [Fintype Coord]
    (p : DynGateParams)
    (sched : PhaseSchedule)
    (F : ℝ → (Coord → ℝ) → Coord → ℝ)
    extends DynMovingTargetIteratorSol Coord p sched where
  target_eq : ∀ t ∈ sched.domain, w t = F (μ t) (u t)
  F_is_rational : IsRationalFamily Coord F

/-! ## Contract cycle recurrence glue -/

/-- Contract additive error for the variable-`μ` live cycle. -/
def contractCycleEta {Conf : Type} [Primcodable Conf]
    {M : DiscreteMachine Conf} {d nS : ℕ} {E : StackMachineEncoding d nS M}
    (S : VarMuRobustStep M E) (kappa chi : ℕ → ℝ) (j : ℕ) : ℝ :=
  S.eps (S.muAt j) + 2 * kappa j * S.D + (((E.k : ℝ) + 1) * chi j * S.D)

/--
G2. Contract-facing wrapper around
`CycleTracking.VarMuRobustStep.variable_mu_cycle_recurrence`.

The solution object supplies the live registers `z` and `u`; the analytic
premises are exactly the per-cycle hypotheses expected by the existing
moving-target recurrence theorem.
-/
theorem contract_variable_mu_cycle_recurrence
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {d nS : ℕ} {E : StackMachineEncoding d nS M}
    (S : VarMuRobustStep M E)
    (p : DynGateParams) (sched : PhaseSchedule)
    (sol : DynContractIteratorSol (Fin d) p sched S.F)
    (c : ℕ → Conf)
    (gZ gU : ℝ → ℝ)
    (kappa chi : ℕ → ℝ) (j : ℕ) (s : Fin nS)
    (hstart_mid : S.cycleStart j ≤ S.cycleMid j)
    (hmid_end : S.cycleMid j ≤ S.cycleEnd j)
    (hcstep : c (j + 1) = M.step (c j))
    (hmu_min : S.mu_min ≤ S.muAt j)
    (hchi_nonneg : 0 ≤ chi j)
    (hkappa_nonneg : 0 ≤ kappa j)
    (hgZ_cont : Continuous (fun t => gZ t))
    (hgZ_nonneg : ∀ t ∈ Set.Icc (S.cycleStart j) (S.cycleMid j), 0 ≤ gZ t)
    (hwZ_cont : Continuous (fun t => S.F (S.mu t) (sol.u t) (E.stackCoord s)))
    (hz_deriv : ∀ t ∈ Set.Icc (S.cycleStart j) (S.cycleMid j),
      HasDerivAt (fun τ => sol.z τ (E.stackCoord s))
        (gZ t * (S.F (S.mu t) (sol.u t) (E.stackCoord s) -
          sol.z t (E.stackCoord s))) t)
    (hgU_cont : Continuous (fun t => gU t))
    (hgU_nonneg : ∀ t ∈ Set.Icc (S.cycleMid j) (S.cycleEnd j), 0 ≤ gU t)
    (hwU_cont : Continuous (fun t => sol.z t (E.stackCoord s)))
    (hu_deriv : ∀ t ∈ Set.Icc (S.cycleMid j) (S.cycleEnd j),
      HasDerivAt (fun τ => sol.u τ (E.stackCoord s))
        (gU t * (sol.z t (E.stackCoord s) - sol.u t (E.stackCoord s))) t)
    (hz_decay :
      Real.exp (-(∫ t in (S.cycleStart j)..(S.cycleMid j), gZ t)) ≤ kappa j)
    (hu_decay :
      Real.exp (-(∫ t in (S.cycleMid j)..(S.cycleEnd j), gU t)) ≤ kappa j)
    (hz_start :
      |sol.z (S.cycleStart j) (E.stackCoord s) -
          E.enc (c (j + 1)) (E.stackCoord s)| ≤ S.D)
    (hu_mid :
      |sol.u (S.cycleMid j) (E.stackCoord s) -
          E.enc (c (j + 1)) (E.stackCoord s)| ≤ S.D)
    (hu_active :
      ∀ t ∈ Set.Icc (S.cycleStart j) (S.cycleMid j), S.K_LE (c j) (sol.u t))
    (hu_hold :
      ∀ t ∈ Set.Icc (S.cycleStart j) (S.cycleMid j),
        |sol.u t (E.stackCoord s) - sol.u (S.cycleStart j) (E.stackCoord s)| ≤
          chi j * S.D)
    (hz_hold :
      ∀ t ∈ Set.Icc (S.cycleMid j) (S.cycleEnd j),
        |sol.z t (E.stackCoord s) - sol.z (S.cycleMid j) (E.stackCoord s)| ≤
          chi j * S.D) :
    VarMuRobustStep.boundaryError S sol.u c (j + 1) (E.stackCoord s) ≤
      (E.k : ℝ) ^ E.coordDelta (c j) (E.stackCoord s) *
          VarMuRobustStep.boundaryError S sol.u c j (E.stackCoord s) +
        contractCycleEta S kappa chi j := by
  simpa [contractCycleEta, VarMuRobustStep.cycleEta] using
    VarMuRobustStep.variable_mu_cycle_recurrence
      (S := S) (u := sol.u) (z := sol.z) (c := c)
      (gZ := gZ) (gU := gU) (kappa := kappa) (chi := chi)
      (j := j) (s := s)
      hstart_mid hmid_end hcstep hmu_min hchi_nonneg hkappa_nonneg
      hgZ_cont hgZ_nonneg hwZ_cont hz_deriv
      hgU_cont hgU_nonneg hwU_cont hu_deriv
      hz_decay hu_decay hz_start hu_mid hu_active hu_hold hz_hold

/-! ## All-time simultaneous induction -/

/-- Boundary error controlling both dynamic registers at cycle starts. -/
def contractBoundaryError
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {d nS : ℕ} {E : StackMachineEncoding d nS M}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (c : ℕ → Conf) (j : ℕ) (i : Fin d) : ℝ :=
  max
    |sol.z (sched.cycleStart j) i - E.enc (c j) i|
    |sol.u (sched.cycleStart j) i - E.enc (c j) i|

theorem contractBoundaryError_nonneg
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {d nS : ℕ} {E : StackMachineEncoding d nS M}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (c : ℕ → Conf) (j : ℕ) (i : Fin d) :
    0 ≤ contractBoundaryError (E := E) sol c j i := by
  unfold contractBoundaryError
  exact le_trans (abs_nonneg _) (le_max_left _ _)

def ContractWeightedBound
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {d nS : ℕ} {E : StackMachineEncoding d nS M}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (c : ℕ → Conf) (depth : ℕ → Fin d → ℤ) (W : ℕ → Fin d → ℝ)
    (j : ℕ) : Prop :=
  ∀ i : Fin d,
    (E.k : ℝ) ^ depth j i * contractBoundaryError (E := E) sol c j i ≤ W j i

def ContractSampleTube
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {d nS : ℕ} {E : StackMachineEncoding d nS M}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (c : ℕ → Conf) (rLE : Fin d → ℝ) (j : ℕ) : Prop :=
  ∀ i : Fin d, contractBoundaryError (E := E) sol c j i ≤ rLE i

def ContractWindowTube
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {d nS : ℕ} {E : StackMachineEncoding d nS M}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (c : ℕ → Conf) (rLE : Fin d → ℝ) (j : ℕ) : Prop :=
  ∀ t ∈ sched.zActiveWindow j, ∀ i : Fin d,
    |sol.u t i - E.enc (c j) i| ≤ rLE i

def ContractZWindowTube
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {d nS : ℕ} {E : StackMachineEncoding d nS M}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (c : ℕ → Conf) (rLE : Fin d → ℝ) (j : ℕ) : Prop :=
  ∀ t ∈ sched.zActiveWindow j, ∀ i : Fin d,
    |sol.z t i - E.enc (c j) i| ≤ rLE i

def ContractBranchLocked
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {d nS : ℕ} {E : StackMachineEncoding d nS M}
    (S : RobustStepContract M E)
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (c : ℕ → Conf) (j : ℕ) : Prop :=
  ∀ t ∈ sched.zActiveWindow j,
    S.localExtract (sol.μ t) (sol.u t) = S.localView (c j)

def ContractRecurrenceAt
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {d nS : ℕ} {E : StackMachineEncoding d nS M}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (c : ℕ → Conf) (amp η : ℕ → Fin d → ℝ) (j : ℕ) : Prop :=
  ∀ i : Fin d,
    contractBoundaryError (E := E) sol c (j + 1) i ≤
      amp j i * contractBoundaryError (E := E) sol c j i + η j i

/-- Result package returned by `contract_all_time_tracking`. -/
structure ContractTrackingResult
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {d nS : ℕ} {E : StackMachineEncoding d nS M}
    (S : RobustStepContract M E)
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (c : ℕ → Conf)
    (rLE : Fin d → ℝ)
    (amp η W : ℕ → Fin d → ℝ)
    (depth : ℕ → Fin d → ℤ)
    (movingBox : ℝ → (Fin d → ℝ) → (Fin d → ℝ) → Prop)
    (flagCoord : Fin d) where
  weighted :
    ∀ j, ContractWeightedBound (E := E) sol c depth W j
  sample_tube :
    ∀ j, ContractSampleTube (E := E) sol c rLE j
  window_tube :
    ∀ j, ContractWindowTube (E := E) sol c rLE j
  z_window_tube :
    ∀ j, ContractZWindowTube (E := E) sol c rLE j
  branch_locked :
    ∀ j, ContractBranchLocked (E := E) S sol c j
  recurrence :
    ∀ j, ContractRecurrenceAt (E := E) sol c amp η j
  moving_box :
    ∀ t ∈ sched.domain, movingBox t (sol.z t) (sol.u t)
  flag_reset_bound :
    ∀ j, contractBoundaryError (E := E) sol c (j + 1) flagCoord ≤ η j flagCoord
  flag_z_read_window :
    ∀ j t, t ∈ sched.zActiveWindow j →
      |sol.z t flagCoord - E.enc (c j) flagCoord| ≤ η j flagCoord

/--
G3. Simultaneous all-time contract tracking.

The induction step follows the design note's order.  In particular, the
window tube is derived from the current weighted bound through the explicit
hold-slack hypothesis before branch locking and recurrence are used.
-/
theorem contract_all_time_tracking
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {d nS : ℕ} {E : StackMachineEncoding d nS M}
    (S : RobustStepContract M E)
    (p : DynGateParams)
    (sched : PhaseSchedule)
    (sol : DynContractIteratorSol (Fin d) p sched S.F)
    (c : ℕ → Conf)
    (hc_step : ∀ j, c (j + 1) = M.step (c j))
    (κ χ : ℕ → ℝ)
    (rLE : Fin d → ℝ)
    (amp η W : ℕ → Fin d → ℝ)
    (depth : ℕ → Fin d → ℤ)
    (movingBox : ℝ → (Fin d → ℝ) → (Fin d → ℝ) → Prop)
    (flagCoord : Fin d)
    (hamp_stack :
      ∀ j s, amp j (E.stackCoord s) = (E.k : ℝ) ^ E.stackDelta (c j) s)
    (hamp_reset :
      ∀ j i, E.coordStackIndex i = none → amp j i = 0)
    (hflag_reset : E.coordStackIndex flagCoord = none)
    (hmu_large :
      ∀ j t, t ∈ sched.zActiveWindow j → S.mu_min ≤ sol.μ t)
    (heps_mono :
      ∀ i {mu0 mu1 : ℝ}, mu0 ≤ mu1 → S.epsF mu1 i ≤ S.epsF mu0 i)
    (hinit_weighted :
      ContractWeightedBound (E := E) sol c depth W 0)
    (hchiD_nonneg : ∀ j, 0 ≤ χ j * S.D)
    (hhold_slack :
      ∀ j, ContractWeightedBound (E := E) sol c depth W j →
        ∀ i, contractBoundaryError (E := E) sol c j i + χ j * S.D ≤ rLE i)
    (hwindow_hold :
      ∀ j t, t ∈ sched.zActiveWindow j → ∀ i,
        |sol.u t i - E.enc (c j) i| ≤
          contractBoundaryError (E := E) sol c j i + χ j * S.D)
    (hz_window_hold :
      ∀ j t, t ∈ sched.zActiveWindow j → ∀ i,
        |sol.z t i - E.enc (c j) i| ≤
          contractBoundaryError (E := E) sol c j i + χ j * S.D)
    (hflag_z_read_window_bridge :
      ∀ j t, t ∈ sched.zActiveWindow j →
        |sol.z t flagCoord - E.enc (c j) flagCoord| ≤
          contractBoundaryError (E := E) sol c (j + 1) flagCoord)
    (hbranch_of_window :
      ∀ j, ContractWindowTube (E := E) sol c rLE j →
        ContractBranchLocked (E := E) S sol c j)
    (hrecurrence_of_branch :
      ∀ j,
        ContractWeightedBound (E := E) sol c depth W j →
        ContractWindowTube (E := E) sol c rLE j →
        ContractBranchLocked (E := E) S sol c j →
        ContractRecurrenceAt (E := E) sol c amp η j)
    (hweighted_step :
      ∀ j,
        ContractWeightedBound (E := E) sol c depth W j →
        ContractRecurrenceAt (E := E) sol c amp η j →
        ContractWeightedBound (E := E) sol c depth W (j + 1))
    (hmoving_box :
      ∀ t ∈ sched.domain, movingBox t (sol.z t) (sol.u t)) :
    ContractTrackingResult (E := E) S sol c rLE amp η W depth movingBox flagCoord := by
  have _ := hc_step
  have _ := hamp_stack
  have _ := hmu_large
  have _ := heps_mono
  have hsample_of_weighted :
      ∀ j,
        ContractWeightedBound (E := E) sol c depth W j →
          ContractSampleTube (E := E) sol c rLE j := by
    intro j hw i
    exact (le_add_of_nonneg_right (hchiD_nonneg j)).trans (hhold_slack j hw i)
  have hwindow_of_weighted :
      ∀ j,
        ContractWeightedBound (E := E) sol c depth W j →
          ContractWindowTube (E := E) sol c rLE j := by
    intro j hw t ht i
    exact (hwindow_hold j t ht i).trans (hhold_slack j hw i)
  have hz_window_of_weighted :
      ∀ j,
        ContractWeightedBound (E := E) sol c depth W j →
          ContractZWindowTube (E := E) sol c rLE j := by
    intro j hw t ht i
    exact (hz_window_hold j t ht i).trans (hhold_slack j hw i)
  have hAll :
      ∀ j,
        ContractWeightedBound (E := E) sol c depth W j ∧
        ContractSampleTube (E := E) sol c rLE j ∧
        ContractWindowTube (E := E) sol c rLE j ∧
        ContractZWindowTube (E := E) sol c rLE j ∧
        ContractBranchLocked (E := E) S sol c j ∧
        ContractRecurrenceAt (E := E) sol c amp η j := by
    intro j
    induction j with
    | zero =>
        have hw : ContractWeightedBound (E := E) sol c depth W 0 := hinit_weighted
        have hs := hsample_of_weighted 0 hw
        have hwin := hwindow_of_weighted 0 hw
        have hzwin := hz_window_of_weighted 0 hw
        have hb := hbranch_of_window 0 hwin
        have hr := hrecurrence_of_branch 0 hw hwin hb
        exact ⟨hw, hs, hwin, hzwin, hb, hr⟩
    | succ j ih =>
        have hw : ContractWeightedBound (E := E) sol c depth W (j + 1) :=
          hweighted_step j ih.1 ih.2.2.2.2.2
        have hs := hsample_of_weighted (j + 1) hw
        have hwin := hwindow_of_weighted (j + 1) hw
        have hzwin := hz_window_of_weighted (j + 1) hw
        have hb := hbranch_of_window (j + 1) hwin
        have hr := hrecurrence_of_branch (j + 1) hw hwin hb
        exact ⟨hw, hs, hwin, hzwin, hb, hr⟩
  refine
    { weighted := ?_
      sample_tube := ?_
      window_tube := ?_
      z_window_tube := ?_
      branch_locked := ?_
      recurrence := ?_
      moving_box := hmoving_box
      flag_reset_bound := ?_
      flag_z_read_window := ?_ }
  · intro j
    exact (hAll j).1
  · intro j
    exact (hAll j).2.1
  · intro j
    exact (hAll j).2.2.1
  · intro j
    exact (hAll j).2.2.2.1
  · intro j
    exact (hAll j).2.2.2.2.1
  · intro j
    exact (hAll j).2.2.2.2.2
  · intro j
    have hr := (hAll j).2.2.2.2.2 flagCoord
    have hzero := hamp_reset j flagCoord hflag_reset
    simpa [ContractRecurrenceAt, hzero] using hr
  · intro j t ht
    exact (hflag_z_read_window_bridge j t ht).trans
      (by
        have hr := (hAll j).2.2.2.2.2 flagCoord
        have hzero := hamp_reset j flagCoord hflag_reset
        simpa [ContractRecurrenceAt, hzero] using hr)

end

end Ripple.BoundedUniversality.BGP
