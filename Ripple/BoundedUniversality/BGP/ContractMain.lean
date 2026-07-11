import Ripple.BoundedUniversality.BGP.ContractTracking
import Ripple.BoundedUniversality.BGP.DynamicMain

/-!
Ripple.BoundedUniversality.BGP.ContractMain
-----------------------
Contract readout and main assembly interface.

Design source:
* `notes/gpt-life2-contract-main.md`, section "Important latch issue" onward.

This file is intentionally additive.  It keeps the contract chain separate from
the strict-snap dynamic chain and exposes the remaining field-realization data
as explicit polynomial/compactification hypotheses.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Ripple.BoundedUniversality.Core
open scoped BigOperators

/-! ## Contract flag readout -/

/-- Eventual latch semantics before compactification. -/
structure ContractFlagReadout (haltedAt : ℕ → Prop) (out : ℝ → ℝ) where
  correct_halt :
    (∃ N : ℕ, haltedAt N) →
      ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ out t ∧ out t ≤ 1
  correct_nonhalt :
    (∀ N : ℕ, ¬ haltedAt N) →
      ∃ T : ℝ, ∀ t ≥ T, 0 ≤ out t ∧ out t ≤ 1 / 4

/-- Halt flag semantics for a reset coordinate. -/
structure HaltFlagPackage
    {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    (E : StackMachineEncoding d nS M) (flagCoord : Fin d) where
  flagMargin : ℝ
  margin_pos : 0 < flagMargin
  margin_le_quarter : flagMargin ≤ 1 / 4
  halted_flag : ∀ c : Conf, M.halted c = true → E.enc c flagCoord = 1
  running_flag : ∀ c : Conf, M.halted c = false → E.enc c flagCoord = 0
  flag_reset : E.coordStackIndex flagCoord = none

/--
Bernstein-style indicator specialized to the flag coordinate.  The domain
condition is explicit: on read windows the flag coordinate must lie in `[0,1]`
or the caller must feed a clipped coordinate.
-/
structure ContractFlagIndicatorPackage {d : ℕ} (flagCoord : Fin d) where
  Hval : (Fin d → ℝ) → ℝ
  eta : ℝ
  eta_nonneg : 0 ≤ eta
  eta_lt : eta < 1 / 8
  in_unit :
    ∀ x : Fin d → ℝ, x flagCoord ∈ Set.Icc (0 : ℝ) 1 →
      0 ≤ Hval x ∧ Hval x ≤ 1
  on_flag_one :
    ∀ x : Fin d → ℝ, x flagCoord ∈ Set.Icc (0 : ℝ) 1 →
      |x flagCoord - 1| ≤ 1 / 4 →
        1 - eta ≤ Hval x
  on_flag_zero :
    ∀ x : Fin d → ℝ, x flagCoord ∈ Set.Icc (0 : ℝ) 1 →
      |x flagCoord - 0| ≤ 1 / 4 →
        Hval x ≤ eta

/-- Latch coordinate riding on the contract iterator's `z` register. -/
structure ContractHaltLatchSol
    {d : ℕ}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (Hval : (Fin d → ℝ) → ℝ) (K : ℝ) (R : ℕ) where
  a : ℝ → ℝ
  init_a : a 0 = 0
  ode_a : ∀ t : ℝ,
    HasDerivAt a (K * gPulse R t * (Hval (sol.z t) - a t)) t

/--
Analytic latch convergence supplied by the already-proved latch machinery.
The contract theorem below supplies only the flag-to-indicator facts; this
kernel supplies the scalar ODE convergence constants.
-/
structure ContractLatchConvergenceKernel
    {d : ℕ}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (flagCoord : Fin d)
    (I : ContractFlagIndicatorPackage flagCoord)
    (La : ContractHaltLatchSol sol I.Hval K R) where
  K_pos : 0 < K
  high_from_eventual_indicator :
    (∃ J : ℕ, ∀ j ≥ J, ∀ t ∈ sched.zActiveWindow j,
      1 - I.eta ≤ I.Hval (sol.z t)) →
      ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ La.a t ∧ La.a t ≤ 1
  low_from_all_indicator :
    (∀ j : ℕ, ∀ t ∈ sched.zActiveWindow j,
      I.Hval (sol.z t) ≤ I.eta) →
      ∃ T : ℝ, ∀ t ≥ T, 0 ≤ La.a t ∧ La.a t ≤ 1 / 4

lemma contract_flag_error_bound
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {d nS : ℕ} {E : StackMachineEncoding d nS M}
    {S : RobustStepContract M E}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {sol : DynContractIteratorSol (Fin d) p sched F}
    {c : ℕ → Conf} {rLE : Fin d → ℝ}
    {amp η W : ℕ → Fin d → ℝ} {depth : ℕ → Fin d → ℤ}
    {movingBox : ℝ → (Fin d → ℝ) → (Fin d → ℝ) → Prop}
    {flagCoord : Fin d}
    (track :
      ContractTrackingResult (E := E) S sol c rLE amp η W depth movingBox flagCoord) :
    ∀ j, contractBoundaryError (E := E) sol c (j + 1) flagCoord ≤ η j flagCoord :=
  track.flag_reset_bound

private lemma discrete_halted_of_step_orbit
    {Conf : Type} [Primcodable Conf] (M : DiscreteMachine Conf)
    {c : ℕ → Conf}
    (hc_step : ∀ j, c (j + 1) = M.step (c j))
    {n : ℕ} (hn : M.halted (c n) = true) :
    ∀ m : ℕ, n ≤ m → M.halted (c m) = true := by
  intro m hnm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  induction k with
  | zero =>
      simpa using hn
  | succ k ih =>
      rw [Nat.add_succ]
      rw [hc_step]
      have ih' : M.halted (c (n + k)) = true := ih (Nat.le_add_right n k)
      have hfix : M.step (c (n + k)) = c (n + k) :=
        M.halted_absorbing _ ih'
      simpa [hfix] using ih'

private lemma abs_sub_le_of_eq_right
    {a b c r : ℝ} (hb : b = c) (h : |a - b| ≤ r) :
    |a - c| ≤ r := by
  simpa [hb] using h

/--
H1. Contract halt-flag readout.

The latch reads the reset flag coordinate.  The irreversible-latch issue is
handled by Design 1: `hflag_margin_all` is an all-cycle read-window margin.
The indicator domain is a separate read-window hypothesis.
-/
theorem contract_halt_flag_readout
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {d nS : ℕ} {E : StackMachineEncoding d nS M}
    {S : RobustStepContract M E}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (c : ℕ → Conf)
    (hc_step : ∀ j, c (j + 1) = M.step (c j))
    {rLE : Fin d → ℝ}
    {amp η W : ℕ → Fin d → ℝ} {depth : ℕ → Fin d → ℤ}
    {movingBox : ℝ → (Fin d → ℝ) → (Fin d → ℝ) → Prop}
    (flagCoord : Fin d)
    (track :
      ContractTrackingResult (E := E) S sol c rLE amp η W depth movingBox flagCoord)
    (flagPkg : HaltFlagPackage E flagCoord)
    (I : ContractFlagIndicatorPackage flagCoord)
    {K : ℝ} {R : ℕ}
    (La : ContractHaltLatchSol sol I.Hval K R)
    (kernel : ContractLatchConvergenceKernel sol flagCoord I La)
    (hflag_margin_all : ∀ j, η j flagCoord ≤ flagPkg.flagMargin)
    (hflag_margin_indicator : flagPkg.flagMargin ≤ 1 / 4)
    (hflag_domain :
      ∀ j t, t ∈ sched.zActiveWindow j →
        sol.z t flagCoord ∈ Set.Icc (0 : ℝ) 1) :
    ContractFlagReadout
      (fun j => M.halted (c j) = true)
      La.a := by
  classical
  have _hreset := flagPkg.flag_reset
  have _hboundary := contract_flag_error_bound track
  refine
    { correct_halt := ?_
      correct_nonhalt := ?_ }
  · rintro ⟨N, hN⟩
    apply kernel.high_from_eventual_indicator
    refine ⟨N, ?_⟩
    intro j hj t ht
    have hhalt_j : M.halted (c j) = true :=
      discrete_halted_of_step_orbit M hc_step hN j hj
    have hflag_eq : E.enc (c j) flagCoord = 1 :=
      flagPkg.halted_flag (c j) hhalt_j
    have hclose_to_one :
        |sol.z t flagCoord - 1| ≤ 1 / 4 := by
      exact (abs_sub_le_of_eq_right hflag_eq (track.flag_z_read_window j t ht)).trans
        ((hflag_margin_all j).trans hflag_margin_indicator)
    exact I.on_flag_one (sol.z t) (hflag_domain j t ht) hclose_to_one
  · intro hnonhalt
    apply kernel.low_from_all_indicator
    intro j t ht
    have hhalt_false : M.halted (c j) = false := by
      cases h : M.halted (c j) with
      | false => rfl
      | true => exact False.elim (hnonhalt j h)
    have hflag_eq : E.enc (c j) flagCoord = 0 :=
      flagPkg.running_flag (c j) hhalt_false
    have hclose_to_zero :
        |sol.z t flagCoord - 0| ≤ 1 / 4 := by
      exact (abs_sub_le_of_eq_right hflag_eq (track.flag_z_read_window j t ht)).trans
        ((hflag_margin_all j).trans hflag_margin_indicator)
    exact I.on_flag_zero (sol.z t) (hflag_domain j t ht) hclose_to_zero

/-! ## Contract Euclidean assembly -/

def contractOrbit
    {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    (E : StackMachineEncoding d nS M) (w j : ℕ) : Fin d → ℝ :=
  E.enc (M.step^[j] (M.init w))

structure ContractPerCycleBox
    {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    (E : StackMachineEncoding d nS M)
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (w : ℕ) (D : ℝ) where
  box :
    ∀ j t, t ∈ sched.zActiveWindow j →
      (∀ i, |contractOrbit E w (j + 1) i - contractOrbit E w j i| ≤ D) ∧
      (∀ i, |sol.z t i - contractOrbit E w j i| ≤ D) ∧
      (∀ i, |sol.u t i - contractOrbit E w j i| ≤ D) ∧
      (∀ i, |sol.w t i - contractOrbit E w j i| ≤ D)

structure ContractTrackingInputs
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {d nS : ℕ} {E : StackMachineEncoding d nS M}
    (S : RobustStepContract M E)
    (p : DynGateParams)
    (sched : PhaseSchedule)
    (sol : DynContractIteratorSol (Fin d) p sched S.F)
    (c : ℕ → Conf)
    (κ χ : ℕ → ℝ)
    (rLE : Fin d → ℝ)
    (amp η W : ℕ → Fin d → ℝ)
    (depth : ℕ → Fin d → ℤ)
    (movingBox : ℝ → (Fin d → ℝ) → (Fin d → ℝ) → Prop)
    (flagCoord : Fin d) where
  hamp_stack :
    ∀ j s, amp j (E.stackCoord s) = (E.k : ℝ) ^ E.stackDelta (c j) s
  hamp_reset :
    ∀ j i, E.coordStackIndex i = none → amp j i = 0
  hmu_large :
    ∀ j t, t ∈ sched.zActiveWindow j → S.mu_min ≤ sol.μ t
  heps_mono :
    ∀ i {mu0 mu1 : ℝ}, mu0 ≤ mu1 → S.epsF mu1 i ≤ S.epsF mu0 i
  hinit_weighted :
    ContractWeightedBound (E := E) sol c depth W 0
  hchiD_nonneg : ∀ j, 0 ≤ χ j * S.D
  hhold_slack :
    ∀ j, ContractWeightedBound (E := E) sol c depth W j →
      ∀ i, contractBoundaryError (E := E) sol c j i + χ j * S.D ≤ rLE i
  hwindow_hold :
    ∀ j t, t ∈ sched.zActiveWindow j → ∀ i,
      |sol.u t i - E.enc (c j) i| ≤
        contractBoundaryError (E := E) sol c j i + χ j * S.D
  hz_window_hold :
    ∀ j t, t ∈ sched.zActiveWindow j → ∀ i,
      |sol.z t i - E.enc (c j) i| ≤
        contractBoundaryError (E := E) sol c j i + χ j * S.D
  hflag_z_read_window_bridge :
    ∀ j t, t ∈ sched.zActiveWindow j →
      |sol.z t flagCoord - E.enc (c j) flagCoord| ≤
        contractBoundaryError (E := E) sol c (j + 1) flagCoord
  hbranch_of_window :
    ∀ j, ContractWindowTube (E := E) sol c rLE j →
      ContractBranchLocked (E := E) S sol c j
  hrecurrence_of_branch :
    ∀ j,
      ContractWeightedBound (E := E) sol c depth W j →
      ContractWindowTube (E := E) sol c rLE j →
      ContractBranchLocked (E := E) S sol c j →
      ContractRecurrenceAt (E := E) sol c amp η j
  hweighted_step :
    ∀ j,
      ContractWeightedBound (E := E) sol c depth W j →
      ContractRecurrenceAt (E := E) sol c amp η j →
      ContractWeightedBound (E := E) sol c depth W (j + 1)
  hmoving_box :
    ∀ t ∈ sched.domain, movingBox t (sol.z t) (sol.u t)

structure ContractDynAssembledEuclideanSimulation
    {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    (M : DiscreteMachine Conf) (E : StackMachineEncoding d nS M)
    (S : RobustStepContract M E)
    (p : DynGateParams) (sched : PhaseSchedule)
    (flagCoord : Fin d)
    (I : ContractFlagIndicatorPackage flagCoord)
    (K : ℝ) (R : ℕ) where
  K_pos : 0 < K
  per_input :
    ∀ w : ℕ,
      ∃ (sol : DynContractIteratorSol (Fin d) p sched S.F)
        (La : ContractHaltLatchSol sol I.Hval K R),
        (M.haltsOn w →
          ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ La.a t ∧ La.a t ≤ 1) ∧
        (¬ M.haltsOn w →
          ∃ T : ℝ, ∀ t ≥ T, 0 ≤ La.a t ∧ La.a t ≤ 1 / 4)

private lemma step_orbit_step
    {Conf : Type} [Primcodable Conf] (M : DiscreteMachine Conf) (w j : ℕ) :
    M.step^[j + 1] (M.init w) = M.step (M.step^[j] (M.init w)) := by
  rw [Function.iterate_succ_apply']

private lemma haltsOn_iff_orbit_halted
    {Conf : Type} [Primcodable Conf] (M : DiscreteMachine Conf) (w : ℕ) :
    M.haltsOn w ↔ ∃ N : ℕ, M.halted (M.step^[N] (M.init w)) = true := by
  rfl

/--
H2. Contract Euclidean simulation assembly.

The supplier is box-only.  Tracking is rebuilt with
`contract_all_time_tracking`, and readout comes from H1 on the reset flag.
-/
theorem contract_dyn_assembled_euclidean_simulation
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
    (movingBox : ℕ → ℝ → (Fin d → ℝ) → (Fin d → ℝ) → Prop)
    (D : ℝ)
    (hsupply :
      ∀ w : ℕ,
        ∃ sol : DynContractIteratorSol (Fin d) p sched S.F,
          ContractPerCycleBox E sol w D)
    (htracking_inputs :
      ∀ (w : ℕ) (sol : DynContractIteratorSol (Fin d) p sched S.F),
        ContractPerCycleBox E sol w D →
          ContractTrackingInputs S p sched sol
            (fun j => M.step^[j] (M.init w))
            κ χ rLE (amp w) (η sol) (W w) (depth w) (movingBox w) flagCoord)
    (hlatch :
      ∀ sol : DynContractIteratorSol (Fin d) p sched S.F,
        ∃ La : ContractHaltLatchSol sol I.Hval K R,
          ContractLatchConvergenceKernel sol flagCoord I La)
    (hflag_margin_all : ∀ sol j, η sol j flagCoord ≤ flagPkg.flagMargin)
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
    exact step_orbit_step M w j
  have inputs := htracking_inputs w sol box
  have track :
      ContractTrackingResult (E := E) S sol c rLE (amp w) (η sol) (W w) (depth w)
        (movingBox w) flagCoord :=
    contract_all_time_tracking
      (S := S) p sched sol c hc_step κ χ rLE (amp w) (η sol) (W w) (depth w)
        (movingBox w) flagCoord
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
      (hflag_margin_all sol) hflag_margin_indicator (hflag_domain w sol box)
  refine ⟨sol, La, ?_, ?_⟩
  · intro hw
    exact readout.correct_halt ((haltsOn_iff_orbit_halted M w).mp hw)
  · intro hw
    apply readout.correct_nonhalt
    intro N hN
    exact hw ((haltsOn_iff_orbit_halted M w).mpr ⟨N, hN⟩)

/-! ## Contract main theorem packaging -/

structure ContractPolynomialFieldPackage
    {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    (M : UndecidableMachine Conf)
    (E : StackMachineEncoding d nS M.toDiscreteMachine)
    (S : RobustStepContract M.toDiscreteMachine E)
    (p : DynGateParams) (sched : PhaseSchedule)
    (flagCoord : Fin d)
    (I : ContractFlagIndicatorPackage flagCoord)
    (K : ℝ) (R : ℕ) where
  nE : ℕ
  field : Fin nE → MvPolynomial (Fin nE) ℚ
  tuple :
    ∀ (_w : ℕ) (sol : DynContractIteratorSol (Fin d) p sched S.F),
      ContractHaltLatchSol sol I.Hval K R → ℝ → Fin nE → ℝ
  tuple_ode :
    ∀ (w : ℕ) (sol : DynContractIteratorSol (Fin d) p sched S.F)
      (La : ContractHaltLatchSol sol I.Hval K R) (t : ℝ), 0 ≤ t →
        HasDerivAt (tuple w sol La)
          (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ)
            (tuple w sol La t) (field i)) t
  init : ℕ → Fin (nE + 1) → ℚ
  init_presented : ∃ f : ℕ → Fin (nE + 1) → ℤ × ℕ, Computable f ∧
    ∀ w i, (f w i).2 ≠ 0 ∧ init w i = (f w i).1 / ((f w i).2 : ℚ)
  init_zero :
    ∀ (w : ℕ) (sol : DynContractIteratorSol (Fin d) p sched S.F)
      (La : ContractHaltLatchSol sol I.Hval K R),
        ((init w 0 : ℚ) : ℝ) =
          ((∑ i : Fin nE, tuple w sol La 0 i ^ 2) - 1) /
            ((∑ i : Fin nE, tuple w sol La 0 i ^ 2) + 1)
  init_succ :
    ∀ (w : ℕ) (sol : DynContractIteratorSol (Fin d) p sched S.F)
      (La : ContractHaltLatchSol sol I.Hval K R) (i : Fin nE),
        ((init w i.succ : ℚ) : ℝ) =
          2 * tuple w sol La 0 i /
            ((∑ k : Fin nE, tuple w sol La 0 k ^ 2) + 1)
  latchCoord : Fin nE
  latch_value :
    ∀ (w : ℕ) (sol : DynContractIteratorSol (Fin d) p sched S.F)
      (La : ContractHaltLatchSol sol I.Hval K R) (t : ℝ),
        tuple w sol La t latchCoord = La.a t

private theorem contract_stereo_sum_sq {nE : ℕ} (x : Fin nE → ℝ) :
    (∑ j : Fin (nE + 1), stereo x j ^ 2) = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [stereo, Fin.cases_zero, Fin.cases_succ]
  set r : ℝ := ∑ i : Fin nE, x i ^ 2 with hr
  have hden : r + 1 ≠ 0 := by
    have hr0 : 0 ≤ r := by
      dsimp [r]
      exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)
    nlinarith
  have htail :
      (∑ i : Fin nE, (2 * x i / (r + 1)) ^ 2) =
        4 * r / (r + 1) ^ 2 := by
    simp only [div_pow, mul_pow]
    calc
      (∑ i : Fin nE, (2 ^ 2 * x i ^ 2) / (r + 1) ^ 2)
          = (∑ i : Fin nE, (4 / (r + 1) ^ 2) * x i ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = (4 / (r + 1) ^ 2) * r := by
            rw [← Finset.mul_sum]
      _ = 4 * r / (r + 1) ^ 2 := by ring
  simp only [stereoDenom, ← hr]
  rw [htail]
  field_simp [hden]
  ring

private theorem contract_stereo_abs_le_one {nE : ℕ} (x : Fin nE → ℝ)
    (j : Fin (nE + 1)) : |stereo x j| ≤ 1 := by
  have hterm :
      stereo x j ^ 2 ≤ ∑ k : Fin (nE + 1), stereo x k ^ 2 :=
    Finset.single_le_sum
      (fun k _hk => sq_nonneg (stereo x k))
      (Finset.mem_univ j)
  have hsq : stereo x j ^ 2 ≤ 1 := by
    simpa [contract_stereo_sum_sq x] using hterm
  exact (sq_le_one_iff_abs_le_one (stereo x j)).mp hsq

/--
H3. Final contract main theorem.

The polynomial field package carries only the Euclidean tuple field layer:
the assembled rational vector field, the tuple trajectory ODE, honest initial
presentation data, and the ambient latch coordinate.  This theorem constructs
the compactified sphere trajectory and performs the chart readout transfer.
-/
theorem main_assembled_dyn_contract
    {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    (M : UndecidableMachine Conf)
    (E : StackMachineEncoding d nS M.toDiscreteMachine)
    (S : RobustStepContract M.toDiscreteMachine E)
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
    (movingBox : ℕ → ℝ → (Fin d → ℝ) → (Fin d → ℝ) → Prop)
    (D : ℝ)
    (hsupply :
      ∀ w : ℕ,
        ∃ sol : DynContractIteratorSol (Fin d) p sched S.F,
          ContractPerCycleBox E sol w D)
    (htracking_inputs :
      ∀ (w : ℕ) (sol : DynContractIteratorSol (Fin d) p sched S.F),
        ContractPerCycleBox E sol w D →
          ContractTrackingInputs S p sched sol
            (fun j => M.toDiscreteMachine.step^[j] (M.toDiscreteMachine.init w))
            κ χ rLE (amp w) (η sol) (W w) (depth w) (movingBox w) flagCoord)
    (hlatch :
      ∀ sol : DynContractIteratorSol (Fin d) p sched S.F,
        ∃ La : ContractHaltLatchSol sol I.Hval K R,
          ContractLatchConvergenceKernel sol flagCoord I La)
    (hflag_margin_all : ∀ sol j, η sol j flagCoord ≤ flagPkg.flagMargin)
    (hflag_margin_indicator : flagPkg.flagMargin ≤ 1 / 4)
    (hflag_domain :
      ∀ (w : ℕ) (sol : DynContractIteratorSol (Fin d) p sched S.F)
        (_box : ContractPerCycleBox E sol w D),
        ∀ j t, t ∈ sched.zActiveWindow j →
          sol.z t flagCoord ∈ Set.Icc (0 : ℝ) 1)
    (fieldPkg :
      ContractPolynomialFieldPackage M E S p sched flagCoord I K R) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P M) := by
  classical
  have euclidean :
      ContractDynAssembledEuclideanSimulation
        M.toDiscreteMachine E S p sched flagCoord I K R :=
    contract_dyn_assembled_euclidean_simulation
      M.toDiscreteMachine E S p sched flagCoord flagPkg I hK
      κ χ rLE amp η W depth movingBox D hsupply htracking_inputs hlatch
      hflag_margin_all hflag_margin_indicator hflag_domain
  choose sol La hhalt hnonhalt using euclidean.per_input
  obtain ⟨Y, _htang, htransfer⟩ :=
    compactification_exists fieldPkg.nE fieldPkg.field
  let P : Ripple.BoundedUniversality.GPAC.PIVP ℚ :=
    { n := fieldPkg.nE + 1
      vf := Y
      init := fieldPkg.init }
  have htrans : ∀ w,
      ∃ s : ℝ → ℝ, s 0 = 0 ∧ StrictMonoOn s (Set.Ici 0) ∧
        Filter.Tendsto s Filter.atTop Filter.atTop ∧
        ∀ τ : ℝ, 0 ≤ τ → HasDerivAt
          (fun σ => stereo (fieldPkg.tuple w (sol w) (La w) (s σ)))
          (fun j => MvPolynomial.eval₂ (algebraMap ℚ ℝ)
            (stereo (fieldPkg.tuple w (sol w) (La w) (s τ))) (Y j)) τ := by
    intro w
    exact htransfer (fieldPkg.tuple w (sol w) (La w))
      (fieldPkg.tuple_ode w (sol w) (La w))
  choose s hs0 _hsmono hstend hsphere using htrans
  refine ⟨P, ⟨{
    traj := fun w τ => stereo (fieldPkg.tuple w (sol w) (La w) (s w τ))
    init_at_zero := ?_
    solves_ode := ?_
    bounded := ?_
    encoder_presented := fieldPkg.init_presented
    readout := ?_
    correct_halt := ?_
    correct_nonhalt := ?_
  }⟩⟩
  · intro w
    funext j
    rw [hs0 w]
    dsimp [P, Ripple.BoundedUniversality.GPAC.PIVP.realInit]
    refine Fin.cases ?_ ?_ j
    · simp [stereo, stereoDenom, fieldPkg.init_zero w (sol w) (La w)]
    · intro i
      simp [stereo, stereoDenom, fieldPkg.init_succ w (sol w) (La w) i]
  · intro w τ hτ
    simpa [P, Ripple.BoundedUniversality.GPAC.PIVP.evalVF] using hsphere w τ hτ
  · refine ⟨1, by norm_num, ?_⟩
    intro w τ i hτ
    exact contract_stereo_abs_le_one _ _
  · exact { hA := fieldPkg.latchCoord.succ, h0 := 0, ne := by simp }
  · intro w hw
    obtain ⟨T, hT⟩ := hhalt w hw
    have hev : ∀ᶠ τ in Filter.atTop, max T 0 ≤ s w τ :=
      (hstend w).eventually (Filter.eventually_ge_atTop (max T 0))
    obtain ⟨Θ, hΘ⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max Θ 0, ?_⟩
    intro τ hτ
    have hΘτ : Θ ≤ τ := le_trans (le_max_left Θ 0) hτ
    have hsge : max T 0 ≤ s w τ := hΘ τ hΘτ
    have hTle : T ≤ s w τ := le_trans (le_max_left T 0) hsge
    have hLatch := hT (s w τ) hTle
    have hreg :=
      (stereo_readout_transfer
        (fieldPkg.tuple w (sol w) (La w) (s w τ)) fieldPkg.latchCoord).1
        (by simpa [fieldPkg.latch_value w (sol w) (La w) (s w τ)] using hLatch)
    simpa [ChartThresholdReadout.HaltRegion, P] using hreg
  · intro w hw
    obtain ⟨T, hT⟩ := hnonhalt w hw
    have hev : ∀ᶠ τ in Filter.atTop, max T 0 ≤ s w τ :=
      (hstend w).eventually (Filter.eventually_ge_atTop (max T 0))
    obtain ⟨Θ, hΘ⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max Θ 0, ?_⟩
    intro τ hτ
    have hΘτ : Θ ≤ τ := le_trans (le_max_left Θ 0) hτ
    have hsge : max T 0 ≤ s w τ := hΘ τ hΘτ
    have hTle : T ≤ s w τ := le_trans (le_max_left T 0) hsge
    have hLatch := hT (s w τ) hTle
    have hreg :=
      (stereo_readout_transfer
        (fieldPkg.tuple w (sol w) (La w) (s w τ)) fieldPkg.latchCoord).2
        (by simpa [fieldPkg.latch_value w (sol w) (La w) (s w τ)] using hLatch)
    simpa [ChartThresholdReadout.NonhaltRegion, P] using hreg

/--
Compactification/readout transfer from an already assembled Euclidean contract
simulation.

This is the tail of `main_assembled_dyn_contract` factored out so that callers
can build the Euclidean simulation with a solution-specific hypothesis shape,
instead of proving tracking/margin/domain/latch facts for arbitrary ODE
solutions.
-/
theorem main_assembled_dyn_contract_of_euclidean
    {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    (M : UndecidableMachine Conf)
    (E : StackMachineEncoding d nS M.toDiscreteMachine)
    (S : RobustStepContract M.toDiscreteMachine E)
    (p : DynGateParams) (sched : PhaseSchedule)
    (flagCoord : Fin d)
    (I : ContractFlagIndicatorPackage flagCoord)
    {K : ℝ} {R : ℕ}
    (euclidean :
      ContractDynAssembledEuclideanSimulation
        M.toDiscreteMachine E S p sched flagCoord I K R)
    (fieldPkg :
      ContractPolynomialFieldPackage M E S p sched flagCoord I K R) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P M) := by
  classical
  choose sol La hhalt hnonhalt using euclidean.per_input
  obtain ⟨Y, _htang, htransfer⟩ :=
    compactification_exists fieldPkg.nE fieldPkg.field
  let P : Ripple.BoundedUniversality.GPAC.PIVP ℚ :=
    { n := fieldPkg.nE + 1
      vf := Y
      init := fieldPkg.init }
  have htrans : ∀ w,
      ∃ s : ℝ → ℝ, s 0 = 0 ∧ StrictMonoOn s (Set.Ici 0) ∧
        Filter.Tendsto s Filter.atTop Filter.atTop ∧
        ∀ τ : ℝ, 0 ≤ τ → HasDerivAt
          (fun σ => stereo (fieldPkg.tuple w (sol w) (La w) (s σ)))
          (fun j => MvPolynomial.eval₂ (algebraMap ℚ ℝ)
            (stereo (fieldPkg.tuple w (sol w) (La w) (s τ))) (Y j)) τ := by
    intro w
    exact htransfer (fieldPkg.tuple w (sol w) (La w))
      (fieldPkg.tuple_ode w (sol w) (La w))
  choose s hs0 _hsmono hstend hsphere using htrans
  refine ⟨P, ⟨{
    traj := fun w τ => stereo (fieldPkg.tuple w (sol w) (La w) (s w τ))
    init_at_zero := ?_
    solves_ode := ?_
    bounded := ?_
    encoder_presented := fieldPkg.init_presented
    readout := ?_
    correct_halt := ?_
    correct_nonhalt := ?_
  }⟩⟩
  · intro w
    funext j
    rw [hs0 w]
    dsimp [P, Ripple.BoundedUniversality.GPAC.PIVP.realInit]
    refine Fin.cases ?_ ?_ j
    · simp [stereo, stereoDenom, fieldPkg.init_zero w (sol w) (La w)]
    · intro i
      simp [stereo, stereoDenom, fieldPkg.init_succ w (sol w) (La w) i]
  · intro w τ hτ
    simpa [P, Ripple.BoundedUniversality.GPAC.PIVP.evalVF] using hsphere w τ hτ
  · refine ⟨1, by norm_num, ?_⟩
    intro w τ i hτ
    exact contract_stereo_abs_le_one _ _
  · exact { hA := fieldPkg.latchCoord.succ, h0 := 0, ne := by simp }
  · intro w hw
    obtain ⟨T, hT⟩ := hhalt w hw
    have hev : ∀ᶠ τ in Filter.atTop, max T 0 ≤ s w τ :=
      (hstend w).eventually (Filter.eventually_ge_atTop (max T 0))
    obtain ⟨Θ, hΘ⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max Θ 0, ?_⟩
    intro τ hτ
    have hΘτ : Θ ≤ τ := le_trans (le_max_left Θ 0) hτ
    have hsge : max T 0 ≤ s w τ := hΘ τ hΘτ
    have hTle : T ≤ s w τ := le_trans (le_max_left T 0) hsge
    have hLatch := hT (s w τ) hTle
    have hreg :=
      (stereo_readout_transfer
        (fieldPkg.tuple w (sol w) (La w) (s w τ)) fieldPkg.latchCoord).1
        (by simpa [fieldPkg.latch_value w (sol w) (La w) (s w τ)] using hLatch)
    simpa [ChartThresholdReadout.HaltRegion, P] using hreg
  · intro w hw
    obtain ⟨T, hT⟩ := hnonhalt w hw
    have hev : ∀ᶠ τ in Filter.atTop, max T 0 ≤ s w τ :=
      (hstend w).eventually (Filter.eventually_ge_atTop (max T 0))
    obtain ⟨Θ, hΘ⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max Θ 0, ?_⟩
    intro τ hτ
    have hΘτ : Θ ≤ τ := le_trans (le_max_left Θ 0) hτ
    have hsge : max T 0 ≤ s w τ := hΘ τ hΘτ
    have hTle : T ≤ s w τ := le_trans (le_max_left T 0) hsge
    have hLatch := hT (s w τ) hTle
    have hreg :=
      (stereo_readout_transfer
        (fieldPkg.tuple w (sol w) (La w) (s w τ)) fieldPkg.latchCoord).2
        (by simpa [fieldPkg.latch_value w (sol w) (La w) (s w τ)] using hLatch)
    simpa [ChartThresholdReadout.NonhaltRegion, P] using hreg

/--
Euclidean contract assembly with solution-specific data.

For each input, the same supplied solution carries its per-cycle box, tracking
inputs, latch kernel, flag margin, and flag-domain facts.  This is the
hypothesis shape needed by finite-horizon ODE producers: no downstream fact is
required for arbitrary solutions that were not constructed by the supply
argument.
-/
theorem contract_dyn_assembled_euclidean_simulation_rich_supply
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
    (movingBox : ℕ → ℝ → (Fin d → ℝ) → (Fin d → ℝ) → Prop)
    (D : ℝ)
    (hsupply_rich :
      ∀ w : ℕ,
        ∃ sol : DynContractIteratorSol (Fin d) p sched S.F,
        ∃ _box : ContractPerCycleBox E sol w D,
          ContractTrackingInputs S p sched sol
            (fun j => M.step^[j] (M.init w))
            κ χ rLE (amp w) (η sol) (W w) (depth w) (movingBox w) flagCoord ∧
          (∃ La : ContractHaltLatchSol sol I.Hval K R,
            ContractLatchConvergenceKernel sol flagCoord I La) ∧
          (∀ j, η sol j flagCoord ≤ flagPkg.flagMargin) ∧
          (∀ j t, t ∈ sched.zActiveWindow j →
            sol.z t flagCoord ∈ Set.Icc (0 : ℝ) 1))
    (hflag_margin_indicator : flagPkg.flagMargin ≤ 1 / 4) :
    ContractDynAssembledEuclideanSimulation M E S p sched flagCoord I K R := by
  classical
  refine
    { K_pos := hK
      per_input := ?_ }
  intro w
  obtain ⟨sol, _box, inputs, hlatch, hflag_margin_all, hflag_domain⟩ :=
    hsupply_rich w
  let c : ℕ → Conf := fun j => M.step^[j] (M.init w)
  have hc_step : ∀ j, c (j + 1) = M.step (c j) := by
    intro j
    dsimp [c]
    exact step_orbit_step M w j
  have track :
      ContractTrackingResult (E := E) S sol c rLE (amp w) (η sol) (W w) (depth w)
        (movingBox w) flagCoord :=
    contract_all_time_tracking
      (S := S) p sched sol c hc_step κ χ rLE (amp w) (η sol) (W w) (depth w)
        (movingBox w) flagCoord
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
    exact readout.correct_halt ((haltsOn_iff_orbit_halted M w).mp hw)
  · intro hw
    apply readout.correct_nonhalt
    intro N hN
    exact hw ((haltsOn_iff_orbit_halted M w).mpr ⟨N, hN⟩)

/--
Final contract main theorem with rich, solution-specific supply data.

This is definitionally the same compactified conclusion as
`main_assembled_dyn_contract`, but its analytical inputs are bundled with the
solution constructed for each input word.
-/
theorem main_assembled_dyn_contract_rich_supply
    {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    (M : UndecidableMachine Conf)
    (E : StackMachineEncoding d nS M.toDiscreteMachine)
    (S : RobustStepContract M.toDiscreteMachine E)
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
    (movingBox : ℕ → ℝ → (Fin d → ℝ) → (Fin d → ℝ) → Prop)
    (D : ℝ)
    (hsupply_rich :
      ∀ w : ℕ,
        ∃ sol : DynContractIteratorSol (Fin d) p sched S.F,
        ∃ _box : ContractPerCycleBox E sol w D,
          ContractTrackingInputs S p sched sol
            (fun j => M.toDiscreteMachine.step^[j] (M.toDiscreteMachine.init w))
            κ χ rLE (amp w) (η sol) (W w) (depth w) (movingBox w) flagCoord ∧
          (∃ La : ContractHaltLatchSol sol I.Hval K R,
            ContractLatchConvergenceKernel sol flagCoord I La) ∧
          (∀ j, η sol j flagCoord ≤ flagPkg.flagMargin) ∧
          (∀ j t, t ∈ sched.zActiveWindow j →
            sol.z t flagCoord ∈ Set.Icc (0 : ℝ) 1))
    (hflag_margin_indicator : flagPkg.flagMargin ≤ 1 / 4)
    (fieldPkg :
      ContractPolynomialFieldPackage M E S p sched flagCoord I K R) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P M) :=
  main_assembled_dyn_contract_of_euclidean
    M E S p sched flagCoord I
    (contract_dyn_assembled_euclidean_simulation_rich_supply
      M.toDiscreteMachine E S p sched flagCoord flagPkg I hK
      κ χ rLE amp η W depth movingBox D hsupply_rich hflag_margin_indicator)
    fieldPkg

#print axioms main_assembled_dyn_contract_of_euclidean
#print axioms contract_dyn_assembled_euclidean_simulation_rich_supply
#print axioms main_assembled_dyn_contract_rich_supply

end Ripple.BoundedUniversality.BGP
