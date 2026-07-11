import Ripple.BoundedUniversality.BGP.ContractMain
import Ripple.BoundedUniversality.BGP.ContractSchedules
import Ripple.BoundedUniversality.BGP.LatchAssembly
import Ripple.BoundedUniversality.BGP.DynamicAssembly

/-!
Ripple.BoundedUniversality.BGP.ContractLatch
------------------------
Contract latch and flag-readout adapters for SPEC3 items 19/20/21/22/24.

This file is intentionally additive.  The contract tracking and schedule
records now export the two bridge facts needed by the adapters:

* `PhaseSchedule.stableWindow_subset_zActiveWindow`;
* `ContractTrackingResult.flag_z_read_window`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Ripple.BoundedUniversality.Core
open scoped BigOperators

/-! ## L1: contract latch solution adapter -/

/--
Scalar latch existence for `DynContractIteratorSol`.

This is the contract-solution analogue of `latch_solution_exists` /
`dyn_latch_solution_exists`: the same linear ODE is solved explicitly once the
driving signal `t ↦ Hval (sol.z t)` is continuous.
-/
theorem contract_latch_solution_exists
    {d : ℕ} {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (Hval : (Fin d → ℝ) → ℝ)
    (hHcont : Continuous fun t => Hval (sol.z t))
    (K : ℝ) (R : ℕ) :
    Nonempty (ContractHaltLatchSol sol Hval K R) := by
  classical
  set φ : ℝ → ℝ := fun t => K * gPulse R t with hφdef
  have hφcont : Continuous φ := by
    have hg : Continuous (gPulse R) := gPulse_continuous R
    fun_prop
  set Φ : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, φ s with hΦdef
  have hΦderiv : ∀ t : ℝ, HasDerivAt Φ (φ t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right
      (hφcont.intervalIntegrable 0 t)
      (hφcont.stronglyMeasurableAtFilter _ _)
      hφcont.continuousAt
  have hΦcont : Continuous Φ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hΦderiv t).continuousAt
  set B : ℝ → ℝ :=
    fun t => ∫ s in (0:ℝ)..t, φ s * Hval (sol.z s) * Real.exp (Φ s) with hBdef
  have hBcont_integrand :
      Continuous (fun s : ℝ => φ s * Hval (sol.z s) * Real.exp (Φ s)) := by
    have hE : Continuous fun s : ℝ => Real.exp (Φ s) :=
      Real.continuous_exp.comp hΦcont
    exact (hφcont.mul hHcont).mul hE
  have hBderiv : ∀ t : ℝ,
      HasDerivAt B (φ t * Hval (sol.z t) * Real.exp (Φ t)) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right
      (hBcont_integrand.intervalIntegrable 0 t)
      (hBcont_integrand.stronglyMeasurableAtFilter _ _)
      hBcont_integrand.continuousAt
  set a : ℝ → ℝ := fun t => Real.exp (-(Φ t)) * B t with hadef
  refine ⟨{ a := a, init_a := ?_, ode_a := ?_ }⟩
  · simp [hadef, hBdef]
  · intro t
    have hExpDeriv : HasDerivAt (fun τ : ℝ => Real.exp (-(Φ τ)))
        (-(φ t) * Real.exp (-(Φ t))) t := by
      have hneg : HasDerivAt (fun τ : ℝ => -(Φ τ)) (-(φ t)) t :=
        (hΦderiv t).neg
      have h := hneg.exp
      convert h using 1
      ring
    have hprod := hExpDeriv.mul (hBderiv t)
    convert hprod using 1
    simp only [hadef, hφdef, hBdef]
    have hexp : Real.exp (-(Φ t)) * Real.exp (Φ t) = 1 := by
      rw [← Real.exp_add]
      simp
    have hterm :
        Real.exp (-(Φ t)) *
            (K * gPulse R t * Hval (sol.z t) * Real.exp (Φ t)) =
          K * gPulse R t * Hval (sol.z t) := by
      calc
        Real.exp (-(Φ t)) *
            (K * gPulse R t * Hval (sol.z t) * Real.exp (Φ t)) =
            (Real.exp (-(Φ t)) * Real.exp (Φ t)) *
              (K * gPulse R t * Hval (sol.z t)) := by ring
        _ = K * gPulse R t * Hval (sol.z t) := by
              rw [hexp]
              ring
    rw [hterm]
    ring

/-- Constructor wrapper for a contract convergence kernel. -/
theorem contract_latch_kernel_of_readout_bounds
    {d : ℕ} {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {sol : DynContractIteratorSol (Fin d) p sched F}
    {flagCoord : Fin d} {I : ContractFlagIndicatorPackage flagCoord}
    {K : ℝ} {R : ℕ}
    (La : ContractHaltLatchSol sol I.Hval K R)
    (hK : 0 < K)
    (hhigh :
      (∃ J : ℕ, ∀ j ≥ J, ∀ t ∈ sched.zActiveWindow j,
        1 - I.eta ≤ I.Hval (sol.z t)) →
        ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ La.a t ∧ La.a t ≤ 1)
    (hlow :
      (∀ j : ℕ, ∀ t ∈ sched.zActiveWindow j,
        I.Hval (sol.z t) ≤ I.eta) →
        ∃ T : ℝ, ∀ t ≥ T, 0 ≤ La.a t ∧ La.a t ≤ 1 / 4) :
    ContractLatchConvergenceKernel sol flagCoord I La :=
  { K_pos := hK
    high_from_eventual_indicator := hhigh
    low_from_all_indicator := hlow }

/-- Constructor wrapper for scalar convergence stated on the concrete stable
read window used by the latch analysis. -/
theorem contract_latch_kernel_of_stable_readout_bounds
    {d : ℕ} {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {sol : DynContractIteratorSol (Fin d) p sched F}
    {flagCoord : Fin d} {I : ContractFlagIndicatorPackage flagCoord}
    {K : ℝ} {R : ℕ}
    (La : ContractHaltLatchSol sol I.Hval K R)
    (hK : 0 < K)
    (hhigh :
      (∃ J : ℕ, ∀ j ≥ J,
        ∀ t ∈ Set.Icc
          (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
          (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6),
          1 - I.eta ≤ I.Hval (sol.z t)) →
        ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ La.a t ∧ La.a t ≤ 1)
    (hlow :
      (∀ j : ℕ,
        ∀ t ∈ Set.Icc
          (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
          (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6),
          I.Hval (sol.z t) ≤ I.eta) →
        ∃ T : ℝ, ∀ t ≥ T, 0 ≤ La.a t ∧ La.a t ≤ 1 / 4) :
    ContractLatchConvergenceKernel sol flagCoord I La := by
  refine
    { K_pos := hK
      high_from_eventual_indicator := ?_
      low_from_all_indicator := ?_ }
  · rintro ⟨J, hJ⟩
    apply hhigh
    refine ⟨J, ?_⟩
    intro j hj t ht
    exact hJ j hj t (sched.stableWindow_subset_zActiveWindow j ht)
  · intro hJ
    apply hlow
    intro j t ht
    exact hJ j t (sched.stableWindow_subset_zActiveWindow j ht)

/--
SPEC3 item 19 adapter shape.

The latch solution itself is constructed here.  The two convergence fields are
supplied as scalar readout hypotheses over `sched.zActiveWindow`.  For scalar
readout hypotheses over the concrete pulse-stable interval, use
`hlatch_adapter_of_stable_bounds`.
-/
theorem hlatch_adapter
    {d : ℕ} {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {flagCoord : Fin d} (I : ContractFlagIndicatorPackage flagCoord)
    {K : ℝ} {R : ℕ}
    (hK : 0 < K)
    (hHcont :
      ∀ sol : DynContractIteratorSol (Fin d) p sched F,
        Continuous fun t => I.Hval (sol.z t))
    (hhigh :
      ∀ (sol : DynContractIteratorSol (Fin d) p sched F)
        (La : ContractHaltLatchSol (p := p) (sched := sched) (F := F)
          sol I.Hval K R),
        (∃ J : ℕ, ∀ j ≥ J, ∀ t ∈ sched.zActiveWindow j,
          1 - I.eta ≤ I.Hval (sol.z t)) →
          ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ La.a t ∧ La.a t ≤ 1)
    (hlow :
      ∀ (sol : DynContractIteratorSol (Fin d) p sched F)
        (La : ContractHaltLatchSol (p := p) (sched := sched) (F := F)
          sol I.Hval K R),
        (∀ j : ℕ, ∀ t ∈ sched.zActiveWindow j,
          I.Hval (sol.z t) ≤ I.eta) →
          ∃ T : ℝ, ∀ t ≥ T, 0 ≤ La.a t ∧ La.a t ≤ 1 / 4) :
    ∀ sol : DynContractIteratorSol (Fin d) p sched F,
      ∃ La : ContractHaltLatchSol sol I.Hval K R,
        ContractLatchConvergenceKernel sol flagCoord I La := by
  intro sol
  obtain ⟨La⟩ := contract_latch_solution_exists sol I.Hval (hHcont sol) K R
  exact ⟨La, contract_latch_kernel_of_readout_bounds La hK
    (hhigh sol La) (hlow sol La)⟩

/-- SPEC3 item 19 adapter fed by stable-window scalar readout bounds. -/
theorem hlatch_adapter_of_stable_bounds
    {d : ℕ} {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {flagCoord : Fin d} (I : ContractFlagIndicatorPackage flagCoord)
    {K : ℝ} {R : ℕ}
    (hK : 0 < K)
    (hHcont :
      ∀ sol : DynContractIteratorSol (Fin d) p sched F,
        Continuous fun t => I.Hval (sol.z t))
    (hhigh :
      ∀ (sol : DynContractIteratorSol (Fin d) p sched F)
        (La : ContractHaltLatchSol (p := p) (sched := sched) (F := F)
          sol I.Hval K R),
        (∃ J : ℕ, ∀ j ≥ J,
          ∀ t ∈ Set.Icc
            (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
            (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6),
            1 - I.eta ≤ I.Hval (sol.z t)) →
          ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ La.a t ∧ La.a t ≤ 1)
    (hlow :
      ∀ (sol : DynContractIteratorSol (Fin d) p sched F)
        (La : ContractHaltLatchSol (p := p) (sched := sched) (F := F)
          sol I.Hval K R),
        (∀ j : ℕ,
          ∀ t ∈ Set.Icc
            (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
            (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6),
            I.Hval (sol.z t) ≤ I.eta) →
          ∃ T : ℝ, ∀ t ≥ T, 0 ≤ La.a t ∧ La.a t ≤ 1 / 4) :
    ∀ sol : DynContractIteratorSol (Fin d) p sched F,
      ∃ La : ContractHaltLatchSol sol I.Hval K R,
        ContractLatchConvergenceKernel sol flagCoord I La := by
  intro sol
  obtain ⟨La⟩ := contract_latch_solution_exists sol I.Hval (hHcont sol) K R
  exact ⟨La, contract_latch_kernel_of_stable_readout_bounds La hK
    (hhigh sol La) (hlow sol La)⟩

/-! ## L2/L3: flag read-window tracking radius -/

/-- SPEC3 items 20/21 candidate: the flag projection of the eta envelope. -/
def rhoflagU {d : ℕ} (η : ℕ → Fin d → ℝ) (flagCoord : Fin d) : ℕ → ℝ :=
  fun j => η j flagCoord

/--
SPEC3 item 21 read-window flag tracking wrapper.

`ContractTrackingResult.flag_z_read_window` supplies the eta-sized read-window
bound directly.
-/
theorem hrhoflagU
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
    ∀ j t, t ∈ sched.zActiveWindow j →
      |sol.z t flagCoord - E.enc (c j) flagCoord| ≤ rhoflagU η flagCoord j := by
  intro j t ht
  exact track.flag_z_read_window j t ht

/-- Named discharged corollary for audit scripts. -/
theorem hrhoflagU_discharged
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
    ∀ j t, t ∈ sched.zActiveWindow j →
      |sol.z t flagCoord - E.enc (c j) flagCoord| ≤ rhoflagU η flagCoord j :=
  hrhoflagU track

/-- SPEC3 item 22, in the exact margin shape used by `ContractMain`. -/
theorem hflag_margin_all_of_rhoflagU
    {d : ℕ} {η : ℕ → Fin d → ℝ} {flagCoord : Fin d}
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {nS : ℕ} {E : StackMachineEncoding d nS M}
    (flagPkg : HaltFlagPackage E flagCoord)
    (hη_flag_margin : ∀ j, η j flagCoord ≤ flagPkg.flagMargin) :
    ∀ j, rhoflagU η flagCoord j ≤ flagPkg.flagMargin := by
  intro j
  exact hη_flag_margin j

/-- Numeric quarter-margin version for the universal halt package. -/
theorem rhoflagU_le_quarter
    {d : ℕ} {η : ℕ → Fin d → ℝ} {flagCoord : Fin d}
    (hη_flag_quarter : ∀ j, η j flagCoord ≤ (1 / 4 : ℝ)) :
    ∀ j, rhoflagU η flagCoord j ≤ (1 / 4 : ℝ) := by
  intro j
  exact hη_flag_quarter j

/-! ## L4: flag domain bookkeeping -/

/--
The domain condition required by `ContractMain`.

This is not derivable from a `1/4` tube around a Boolean encoded flag; that only
gives the wider interval `[-1/4, 5/4]`.  The exact `[0,1]` fact is therefore an
explicit hypothesis at this interface.
-/
theorem hflag_domain_of_read_window_unit
    {d : ℕ} {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {sol : DynContractIteratorSol (Fin d) p sched F}
    {flagCoord : Fin d}
    (hunit :
      ∀ j t, t ∈ sched.zActiveWindow j →
        sol.z t flagCoord ∈ Set.Icc (0 : ℝ) 1) :
    ∀ j t, t ∈ sched.zActiveWindow j →
      sol.z t flagCoord ∈ Set.Icc (0 : ℝ) 1 := by
  intro j t ht
  exact hunit j t ht

/-- A documented consequence of a quarter tube around a Boolean flag. -/
theorem flag_mem_fattened_interval_of_quarter_tube
    {x b ρ : ℝ}
    (hb : b = 0 ∨ b = 1)
    (hρ : |x - b| ≤ ρ)
    (hρq : ρ ≤ 1 / 4) :
    x ∈ Set.Icc (-(1 / 4) : ℝ) (5 / 4) := by
  rw [Set.mem_Icc]
  have hclose : |x - b| ≤ (1 / 4 : ℝ) := hρ.trans hρq
  rw [abs_le] at hclose
  rcases hb with rfl | rfl
  · constructor <;> linarith
  · constructor <;> linarith

end BGP

end Ripple.BoundedUniversality
