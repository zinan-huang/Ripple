import Ripple.BoundedUniversality.BGP.SelectorInitTube
import Ripple.Core.ODEBox
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
Ripple.BoundedUniversality.BGP.SelectorMUBox
------------------------

D-box audit for the universal halt flag coordinate.

The halt-coordinate branch target itself is Boolean (`MachineInstance.branchU_halt_target_mem_Icc`).
However `selectorF` is the unnormalized sum

`fun i => ∑ v, Λ v * BranchData.evalBranch (branch v) Z i`

from `SelectorPolynomial.lean`, not a normalized convex combination.  Therefore the
halt-coordinate mixture is in `[0,1]` from the branch range only under an additional
weight-mass hypothesis such as `∑ v, λ_v(t) ≤ 1` (or equality to `1`).  The
`SelectorDynSol` logistic coordinate bounds give each `λ_v ∈ [0,1]`, but do not by
themselves give this total-mass bound.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set
open scoped BigOperators

/-- Public wrapper for the universal-machine halt-coordinate branch target range. -/
theorem branchU_halt_target_mem_Icc
    (v : MachineInstance.UniversalLocalView)
    (u : Fin MachineInstance.d_U → ℝ) :
    BranchData.evalBranch (MachineInstance.branchU v) u MachineInstance.haltCoordU ∈
      Icc (0 : ℝ) 1 :=
  MachineInstance.branchU_halt_target_mem_Icc v u

#print axioms branchU_halt_target_mem_Icc

/-- If the live selector weights have total mass at most `1`, then the
halt-coordinate dynamic mixture is a sub-convex combination of Boolean branch
targets, hence lies in `[0,1]`. -/
theorem selectorMixTarget_haltCoord_mem_Icc_of_lam_sum_le_one
    (u : ℝ → Fin MachineInstance.d_U → ℝ)
    (lam : MachineInstance.UniversalLocalView → ℝ → ℝ)
    (t : ℝ)
    (hlam_nonneg : ∀ v : MachineInstance.UniversalLocalView, 0 ≤ lam v t)
    (hlam_sum_le :
      (∑ v : MachineInstance.UniversalLocalView, lam v t) ≤ 1) :
    selectorMixTarget MachineInstance.branchU u lam t MachineInstance.haltCoordU ∈
      Icc (0 : ℝ) 1 := by
  constructor
  · rw [selectorMixTarget, selectorF]
    exact Finset.sum_nonneg fun v _ =>
      mul_nonneg (hlam_nonneg v)
        (MachineInstance.branchU_halt_target_mem_Icc v (u t)).1
  · rw [selectorMixTarget, selectorF]
    calc
      (∑ v : MachineInstance.UniversalLocalView,
          lam v t *
            BranchData.evalBranch (MachineInstance.branchU v) (u t)
              MachineInstance.haltCoordU)
          ≤ ∑ v : MachineInstance.UniversalLocalView, lam v t * 1 := by
            exact Finset.sum_le_sum fun v _ =>
              mul_le_mul_of_nonneg_left
                (MachineInstance.branchU_halt_target_mem_Icc v (u t)).2
                (hlam_nonneg v)
      _ = ∑ v : MachineInstance.UniversalLocalView, lam v t := by simp
      _ ≤ 1 := hlam_sum_le

#print axioms selectorMixTarget_haltCoord_mem_Icc_of_lam_sum_le_one

/-- Equality of total selector mass to `1` is the usual convex-combination
special case of `selectorMixTarget_haltCoord_mem_Icc_of_lam_sum_le_one`. -/
theorem selectorMixTarget_haltCoord_mem_Icc_of_lam_sum_eq_one
    (u : ℝ → Fin MachineInstance.d_U → ℝ)
    (lam : MachineInstance.UniversalLocalView → ℝ → ℝ)
    (t : ℝ)
    (hlam_nonneg : ∀ v : MachineInstance.UniversalLocalView, 0 ≤ lam v t)
    (hlam_sum :
      (∑ v : MachineInstance.UniversalLocalView, lam v t) = 1) :
    selectorMixTarget MachineInstance.branchU u lam t MachineInstance.haltCoordU ∈
      Icc (0 : ℝ) 1 :=
  selectorMixTarget_haltCoord_mem_Icc_of_lam_sum_le_one u lam t
    hlam_nonneg (le_of_eq hlam_sum)

#print axioms selectorMixTarget_haltCoord_mem_Icc_of_lam_sum_eq_one

theorem selectorSchedule_domain_of_nonneg_box :
    ∀ t : ℝ, 0 ≤ t → t ∈ selectorSchedule.domain := by
  intro t ht
  simpa [selectorSchedule] using ht

#print axioms selectorSchedule_domain_of_nonneg_box

/-- Conditional exterior-barrier version of the halt flag D-box.

This is exactly the scalar-barrier step, but it is intentionally conditional on
the missing part-2 input: the halt-coordinate mixture must stay in `[0,1]`. -/
theorem selectorDynSol_flag_box_of_mixTarget_haltCoord_mem_Icc
    {eta : ℚ} {heta : 0 < eta} {M : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
      MachineInstance.UniversalLocalView bgpParams38 selectorSchedule
      MachineInstance.branchU
      (fun t => ((1 + Real.cos t) / 2) ^ M)
      (fun t => ((1 + Real.sin t) / 2) ^ M)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (hz0 : sol.z 0 MachineInstance.haltCoordU ∈ Icc (0 : ℝ) 1)
    (hmix : ∀ t : ℝ, 0 ≤ t →
      selectorMixTarget MachineInstance.branchU sol.u sol.lam t
          MachineInstance.haltCoordU ∈ Icc (0 : ℝ) 1) :
    (∀ t : ℝ, 0 ≤ t → sol.z t MachineInstance.haltCoordU ≤ 1) ∧
      (∀ t : ℝ, 0 ≤ t → 0 ≤ sol.z t MachineInstance.haltCoordU) := by
  constructor
  · intro T hT
    have hupper := Ripple.scalar_upper_barrier_exterior_on_Icc
      (T := T) (b := (1 : ℝ)) hT
      (fun t : ℝ => sol.z t MachineInstance.haltCoordU)
      (fun t : ℝ =>
        bgpParams38.A * sol.α t *
          bGateZ bgpParams38.L (sol.μ t) t *
            (selectorMixTarget MachineInstance.branchU sol.u sol.lam t
              MachineInstance.haltCoordU - sol.z t MachineInstance.haltCoordU))
      hz0.2
      ((sol.cont_z MachineInstance.haltCoordU).continuousOn)
      (fun t ht =>
        (sol.z_hasDeriv t
          (selectorSchedule_domain_of_nonneg_box t ht.1)
          MachineInstance.haltCoordU).hasDerivWithinAt)
      (fun t ht hwall => by
        have hcoef :
            0 ≤ bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t := by
          have halpha :
              sol.α t = Real.exp (bgpParams38.cα * t) :=
            sol.alpha_eq_exp selectorSchedule_domain_of_nonneg_box ht.1
          rw [halpha]
          exact mul_nonneg (mul_nonneg (by norm_num [bgpParams38])
            (Real.exp_pos _).le) (bGateZ_pos bgpParams38.L (sol.μ t) t).le
        have hdiff :
            selectorMixTarget MachineInstance.branchU sol.u sol.lam t
                MachineInstance.haltCoordU -
              sol.z t MachineInstance.haltCoordU ≤ 0 := by
          linarith [(hmix t ht.1).2]
        exact mul_nonpos_of_nonneg_of_nonpos hcoef hdiff)
    exact hupper T (right_mem_Icc.mpr hT)
  · intro T hT
    have hlower := Ripple.scalar_lower_barrier_exterior_on_Icc
      (T := T) (a := (0 : ℝ)) hT
      (fun t : ℝ => sol.z t MachineInstance.haltCoordU)
      (fun t : ℝ =>
        bgpParams38.A * sol.α t *
          bGateZ bgpParams38.L (sol.μ t) t *
            (selectorMixTarget MachineInstance.branchU sol.u sol.lam t
              MachineInstance.haltCoordU - sol.z t MachineInstance.haltCoordU))
      hz0.1
      ((sol.cont_z MachineInstance.haltCoordU).continuousOn)
      (fun t ht =>
        (sol.z_hasDeriv t
          (selectorSchedule_domain_of_nonneg_box t ht.1)
          MachineInstance.haltCoordU).hasDerivWithinAt)
      (fun t ht hwall => by
        have hcoef :
            0 ≤ bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t := by
          have halpha :
              sol.α t = Real.exp (bgpParams38.cα * t) :=
            sol.alpha_eq_exp selectorSchedule_domain_of_nonneg_box ht.1
          rw [halpha]
          exact mul_nonneg (mul_nonneg (by norm_num [bgpParams38])
            (Real.exp_pos _).le) (bGateZ_pos bgpParams38.L (sol.μ t) t).le
        have hdiff :
            0 ≤ selectorMixTarget MachineInstance.branchU sol.u sol.lam t
                MachineInstance.haltCoordU -
              sol.z t MachineInstance.haltCoordU := by
          linarith [(hmix t ht.1).1]
        exact mul_nonneg hcoef hdiff)
    exact hlower T (right_mem_Icc.mpr hT)

#print axioms selectorDynSol_flag_box_of_mixTarget_haltCoord_mem_Icc

end Ripple.BoundedUniversality.BGP
