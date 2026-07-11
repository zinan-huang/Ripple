import Ripple.BoundedUniversality.BGP.SelectorReplicator
import Ripple.BoundedUniversality.BGP.SelectorMUBox
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorBox
---------------------------------
Stage-4 composition: the simplex-replicator invariants feed the universal
halt-coordinate mixture box, which feeds the exterior halt-flag barrier.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators

/-- Replicator-driven halt-flag box on the forward-time domain.

Inputs:
* `hlam_repl`: the selector weights solve the simplex-replicator ODE with the
  concrete M_U reset/gate coefficients.
* `hlam_sum0`: initial selector mass is `1`.
* `hcr_nonneg`: the reset coefficient is nonnegative.
* `hlam_init_nonneg`: initial selector weights are coordinatewise nonnegative.
* `hz0`: the initial halt flag is in `[0,1]`.

The proof composes `replicator_sum_lam_eq_one`,
`replicator_lam_nonneg`,
`selectorMixTarget_haltCoord_mem_Icc_of_lam_sum_eq_one`, and
`selectorDynSol_flag_box_of_mixTarget_haltCoord_mem_Icc`. -/
theorem selector_replicator_flag_box_on_nonneg
    {eta : ℚ} {heta : 0 < eta} {M : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
      MachineInstance.UniversalLocalView bgpParams38 selectorSchedule
      MachineInstance.branchU
      (fun t => ((1 + Real.cos t) / 2) ^ M)
      (fun t => ((1 + Real.sin t) / 2) ^ M)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (hcr_cont :
      Continuous fun t : ℝ => ((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ))
    (hcg_cont :
      Continuous fun t : ℝ =>
        ((1 + Real.sin t) / 2) ^ M *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
    (hP_cont : ∀ v : MachineInstance.UniversalLocalView,
      Continuous fun t : ℝ => universalPval eta heta v (sol.u t))
    (hcr_nonneg :
      ∀ t : ℝ, 0 ≤ ((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ))
    (hlam_repl :
      ∀ v : MachineInstance.UniversalLocalView, ∀ t : ℝ, 0 ≤ t →
        HasDerivAt (sol.lam v)
          ((((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ)) *
              (1 / (Fintype.card MachineInstance.UniversalLocalView : ℝ) - sol.lam v t)
            + (((1 + Real.sin t) / 2) ^ M *
                ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t))) *
              sol.lam v t *
                (universalPval eta heta v (sol.u t)
                  - ∑ w : MachineInstance.UniversalLocalView,
                      sol.lam w t * universalPval eta heta w (sol.u t))) t)
    (hlam_sum0 : (∑ v : MachineInstance.UniversalLocalView, sol.lam v 0) = 1)
    (hlam_init_nonneg :
      ∀ v : MachineInstance.UniversalLocalView, 0 ≤ sol.lam v 0)
    (hz0 : sol.z 0 MachineInstance.haltCoordU ∈ Set.Icc (0 : ℝ) 1) :
    (∀ t : ℝ, 0 ≤ t → sol.z t MachineInstance.haltCoordU ≤ 1) ∧
      (∀ t : ℝ, 0 ≤ t → 0 ≤ sol.z t MachineInstance.haltCoordU) := by
  classical
  haveI : Nonempty MachineInstance.UniversalLocalView :=
    ⟨MachineInstance.defaultLocalViewU⟩
  have hsum :
      ∀ t : ℝ, 0 ≤ t →
        (∑ v : MachineInstance.UniversalLocalView, sol.lam v t) = 1 :=
    replicator_sum_lam_eq_one
      (lam := fun v t => sol.lam v t)
      (P := fun v t => universalPval eta heta v (sol.u t))
      (cr := fun t => ((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ))
      (cg := fun t =>
        ((1 + Real.sin t) / 2) ^ M *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
      hcr_cont hcg_cont
      (fun v => sol.cont_lam v)
      hP_cont
      (fun v t ht => hlam_repl v t ht)
      hlam_sum0
  have hlam_nonneg_forward :
      ∀ v : MachineInstance.UniversalLocalView, ∀ t : ℝ, 0 ≤ t → 0 ≤ sol.lam v t :=
    replicator_lam_nonneg
      (lam := fun v t => sol.lam v t)
      (P := fun v t => universalPval eta heta v (sol.u t))
      (cr := fun t => ((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ))
      (cg := fun t =>
        ((1 + Real.sin t) / 2) ^ M *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
      hcr_cont hcg_cont
      (fun v => sol.cont_lam v)
      hP_cont
      hcr_nonneg
      (fun v t ht => hlam_repl v t ht)
      hlam_init_nonneg
  have hmix : ∀ t : ℝ, 0 ≤ t →
      selectorMixTarget MachineInstance.branchU sol.u sol.lam t
          MachineInstance.haltCoordU ∈ Set.Icc (0 : ℝ) 1 := by
    intro t ht
    exact selectorMixTarget_haltCoord_mem_Icc_of_lam_sum_eq_one
      sol.u sol.lam t
      (fun v => hlam_nonneg_forward v t ht)
      (hsum t ht)
  exact selectorDynSol_flag_box_of_mixTarget_haltCoord_mem_Icc sol hz0 hmix

#print axioms selector_replicator_flag_box_on_nonneg

/-- Global halt-flag box from the forward-time replicator box plus an explicit
negative-time extension.

The existing exterior barrier lemma is forward-time only (`0 ≤ t`).  For an
abstract `SelectorDynSol`, there is no negative-time equation or domain hypothesis
that can supply the same conclusion, so the two negative-time bounds are carried
as explicit hypotheses here. -/
theorem selector_replicator_flag_box
    {eta : ℚ} {heta : 0 < eta} {M : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
      MachineInstance.UniversalLocalView bgpParams38 selectorSchedule
      MachineInstance.branchU
      (fun t => ((1 + Real.cos t) / 2) ^ M)
      (fun t => ((1 + Real.sin t) / 2) ^ M)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (hcr_cont :
      Continuous fun t : ℝ => ((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ))
    (hcg_cont :
      Continuous fun t : ℝ =>
        ((1 + Real.sin t) / 2) ^ M *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
    (hP_cont : ∀ v : MachineInstance.UniversalLocalView,
      Continuous fun t : ℝ => universalPval eta heta v (sol.u t))
    (hcr_nonneg :
      ∀ t : ℝ, 0 ≤ ((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ))
    (hlam_repl :
      ∀ v : MachineInstance.UniversalLocalView, ∀ t : ℝ, 0 ≤ t →
        HasDerivAt (sol.lam v)
          ((((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ)) *
              (1 / (Fintype.card MachineInstance.UniversalLocalView : ℝ) - sol.lam v t)
            + (((1 + Real.sin t) / 2) ^ M *
                ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t))) *
              sol.lam v t *
                (universalPval eta heta v (sol.u t)
                  - ∑ w : MachineInstance.UniversalLocalView,
                      sol.lam w t * universalPval eta heta w (sol.u t))) t)
    (hlam_sum0 : (∑ v : MachineInstance.UniversalLocalView, sol.lam v 0) = 1)
    (hlam_init_nonneg :
      ∀ v : MachineInstance.UniversalLocalView, 0 ≤ sol.lam v 0)
    (hz0 : sol.z 0 MachineInstance.haltCoordU ∈ Set.Icc (0 : ℝ) 1)
    (hneg_hi : ∀ t : ℝ, t < 0 → sol.z t MachineInstance.haltCoordU ≤ 1)
    (hneg_lo : ∀ t : ℝ, t < 0 → 0 ≤ sol.z t MachineInstance.haltCoordU) :
    (∀ t : ℝ, sol.z t MachineInstance.haltCoordU ≤ 1) ∧
      (∀ t : ℝ, 0 ≤ sol.z t MachineInstance.haltCoordU) := by
  have hforward :=
    selector_replicator_flag_box_on_nonneg sol hcr_cont hcg_cont hP_cont
      hcr_nonneg hlam_repl hlam_sum0 hlam_init_nonneg hz0
  constructor
  · intro t
    by_cases ht : 0 ≤ t
    · exact hforward.1 t ht
    · exact hneg_hi t (lt_of_not_ge ht)
  · intro t
    by_cases ht : 0 ≤ t
    · exact hforward.2 t ht
    · exact hneg_lo t (lt_of_not_ge ht)

#print axioms selector_replicator_flag_box

end Ripple.BoundedUniversality.BGP
