import Ripple.BoundedUniversality.BGP.SelectorReplicatorWarmEuclidean
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
# SelectorReplicatorWarmHeadline

Per-input warm-gain BGP headline via the replicator-specific z-readout route.

The Euclidean input is produced by `bgp_headline_warmGain_euclidean`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open MachineInstance UniversalMachine
open scoped BigOperators

set_option maxHeartbeats 1200000

private theorem selectorSchedule_domain_nonneg_warm_repl :
    ∀ t : ℝ, 0 ≤ t → t ∈ selectorSchedule.domain := by
  intro t ht
  simpa [selectorSchedule] using ht

private theorem bgpParams_A_rat_warm_repl : bgpParams38.A = ((1 : ℚ) : ℝ) := by
  norm_num [bgpParams38]

private theorem bgpParams_cμ_rat_warm_repl : bgpParams38.cμ = ((1000 : ℚ) : ℝ) := by
  norm_num [bgpParams38]

private theorem bgpParams_cα_rat_warm_repl : bgpParams38.cα = ((300 : ℚ) : ℝ) := by
  norm_num [bgpParams38]

private theorem zero_eq_rat_zero_warm_repl : (0 : ℝ) = ((0 : ℚ) : ℝ) := by
  norm_num

private theorem bgpParams_L_eq_warm_repl : bgpParams38.L = 1 := by
  rfl

theorem bgp_headline_warmGain
    (eta : ℚ) (heta : 0 < eta)
    (M : ℕ) (κ₀ : ℚ) (warmGainQ : ℕ → ℚ) (R : ℕ)
    (init_presented :
      ∃ f : ℕ → Fin (selectorDim d_U UniversalLocalView + 1) → ℤ × ℕ,
        Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧
          selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w
            (warmGainQ w) i =
            (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ)
        (sol : MUReplicatorSolW eta heta M κ₀ warmGainQ w)
        (La : SelectorReplicatorHaltLatchSol sol (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w
              (warmGainQ w) 0 : ℚ) : ℝ) =
            ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj sol La ((warmGainQ w : ℚ) : ℝ) 0 i ^ 2) - 1) /
              ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj sol La ((warmGainQ w : ℚ) : ℝ) 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (sol : MUReplicatorSolW eta heta M κ₀ warmGainQ w)
        (La : SelectorReplicatorHaltLatchSol sol (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R)
        (i : Fin (selectorDim d_U UniversalLocalView)),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w
              (warmGainQ w) i.succ : ℚ) : ℝ) =
            2 * selectorReplicatorTupleTraj sol La ((warmGainQ w : ℚ) : ℝ) 0 i /
              ((∑ k : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj sol La ((warmGainQ w : ℚ) : ℝ) 0 k ^ 2) + 1))
    (euclidean :
      ∀ w : ℕ,
        ∃ (sol : MUReplicatorSolW eta heta M κ₀ warmGainQ w)
          (_La : SelectorReplicatorHaltLatchSol sol (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R),
          (undecidableMachine.toDiscreteMachine.haltsOn w →
            ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ sol.z t haltCoordU ∧ sol.z t haltCoordU ≤ 1) ∧
          (¬ undecidableMachine.toDiscreteMachine.haltsOn w →
            ∃ T : ℝ, ∀ t ≥ T, 0 ≤ sol.z t haltCoordU ∧ sol.z t haltCoordU ≤ 1 / 4)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P undecidableMachine) := by
  classical
  refine main_assembled_dyn_selector_zreadout_nolatch_repl_W
    undecidableMachine bgpParams38 selectorSchedule branchU
    (selectorReplicatorAssembledField d_U B_U UniversalLocalView branchU
      (selChiResetPoly d_U UniversalLocalView M)
      (selChiGatePoly d_U UniversalLocalView M)
      (selKappaPoly d_U UniversalLocalView κ₀)
      (selGainPoly d_U UniversalLocalView)
      (muReadoutPoly eta heta) (0 : MvPolynomial (Fin d_U) ℚ)
      (1 : ℚ) (0 : ℚ) (1000 : ℚ) (300 : ℚ) 1 R)
    (fun w sol La => selectorReplicatorTupleTraj sol La ((warmGainQ w : ℚ) : ℝ))
    ?_
    (fun w => selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w (warmGainQ w))
    init_presented haltCoordU (selZ UniversalLocalView haltCoordU) ?_
    euclidean ?_ ?_
  · intro w sol La t ht
    exact selectorReplicatorTupleTraj_ode sol La ((warmGainQ w : ℚ) : ℝ)
      (selChiResetPoly d_U UniversalLocalView M)
      (selChiGatePoly d_U UniversalLocalView M)
      (selKappaPoly d_U UniversalLocalView κ₀)
      (selGainPoly d_U UniversalLocalView)
      (muReadoutPoly eta heta) (0 : MvPolynomial (Fin d_U) ℚ)
      bgpParams_A_rat_warm_repl zero_eq_rat_zero_warm_repl
      bgpParams_cμ_rat_warm_repl bgpParams_cα_rat_warm_repl bgpParams_L_eq_warm_repl
      selectorSchedule_domain_nonneg_warm_repl
      (fun t _ht =>
        eval_selChiResetPoly_repl (sol := sol) (La := La)
          (warmGainVal := ((warmGainQ w : ℚ) : ℝ)) (t := t) M)
      (fun t _ht =>
        eval_selChiGatePoly_repl (sol := sol) (La := La)
          (warmGainVal := ((warmGainQ w : ℚ) : ℝ)) (t := t) M)
      (fun t _ht =>
        eval_selKappaPoly_repl (sol := sol) (La := La)
          (warmGainVal := ((warmGainQ w : ℚ) : ℝ)) (t := t) κ₀)
      (fun t ht => by
        rw [eval_selGainPoly_repl]
        rw [sol.alpha_eq_exp selectorSchedule_domain_nonneg_warm_repl ht])
      (fun v t _ht =>
        eval_muReadoutPoly_repl eta heta sol La ((warmGainQ w : ℚ) : ℝ) t v)
      (fun _t => by simp)
      t ht
  · intro w s La t
    exact selectorReplicatorTupleTraj_z
      (sol := s) (La := La) (warmGainVal := ((warmGainQ w : ℚ) : ℝ)) (t := t) haltCoordU
  · intro w
    simpa using init_zero w (Classical.choose (euclidean w))
      (selector_replicator_zero_latch_solution (Classical.choose (euclidean w)) R)
  · intro w i
    simpa using init_succ w (Classical.choose (euclidean w))
      (selector_replicator_zero_latch_solution (Classical.choose (euclidean w)) R) i

end Ripple.BoundedUniversality.BGP
