import Ripple.BoundedUniversality.BGP.SelectorReplicatorPackage
import Ripple.BoundedUniversality.BGP.SelectorReplicatorHeadline
import Ripple.BoundedUniversality.BGP.SelectorReplicatorBox
import Ripple.BoundedUniversality.BGP.SelectorReplicatorConc
import Ripple.BoundedUniversality.BGP.SelectorReplicatorExistence
import Ripple.BoundedUniversality.BGP.SelectorReplicatorHStart
import Ripple.BoundedUniversality.BGP.SelectorInitTube
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorFinal
-----------------------------------
Final replicator assembly layer.

This file is intentionally a thin wrapper around the clean-3 pieces:

* `solMURepl` supplies the concrete replicator solution family.
* the simplex-replicator invariants discharge the live halt-coordinate mix box
  and the forward halt-flag box;
* `selector_correct_{halt,nonhalt}_endtoend_hold_gate_repl` turns the carried
  write/hold tracking scalars into eventual halt/nonhalt z-regions;
* `main_assembled_dyn_selector_zreadout_nolatch_repl` turns those z-regions into
  the PIVP headline.

The remaining explicit hypotheses are the satisfiable contract-status content:
solution existence/realization inputs for `solMURepl`, the computable
stereographic initial presentation, the exposed simplex/z initial facts, and the
per-cycle write/hold scalar tracking facts.  The old raw `hbox`/`hmix` premises
are not carried.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open Set MachineInstance

/-- Params-generic per-input solution family (the NW consumer flip carrier).
`MUReplicatorSolFamily` below is the `bgpParams38` instance; the word-coupled
`MUReplicatorSolFamilyNW wg` (HeadlineUnconditional) is defeq to the
`bgpParamsNW wg` instance. -/
abbrev MUReplicatorSolFamilyP (p : DynGateParams) (eta : ℚ) (heta : 0 < eta) (M : ℕ)
    (κ₀ g₀ : ℚ) :=
  ℕ → SelectorReplicatorDynSol d_U B_U UniversalLocalView p selectorSchedule
    branchU
    (fun t => ((1 + Real.cos t) / 2) ^ M)
    (fun t => ((1 + Real.sin t) / 2) ^ M)
    (fun _ => (κ₀ : ℝ))
    (fun t => (g₀ : ℝ) * Real.exp (p.cα * t))
    (universalPval eta heta)

abbrev MUReplicatorSolFamily (eta : ℚ) (heta : 0 < eta) (M : ℕ)
    (κ₀ g₀ : ℚ) :=
  MUReplicatorSolFamilyP bgpParams38 eta heta M κ₀ g₀

/-- Forward-time box inputs not stored in `SelectorReplicatorDynSol`.

These are initial/regularity facts for the replicator weights and the concrete
readout.  They are satisfiable from the uniform `selectorReplicatorEuclInitQ`
initial lambda block and polynomial continuity of the universal readout. -/
structure MUReplicatorBoxInputsP (p : DynGateParams) (eta : ℚ) (heta : 0 < eta) (M : ℕ)
    (κ₀ g₀ : ℚ) (sol : MUReplicatorSolFamilyP p eta heta M κ₀ g₀) : Prop where
  hcr_cont :
    Continuous fun t : ℝ => ((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ)
  hcg_cont :
    Continuous fun t : ℝ =>
      ((1 + Real.sin t) / 2) ^ M *
        ((g₀ : ℝ) * Real.exp (p.cα * t))
  hP_cont : ∀ w v,
    Continuous fun t : ℝ => universalPval eta heta v ((sol w).u t)
  hcr_nonneg :
    ∀ t : ℝ, 0 ≤ ((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ)
  hlam_sum0 : ∀ w,
    (∑ v : UniversalLocalView, (sol w).lam v 0) = 1
  hlam_init_nonneg : ∀ w v, 0 ≤ (sol w).lam v 0
  hz0 : ∀ w, (sol w).z 0 haltCoordU ∈ Icc (0 : ℝ) 1

/-- The `bgpParams38` instance of the box inputs (compat interface). -/
abbrev MUReplicatorBoxInputs (eta : ℚ) (heta : 0 < eta) (M : ℕ)
    (κ₀ g₀ : ℚ) (sol : MUReplicatorSolFamily eta heta M κ₀ g₀) : Prop :=
  MUReplicatorBoxInputsP bgpParams38 eta heta M κ₀ g₀ sol

/-- The remaining contract-status write/hold scalars.

`hstart` is the post-write halt-coordinate estimate (the A3/S3 endpoint after
the write-time mix estimate has been discharged).  `hgateInt` is the S7 drift
budget for the subsequent hold interval. -/
structure MUReplicatorTrackingFacts (eta : ℚ) (heta : 0 < eta) (M : ℕ)
    (κ₀ g₀ : ℚ) (sol : MUReplicatorSolFamily eta heta M κ₀ g₀) where
  ρ : ℕ → ℕ → ℝ
  δhold : ℕ → ℕ → ℝ
  hg_cont : ∀ w,
    Continuous fun t : ℝ =>
      bgpParams38.A * (sol w).α t * bGateZ bgpParams38.L ((sol w).μ t) t
  hgateInt : ∀ (w j : ℕ), ∀ t ∈ Icc
      (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
      (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
    (∫ τ in (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)..t,
      bgpParams38.A * (sol w).α τ * bGateZ bgpParams38.L ((sol w).μ τ) τ) ≤
        δhold w j
  hstart : ∀ (w j : ℕ),
    |(sol w).z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6) haltCoordU
      - stackMachineEncodingU.enc (M_U.step^[j + 1] (M_U.init w)) haltCoordU| ≤
        ρ w j
  hsmall : ∀ w j, ρ w j + δhold w j ≤ 1 / 4

private theorem selectorSchedule_domain_nonneg_final :
    ∀ t : ℝ, 0 ≤ t → t ∈ selectorSchedule.domain := by
  intro t ht
  simpa [selectorSchedule] using ht

private theorem selectorSchedule_tiled_domain_final (j : ℕ) :
    ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      t ∈ selectorSchedule.domain := by
  intro t ht
  have ht0 : 0 ≤ t := by
    have hleft : 0 ≤ 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6 := by
      positivity
    exact le_trans hleft ht.1
  exact selectorSchedule_domain_nonneg_final t ht0

private theorem selectorReplicator_gateZ_nonneg_final
    {eta : ℚ} {heta : 0 < eta} {M : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta M κ₀ g₀) :
    ∀ (w j : ℕ), ∀ t ∈ Icc
        (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      0 ≤ bgpParams38.A * (sol w).α t * bGateZ bgpParams38.L ((sol w).μ t) t := by
  intro w j t ht
  have ht0 : 0 ≤ t := by
    have hleft : 0 ≤ 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6 := by
      positivity
    exact le_trans hleft ht.1
  have hα : (sol w).α t = Real.exp (bgpParams38.cα * t) :=
    (sol w).alpha_eq_exp selectorSchedule_domain_nonneg_final ht0
  rw [hα]
  exact mul_nonneg (mul_nonneg (by norm_num [bgpParams38]) (Real.exp_pos _).le)
    (bGateZ_pos bgpParams38.L ((sol w).μ t) t).le

set_option maxHeartbeats 800000 in
theorem bgp_MU_unconditional_replicator
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hfin : ∀ w,
      Ripple.FiniteHorizonBound (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R)
        (selectorMUReplicatorInit selectorInitX0 w g₀))
    (hgateZ : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateZ d_U)) =
            bGateZ 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (hgateU : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateU d_U)) =
            bGateU 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (h_chiReset : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiResetPoly d_U UniversalLocalView M) =
              ((1 + Real.cos t) / 2) ^ M)
    (h_chiGate : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiGatePoly d_U UniversalLocalView M) =
              ((1 + Real.sin t) / 2) ^ M)
    (h_kappa : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selKappaPoly d_U UniversalLocalView κ₀) = (κ₀ : ℝ))
    (h_gain : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selGainPoly d_U UniversalLocalView) =
              (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
    (h_P : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ (v : UniversalLocalView) (t : ℝ), 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            ((muReadoutPoly eta heta) v) =
              universalPval eta heta v (fun i => y t (selU UniversalLocalView i)))
    (init_presented :
      ∃ f : ℕ → Fin (selectorDim d_U UniversalLocalView + 1) → ℤ × ℕ,
        Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧
          selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ i =
            (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ)
        (s : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
          branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M)
          (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ))
          (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorReplicatorHaltLatchSol s (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ 0 : ℚ) : ℝ) =
            ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj s La (g₀ : ℝ) 0 i ^ 2) - 1) /
              ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj s La (g₀ : ℝ) 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (s : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
          branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M)
          (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ))
          (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorReplicatorHaltLatchSol s (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R)
        (i : Fin (selectorDim d_U UniversalLocalView)),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ i.succ : ℚ) : ℝ) =
            2 * selectorReplicatorTupleTraj s La (g₀ : ℝ) 0 i /
              ((∑ k : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj s La (g₀ : ℝ) 0 k ^ 2) + 1))
    (boxInputs : MUReplicatorBoxInputs eta heta M κ₀ g₀
      (solMURepl eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
        h_chiReset h_chiGate h_kappa h_gain h_P))
    (tracking : MUReplicatorTrackingFacts eta heta M κ₀ g₀
      (solMURepl eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
        h_chiReset h_chiGate h_kappa h_gain h_P)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  let sol : MUReplicatorSolFamily eta heta M κ₀ g₀ :=
    solMURepl eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
      h_chiReset h_chiGate h_kappa h_gain h_P
  have hforward_boxes : ∀ w,
      (∀ t : ℝ, 0 ≤ t →
        selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU ∈ Icc (0 : ℝ) 1) ∧
      (∀ t : ℝ, 0 ≤ t → (sol w).z t haltCoordU ≤ 1) ∧
      (∀ t : ℝ, 0 ≤ t → 0 ≤ (sol w).z t haltCoordU) := by
    intro w
    have hode : ∀ v : UniversalLocalView, ∀ t : ℝ, 0 ≤ t →
        HasDerivAt ((sol w).lam v)
          ((((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ)) *
              (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v t)
            + (((1 + Real.sin t) / 2) ^ M *
                ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t))) *
              (sol w).lam v t *
                (universalPval eta heta v ((sol w).u t)
                  - ∑ u : UniversalLocalView,
                      (sol w).lam u t * universalPval eta heta u ((sol w).u t))) t := by
      intro v t ht
      simpa [selectorSchedule] using
        (sol w).lam_hasDeriv v t (by simpa [selectorSchedule] using ht)
    have hsum : ∀ t : ℝ, 0 ≤ t →
        (∑ v : UniversalLocalView, (sol w).lam v t) = 1 :=
      replicator_sum_lam_eq_one
        (lam := fun v t => (sol w).lam v t)
        (P := fun v t => universalPval eta heta v ((sol w).u t))
        (cr := fun t => ((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ))
        (cg := fun t =>
          ((1 + Real.sin t) / 2) ^ M *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
        boxInputs.hcr_cont boxInputs.hcg_cont
        (fun v => (sol w).cont_lam v)
        (boxInputs.hP_cont w) hode (boxInputs.hlam_sum0 w)
    have hlam_nonneg_forward :
        ∀ v : UniversalLocalView, ∀ t : ℝ, 0 ≤ t → 0 ≤ (sol w).lam v t :=
      replicator_lam_nonneg
        (lam := fun v t => (sol w).lam v t)
        (P := fun v t => universalPval eta heta v ((sol w).u t))
        (cr := fun t => ((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ))
        (cg := fun t =>
          ((1 + Real.sin t) / 2) ^ M *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
        boxInputs.hcr_cont boxInputs.hcg_cont
        (fun v => (sol w).cont_lam v)
        (boxInputs.hP_cont w) boxInputs.hcr_nonneg hode
        (boxInputs.hlam_init_nonneg w)
    have hmix : ∀ t : ℝ, 0 ≤ t →
        selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU ∈ Icc (0 : ℝ) 1 := by
      intro t ht
      exact selectorMixTarget_haltCoord_mem_Icc_of_lam_sum_eq_one
        (sol w).u (sol w).lam t
        (fun v => hlam_nonneg_forward v t ht)
        (hsum t ht)
    have hzbox :=
      selector_replicator_flag_box_on_nonneg_repl (sol w)
        boxInputs.hcr_cont boxInputs.hcg_cont (boxInputs.hP_cont w)
        boxInputs.hcr_nonneg (boxInputs.hlam_sum0 w)
        (boxInputs.hlam_init_nonneg w) (boxInputs.hz0 w)
    exact ⟨hmix, hzbox.1, hzbox.2⟩
  have correct_halt_z :
      ∀ w, UniversalMachine.undecidableMachine.toDiscreteMachine.haltsOn w →
        ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ (sol w).z t haltCoordU ∧
          (sol w).z t haltCoordU ≤ 1 := by
    intro w hw
    have hwU : M_U.haltsOn w := by
      simpa using hw
    let cfg : ℕ → UConf := fun j => M_U.step^[j] (M_U.init w)
    have hcfg : ∀ j, cfg j = M_U.step^[j] (M_U.init w) := by
      intro j
      rfl
    refine selector_correct_halt_endtoend_hold_gate_repl (sol w) w hwU cfg hcfg
      (tracking.ρ w) (tracking.δhold w)
      selectorSchedule_tiled_domain_final (tracking.hg_cont w)
      (selectorReplicator_gateZ_nonneg_final sol w)
      ?_ ?_ (tracking.hgateInt w) (tracking.hstart w) (tracking.hsmall w)
      (hforward_boxes w).2.1
    · intro j t ht
      have ht0 : 0 ≤ t := by
        have hleft : 0 ≤ 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6 := by
          positivity
        exact le_trans hleft ht.1
      exact (hforward_boxes w).1 t ht0
    · intro j t ht
      have ht0 : 0 ≤ t := by
        have hleft : 0 ≤ 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6 := by
          positivity
        exact le_trans hleft ht.1
      exact ⟨(hforward_boxes w).2.2 t ht0, (hforward_boxes w).2.1 t ht0⟩
  have correct_nonhalt_z :
      ∀ w, ¬ UniversalMachine.undecidableMachine.toDiscreteMachine.haltsOn w →
        ∃ T : ℝ, ∀ t ≥ T, 0 ≤ (sol w).z t haltCoordU ∧
          (sol w).z t haltCoordU ≤ 1 / 4 := by
    intro w hw
    have hwU : ¬ M_U.haltsOn w := by
      simpa using hw
    let cfg : ℕ → UConf := fun j => M_U.step^[j] (M_U.init w)
    have hcfg : ∀ j, cfg j = M_U.step^[j] (M_U.init w) := by
      intro j
      rfl
    refine selector_correct_nonhalt_endtoend_hold_gate_repl (sol w) w hwU cfg hcfg
      (tracking.ρ w) (tracking.δhold w)
      selectorSchedule_tiled_domain_final (tracking.hg_cont w)
      (selectorReplicator_gateZ_nonneg_final sol w)
      ?_ ?_ (tracking.hgateInt w) (tracking.hstart w) (tracking.hsmall w)
      (hforward_boxes w).2.2
    · intro j t ht
      have ht0 : 0 ≤ t := by
        have hleft : 0 ≤ 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6 := by
          positivity
        exact le_trans hleft ht.1
      exact (hforward_boxes w).1 t ht0
    · intro j t ht
      have ht0 : 0 ≤ t := by
        have hleft : 0 ≤ 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6 := by
          positivity
        exact le_trans hleft ht.1
      exact ⟨(hforward_boxes w).2.2 t ht0, (hforward_boxes w).2.1 t ht0⟩
  let fieldPkg :=
    muReplicatorSelectorFieldPackage eta heta M κ₀ g₀ R selectorInitX0
      init_presented init_zero init_succ
  refine main_assembled_dyn_selector_zreadout_nolatch_repl
    UniversalMachine.undecidableMachine bgpParams38 selectorSchedule branchU
    fieldPkg sol haltCoordU (selZ UniversalLocalView haltCoordU) ?_
    correct_halt_z correct_nonhalt_z
  intro w s La t
  show selectorReplicatorTupleTraj s La (g₀ : ℝ) t (selZ UniversalLocalView haltCoordU) =
      s.z t haltCoordU
  exact selectorReplicatorTupleTraj_z (sol := s) La (g₀ : ℝ) t haltCoordU

#print axioms bgp_MU_unconditional_replicator

end Ripple.BoundedUniversality.BGP
