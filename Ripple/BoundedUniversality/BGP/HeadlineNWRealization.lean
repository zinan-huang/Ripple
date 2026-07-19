/-
Ripple.BoundedUniversality.BGP.HeadlineNWRealization
---------------------------------
The NW (word-coupled) consumer realization surface.

Part 1 (this stage): `main_assembled_dyn_selector_zreadout_nolatch_repl_W_explicit_pF`
— the per-word-params generalization of the realization theorem
(HeadlineUnconditional:4307).  The original fixes ONE `p : DynGateParams`
across all inputs `w`; the NW family needs `pF w := bgpParamsNW w`.  The proof
body is IDENTICAL (the original never uses `p` outside the solution types);
only the binders generalize.  The private stereo helpers are file-local
clones of the HeadlineUnconditional privates.
-/

import Ripple.BoundedUniversality.BGP.HeadlineUnconditional
import Ripple.BoundedUniversality.BGP.SelectorReplicatorCC

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open MvPolynomial Set MachineInstance UniversalMachine

-- `bgp_warm_stereo_sum_sq` and `bgp_warm_stereo_abs_le_one` are now public
-- in `HeadlineUnconditional` (un-privated by the 2026-07 split); the private
-- copies that used to live here collided with those public names on a cold
-- build, so they are removed and the imported public versions are used below.

set_option maxHeartbeats 1200000 in
/-- Explicit-solution version of
`main_assembled_dyn_selector_zreadout_nolatch_repl_W`.

The upstream theorem chooses the Euclidean witness and therefore needs
initialization identities for every possible `sol`.  This version threads the
intended solution family directly, so the initialization identities only concern
that family. -/
theorem main_assembled_dyn_selector_zreadout_nolatch_repl_W_explicit_pF
    {d B : ℕ} {Conf : Type} [Primcodable Conf]
    (M₀ : UndecidableMachine Conf)
    (pF : ℕ → DynGateParams) (sched : PhaseSchedule)
    {V : Type} [Fintype V] (branch : V → BranchData d B)
    {chiResetF chiGateF kappaF : ℝ → ℝ} {gainF : ℕ → ℝ → ℝ}
    {Pv : V → (Fin d → ℝ) → ℝ}
    {R : ℕ} {nE : ℕ}
    (field : Fin nE → MvPolynomial (Fin nE) ℚ)
    (tuple :
      ∀ (w : ℕ)
        (sol : SelectorReplicatorDynSol d B V (pF w) sched branch
          chiResetF chiGateF kappaF (gainF w) Pv),
        SelectorReplicatorHaltLatchSol sol (fun _ : (Fin d → ℝ) => (0 : ℝ)) 0 R →
          ℝ → Fin nE → ℝ)
    (tuple_ode :
      ∀ (w : ℕ)
        (sol : SelectorReplicatorDynSol d B V (pF w) sched branch
          chiResetF chiGateF kappaF (gainF w) Pv)
        (La : SelectorReplicatorHaltLatchSol sol (fun _ : (Fin d → ℝ) => (0 : ℝ)) 0 R)
        (t : ℝ), 0 ≤ t →
          HasDerivAt (tuple w sol La)
            (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ)
              (tuple w sol La t) (field i)) t)
    (init : ℕ → Fin (nE + 1) → ℚ)
    (init_presented : ∃ f : ℕ → Fin (nE + 1) → ℤ × ℕ, Computable f ∧
      ∀ w i, (f w i).2 ≠ 0 ∧ init w i = (f w i).1 / ((f w i).2 : ℚ))
    (readCoord : Fin d) (readCoordE : Fin nE)
    (hread_value :
      ∀ (w : ℕ)
        (s : SelectorReplicatorDynSol d B V (pF w) sched branch
          chiResetF chiGateF kappaF (gainF w) Pv)
        (La : SelectorReplicatorHaltLatchSol s (fun _ : (Fin d → ℝ) => (0 : ℝ)) 0 R)
        (t : ℝ),
          tuple w s La t readCoordE = s.z t readCoord)
    (sol :
      ∀ w : ℕ, SelectorReplicatorDynSol d B V (pF w) sched branch
        chiResetF chiGateF kappaF (gainF w) Pv)
    (La0 :
      ∀ w : ℕ, SelectorReplicatorHaltLatchSol (sol w)
        (fun _ : (Fin d → ℝ) => (0 : ℝ)) 0 R)
    (hhalt :
      ∀ w, M₀.toDiscreteMachine.haltsOn w →
        ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ (sol w).z t readCoord ∧
          (sol w).z t readCoord ≤ 1)
    (hnonhalt :
      ∀ w, ¬ M₀.toDiscreteMachine.haltsOn w →
        ∃ T : ℝ, ∀ t ≥ T, 0 ≤ (sol w).z t readCoord ∧
          (sol w).z t readCoord ≤ 1 / 4)
    (init_zero :
      ∀ (w : ℕ),
        ((init w 0 : ℚ) : ℝ) =
          ((∑ i : Fin nE, tuple w (sol w) (La0 w) 0 i ^ 2) - 1) /
            ((∑ i : Fin nE, tuple w (sol w) (La0 w) 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ) (i : Fin nE),
        ((init w i.succ : ℚ) : ℝ) =
          2 * tuple w (sol w) (La0 w) 0 i /
            ((∑ k : Fin nE, tuple w (sol w) (La0 w) 0 k ^ 2) + 1)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P M₀) := by
  classical
  obtain ⟨Y, _htang, htransfer⟩ := compactification_exists nE field
  let P : Ripple.BoundedUniversality.GPAC.PIVP ℚ :=
    { n := nE + 1
      vf := Y
      init := init }
  have htrans : ∀ w,
      ∃ s : ℝ → ℝ, s 0 = 0 ∧ StrictMonoOn s (Set.Ici 0) ∧
        Filter.Tendsto s Filter.atTop Filter.atTop ∧
        ∀ τ : ℝ, 0 ≤ τ → HasDerivAt
          (fun σ => stereo (tuple w (sol w) (La0 w) (s σ)))
          (fun j => MvPolynomial.eval₂ (algebraMap ℚ ℝ)
            (stereo (tuple w (sol w) (La0 w) (s τ))) (Y j)) τ := by
    intro w
    exact htransfer (tuple w (sol w) (La0 w)) (tuple_ode w (sol w) (La0 w))
  choose s hs0 _hsmono hstend hsphere using htrans
  refine ⟨P, ⟨{
    traj := fun w τ => stereo (tuple w (sol w) (La0 w) (s w τ))
    init_at_zero := ?_
    solves_ode := ?_
    bounded := ?_
    encoder_presented := init_presented
    readout := ?_
    correct_halt := ?_
    correct_nonhalt := ?_
  }⟩⟩
  · intro w
    funext j
    rw [hs0 w]
    dsimp [P, Ripple.BoundedUniversality.GPAC.PIVP.realInit]
    refine Fin.cases ?_ ?_ j
    · simp [stereo, stereoDenom, init_zero w]
    · intro i
      simp [stereo, stereoDenom, init_succ w i]
  · intro w τ hτ
    simpa [P, Ripple.BoundedUniversality.GPAC.PIVP.evalVF] using hsphere w τ hτ
  · refine ⟨1, by norm_num, ?_⟩
    intro w τ i hτ
    exact bgp_warm_stereo_abs_le_one _ _
  · exact { hA := readCoordE.succ, h0 := 0, ne := by simp }
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
    have hz := hT (s w τ) hTle
    have hcoord :
        3 / 4 ≤ tuple w (sol w) (La0 w) (s w τ) readCoordE ∧
          tuple w (sol w) (La0 w) (s w τ) readCoordE ≤ 1 := by
      simpa [hread_value w (sol w) (La0 w) (s w τ)] using hz
    have hreg :=
      (stereo_readout_transfer (tuple w (sol w) (La0 w) (s w τ)) readCoordE).1
        hcoord
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
    have hz := hT (s w τ) hTle
    have hcoord :
        0 ≤ tuple w (sol w) (La0 w) (s w τ) readCoordE ∧
          tuple w (sol w) (La0 w) (s w τ) readCoordE ≤ 1 / 4 := by
      simpa [hread_value w (sol w) (La0 w) (s w τ)] using hz
    have hreg :=
      (stereo_readout_transfer (tuple w (sol w) (La0 w) (s w τ)) readCoordE).2
        hcoord
    simpa [ChartThresholdReadout.NonhaltRegion, P] using hreg


/-! ## The NW consumer (A5): headline from NW late-start facts

`init_presented` and the halt/nonhalt readout facts are carried as hypotheses
at this stage: the former is discharged by the `WarmIndexComputable` +
CC-presenter layer (in flight), the latter by the Seg B–F NW migration
(`bgpHeadlineCorrectOfLateStart`-NW).  Assembling early surfaces any
keystone mismatch now, per the campaign doctrine. -/

/-- Rational value of the NW `cμ` initial coordinate. -/
def bgpNWCmuInitQ (w : ℕ) : ℚ := ((1000 * bgpScaleW w : ℕ) : ℚ)

/-- Rational value of the NW `cα` initial coordinate. -/
def bgpNWCalphaInitQ (w : ℕ) : ℚ := ((300 * bgpScaleW w : ℕ) : ℚ)

theorem bgp_bgpParamsNW_cμ_rat (w : ℕ) :
    (bgpParamsNW w).cμ = ((bgpNWCmuInitQ w : ℚ) : ℝ) := by
  rw [bgpParamsNW_cμ_def, bgpNWCmuInitQ]
  push_cast
  ring

theorem bgp_bgpParamsNW_cα_rat (w : ℕ) :
    (bgpParamsNW w).cα = ((bgpNWCalphaInitQ w : ℚ) : ℝ) := by
  rw [bgpParamsNW_cα_def, bgpNWCalphaInitQ]
  push_cast
  ring

private theorem bgpParamsNW_A_eq_ratCast (w : ℕ) :
    (bgpParamsNW w).A = ((1 : ℚ) : ℝ) := by
  rw [bgpParamsNW_A_eq]
  norm_num

private theorem bgpNW_zero_eq_rat_zero : (0 : ℝ) = ((0 : ℚ) : ℝ) := by
  norm_num

private theorem bgpNW_selectorSchedule_domain_nonneg :
    ∀ t : ℝ, 0 ≤ t → t ∈ selectorSchedule.domain := by
  intro t ht
  simpa [selectorSchedule] using ht

/-- The CC headline field: the assembled replicator field with the two rate
coordinates, at the headline polynomial data. -/
noncomputable def bgpHeadlineFieldCC :
    Fin (selectorDimCC d_U UniversalLocalView) →
      MvPolynomial (Fin (selectorDimCC d_U UniversalLocalView)) ℚ :=
  selectorReplicatorAssembledFieldCC d_U B_U UniversalLocalView branchU
    (selChiResetPoly d_U UniversalLocalView bgpHeadlineM)
    (selChiGatePoly d_U UniversalLocalView bgpHeadlineM)
    (selKappaPoly d_U UniversalLocalView bgpHeadlineKappa)
    (selGainPoly d_U UniversalLocalView)
    (muReadoutPoly bgpHeadlineEta bgpHeadlineEta_pos)
    (0 : MvPolynomial (Fin d_U) ℚ)
    (1 : ℚ) (0 : ℚ) 1 bgpHeadlineR

set_option maxHeartbeats 1800000 in
/-- **The NW consumer**: the unconditional headline from NW-family readout
facts, realized through the CC (constant-rate-coordinate) PIVP. -/
theorem bgp_headline_unconditional_of_NW_readout_explicit
    (init_presented :
      ∃ f : ℕ → Fin (selectorDimCC d_U UniversalLocalView + 1) → ℤ × ℕ,
        Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧
          selectorReplicatorSphereInitQCC d_U UniversalLocalView selectorInitX0 w
            (bgpWarmGainQNW w) (bgpNWCmuInitQ w) (bgpNWCalphaInitQ w) i =
            (f w i).1 / ((f w i).2 : ℚ))
    (hhalt : ∀ w, undecidableMachine.toDiscreteMachine.haltsOn w →
      ∃ T : ℝ, ∀ t ≥ T,
        3 / 4 ≤ ((bgpHeadlineSolFamNW w) w).z t haltCoordU ∧
          ((bgpHeadlineSolFamNW w) w).z t haltCoordU ≤ 1)
    (hnonhalt : ∀ w, ¬ undecidableMachine.toDiscreteMachine.haltsOn w →
      ∃ T : ℝ, ∀ t ≥ T,
        0 ≤ ((bgpHeadlineSolFamNW w) w).z t haltCoordU ∧
          ((bgpHeadlineSolFamNW w) w).z t haltCoordU ≤ 1 / 4) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P undecidableMachine) := by
  classical
  refine main_assembled_dyn_selector_zreadout_nolatch_repl_W_explicit_pF
    (Conf := UniversalMachine.FinConf UniversalMachine.c_f)
    undecidableMachine (fun w => bgpParamsNW w) selectorSchedule branchU
    bgpHeadlineFieldCC
    (fun w sol La => selectorReplicatorTupleTrajCC sol La
      ((bgpWarmGainQNW w : ℚ) : ℝ)
      ((bgpNWCmuInitQ w : ℚ) : ℝ) ((bgpNWCalphaInitQ w : ℚ) : ℝ))
    ?_
    (fun w => selectorReplicatorSphereInitQCC d_U UniversalLocalView selectorInitX0 w
      (bgpWarmGainQNW w) (bgpNWCmuInitQ w) (bgpNWCalphaInitQ w))
    init_presented haltCoordU (selEmbCC (selZ UniversalLocalView haltCoordU)) ?_
    (fun w => (bgpHeadlineSolFamNW w) w)
    (fun w => selector_replicator_zero_latch_solution ((bgpHeadlineSolFamNW w) w)
      bgpHeadlineR)
    hhalt hnonhalt ?_ ?_
  · intro w sol La t ht
    exact selectorReplicatorTupleTrajCC_ode sol La ((bgpWarmGainQNW w : ℚ) : ℝ)
      (selChiResetPoly d_U UniversalLocalView bgpHeadlineM)
      (selChiGatePoly d_U UniversalLocalView bgpHeadlineM)
      (selKappaPoly d_U UniversalLocalView bgpHeadlineKappa)
      (selGainPoly d_U UniversalLocalView)
      (muReadoutPoly bgpHeadlineEta bgpHeadlineEta_pos)
      (0 : MvPolynomial (Fin d_U) ℚ)
      (bgpParamsNW_A_eq_ratCast w) bgpNW_zero_eq_rat_zero
      (bgp_bgpParamsNW_cμ_rat w) (bgp_bgpParamsNW_cα_rat w)
      (bgpParamsNW_L_eq w)
      bgpNW_selectorSchedule_domain_nonneg
      (fun t _ht =>
        eval_selChiResetPoly_repl (sol := sol) (La := La)
          (warmGainVal := ((bgpWarmGainQNW w : ℚ) : ℝ)) (t := t) bgpHeadlineM)
      (fun t _ht =>
        eval_selChiGatePoly_repl (sol := sol) (La := La)
          (warmGainVal := ((bgpWarmGainQNW w : ℚ) : ℝ)) (t := t) bgpHeadlineM)
      (fun t _ht =>
        eval_selKappaPoly_repl (sol := sol) (La := La)
          (warmGainVal := ((bgpWarmGainQNW w : ℚ) : ℝ)) (t := t) bgpHeadlineKappa)
      (fun t ht => by
        rw [eval_selGainPoly_repl]
        rw [sol.alpha_eq_exp bgpNW_selectorSchedule_domain_nonneg ht])
      (fun v t _ht =>
        eval_muReadoutPoly_repl bgpHeadlineEta bgpHeadlineEta_pos sol La
          ((bgpWarmGainQNW w : ℚ) : ℝ) t v)
      (fun _t => by simp)
      t ht
  · intro w s La t
    simp only [selectorReplicatorTupleTrajCC_castAdd, selectorReplicatorTupleTraj_z]
  · intro w
    obtain ⟨hz0, hu0, hlam0, hG0⟩ := bgpHeadlineSolFamNW_initial_values w w
    exact selector_replicator_init_zero_of_initial_values_CC selectorInitX0 w
      (bgpWarmGainQNW w) (bgpNWCmuInitQ w) (bgpNWCalphaInitQ w)
      ((bgpHeadlineSolFamNW w) w)
      (selector_replicator_zero_latch_solution ((bgpHeadlineSolFamNW w) w)
        bgpHeadlineR) hz0 hu0 hlam0 hG0
  · intro w i
    obtain ⟨hz0, hu0, hlam0, hG0⟩ := bgpHeadlineSolFamNW_initial_values w w
    exact selector_replicator_init_succ_of_initial_values_CC selectorInitX0 w
      (bgpWarmGainQNW w) (bgpNWCmuInitQ w) (bgpNWCalphaInitQ w)
      ((bgpHeadlineSolFamNW w) w)
      (selector_replicator_zero_latch_solution ((bgpHeadlineSolFamNW w) w)
        bgpHeadlineR) hz0 hu0 hlam0 hG0 i

end Ripple.BoundedUniversality.BGP
