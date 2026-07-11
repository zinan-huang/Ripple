import Ripple.BoundedUniversality.BGP.SelectorReplicatorSettledFinal
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
# SelectorReplicatorWarmEuclidean

Per-input warm-gain Euclidean data for the settled selector-replicator route.

The fixed-gain theorem `bgp_MU_replicator_settled` constructs one global
`MUReplicatorSolFamily` at a fixed `g₀`.  Here the gain is input-indexed:
for input `w`, we instantiate the same construction with
`g₀ = warmGainQ w` and use only the `w` member of that family.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance UniversalMachine
open Filter
open scoped BigOperators Topology

private theorem warm_stereo_sum_sq {nE : ℕ} (x : Fin nE → ℝ) :
    (∑ j : Fin (nE + 1), stereo x j ^ 2) = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [stereo, Fin.cases_zero, Fin.cases_succ]
  set r : ℝ := ∑ i : Fin nE, x i ^ 2 with hr
  have hden : r + 1 ≠ 0 := by
    have hr0 : 0 ≤ r := by
      dsimp [r]
      exact Finset.sum_nonneg fun i _hi => sq_nonneg (x i)
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
      _ = (4 / (r + 1) ^ 2) * r := by rw [← Finset.mul_sum]
      _ = 4 * r / (r + 1) ^ 2 := by ring
  simp only [stereoDenom, ← hr]
  rw [htail]
  field_simp [hden]
  ring

private theorem warm_stereo_abs_le_one {nE : ℕ} (x : Fin nE → ℝ)
    (j : Fin (nE + 1)) : |stereo x j| ≤ 1 := by
  have hterm : stereo x j ^ 2 ≤ ∑ k : Fin (nE + 1), stereo x k ^ 2 :=
    Finset.single_le_sum (fun k _hk => sq_nonneg (stereo x k)) (Finset.mem_univ j)
  have hsq : stereo x j ^ 2 ≤ 1 := by
    simpa [warm_stereo_sum_sq x] using hterm
  exact (sq_le_one_iff_abs_le_one (stereo x j)).mp hsq

/-- The per-input warm-gain selector-replicator solution type. -/
abbrev MUReplicatorSolW (eta : ℚ) (heta : 0 < eta) (M : ℕ)
    (κ₀ : ℚ) (warmGainQ : ℕ → ℚ) (w : ℕ) :=
  SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
    branchU
    (fun t => ((1 + Real.cos t) / 2) ^ M)
    (fun t => ((1 + Real.sin t) / 2) ^ M)
    (fun _ => (κ₀ : ℝ))
    (fun t => ((warmGainQ w : ℚ) : ℝ) * Real.exp (bgpParams38.cα * t))
    (universalPval eta heta)

/-- The `solMURepl` family instantiated at the warm gain of the outer input. -/
noncomputable def solMUReplWarm
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ : ℚ) (warmGainQ : ℕ → ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hfin : ∀ wg w,
      Ripple.FiniteHorizonBound
        (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R)
        (selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg)))
    (hgateZ : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateZ d_U)) =
            bGateZ 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (hgateU : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateU d_U)) =
            bGateU 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (h_chiReset : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiResetPoly d_U UniversalLocalView M) =
              ((1 + Real.cos t) / 2) ^ M)
    (h_chiGate : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiGatePoly d_U UniversalLocalView M) =
              ((1 + Real.sin t) / 2) ^ M)
    (h_kappa : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selKappaPoly d_U UniversalLocalView κ₀) = (κ₀ : ℝ))
    (h_gain : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selGainPoly d_U UniversalLocalView) =
              ((warmGainQ wg : ℚ) : ℝ) * Real.exp (bgpParams38.cα * t))
    (h_P : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ (v : UniversalLocalView) (t : ℝ), 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            ((muReadoutPoly eta heta) v) =
              universalPval eta heta v (fun i => y t (selU UniversalLocalView i)))
    (wg : ℕ) :
    MUReplicatorSolFamily eta heta M κ₀ (warmGainQ wg) :=
  solMURepl eta heta M κ₀ (warmGainQ wg) HP Kq R selectorInitX0
    (hfin wg) (hgateZ wg) (hgateU wg)
    (h_chiReset wg) (h_chiGate wg) (h_kappa wg) (h_gain wg) (h_P wg)

set_option maxHeartbeats 1200000 in
-- per-w replicator assembly elaboration

/-- Per-input-gain no-latch z-readout compactification for replicator solutions. -/
theorem main_assembled_dyn_selector_zreadout_nolatch_repl_W
    {d B : ℕ} {Conf : Type} [Primcodable Conf]
    (M₀ : UndecidableMachine Conf)
    (p : DynGateParams) (sched : PhaseSchedule)
    {V : Type} [Fintype V] (branch : V → BranchData d B)
    {chiResetF chiGateF kappaF : ℝ → ℝ} {gainF : ℕ → ℝ → ℝ}
    {Pv : V → (Fin d → ℝ) → ℝ}
    {R : ℕ} {nE : ℕ}
    (field : Fin nE → MvPolynomial (Fin nE) ℚ)
    (tuple :
      ∀ (w : ℕ)
        (sol : SelectorReplicatorDynSol d B V p sched branch
          chiResetF chiGateF kappaF (gainF w) Pv),
        SelectorReplicatorHaltLatchSol sol (fun _ : (Fin d → ℝ) => (0 : ℝ)) 0 R →
          ℝ → Fin nE → ℝ)
    (tuple_ode :
      ∀ (w : ℕ)
        (sol : SelectorReplicatorDynSol d B V p sched branch
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
        (s : SelectorReplicatorDynSol d B V p sched branch
          chiResetF chiGateF kappaF (gainF w) Pv)
        (La : SelectorReplicatorHaltLatchSol s (fun _ : (Fin d → ℝ) => (0 : ℝ)) 0 R)
        (t : ℝ),
          tuple w s La t readCoordE = s.z t readCoord)
    (euclidean :
      ∀ w : ℕ,
        ∃ (sol : SelectorReplicatorDynSol d B V p sched branch
              chiResetF chiGateF kappaF (gainF w) Pv)
          (_La : SelectorReplicatorHaltLatchSol sol (fun _ : (Fin d → ℝ) => (0 : ℝ)) 0 R),
          (M₀.toDiscreteMachine.haltsOn w →
            ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ sol.z t readCoord ∧ sol.z t readCoord ≤ 1) ∧
          (¬ M₀.toDiscreteMachine.haltsOn w →
            ∃ T : ℝ, ∀ t ≥ T, 0 ≤ sol.z t readCoord ∧ sol.z t readCoord ≤ 1 / 4))
    (init_zero :
      ∀ (w : ℕ),
        let sol := Classical.choose (euclidean w)
        let La := selector_replicator_zero_latch_solution sol R
        ((init w 0 : ℚ) : ℝ) =
          ((∑ i : Fin nE, tuple w sol La 0 i ^ 2) - 1) /
            ((∑ i : Fin nE, tuple w sol La 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ) (i : Fin nE),
        let sol := Classical.choose (euclidean w)
        let La := selector_replicator_zero_latch_solution sol R
        ((init w i.succ : ℚ) : ℝ) =
          2 * tuple w sol La 0 i /
            ((∑ k : Fin nE, tuple w sol La 0 k ^ 2) + 1)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P M₀) := by
  classical
  let sol := fun w => Classical.choose (euclidean w)
  have hhalt :
      ∀ w, M₀.toDiscreteMachine.haltsOn w →
        ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ (sol w).z t readCoord ∧ (sol w).z t readCoord ≤ 1 := by
    intro w
    exact (Classical.choose_spec (Classical.choose_spec (euclidean w))).1
  have hnonhalt :
      ∀ w, ¬ M₀.toDiscreteMachine.haltsOn w →
        ∃ T : ℝ, ∀ t ≥ T, 0 ≤ (sol w).z t readCoord ∧ (sol w).z t readCoord ≤ 1 / 4 := by
    intro w
    exact (Classical.choose_spec (Classical.choose_spec (euclidean w))).2
  let La0 := fun w => selector_replicator_zero_latch_solution (sol w) R
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
    · simp [stereo, stereoDenom, init_zero w, La0, sol]
    · intro i
      simp [stereo, stereoDenom, init_succ w i, La0, sol]
  · intro w τ hτ
    simpa [P, Ripple.BoundedUniversality.GPAC.PIVP.evalVF] using hsphere w τ hτ
  · refine ⟨1, by norm_num, ?_⟩
    intro w τ i hτ
    exact warm_stereo_abs_le_one _ _
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

set_option maxHeartbeats 1600000 in
-- per-w settled-to-euclidean elaboration

/-- The settled per-input warm-gain data packaged as the Euclidean z-readout input. -/
theorem bgp_headline_warmGain_euclidean
    (eta : ℚ) (heta : 0 < eta)
    (M : ℕ) (κ₀ : ℚ) (warmGainQ : ℕ → ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hfin : ∀ wg w,
      Ripple.FiniteHorizonBound
        (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R)
        (selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg)))
    (hgateZ : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateZ d_U)) =
            bGateZ 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (hgateU : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateU d_U)) =
            bGateU 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (h_chiReset : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiResetPoly d_U UniversalLocalView M) =
              ((1 + Real.cos t) / 2) ^ M)
    (h_chiGate : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiGatePoly d_U UniversalLocalView M) =
              ((1 + Real.sin t) / 2) ^ M)
    (h_kappa : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selKappaPoly d_U UniversalLocalView κ₀) = (κ₀ : ℝ))
    (h_gain : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selGainPoly d_U UniversalLocalView) =
              ((warmGainQ wg : ℚ) : ℝ) * Real.exp (bgpParams38.cα * t))
    (h_P : ∀ wg w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w (warmGainQ wg) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUReplicatorField eta heta M κ₀ (warmGainQ wg) HP Kq R (y t)) t) →
        ∀ (v : UniversalLocalView) (t : ℝ), 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            ((muReadoutPoly eta heta) v) =
              universalPval eta heta v (fun i => y t (selU UniversalLocalView i)))
    (boxInputs : ∀ wg, MUReplicatorBoxInputs eta heta M κ₀ (warmGainQ wg)
      (solMUReplWarm eta heta M κ₀ warmGainQ HP Kq R hfin hgateZ hgateU
        h_chiReset h_chiGate h_kappa h_gain h_P wg))
    (settled : ∀ wg, MUReplicatorSettledHaltFacts
      (solMUReplWarm eta heta M κ₀ warmGainQ HP Kq R hfin hgateZ hgateU
        h_chiReset h_chiGate h_kappa h_gain h_P wg)) :
    ∀ w : ℕ,
      ∃ (sol : MUReplicatorSolW eta heta M κ₀ warmGainQ w)
        (_La : SelectorReplicatorHaltLatchSol sol (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R),
        (undecidableMachine.toDiscreteMachine.haltsOn w →
          ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ sol.z t haltCoordU ∧ sol.z t haltCoordU ≤ 1) ∧
        (¬ undecidableMachine.toDiscreteMachine.haltsOn w →
          ∃ T : ℝ, ∀ t ≥ T, 0 ≤ sol.z t haltCoordU ∧ sol.z t haltCoordU ≤ 1 / 4) := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  intro w
  let solFam : MUReplicatorSolFamily eta heta M κ₀ (warmGainQ w) :=
    solMUReplWarm eta heta M κ₀ warmGainQ HP Kq R hfin hgateZ hgateU
      h_chiReset h_chiGate h_kappa h_gain h_P w
  have hforward_boxes :
      (∀ t : ℝ, 0 ≤ t →
        selectorMixTarget branchU (solFam w).u (solFam w).lam t haltCoordU ∈ Icc (0 : ℝ) 1) ∧
      (∀ t : ℝ, 0 ≤ t → (solFam w).z t haltCoordU ≤ 1) ∧
      (∀ t : ℝ, 0 ≤ t → 0 ≤ (solFam w).z t haltCoordU) := by
    have boxW := boxInputs w
    have hode : ∀ v : UniversalLocalView, ∀ t : ℝ, 0 ≤ t →
        HasDerivAt ((solFam w).lam v)
          ((((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ)) *
              (1 / (Fintype.card UniversalLocalView : ℝ) - (solFam w).lam v t)
            + (((1 + Real.sin t) / 2) ^ M *
                (((warmGainQ w : ℚ) : ℝ) * Real.exp (bgpParams38.cα * t))) *
              (solFam w).lam v t *
                (universalPval eta heta v ((solFam w).u t)
                  - ∑ u : UniversalLocalView,
                      (solFam w).lam u t * universalPval eta heta u ((solFam w).u t))) t := by
      intro v t ht
      simpa [selectorSchedule] using
        (solFam w).lam_hasDeriv v t (by simpa [selectorSchedule] using ht)
    have hsum : ∀ t : ℝ, 0 ≤ t →
        (∑ v : UniversalLocalView, (solFam w).lam v t) = 1 :=
      replicator_sum_lam_eq_one
        (lam := fun v t => (solFam w).lam v t)
        (P := fun v t => universalPval eta heta v ((solFam w).u t))
        (cr := fun t => ((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ))
        (cg := fun t =>
          ((1 + Real.sin t) / 2) ^ M *
            (((warmGainQ w : ℚ) : ℝ) * Real.exp (bgpParams38.cα * t)))
        boxW.hcr_cont boxW.hcg_cont
        (fun v => (solFam w).cont_lam v)
        (boxW.hP_cont w) hode (boxW.hlam_sum0 w)
    have hlam_nonneg_forward :
        ∀ v : UniversalLocalView, ∀ t : ℝ, 0 ≤ t → 0 ≤ (solFam w).lam v t :=
      replicator_lam_nonneg
        (lam := fun v t => (solFam w).lam v t)
        (P := fun v t => universalPval eta heta v ((solFam w).u t))
        (cr := fun t => ((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ))
        (cg := fun t =>
          ((1 + Real.sin t) / 2) ^ M *
            (((warmGainQ w : ℚ) : ℝ) * Real.exp (bgpParams38.cα * t)))
        boxW.hcr_cont boxW.hcg_cont
        (fun v => (solFam w).cont_lam v)
        (boxW.hP_cont w) boxW.hcr_nonneg hode
        (boxW.hlam_init_nonneg w)
    have hmix : ∀ t : ℝ, 0 ≤ t →
        selectorMixTarget branchU (solFam w).u (solFam w).lam t haltCoordU ∈ Icc (0 : ℝ) 1 := by
      intro t ht
      exact selectorMixTarget_haltCoord_mem_Icc_of_lam_sum_eq_one
        (solFam w).u (solFam w).lam t
        (fun v => hlam_nonneg_forward v t ht)
        (hsum t ht)
    have hzbox :=
      selector_replicator_flag_box_on_nonneg_repl (solFam w)
        boxW.hcr_cont boxW.hcg_cont (boxW.hP_cont w)
        boxW.hcr_nonneg (boxW.hlam_sum0 w)
        (boxW.hlam_init_nonneg w) (boxW.hz0 w)
    exact ⟨hmix, hzbox.1, hzbox.2⟩
  have correct_halt_z :
      undecidableMachine.toDiscreteMachine.haltsOn w →
        ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ (solFam w).z t haltCoordU ∧
          (solFam w).z t haltCoordU ≤ 1 := by
    intro hw
    have hwU : M_U.haltsOn w := by
      simpa using hw
    have settledW := settled w
    have hstart := settledW.hstart_haltOnly w
    have hhold :=
      solMURepl_settled_hhold_of_halts (solFam w) w hwU (settledW.cfg w)
        (settledW.hcfg w)
        (solMUReplSettledRho (settledW.Λ w) (settledW.Bz w)
          (solMUReplSettledHaltDelta settledW.inputs w))
        (settledW.δnext w) (settledW.holdPrefix w)
        hstart.2.2 (settledW.hδnext_nonneg w) (settledW.hholdPrefix_nonneg w)
        hstart.2.1 (settledW.hδnext w) hstart.1
        (settledW.hoff w) (settledW.hnextWrite w) (settledW.hfiniteHold w)
    obtain ⟨δhold, hhold_all, hδhold, hδhold_nonneg⟩ := hhold
    exact selector_correct_halt_endtoend_hold_repl_of_tendsto (solFam w) w hwU
      (settledW.cfg w) (settledW.hcfg w)
      (solMUReplSettledRho (settledW.Λ w) (settledW.Bz w)
        (solMUReplSettledHaltDelta settledW.inputs w))
      δhold hstart.1 hhold_all hforward_boxes.2.1
      hstart.2.1 hδhold hstart.2.2 hδhold_nonneg
  have correct_nonhalt_z :
      ¬ undecidableMachine.toDiscreteMachine.haltsOn w →
        ∃ T : ℝ, ∀ t ≥ T, 0 ≤ (solFam w).z t haltCoordU ∧
          (solFam w).z t haltCoordU ≤ 1 / 4 := by
    intro hw
    have hwU : ¬ M_U.haltsOn w := by
      simpa using hw
    have settledW := settled w
    have hstart := settledW.hstart_haltOnly w
    have hhold :=
      solMURepl_settled_hhold_of_nonhalts (solFam w) w hwU (settledW.cfg w)
        (settledW.hcfg w)
        (solMUReplSettledRho (settledW.Λ w) (settledW.Bz w)
          (solMUReplSettledHaltDelta settledW.inputs w))
        (settledW.δnext w)
        hstart.2.2 (settledW.hδnext_nonneg w) hstart.2.1
        (settledW.hδnext w) hstart.1 (settledW.hoff w) (settledW.hnextWrite w)
    exact selector_correct_nonhalt_endtoend_hold_repl_of_tendsto (solFam w) w hwU
      (settledW.cfg w) (settledW.hcfg w)
      (solMUReplSettledRho (settledW.Λ w) (settledW.Bz w)
        (solMUReplSettledHaltDelta settledW.inputs w))
      (selectorMUSelfHoldDelta (settledW.δnext w)
        (solMUReplSettledRho (settledW.Λ w) (settledW.Bz w)
          (solMUReplSettledHaltDelta settledW.inputs w)))
      hstart.1 hhold.1 hforward_boxes.2.2
      hstart.2.1 hhold.2.1 hstart.2.2 hhold.2.2
  exact ⟨solFam w, selector_replicator_zero_latch_solution (solFam w) R,
    correct_halt_z, correct_nonhalt_z⟩

end Ripple.BoundedUniversality.BGP
