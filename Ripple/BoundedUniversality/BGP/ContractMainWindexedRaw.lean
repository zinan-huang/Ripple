/-
Ripple.BoundedUniversality.BGP.ContractMainWindexedRaw
----------------------------------
The WINDEXED + RAW final contract main theorem: per-input phase schedules AND
box-free.  Copy of `ContractMainWindexed.main_assembled_dyn_contract_windexed`
with the Euclidean assembly call routed through
`contract_dyn_assembled_euclidean_simulation_windexed_raw` (no
`ContractPerCycleBox`), and the box-threaded hypotheses replaced by their raw
counterparts.  The compactification / stereographic-readout tail is byte-identical
(it does not touch the box or the schedules).

This is the assembly the warmed de-axiom headline applies.
-/

import Ripple.BoundedUniversality.BGP.ContractWindexedRaw

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Ripple.BoundedUniversality.Core
open scoped BigOperators

private theorem contract_stereo_sum_sq_wraw {nE : ℕ} (x : Fin nE → ℝ) :
    (∑ j : Fin (nE + 1), stereo x j ^ 2) = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [stereo, Fin.cases_zero, Fin.cases_succ]
  set r : ℝ := ∑ i : Fin nE, x i ^ 2 with hr
  have hden : r + 1 ≠ 0 := by
    have hr0 : 0 ≤ r := by
      dsimp [r]; exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)
    nlinarith
  have htail :
      (∑ i : Fin nE, (2 * x i / (r + 1)) ^ 2) = 4 * r / (r + 1) ^ 2 := by
    simp only [div_pow, mul_pow]
    calc
      (∑ i : Fin nE, (2 ^ 2 * x i ^ 2) / (r + 1) ^ 2)
          = (∑ i : Fin nE, (4 / (r + 1) ^ 2) * x i ^ 2) := by
            apply Finset.sum_congr rfl; intro i _hi; ring
      _ = (4 / (r + 1) ^ 2) * r := by rw [← Finset.mul_sum]
      _ = 4 * r / (r + 1) ^ 2 := by ring
  simp only [stereoDenom, ← hr]
  rw [htail]; field_simp [hden]; ring

private theorem contract_stereo_abs_le_one_wraw {nE : ℕ} (x : Fin nE → ℝ)
    (j : Fin (nE + 1)) : |stereo x j| ≤ 1 := by
  have hterm : stereo x j ^ 2 ≤ ∑ k : Fin (nE + 1), stereo x k ^ 2 :=
    Finset.single_le_sum (fun k _hk => sq_nonneg (stereo x k)) (Finset.mem_univ j)
  have hsq : stereo x j ^ 2 ≤ 1 := by
    simpa [contract_stereo_sum_sq_wraw x] using hterm
  exact (sq_le_one_iff_abs_le_one (stereo x j)).mp hsq

/-- Windexed + box-free final contract main theorem. -/
theorem main_assembled_dyn_contract_windexed_raw
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
    (κ χ : ℕ → ℕ → ℝ)
    (rLE : Fin d → ℝ)
    (amp : ℕ → ℕ → Fin d → ℝ)
    (η : ℕ → DynContractIteratorSol (Fin d) p sched S.F → ℕ → Fin d → ℝ)
    (W : ℕ → ℕ → Fin d → ℝ)
    (depth : ℕ → ℕ → Fin d → ℤ)
    (hsupply :
      ∀ w : ℕ, ∃ _sol : DynContractIteratorSol (Fin d) p sched S.F, True)
    (htracking_inputs :
      ∀ (w : ℕ) (sol : DynContractIteratorSol (Fin d) p sched S.F),
        ContractTrackingInputs S p sched sol
          (fun j => M.toDiscreteMachine.step^[j] (M.toDiscreteMachine.init w))
          (κ w) (χ w) rLE (amp w) (η w sol) (W w) (depth w)
          (trueMovingBox (d := d)) flagCoord)
    (hlatch :
      ∀ sol : DynContractIteratorSol (Fin d) p sched S.F,
        ∃ La : ContractHaltLatchSol sol I.Hval K R,
          ContractLatchConvergenceKernel sol flagCoord I La)
    (hflag_margin_all : ∀ w sol j, η w sol j flagCoord ≤ flagPkg.flagMargin)
    (hflag_margin_indicator : flagPkg.flagMargin ≤ 1 / 4)
    (hflag_domain :
      ∀ (w : ℕ) (sol : DynContractIteratorSol (Fin d) p sched S.F),
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
    contract_dyn_assembled_euclidean_simulation_windexed_raw
      M.toDiscreteMachine E S p sched flagCoord flagPkg I hK
      κ χ rLE amp η W depth hsupply htracking_inputs hlatch
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
    exact contract_stereo_abs_le_one_wraw _ _
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
Windexed + box-free final contract main theorem with solution-specific supply
data.

This is the rich-supply analogue of `main_assembled_dyn_contract_windexed_raw`:
the supplied solution for each input carries its tracking, latch, margin, and
flag-domain facts.
-/
theorem main_assembled_dyn_contract_windexed_raw_rich_supply
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
    (κ χ : ℕ → ℕ → ℝ)
    (rLE : Fin d → ℝ)
    (amp : ℕ → ℕ → Fin d → ℝ)
    (η : ℕ → DynContractIteratorSol (Fin d) p sched S.F → ℕ → Fin d → ℝ)
    (W : ℕ → ℕ → Fin d → ℝ)
    (depth : ℕ → ℕ → Fin d → ℤ)
    (hsupply_rich :
      ∀ w : ℕ,
        ∃ sol : DynContractIteratorSol (Fin d) p sched S.F,
          ContractTrackingInputs S p sched sol
            (fun j => M.toDiscreteMachine.step^[j] (M.toDiscreteMachine.init w))
            (κ w) (χ w) rLE (amp w) (η w sol) (W w) (depth w)
            (trueMovingBox (d := d)) flagCoord ∧
          (∃ La : ContractHaltLatchSol sol I.Hval K R,
            ContractLatchConvergenceKernel sol flagCoord I La) ∧
          (∀ j, η w sol j flagCoord ≤ flagPkg.flagMargin) ∧
          (∀ j t, t ∈ sched.zActiveWindow j →
            sol.z t flagCoord ∈ Set.Icc (0 : ℝ) 1))
    (hflag_margin_indicator : flagPkg.flagMargin ≤ 1 / 4)
    (fieldPkg :
      ContractPolynomialFieldPackage M E S p sched flagCoord I K R) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P M) :=
  main_assembled_dyn_contract_of_euclidean
    M E S p sched flagCoord I
    (contract_dyn_assembled_euclidean_simulation_windexed_raw_rich_supply
      M.toDiscreteMachine E S p sched flagCoord flagPkg I hK
      κ χ rLE amp η W depth hsupply_rich hflag_margin_indicator)
    fieldPkg

#print axioms main_assembled_dyn_contract_windexed_raw_rich_supply

end Ripple.BoundedUniversality.BGP
