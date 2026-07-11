import Ripple.BoundedUniversality.BGP.HeadlineNW2
import Ripple.BoundedUniversality.BGP.HeadlineHoffNW
import Ripple.BoundedUniversality.BGP.HeadlineFlipNW
import Ripple.BoundedUniversality.BGP.HeadlineNextWriteNW
import Ripple.BoundedUniversality.BGP.SelectorReplicatorSettledResidualShifted
import Ripple.BoundedUniversality.BGP.SelectorReplicatorHoffP

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance UniversalMachine Filter
open scoped BigOperators Topology

/-! ## P-generic exact-tracking edge bounds -/

private theorem selectorMU_mixTargetDerivRHS_continuous_for_edgeP
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (w : ℕ) (s : Fin d_U) :
    Continuous fun τ : ℝ =>
      SelectorReplicatorDynSol.mixTargetDerivRHS (sol w) τ s := by
  classical
  have hP : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ => universalPval eta heta v ((sol w).u τ) := by
    intro v
    exact universalPval_continuous_of_cont_u eta heta v
      (fun i => (sol w).cont_u i)
  have hphi : Continuous fun τ : ℝ =>
      ∑ v : UniversalLocalView,
        (sol w).lam v τ * universalPval eta heta v ((sol w).u τ) := by
    exact continuous_finset_sum Finset.univ (fun v _ =>
      ((sol w).cont_lam v).mul (hP v))
  have hbranch : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ =>
        BranchData.evalBranch (branchU v) ((sol w).u τ) s := by
    intro v
    simp only [BranchData.evalBranch, BranchAction.evalReal]
    exact (continuous_const.mul ((sol w).cont_u s)).add continuous_const
  have hq : Continuous fun τ : ℝ => qPulse p.L τ := by
    simp only [qPulse]
    exact ((continuous_const.add Real.continuous_sin).div_const 2).pow p.L
  have hgateU : Continuous fun τ : ℝ =>
      bGateU p.L ((sol w).μ τ) τ := by
    simp only [bGateU]
    exact Real.continuous_exp.comp ((((sol w).cont_μ).mul hq).neg)
  have hcr : Continuous fun τ : ℝ => ((1 + Real.cos τ) / 2) ^ Mcy := by
    fun_prop
  have hcg : Continuous fun τ : ℝ => ((1 + Real.sin τ) / 2) ^ Mcy := by
    fun_prop
  have hgain : Continuous fun τ : ℝ =>
      (g₀ : ℝ) * Real.exp (p.cα * τ) := by
    fun_prop
  dsimp [SelectorReplicatorDynSol.mixTargetDerivRHS]
  refine continuous_finset_sum Finset.univ ?_
  intro v _hv
  exact (((hcr.mul continuous_const).mul
      (continuous_const.sub ((sol w).cont_lam v))).add
        (((hcg.mul hgain).mul ((sol w).cont_lam v)).mul
          ((hP v).sub hphi))).mul (hbranch v) |>.add
    ((((sol w).cont_lam v).mul continuous_const).mul
      ((((continuous_const.mul (sol w).cont_α).mul hgateU).mul
        (((sol w).cont_z s).sub ((sol w).cont_u s)))))

private theorem selectorMUHoffCapLeftField_le_initial_tracking_add_mixTargetDerivRHSP
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (hA : 0 ≤ p.A) (w j : ℕ) :
    (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
      selectorMUHoffIntegrandP sol w τ) ≤
      |selectorMixTarget branchU (sol w).u (sol w).lam
          (selectorMUInterReadStart j) haltCoordU -
        (sol w).z (selectorMUInterReadStart j) haltCoordU| +
      (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
        |SelectorReplicatorDynSol.mixTargetDerivRHS (sol w) τ haltCoordU|) := by
  let a : ℝ := selectorMUInterReadStart j
  let b : ℝ := selectorMUZOffStart j
  let y : ℝ → ℝ := fun τ => (sol w).z τ haltCoordU
  let m : ℝ → ℝ := fun τ =>
    selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU
  let k : ℝ → ℝ := fun τ => selectorMUHoffGateCoeffP sol w τ
  let mdot : ℝ → ℝ := fun τ =>
    SelectorReplicatorDynSol.mixTargetDerivRHS (sol w) τ haltCoordU
  have hab : a ≤ b := by
    simpa [a, b] using selectorMUInterReadStart_le_zOffStart j
  have hk_cont : Continuous k := by
    simpa [k] using selectorMUHoffGateCoeffP_continuous (sol := sol) w
  have hm_cont : Continuous m := by simpa [m] using (sol w).cont_mixTarget haltCoordU
  have hy_cont : Continuous y := by simpa [y] using (sol w).cont_z haltCoordU
  have hmdot_cont : Continuous mdot := by
    simpa [mdot] using
      selectorMU_mixTargetDerivRHS_continuous_for_edgeP (sol := sol) w haltCoordU
  have ha0 : 0 ≤ a := by
    simp [a, selectorMUInterReadStart, selectorMUWriteReadTime]
    positivity
  have hk_nonneg : ∀ τ ∈ Icc a b, 0 ≤ k τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    simpa [k, selectorMUHoffGateCoeffP] using
      selector_replicator_gateZ_integrand_nonneg (sol w)
        selectorSchedule_domain_of_nonneg_structural hA hτ0
  have hm_deriv : ∀ τ ∈ Icc a b, HasDerivAt m (mdot τ) τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    simpa [m, mdot] using
      SelectorReplicatorDynSol.mixTarget_hasDerivAt_ode (sol w)
        (selectorSchedule_domain_of_nonneg_structural τ hτ0) haltCoordU
  have hy_ode : ∀ τ ∈ Icc a b,
      HasDerivAt y (k τ * (m τ - y τ)) τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    simpa [y, m, k, selectorMUHoffGateCoeffP] using
      (sol w).z_hasDeriv τ
        (selectorSchedule_domain_of_nonneg_structural τ hτ0) haltCoordU
  have hscalar := stack_write_tracking_total_variation_le
    y m k mdot hab hk_cont hk_nonneg hm_cont hmdot_cont hm_deriv hy_ode
  have hcap_le :
      (∫ τ in a..b, selectorMUHoffIntegrandP sol w τ) ≤
        ∫ τ in a..b, k τ * |m τ - y τ| := by
    apply intervalIntegral.integral_mono_on hab
      ((selectorMUHoffIntegrandP_continuous (sol := sol) w).intervalIntegrable a b)
      ((hk_cont.mul ((hm_cont.sub hy_cont).abs)).intervalIntegrable a b)
    intro τ hτ
    have hk0 := hk_nonneg τ hτ
    rw [show selectorMUHoffIntegrandP sol w τ =
      |k τ * (m τ - y τ)| by
        simp [selectorMUHoffIntegrandP, selectorMUHoffGateCoeffP, k, m, y],
      abs_mul, abs_of_nonneg hk0]
    change k τ * |m τ - y τ| ≤ k τ * |m τ - y τ|
    exact le_rfl
  exact le_trans hcap_le (by simpa [a, b, y, m, k, mdot] using hscalar)

private theorem selectorMUHoffCapRightField_le_initial_tracking_add_mixTargetDerivRHSP
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (hA : 0 ≤ p.A) (w j : ℕ) :
    (∫ τ in (selectorMUZOffEnd j)..(selectorMUNextWriteStart j),
      selectorMUHoffIntegrandP sol w τ) ≤
      |selectorMixTarget branchU (sol w).u (sol w).lam
          (selectorMUZOffEnd j) haltCoordU -
        (sol w).z (selectorMUZOffEnd j) haltCoordU| +
      (∫ τ in (selectorMUZOffEnd j)..(selectorMUNextWriteStart j),
        |SelectorReplicatorDynSol.mixTargetDerivRHS (sol w) τ haltCoordU|) := by
  let a : ℝ := selectorMUZOffEnd j
  let b : ℝ := selectorMUNextWriteStart j
  let y : ℝ → ℝ := fun τ => (sol w).z τ haltCoordU
  let m : ℝ → ℝ := fun τ =>
    selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU
  let k : ℝ → ℝ := fun τ => selectorMUHoffGateCoeffP sol w τ
  let mdot : ℝ → ℝ := fun τ =>
    SelectorReplicatorDynSol.mixTargetDerivRHS (sol w) τ haltCoordU
  have hab : a ≤ b := by simpa [a, b] using selectorMUZOffEnd_le_nextWriteStart j
  have hk_cont : Continuous k := by
    simpa [k] using selectorMUHoffGateCoeffP_continuous (sol := sol) w
  have hm_cont : Continuous m := by simpa [m] using (sol w).cont_mixTarget haltCoordU
  have hy_cont : Continuous y := by simpa [y] using (sol w).cont_z haltCoordU
  have hmdot_cont : Continuous mdot := by
    simpa [mdot] using
      selectorMU_mixTargetDerivRHS_continuous_for_edgeP (sol := sol) w haltCoordU
  have ha0 : 0 ≤ a := by simp [a, selectorMUZOffEnd]; positivity
  have hk_nonneg : ∀ τ ∈ Icc a b, 0 ≤ k τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    simpa [k, selectorMUHoffGateCoeffP] using
      selector_replicator_gateZ_integrand_nonneg (sol w)
        selectorSchedule_domain_of_nonneg_structural hA hτ0
  have hm_deriv : ∀ τ ∈ Icc a b, HasDerivAt m (mdot τ) τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    simpa [m, mdot] using
      SelectorReplicatorDynSol.mixTarget_hasDerivAt_ode (sol w)
        (selectorSchedule_domain_of_nonneg_structural τ hτ0) haltCoordU
  have hy_ode : ∀ τ ∈ Icc a b,
      HasDerivAt y (k τ * (m τ - y τ)) τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    simpa [y, m, k, selectorMUHoffGateCoeffP] using
      (sol w).z_hasDeriv τ
        (selectorSchedule_domain_of_nonneg_structural τ hτ0) haltCoordU
  have hscalar := stack_write_tracking_total_variation_le
    y m k mdot hab hk_cont hk_nonneg hm_cont hmdot_cont hm_deriv hy_ode
  have hcap_le :
      (∫ τ in a..b, selectorMUHoffIntegrandP sol w τ) ≤
        ∫ τ in a..b, k τ * |m τ - y τ| := by
    apply intervalIntegral.integral_mono_on hab
      ((selectorMUHoffIntegrandP_continuous (sol := sol) w).intervalIntegrable a b)
      ((hk_cont.mul ((hm_cont.sub hy_cont).abs)).intervalIntegrable a b)
    intro τ hτ
    have hk0 := hk_nonneg τ hτ
    rw [show selectorMUHoffIntegrandP sol w τ =
      |k τ * (m τ - y τ)| by
        simp [selectorMUHoffIntegrandP, selectorMUHoffGateCoeffP, k, m, y],
      abs_mul, abs_of_nonneg hk0]
    change k τ * |m τ - y τ| ≤ k τ * |m τ - y τ|
    exact le_rfl
  exact le_trans hcap_le (by simpa [a, b, y, m, k, mdot] using hscalar)

/-! ## Fixed-target reduction for the diagonal NW family -/

private noncomputable def paper3HoffBadPairNW (w j : ℕ) (t : ℝ) : ℝ :=
  (Finset.univ.filter (fun v : UniversalLocalView =>
    v ≠ localViewU (solMUReplStaticCfg w j) ∧
      v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
        (fun v => ((paper3HeadlineSolFamNW w) w).lam v t)

private noncomputable def paper3HoffOldLoserNW (w j : ℕ) (t : ℝ) : ℝ :=
  (Finset.univ.filter (fun v : UniversalLocalView =>
    v ≠ localViewU (solMUReplStaticCfg w j))).sum
      (fun v => ((paper3HeadlineSolFamNW w) w).lam v t)

private theorem paper3Hoff_mix_pointwise_le_oldLoser_NW
    (w j : ℕ) {t : ℝ} (ht0 : 0 ≤ t) :
    |selectorMixTarget branchU ((paper3HeadlineSolFamNW w) w).u
        ((paper3HeadlineSolFamNW w) w).lam t haltCoordU -
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤
      paper3HoffOldLoserNW w j t := by
  have hraw := selectorMixTarget_halt_to_next_of_loser_sum_sharp
    (u := ((paper3HeadlineSolFamNW w) w).u)
    (Λ := ((paper3HeadlineSolFamNW w) w).lam) (t := t)
    (c := solMUReplStaticCfg w j) (epsLam := paper3HoffOldLoserNW w j t)
    (paper3NW_lam_sum_forward w w t ht0)
    (fun v => paper3NW_lam_nonneg_forward w w v t ht0)
    (show (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j))).sum
        (fun v => ((paper3HeadlineSolFamNW w) w).lam v t) ≤
      paper3HoffOldLoserNW w j t from le_rfl)
  simpa [paper3HoffOldLoserNW, solMUReplStaticCfg_step w j] using hraw

private theorem paper3Hoff_mix_pointwise_le_badPair_NW
    (w j : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (henc : selectorMUHaltEncConst (solMUReplStaticCfg w) j) :
    |selectorMixTarget branchU ((paper3HeadlineSolFamNW w) w).u
        ((paper3HeadlineSolFamNW w) w).lam t haltCoordU -
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤
      paper3HoffBadPairNW w j t := by
  classical
  let sol := (paper3HeadlineSolFamNW w) w
  let oldView : UniversalLocalView := localViewU (solMUReplStaticCfg w j)
  let newView : UniversalLocalView := localViewU (solMUReplStaticCfg w (j + 1))
  let M : ℝ :=
    stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU
  let safe : UniversalLocalView → Prop := fun v => v = oldView ∨ v = newView
  have hMnew :
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU = M := by
    simpa [M, selectorMUHaltEncConst] using henc
  have hsafe_target : ∀ v, safe v →
      BranchData.evalBranch (branchU v) (sol.u t) haltCoordU = M := by
    intro v hv
    rcases hv with rfl | rfl
    · have h := branchU_haltCoord_exact_independent
        (solMUReplStaticCfg w j) (sol.u t)
      simpa [oldView, M, solMUReplStaticCfg_step w j] using h
    · have h := branchU_haltCoord_exact_independent
        (solMUReplStaticCfg w (j + 1)) (sol.u t)
      simpa [newView, M, hMnew, solMUReplStaticCfg_step w (j + 1),
        Nat.add_assoc] using h
  have hold_target :
      BranchData.evalBranch (branchU oldView) (sol.u t) haltCoordU = M :=
    hsafe_target oldView (Or.inl rfl)
  have hspread : ∀ v,
      |BranchData.evalBranch (branchU v) (sol.u t) haltCoordU - M| ≤ (1 : ℝ) := by
    intro v
    simpa [hold_target] using
      branchU_haltCoord_spread_le_one v oldView (sol.u t)
  have hraw := selectorMixTarget_halt_to_const_of_safe_loser_sum
    (u := sol.u) (Λ := sol.lam) (t := t) (M := M) (safe := safe)
    (paper3NW_lam_sum_forward w w t ht0)
    (fun v => paper3NW_lam_nonneg_forward w w v t ht0)
    hsafe_target hspread
  simpa [paper3HoffBadPairNW, sol, M, safe, oldView, newView, not_or] using hraw

private theorem selectorMUHoff_fieldIntegral_le_initial_add_targetP
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (hA : 0 ≤ p.A) (w : ℕ) {a b M : ℝ}
    (hab : a ≤ b) (ha0 : 0 ≤ a) :
    (∫ τ in a..b, selectorMUHoffIntegrandP sol w τ) ≤
      |(sol w).z a haltCoordU - M| +
        2 * (∫ τ in a..b,
          selectorMUHoffGateCoeffP sol w τ *
            |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|) := by
  let y : ℝ → ℝ := fun τ => (sol w).z τ haltCoordU
  let m : ℝ → ℝ := fun τ =>
    selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU
  let k : ℝ → ℝ := fun τ => selectorMUHoffGateCoeffP sol w τ
  have hk_cont : Continuous k := by
    simpa [k] using selectorMUHoffGateCoeffP_continuous (sol := sol) w
  have hm_cont : Continuous m := by simpa [m] using (sol w).cont_mixTarget haltCoordU
  have hy_cont : Continuous y := by simpa [y] using (sol w).cont_z haltCoordU
  have hk_nonneg : ∀ τ ∈ Icc a b, 0 ≤ k τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    simpa [k, selectorMUHoffGateCoeffP] using
      selector_replicator_gateZ_integrand_nonneg (sol w)
        selectorSchedule_domain_of_nonneg_structural hA hτ0
  have hy_ode : ∀ τ ∈ Icc a b,
      HasDerivAt y (k τ * (m τ - y τ)) τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    simpa [y, m, k, selectorMUHoffGateCoeffP] using
      (sol w).z_hasDeriv τ
        (selectorSchedule_domain_of_nonneg_structural τ hτ0) haltCoordU
  have herrorInt :
      (∫ τ in a..b, k τ * |y τ - M|) ≤
        |y a - M| + (∫ τ in a..b, k τ * |m τ - M|) := by
    exact stack_write_error_integral_le_initial_add_target
      y m k M a b hab hk_cont hk_nonneg hy_cont hm_cont hy_ode
  have hscalar := stack_write_field_cap_bound_of_error_integral
    y m k M a b hab hk_cont hk_nonneg hy_cont hm_cont herrorInt
  have hcap_le :
      (∫ τ in a..b, selectorMUHoffIntegrandP sol w τ) ≤
        ∫ τ in a..b, k τ * |m τ - y τ| := by
    apply intervalIntegral.integral_mono_on hab
      ((selectorMUHoffIntegrandP_continuous (sol := sol) w).intervalIntegrable a b)
      ((hk_cont.mul ((hm_cont.sub hy_cont).abs)).intervalIntegrable a b)
    intro τ hτ
    have hk0 := hk_nonneg τ hτ
    rw [show selectorMUHoffIntegrandP sol w τ =
      |k τ * (m τ - y τ)| by
        simp [selectorMUHoffIntegrandP, selectorMUHoffGateCoeffP, k, m, y],
      abs_mul, abs_of_nonneg hk0]
    change k τ * |m τ - y τ| ≤ k τ * |m τ - y τ|
    exact le_rfl
  exact hcap_le.trans (by simpa [y, m, k] using hscalar)

private theorem paper3Hoff_fieldCap_le_readError_add_badIntegral_NW
    (w j : ℕ) {a b : ℝ} (hab : a ≤ b) (ha0 : 0 ≤ a)
    (henc : selectorMUHaltEncConst (solMUReplStaticCfg w) j) :
    (∫ τ in a..b, paper3HeadlineHoffIntegrandNW w τ) ≤
      |((paper3HeadlineSolFamNW w) w).z a haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| +
      2 * (∫ τ in a..b,
        selectorMUHoffGateCoeffP (p := bgpParamsNW w)
          (paper3HeadlineSolFamNW w) w τ * paper3HoffBadPairNW w j τ) := by
  let k : ℝ → ℝ := fun τ => selectorMUHoffGateCoeffP
    (p := bgpParamsNW w) (paper3HeadlineSolFamNW w) w τ
  let e : ℝ → ℝ := fun τ =>
    |selectorMixTarget branchU ((paper3HeadlineSolFamNW w) w).u
        ((paper3HeadlineSolFamNW w) w).lam τ haltCoordU -
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU|
  let bad : ℝ → ℝ := paper3HoffBadPairNW w j
  have hk_cont : Continuous k := by
    simpa [k] using selectorMUHoffGateCoeffP_continuous
      (p := bgpParamsNW w) (sol := paper3HeadlineSolFamNW w) w
  have he_cont : Continuous e := by
    exact (((paper3HeadlineSolFamNW w) w).cont_mixTarget haltCoordU).sub
      continuous_const |>.abs
  have hbad_cont : Continuous bad := by
    dsimp [bad, paper3HoffBadPairNW]
    exact continuous_finsetSum _ (fun v _ =>
      ((paper3HeadlineSolFamNW w) w).cont_lam v)
  have hk0 : ∀ τ ∈ Icc a b, 0 ≤ k τ := by
    intro τ hτ
    have hτ0 := le_trans ha0 hτ.1
    simpa [k, selectorMUHoffGateCoeffP] using
      paper3NW4_zKernel_nonneg w w hτ0
  have hmono :
      (∫ τ in a..b, k τ * e τ) ≤ ∫ τ in a..b, k τ * bad τ := by
    apply intervalIntegral.integral_mono_on hab
      ((hk_cont.mul he_cont).intervalIntegrable a b)
      ((hk_cont.mul hbad_cont).intervalIntegrable a b)
    intro τ hτ
    exact mul_le_mul_of_nonneg_left
      (paper3Hoff_mix_pointwise_le_badPair_NW w j
        (le_trans ha0 hτ.1) henc) (hk0 τ hτ)
  have hbase := selectorMUHoff_fieldIntegral_le_initial_add_targetP
    (p := bgpParamsNW w) (sol := paper3HeadlineSolFamNW w)
    (by rw [bgpParamsNW_A_eq]; norm_num) w hab ha0
    (M := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU)
  have hbase' :
      (∫ τ in a..b, paper3HeadlineHoffIntegrandNW w τ) ≤
      |((paper3HeadlineSolFamNW w) w).z a haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| +
        2 * (∫ τ in a..b, k τ * e τ) := by
    simpa [paper3HeadlineHoffIntegrandNW, k, e] using hbase
  exact hbase'.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (by simpa [k, bad] using hmono) (by norm_num)))

/-! ## Left-edge running-time loser integral -/

private theorem paper3HoffBadPair_le_oldLoser_NW (w j : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) :
    paper3HoffBadPairNW w j t ≤
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j))).sum
          (fun v => ((paper3HeadlineSolFamNW w) w).lam v t) := by
  classical
  unfold paper3HoffBadPairNW
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro v hv
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ v, (Finset.mem_filter.mp hv).2.1⟩
  · intro v _hvold _hvbad
    exact paper3NW_lam_nonneg_forward w w v t ht0

private theorem paper3Hoff_left_bad_pointwise_NW
    (w j : ℕ) {τ : ℝ}
    (hτ : τ ∈ Icc (selectorMUInterReadStart j) (selectorMUZOffStart j)) :
    selectorMUHoffGateCoeffP (p := bgpParamsNW w)
        (paper3HeadlineSolFamNW w) w τ * paper3HoffBadPairNW w j τ ≤
      paper3S4aLoserCoeffNW w j *
        Real.exp (-(250 * (bgpScaleW w : ℝ) * τ)) := by
  let S : ℝ := (bgpScaleW w : ℝ)
  let k : ℝ := selectorMUHoffGateCoeffP (p := bgpParamsNW w)
    (paper3HeadlineSolFamNW w) w τ
  let B : ℝ := paper3HoffBadPairNW w j τ
  let L : ℝ := paper3S4aLoserCoeffNW w j
  have hτ0 : 0 ≤ τ := by
    have ha0 : 0 ≤ selectorMUInterReadStart j := by
      unfold selectorMUInterReadStart selectorMUWriteReadTime
      positivity
    exact le_trans ha0 hτ.1
  have hk0 : 0 ≤ k := by
    dsimp [k, selectorMUHoffGateCoeffP]
    exact paper3NW4_zKernel_nonneg w w hτ0
  have hB0 : 0 ≤ B := by
    dsimp [B, paper3HoffBadPairNW]
    exact Finset.sum_nonneg fun v _ => paper3NW_lam_nonneg_forward w w v τ hτ0
  have hL0 : 0 ≤ L := by
    exact paper3S4aLoserCoeffNW_nonneg w j
  have hk : k ≤ Real.exp (50 * S * τ) := by
    change (bgpParamsNW w).A * ((paper3HeadlineSolFamNW w) w).α τ *
      bGateZ (bgpParamsNW w).L (((paper3HeadlineSolFamNW w) w).μ τ) τ ≤
        Real.exp (50 * (bgpScaleW w : ℝ) * τ)
    exact paper3NW_gateZ_integrand_le_halfphase w hτ0
      (paper3HeadlineLeft_sin_le_half j hτ)
  have hB : B ≤ L * Real.exp (-((bgpParamsNW w).cα * τ)) := by
    have hpair := paper3HoffBadPair_le_oldLoser_NW w j hτ0
    have hold := paper3S4a_loser_mass_timelocal_NW w j τ
      ⟨le_trans (by
        unfold selectorMUWriteHoldTime selectorMUInterReadStart
          selectorMUWriteReadTime
        linarith [Real.pi_pos]) hτ.1, hτ.2⟩
    exact hpair.trans (by simpa [L] using hold)
  have hprod : k * B ≤
      Real.exp (50 * S * τ) *
        (L * Real.exp (-((bgpParamsNW w).cα * τ))) := by
    exact mul_le_mul hk hB hB0 (Real.exp_pos _).le
  calc
    selectorMUHoffGateCoeffP (p := bgpParamsNW w)
        (paper3HeadlineSolFamNW w) w τ * paper3HoffBadPairNW w j τ
        = k * B := rfl
    _ ≤ Real.exp (50 * S * τ) *
        (L * Real.exp (-((bgpParamsNW w).cα * τ))) := hprod
    _ = L * Real.exp (-(250 * S * τ)) := by
      have hcα : (bgpParamsNW w).cα = 300 * S := by
        dsimp only [S]
        exact bgpParamsNW_cα_def w
      rw [hcα]
      calc
        Real.exp (50 * S * τ) * (L * Real.exp (-(300 * S * τ))) =
            L * (Real.exp (50 * S * τ) * Real.exp (-(300 * S * τ))) := by ring
        _ = L * Real.exp (50 * S * τ + -(300 * S * τ)) := by
          rw [Real.exp_add]
        _ = L * Real.exp (-(250 * S * τ)) := by congr 2 <;> ring

private theorem paper3Hoff_left_oldLoser_pointwise_NW
    (w j : ℕ) {τ : ℝ}
    (hτ : τ ∈ Icc (selectorMUInterReadStart j) (selectorMUZOffStart j)) :
    selectorMUHoffGateCoeffP (p := bgpParamsNW w)
        (paper3HeadlineSolFamNW w) w τ * paper3HoffOldLoserNW w j τ ≤
      paper3S4aLoserCoeffNW w j *
        Real.exp (-(250 * (bgpScaleW w : ℝ) * τ)) := by
  let S : ℝ := (bgpScaleW w : ℝ)
  let k : ℝ := selectorMUHoffGateCoeffP (p := bgpParamsNW w)
    (paper3HeadlineSolFamNW w) w τ
  let B : ℝ := paper3HoffOldLoserNW w j τ
  let L : ℝ := paper3S4aLoserCoeffNW w j
  have hτ0 : 0 ≤ τ := by
    exact le_trans (by
      unfold selectorMUInterReadStart selectorMUWriteReadTime
      positivity) hτ.1
  have hk0 : 0 ≤ k := by
    dsimp [k, selectorMUHoffGateCoeffP]
    exact paper3NW4_zKernel_nonneg w w hτ0
  have hB0 : 0 ≤ B := by
    dsimp [B, paper3HoffOldLoserNW]
    exact Finset.sum_nonneg fun v _ => paper3NW_lam_nonneg_forward w w v τ hτ0
  have hk : k ≤ Real.exp (50 * S * τ) := by
    change (bgpParamsNW w).A * ((paper3HeadlineSolFamNW w) w).α τ *
      bGateZ (bgpParamsNW w).L (((paper3HeadlineSolFamNW w) w).μ τ) τ ≤
        Real.exp (50 * (bgpScaleW w : ℝ) * τ)
    exact paper3NW_gateZ_integrand_le_halfphase w hτ0
      (paper3HeadlineLeft_sin_le_half j hτ)
  have hB : B ≤ L * Real.exp (-((bgpParamsNW w).cα * τ)) := by
    have hold := paper3S4a_loser_mass_timelocal_NW w j τ
      ⟨le_trans (by
        unfold selectorMUWriteHoldTime selectorMUInterReadStart
          selectorMUWriteReadTime
        linarith [Real.pi_pos]) hτ.1, hτ.2⟩
    simpa [B, L, paper3HoffOldLoserNW] using hold
  have hprod := mul_le_mul hk hB hB0 (Real.exp_pos _).le
  calc
    selectorMUHoffGateCoeffP (p := bgpParamsNW w)
        (paper3HeadlineSolFamNW w) w τ * paper3HoffOldLoserNW w j τ = k * B := rfl
    _ ≤ Real.exp (50 * S * τ) *
        (L * Real.exp (-((bgpParamsNW w).cα * τ))) := hprod
    _ = L * Real.exp (-(250 * S * τ)) := by
      have hc : (bgpParamsNW w).cα = 300 * S := by
        dsimp [S]; exact bgpParamsNW_cα_def w
      rw [hc]
      calc
        Real.exp (50 * S * τ) * (L * Real.exp (-(300 * S * τ))) =
            L * (Real.exp (50 * S * τ) * Real.exp (-(300 * S * τ))) := by ring
        _ = L * Real.exp (50 * S * τ + -(300 * S * τ)) := by
          rw [Real.exp_add]
        _ = L * Real.exp (-(250 * S * τ)) := by congr 2 <;> ring

private theorem paper3S4aLoserCoeffNW_le_exp_currency
    (w j : ℕ) :
    paper3S4aLoserCoeffNW w j ≤
      Real.exp (100 * (bgpScaleW w : ℝ) + 1000) := by
  let S : ℝ := (bgpScaleW w : ℝ)
  let card : ℝ := (Fintype.card UniversalLocalView : ℝ)
  have hL := paper3S4aLoserCoeffNW_le_card_sq_reset w j
  have hR := paper3S4ResetCoeffNW_le_one w
  have hcard := paper3NW4_card_le_exp w
  have hcard0 : 0 ≤ card := by dsimp [card]; positivity
  have hcard2 : card ^ 2 ≤ Real.exp (12 * S) := by
    have hcard' : card ≤ Real.exp (6 * S) := by
      dsimp only [card, S]
      exact hcard
    have hp := pow_le_pow_left₀ hcard0 hcard' 2
    calc
      card ^ 2 ≤ Real.exp (6 * S) ^ 2 := hp
      _ = Real.exp (12 * S) := by rw [← Real.exp_nat_mul]; ring
  have hLR : paper3S4aLoserCoeffNW w j ≤ card ^ 2 := by
    calc
      paper3S4aLoserCoeffNW w j
          ≤ card ^ 2 * paper3S4ResetCoeffNW w := by
            dsimp only [card]
            exact hL
      _ ≤ card ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hR (sq_nonneg card)
      _ = card ^ 2 := by ring
  calc
    paper3S4aLoserCoeffNW w j ≤ card ^ 2 := hLR
    _ ≤ Real.exp (12 * S) := hcard2
    _ ≤ Real.exp (100 * S + 1000) := by
      apply Real.exp_le_exp.mpr
      have hS0 : 0 ≤ S := by dsimp [S]; exact (bgpScaleWR_pos w).le
      nlinarith

private theorem paper3Hoff_exp250_currency_le_budget_div_32_NW
    (w j : ℕ) {K : ℝ}
    (hK : K ≤ Real.exp (100 * (bgpScaleW w : ℝ) + 1000)) :
    (K / (250 * (bgpScaleW w : ℝ))) *
      Real.exp (-(250 * (bgpScaleW w : ℝ) *
        selectorMUInterReadStart j)) ≤
      selectorMUHoffEdgeBudget3992 j / 32 := by
  let S : ℝ := (bgpScaleW w : ℝ)
  let a : ℝ := selectorMUInterReadStart j
  let T : ℝ := 2 * Real.pi * (j : ℝ) + Real.pi
  have hS4 : (4 : ℝ) ≤ S := by
    dsimp only [S]
    exact bgpScaleWR_ge_four w
  have hSpos : 0 < S := lt_of_lt_of_le (by norm_num) hS4
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hmargin : 100 * S + 1000 + 200 * T ≤ 250 * S * a := by
    dsimp [a, T]
    unfold selectorMUInterReadStart selectorMUWriteReadTime
    have hpi := Real.pi_gt_three
    have hS0 : (0 : ℝ) ≤ S := hSpos.le
    nlinarith [mul_nonneg hj Real.pi_pos.le,
      mul_nonneg (mul_nonneg hS0 hj) Real.pi_pos.le,
      mul_nonneg hS0 Real.pi_pos.le]
  have hKexp : K * Real.exp (-(250 * S * a)) ≤ Real.exp (-(200 * T)) := by
    have hK' : K ≤ Real.exp (100 * S + 1000) := by
      dsimp only [S]
      exact hK
    calc
      K * Real.exp (-(250 * S * a))
          ≤ Real.exp (100 * S + 1000) * Real.exp (-(250 * S * a)) :=
        mul_le_mul_of_nonneg_right hK' (Real.exp_pos _).le
      _ = Real.exp (100 * S + 1000 - 250 * S * a) := by
        rw [← Real.exp_add]
        ring_nf
      _ ≤ Real.exp (-(200 * T)) := Real.exp_le_exp.mpr (by linarith)
  have hcoef : 1 / (250 * S) ≤ (7 : ℝ) / 32 := by
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num : (0 : ℝ) < 32)]
    nlinarith
  have hleft :
      (K / (250 * S)) * Real.exp (-(250 * S * a)) ≤
        (7 / 32) * Real.exp (-(200 * T)) := by
    calc
      (K / (250 * S)) * Real.exp (-(250 * S * a))
          = (1 / (250 * S)) * (K * Real.exp (-(250 * S * a))) := by ring
      _ ≤ (1 / (250 * S)) * Real.exp (-(200 * T)) :=
        mul_le_mul_of_nonneg_left hKexp (by positivity)
      _ ≤ (7 / 32) * Real.exp (-(200 * T)) :=
        mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
  have hbudgetCoeff : (7 : ℝ) ≤ selectorMUHoffEdgeBudgetCoeff := by
    unfold selectorMUHoffEdgeBudgetCoeff
    linarith [selectorReplicatorHoldEnvelopeCoeff_ge_eight]
  unfold selectorMUHoffEdgeBudget3992 selectorMUHoffEdgeBudget
  rw [show bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L -
      bgpParams38.cα = 200 by norm_num [bgpParams38]]
  change (K / (250 * S)) * Real.exp (-(250 * S * a)) ≤
    (selectorMUHoffEdgeBudgetCoeff * Real.exp (-(200 * T))) / 32
  calc
    (K / (250 * S)) * Real.exp (-(250 * S * a))
        ≤ (7 / 32) * Real.exp (-(200 * T)) := hleft
    _ ≤ (selectorMUHoffEdgeBudgetCoeff / 32) * Real.exp (-(200 * T)) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hbudgetCoeff
          (by norm_num)) (Real.exp_pos _).le
    _ = (selectorMUHoffEdgeBudgetCoeff * Real.exp (-(200 * T))) / 32 := by ring

private theorem paper3Hoff_left_badIntegral_le_budget_div_32_NW
    (w j : ℕ) :
    (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
      selectorMUHoffGateCoeffP (p := bgpParamsNW w)
        (paper3HeadlineSolFamNW w) w τ * paper3HoffBadPairNW w j τ) ≤
      selectorMUHoffEdgeBudget3992 j / 32 := by
  let a : ℝ := selectorMUInterReadStart j
  let b : ℝ := selectorMUZOffStart j
  let S : ℝ := (bgpScaleW w : ℝ)
  let K : ℝ := paper3S4aLoserCoeffNW w j
  let F : ℝ → ℝ := fun τ => selectorMUHoffGateCoeffP
    (p := bgpParamsNW w) (paper3HeadlineSolFamNW w) w τ *
      paper3HoffBadPairNW w j τ
  have hab : a ≤ b := by simpa [a, b] using selectorMUInterReadStart_le_zOffStart j
  have hr : 0 < 250 * S := by dsimp [S]; nlinarith [bgpScaleWR_pos w]
  have hK0 : 0 ≤ K := by exact paper3S4aLoserCoeffNW_nonneg w j
  have hFcont : Continuous F := by
    apply Continuous.mul
    · simpa [F] using selectorMUHoffGateCoeffP_continuous
        (p := bgpParamsNW w) (sol := paper3HeadlineSolFamNW w) w
    · dsimp [F, paper3HoffBadPairNW]
      exact continuous_finsetSum _ (fun v _ =>
        ((paper3HeadlineSolFamNW w) w).cont_lam v)
  have hEcont : Continuous fun τ : ℝ => K * Real.exp (-(250 * S * τ)) := by
    fun_prop
  have hmono : (∫ τ in a..b, F τ) ≤
      ∫ τ in a..b, K * Real.exp (-(250 * S * τ)) := by
    apply intervalIntegral.integral_mono_on hab
      (hFcont.intervalIntegrable a b) (hEcont.intervalIntegrable a b)
    intro τ hτ
    change selectorMUHoffGateCoeffP (p := bgpParamsNW w)
      (paper3HeadlineSolFamNW w) w τ * paper3HoffBadPairNW w j τ ≤
        paper3S4aLoserCoeffNW w j *
          Real.exp (-(250 * (bgpScaleW w : ℝ) * τ))
    exact paper3Hoff_left_bad_pointwise_NW w j hτ
  have htail := integral_const_mul_exp_neg_le_left
    (r := 250 * S) (C := K) (a := a) (b := b) hr hK0 hab
  have hcurrency := paper3Hoff_exp250_currency_le_budget_div_32_NW w j
    (paper3S4aLoserCoeffNW_le_exp_currency w j)
  have hcurrency' : (K / (250 * S)) * Real.exp (-(250 * S * a)) ≤
      selectorMUHoffEdgeBudget3992 j / 32 := by
    dsimp only [K, S, a]
    exact hcurrency
  exact hmono.trans (htail.trans hcurrency')

private theorem paper3Hoff_left_oldLoserIntegral_le_budget_div_32_NW
    (w j : ℕ) :
    (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
      selectorMUHoffGateCoeffP (p := bgpParamsNW w)
        (paper3HeadlineSolFamNW w) w τ * paper3HoffOldLoserNW w j τ) ≤
      selectorMUHoffEdgeBudget3992 j / 32 := by
  let a : ℝ := selectorMUInterReadStart j
  let b : ℝ := selectorMUZOffStart j
  let S : ℝ := (bgpScaleW w : ℝ)
  let K : ℝ := paper3S4aLoserCoeffNW w j
  let F : ℝ → ℝ := fun τ => selectorMUHoffGateCoeffP
    (p := bgpParamsNW w) (paper3HeadlineSolFamNW w) w τ *
      paper3HoffOldLoserNW w j τ
  have hab : a ≤ b := by simpa [a, b] using selectorMUInterReadStart_le_zOffStart j
  have hr : 0 < 250 * S := by dsimp [S]; nlinarith [bgpScaleWR_pos w]
  have hK0 : 0 ≤ K := paper3S4aLoserCoeffNW_nonneg w j
  have hFcont : Continuous F := by
    apply Continuous.mul
    · simpa [F] using selectorMUHoffGateCoeffP_continuous
        (p := bgpParamsNW w) (sol := paper3HeadlineSolFamNW w) w
    · dsimp [F, paper3HoffOldLoserNW]
      exact continuous_finsetSum _ (fun v _ =>
        ((paper3HeadlineSolFamNW w) w).cont_lam v)
  have hEcont : Continuous fun τ : ℝ => K * Real.exp (-(250 * S * τ)) := by
    fun_prop
  have hmono : (∫ τ in a..b, F τ) ≤
      ∫ τ in a..b, K * Real.exp (-(250 * S * τ)) := by
    apply intervalIntegral.integral_mono_on hab
      (hFcont.intervalIntegrable a b) (hEcont.intervalIntegrable a b)
    intro τ hτ
    exact paper3Hoff_left_oldLoser_pointwise_NW w j hτ
  have htail := integral_const_mul_exp_neg_le_left
    (r := 250 * S) (C := K) (a := a) (b := b) hr hK0 hab
  have hcurrency := paper3Hoff_exp250_currency_le_budget_div_32_NW w j
    (paper3S4aLoserCoeffNW_le_exp_currency w j)
  have hcurrency' : (K / (250 * S)) * Real.exp (-(250 * S * a)) ≤
      selectorMUHoffEdgeBudget3992 j / 32 := by
    dsimp only [K, S, a]
    exact hcurrency
  exact hmono.trans (htail.trans hcurrency')

/-! #### S4b loser-mass preparation -/

/-- Instantiate the conditional S2 post-copy tube with the landed handoff
entry. -/
private noncomputable def paper3S4bDeltaGFloorNW (w j : ℕ) : ℝ :=
  (Real.pi / 12) * ((1 / 4 : ℝ) ^ paper3HeadlineM *
    (((paper3WarmGainQNW w : ℚ) : ℝ) *
      Real.exp ((bgpParamsNW w).cα * paper3S2Mid j)))

private theorem paper3S4b_G_increment_ge_NW (w j : ℕ) :
    paper3S4bDeltaGFloorNW w j ≤
      ((paper3HeadlineSolFamNW w) w).G (selectorMUZOffEnd j) -
        ((paper3HeadlineSolFamNW w) w).G (paper3S2Mid j) := by
  have hab := paper3S2_mid_le_zOffEnd j
  have ha0 := paper3S2_mid_nonneg j
  rw [paper3NW4_G_sub_eq w w ha0 hab]
  have hconst : paper3S4bDeltaGFloorNW w j =
      ∫ _s in (paper3S2Mid j)..(selectorMUZOffEnd j),
        ((1 / 4 : ℝ) ^ paper3HeadlineM *
          (((paper3WarmGainQNW w : ℚ) : ℝ) *
            Real.exp ((bgpParamsNW w).cα * paper3S2Mid j))) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    unfold paper3S4bDeltaGFloorNW paper3S2Mid selectorMUZOffEnd
    ring
  rw [hconst]
  refine intervalIntegral.integral_mono_on hab intervalIntegrable_const
    ((paper3NW4cg_cont w).intervalIntegrable _ _) ?_
  intro s hs
  have hsin := paper3S2_sin_ge_neg_half j
    (le_trans (paper3S2_recStart_le_mid j) hs.1) hs.2
  have hpow : (1 / 4 : ℝ) ^ paper3HeadlineM ≤
      ((1 + Real.sin s) / 2) ^ paper3HeadlineM :=
    pow_le_pow_left₀ (by norm_num) (by linarith) _
  have hexp : Real.exp ((bgpParamsNW w).cα * paper3S2Mid j) ≤
      Real.exp ((bgpParamsNW w).cα * s) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hs.1 (bgpParamsNW_cα_pos w).le
  unfold paper3NW4cg
  exact mul_le_mul hpow
    (mul_le_mul_of_nonneg_left hexp (paper3WarmGainQNW_nonneg_real w))
    (mul_nonneg (paper3WarmGainQNW_nonneg_real w) (Real.exp_pos _).le)
    (pow_nonneg (by nlinarith [Real.neg_one_le_sin s]) _)

private noncomputable def paper3S4bInitialCoeffNW (w j : ℕ) : ℝ :=
  Real.exp (-(15 / 16 : ℝ) * paper3S4bDeltaGFloorNW w j +
    (bgpParamsNW w).cα * selectorMUZOffEnd j)

private theorem paper3S4bInitialCoeffNW_nonneg (w j : ℕ) :
    0 ≤ paper3S4bInitialCoeffNW w j := (Real.exp_pos _).le

private theorem paper3S4bInitialCoeffNW_le_one (w j : ℕ) :
    paper3S4bInitialCoeffNW w j ≤ 1 := by
  let S : ℝ := (bgpScaleW w : ℝ)
  let g : ℝ := ((paper3WarmGainQNW w : ℚ) : ℝ)
  let c : ℝ := (bgpParamsNW w).cα
  let a : ℝ := paper3S2Mid j
  let z : ℝ := selectorMUZOffEnd j
  let q : ℝ := (Real.pi / 12) * (1 / 4 : ℝ) ^ paper3HeadlineM
  have hS : (5184 : ℝ) ≤ S := by dsimp only [S]; exact paper3NW4_S_ge w
  have hS0 : 0 < S := by dsimp only [S]; exact bgpScaleWR_pos w
  have hg0 : 0 < g := by dsimp only [g]; exact paper3WarmGainQNW_pos_real w
  have hc0 : 0 < c := by dsimp only [c]; exact bgpParamsNW_cα_pos w
  have ha0 : 0 ≤ a := by dsimp only [a]; exact paper3S2_mid_nonneg j
  have hq0 : 0 ≤ q := by
    dsimp only [q]
    positivity
  have hS6 : (5184 : ℝ) ^ 6 ≤ S ^ 6 := pow_le_pow_left₀ (by norm_num) hS 6
  have hgscale : (1734736490 : ℝ) * S ^ 6 ≤ g := by
    dsimp only [g, S]
    unfold paper3WarmGainQNW paper3WarmGainCNW
    push_cast
    have hpow : (1 : ℝ) ≤ (6 : ℝ) ^ w := one_le_pow₀ (by norm_num)
    nlinarith [mul_nonneg
      (by positivity : (0 : ℝ) ≤ 1734736490 * (bgpScaleW w : ℝ) ^ 6)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 6) w)]
  have hgbase : (1734736490 : ℝ) * (5184 : ℝ) ^ 6 ≤ g := by
    exact (mul_le_mul_of_nonneg_left hS6 (by norm_num)).trans hgscale
  have hqg : (2 : ℝ) ≤ q * g := by
    have hq_lb : (3 / 12 : ℝ) * (1 / 4 : ℝ) ^ paper3HeadlineM ≤ q := by
      dsimp only [q]
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right Real.pi_gt_three.le (by norm_num))
        (pow_nonneg (by norm_num) _)
    have hnum : (2 : ℝ) ≤
        ((3 / 12 : ℝ) * (1 / 4 : ℝ) ^ paper3HeadlineM) *
          ((1734736490 : ℝ) * (5184 : ℝ) ^ 6) := by
      norm_num [paper3HeadlineM]
    exact hnum.trans (mul_le_mul hq_lb hgbase (by positivity) hq0)
  have hexp : 1 + c * a ≤ Real.exp (c * a) := by
    simpa [add_comm] using Real.add_one_le_exp (c * a)
  have hD : 2 * (1 + c * a) ≤ paper3S4bDeltaGFloorNW w j := by
    have hmul := mul_le_mul hqg hexp (by positivity) (by positivity)
    dsimp only [paper3S4bDeltaGFloorNW, q, g, c, a] at hmul ⊢
    nlinarith
  have hza : 23 * z ≤ 24 * a := by
    dsimp only [z, a]
    unfold selectorMUZOffEnd paper3S2Mid
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    nlinarith [mul_nonneg Real.pi_pos.le hj]
  have hcza : 23 * (c * z) ≤ 24 * (c * a) := by
    nlinarith [mul_le_mul_of_nonneg_left hza hc0.le]
  have hexponent : c * z ≤ (15 / 16 : ℝ) * paper3S4bDeltaGFloorNW w j := by
    have hca0 : 0 ≤ c * a := mul_nonneg hc0.le ha0
    nlinarith [mul_le_mul_of_nonneg_left hD (by norm_num : (0 : ℝ) ≤ 15 / 16)]
  unfold paper3S4bInitialCoeffNW
  rw [Real.exp_le_one_iff]
  dsimp only [c, z] at hexponent ⊢
  linarith

private theorem paper3S4bInitialCoeffNW_le_reset (w j : ℕ) :
    paper3S4bInitialCoeffNW w j ≤ paper3S4bResetCoeffNW w := by
  let g : ℝ := ((paper3WarmGainQNW w : ℚ) : ℝ)
  let c : ℝ := (bgpParamsNW w).cα
  let a : ℝ := paper3S2Mid j
  let z : ℝ := selectorMUZOffEnd j
  let q : ℝ := (Real.pi / 12) * (1 / 4 : ℝ) ^ paper3HeadlineM
  let A : ℝ := (15 / 16 : ℝ) * q * g
  have hg : 0 < g := by dsimp only [g]; exact paper3WarmGainQNW_pos_real w
  have hc : 0 < c := by dsimp only [c]; exact bgpParamsNW_cα_pos w
  have ha0 : 0 ≤ a := by dsimp only [a]; exact paper3S2_mid_nonneg j
  have hca0 : 0 ≤ c * a := mul_nonneg hc.le ha0
  have hgbase : (1734736490 : ℝ) * (5184 : ℝ) ^ 6 ≤ g := by
    have hS6 : (5184 : ℝ) ^ 6 ≤ (bgpScaleW w : ℝ) ^ 6 :=
      pow_le_pow_left₀ (by norm_num) (paper3NW4_S_ge w) 6
    have hgscale : (1734736490 : ℝ) * (bgpScaleW w : ℝ) ^ 6 ≤ g := by
      dsimp only [g]
      unfold paper3WarmGainQNW paper3WarmGainCNW
      push_cast
      have hpow : (1 : ℝ) ≤ (6 : ℝ) ^ w := one_le_pow₀ (by norm_num)
      nlinarith [mul_nonneg
        (by positivity : (0 : ℝ) ≤ 1734736490 * (bgpScaleW w : ℝ) ^ 6)
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 6) w)]
    exact (mul_le_mul_of_nonneg_left hS6 (by norm_num)).trans hgscale
  have hA4 : (4 : ℝ) ≤ A := by
    have hpi := Real.pi_gt_three
    dsimp only [A, q]
    norm_num [paper3HeadlineM] at *
    nlinarith
  have hca50 : (50 : ℝ) ≤ c * a := by
    dsimp only [c, a]
    rw [bgpParamsNW_cα_def]
    unfold paper3S2Mid
    have hS := paper3NW4_S_ge w
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    nlinarith [Real.pi_gt_three,
      mul_nonneg Real.pi_pos.le hj]
  have he50 : (2 : ℝ) ^ 50 ≤ Real.exp (c * a) :=
    paper3S13_exp_pow_ge hca50
  have hAg : 2 * g ≤ A * Real.exp (c * a) := by
    have hqpow : (2 : ℝ) ≤ (15 / 16 : ℝ) * q * (2 : ℝ) ^ 50 := by
      dsimp only [q]
      norm_num [paper3HeadlineM]
      nlinarith [Real.pi_gt_three]
    have hm := mul_le_mul_of_nonneg_left he50 hg.le
    dsimp only [A]
    nlinarith [mul_le_mul_of_nonneg_right hqpow hg.le]
  have hexp_lin : 1 + c * a ≤ Real.exp (c * a) := by
    simpa [add_comm] using Real.add_one_le_exp (c * a)
  have hAz : 2 * (c * z) ≤ A * Real.exp (c * a) := by
    have hza : 23 * z ≤ 24 * a := by
      dsimp only [z, a]
      unfold selectorMUZOffEnd paper3S2Mid
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      nlinarith [mul_nonneg Real.pi_pos.le hj]
    have hcza : 23 * (c * z) ≤ 24 * (c * a) := by
      nlinarith [mul_le_mul_of_nonneg_left hza hc.le]
    have hm := mul_le_mul_of_nonneg_left hexp_lin (by linarith : 0 ≤ A)
    nlinarith
  have hclock : g + c * z ≤ A * Real.exp (c * a) := by
    nlinarith
  have hfloor : A * Real.exp (c * a) =
      (15 / 16 : ℝ) * paper3S4bDeltaGFloorNW w j := by
    dsimp only [A, q, g, c, a]
    unfold paper3S4bDeltaGFloorNW
    ring
  have hinit_exp : paper3S4bInitialCoeffNW w j ≤ Real.exp (-g) := by
    unfold paper3S4bInitialCoeffNW
    apply Real.exp_le_exp.mpr
    rw [show -(15 / 16 : ℝ) * paper3S4bDeltaGFloorNW w j =
      -((15 / 16 : ℝ) * paper3S4bDeltaGFloorNW w j) by ring,
      ← hfloor]
    dsimp only [c, z]
    linarith
  have hmul := Real.mul_exp_neg_le_exp_neg_one g
  have hexpneg1 : Real.exp (-(1 : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by norm_num)
  have hinv : Real.exp (-g) ≤ 1 / g := by
    rw [le_div_iff₀ hg]
    nlinarith
  calc
    paper3S4bInitialCoeffNW w j ≤ Real.exp (-g) := hinit_exp
    _ ≤ 1 / g := hinv
    _ ≤ (2 : ℝ) ^ (2 * paper3HeadlineM + 3) / g := by
      exact div_le_div_of_nonneg_right
        (by norm_num [paper3HeadlineM]) hg.le
    _ = paper3S4bResetCoeffNW w := by rfl

private theorem paper3S4b_homogeneous_timelocal_NW
    (w j : ℕ) {gap t : ℝ}
    (hgap : (15 : ℝ) / 16 ≤ gap)
    (ht : t ∈ Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j)) :
    Real.exp (-gap *
        (((paper3HeadlineSolFamNW w) w).G t -
          ((paper3HeadlineSolFamNW w) w).G (paper3S2Mid j))) ≤
      paper3S4bInitialCoeffNW w j *
        Real.exp (-((bgpParamsNW w).cα * t)) := by
  let sol := (paper3HeadlineSolFamNW w) w
  let a := paper3S2Mid j
  let z := selectorMUZOffEnd j
  let c := (bgpParamsNW w).cα
  let cg : ℝ → ℝ := paper3NW4cg w
  have hgap0 : 0 < gap := by linarith
  have ha0 : 0 ≤ a := paper3S2_mid_nonneg j
  have haz : a ≤ z := paper3S2_mid_le_zOffEnd j
  have hz0 : 0 ≤ z := le_trans ha0 haz
  have hzt : z ≤ t := ht.1
  have hΔ := paper3S4b_G_increment_ge_NW w j
  have hΔ0 : 0 ≤ paper3S4bDeltaGFloorNW w j := by
    unfold paper3S4bDeltaGFloorNW
    exact mul_nonneg (by positivity)
      (mul_nonneg (by positivity)
        (mul_nonneg (paper3WarmGainQNW_nonneg_real w) (Real.exp_pos _).le))
  have hfirst : Real.exp (-gap * (sol.G z - sol.G a)) ≤
      Real.exp (-(15 / 16 : ℝ) * paper3S4bDeltaGFloorNW w j) := by
    apply Real.exp_le_exp.mpr
    have hG0 : 0 ≤ sol.G z - sol.G a := hΔ0.trans (by simpa [sol, z, a] using hΔ)
    have hΔ' : paper3S4bDeltaGFloorNW w j ≤ sol.G z - sol.G a := by
      simpa [sol, z, a] using hΔ
    nlinarith
  have hpost : Real.exp (-gap * (sol.G t - sol.G z)) ≤
      Real.exp (c * z) * Real.exp (-(c * t)) := by
    have h := exp_neg_G_sub_le_exp_mul_exp_neg_of_rate_le
      (a := z) (t := t) (gap := gap) (c := c)
      (G := sol.G) (cg := cg) hzt
      (fun s hs => by
        have hs0 : 0 ≤ s := le_trans hz0 hs.1
        simpa [sol, cg] using paper3NW4_G_hasDeriv w w hs0)
      (paper3NW4cg_cont w)
      (fun s hs => by
        have hswin : s ∈ Icc (paper3S2Mid j) (selectorMUNextWriteStart j) :=
          ⟨le_trans haz hs.1, le_trans hs.2 ht.2⟩
        simpa [c, cg] using paper3S4b_gap_mul_cg_ge_calpha_NW w j hgap hswin)
    simpa only [neg_mul] using h
  calc
    Real.exp (-gap * (sol.G t - sol.G a)) =
        Real.exp (-gap * (sol.G z - sol.G a)) *
          Real.exp (-gap * (sol.G t - sol.G z)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(15 / 16 : ℝ) * paper3S4bDeltaGFloorNW w j) *
          (Real.exp (c * z) * Real.exp (-(c * t))) :=
      mul_le_mul hfirst hpost (Real.exp_pos _).le (Real.exp_pos _).le
    _ = paper3S4bInitialCoeffNW w j * Real.exp (-(c * t)) := by
      unfold paper3S4bInitialCoeffNW
      rw [Real.exp_add]
      ring
    _ = paper3S4bInitialCoeffNW w j *
          Real.exp (-((bgpParamsNW w).cα * t)) := rfl

private noncomputable def paper3S4bLoserCoeffNW (w j : ℕ) : ℝ :=
  ((Fintype.card UniversalLocalView : ℝ) - 1) *
    ((Fintype.card UniversalLocalView : ℝ) * paper3S4bInitialCoeffNW w j +
      paper3S4bResetCoeffNW w)

private theorem paper3S4bLoserCoeffNW_nonneg (w j : ℕ) :
    0 ≤ paper3S4bLoserCoeffNW w j := by
  have hcard : (1 : ℝ) ≤ (Fintype.card UniversalLocalView : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr
      (⟨defaultLocalViewU⟩ : Nonempty UniversalLocalView)
  unfold paper3S4bLoserCoeffNW
  exact mul_nonneg (sub_nonneg.mpr hcard)
    (add_nonneg
      (mul_nonneg (by positivity) (paper3S4bInitialCoeffNW_nonneg w j))
      (paper3S4bResetCoeffNW_nonneg w))

private theorem paper3S4bLoserCoeffNW_le_card_sq_reset (w j : ℕ) :
    paper3S4bLoserCoeffNW w j ≤
      (Fintype.card UniversalLocalView : ℝ) ^ 2 * paper3S4bResetCoeffNW w := by
  let card : ℝ := (Fintype.card UniversalLocalView : ℝ)
  have hcard : (1 : ℝ) ≤ card := by
    dsimp [card]
    exact_mod_cast Fintype.card_pos_iff.mpr
      (⟨defaultLocalViewU⟩ : Nonempty UniversalLocalView)
  have hC0 := paper3S4bResetCoeffNW_nonneg w
  have hinit := paper3S4bInitialCoeffNW_le_reset w j
  unfold paper3S4bLoserCoeffNW
  dsimp [card] at hcard ⊢
  have hinside :
      (Fintype.card UniversalLocalView : ℝ) * paper3S4bInitialCoeffNW w j +
          paper3S4bResetCoeffNW w ≤
        ((Fintype.card UniversalLocalView : ℝ) + 1) *
          paper3S4bResetCoeffNW w := by
    nlinarith [mul_le_mul_of_nonneg_left hinit (by linarith :
      0 ≤ (Fintype.card UniversalLocalView : ℝ))]
  have hm1 : 0 ≤ (Fintype.card UniversalLocalView : ℝ) - 1 := by linarith
  calc
    ((Fintype.card UniversalLocalView : ℝ) - 1) *
        ((Fintype.card UniversalLocalView : ℝ) * paper3S4bInitialCoeffNW w j +
          paper3S4bResetCoeffNW w)
      ≤ ((Fintype.card UniversalLocalView : ℝ) - 1) *
          (((Fintype.card UniversalLocalView : ℝ) + 1) *
            paper3S4bResetCoeffNW w) :=
        mul_le_mul_of_nonneg_left hinside hm1
    _ ≤ (Fintype.card UniversalLocalView : ℝ) ^ 2 *
          paper3S4bResetCoeffNW w := by nlinarith

private theorem paper3S4b_loser_mass_timelocal_NW (w j : ℕ) :
    ∀ t ∈ Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j),
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => ((paper3HeadlineSolFamNW w) w).lam v t) ≤
      paper3S4bLoserCoeffNW w j *
        Real.exp (-((bgpParamsNW w).cα * t)) := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  intro t ht
  let sol := (paper3HeadlineSolFamNW w) w
  let a := paper3S2Mid j
  let gap := selectorReplicatorGapVal paper3HeadlineEta paper3HeadlineEta_pos
  let Kt := ∫ s in a..t,
    Real.exp (gap * (sol.G s - sol.G a)) *
      (((1 + Real.cos s) / 2) ^ paper3HeadlineM *
        ((paper3HeadlineKappa : ℚ) : ℝ))
  let X := Real.exp (-(gap * (sol.G t - sol.G a)))
  have hgap : (15 : ℝ) / 16 ≤ gap := by
    simpa [gap, paper3RecoveryGap] using paper3RecoveryGap_ge_fifteen_sixteen w (j + 1)
  have hraw := paper3S4b_loser_mass_exact_NW w j t
    ⟨le_trans (paper3S2_mid_le_zOffEnd j) ht.1, ht.2⟩
  rw [epsLamSettled_card_inv] at hraw
  have hX : X ≤ paper3S4bInitialCoeffNW w j *
      Real.exp (-((bgpParamsNW w).cα * t)) := by
    simpa [X, sol, a, gap] using paper3S4b_homogeneous_timelocal_NW w j hgap ht
  have hKX : Kt * X ≤ paper3S4bResetCoeffNW w *
      Real.exp (-((bgpParamsNW w).cα * t)) := by
    simpa [Kt, X, sol, a, gap, neg_mul] using
      paper3S4b_reset_duhamel_timelocal_NW w j hgap
        ⟨le_trans (paper3S2_mid_le_zOffEnd j) ht.1, ht.2⟩
  have hcard0 : 0 ≤ (Fintype.card UniversalLocalView : ℝ) := by positivity
  have hcardm1 : 0 ≤ (Fintype.card UniversalLocalView : ℝ) - 1 := by
    have hcard : (1 : ℝ) ≤ (Fintype.card UniversalLocalView : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr
        (⟨defaultLocalViewU⟩ : Nonempty UniversalLocalView)
    exact sub_nonneg.mpr hcard
  calc
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum (fun v => sol.lam v t)
        ≤ ((Fintype.card UniversalLocalView : ℝ) - 1) *
          (((Fintype.card UniversalLocalView : ℝ) + Kt) * X) := by
            simpa [sol, a, gap, Kt, X] using hraw
    _ = ((Fintype.card UniversalLocalView : ℝ) - 1) *
          ((Fintype.card UniversalLocalView : ℝ) * X + Kt * X) := by ring
    _ ≤ ((Fintype.card UniversalLocalView : ℝ) - 1) *
          ((Fintype.card UniversalLocalView : ℝ) *
              (paper3S4bInitialCoeffNW w j *
                Real.exp (-((bgpParamsNW w).cα * t))) +
            paper3S4bResetCoeffNW w *
              Real.exp (-((bgpParamsNW w).cα * t))) := by
      apply mul_le_mul_of_nonneg_left _ hcardm1
      exact add_le_add (mul_le_mul_of_nonneg_left hX hcard0) hKX
    _ = paper3S4bLoserCoeffNW w j *
          Real.exp (-((bgpParamsNW w).cα * t)) := by
      unfold paper3S4bLoserCoeffNW
      ring

private theorem paper3HoffBadPair_le_newLoser_NW (w j : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) :
    paper3HoffBadPairNW w j t ≤
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => ((paper3HeadlineSolFamNW w) w).lam v t) := by
  classical
  unfold paper3HoffBadPairNW
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro v hv
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ v, (Finset.mem_filter.mp hv).2.2⟩
  · intro v _hvnew _hvbad
    exact paper3NW_lam_nonneg_forward w w v t ht0

private theorem paper3Hoff_rightCross_sin_le_sqrt2 (j : ℕ) {t : ℝ}
    (ht : t ∈ Icc (selectorMUZOffEnd j) (selectorMUEarlyWriteSubStart (j + 1))) :
    Real.sin t ≤ Real.sqrt 2 / 2 := by
  set s := t - 2 * Real.pi * ((j : ℝ) + 1) with hs
  have hsin : Real.sin t = Real.sin s := by
    have ht_eq : t = s + (j + 1 : ℕ) * (2 * Real.pi) := by
      rw [hs]
      push_cast
      ring
    rw [ht_eq, Real.sin_add_nat_mul_two_pi]
  rw [hsin]
  have hs0 : 0 ≤ s := by
    rw [hs]
    rcases ht with ⟨htlo, htup⟩
    unfold selectorMUZOffEnd at htlo
    linarith
  have hs1 : s ≤ Real.pi / 4 := by
    rw [hs]
    rcases ht with ⟨htlo, htup⟩
    unfold selectorMUEarlyWriteSubStart at htup
    push_cast at htup
    linarith
  have hmem_s : s ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hmem_end : Real.pi / 4 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hmono := Real.strictMonoOn_sin.monotoneOn hmem_s hmem_end hs1
  rwa [Real.sin_pi_div_four] at hmono

private theorem paper3Hoff_rightCross_gate_le_exp200_NW
    (w j : ℕ) {τ : ℝ}
    (hτ : τ ∈ Icc (selectorMUZOffEnd j) (selectorMUEarlyWriteSubStart (j + 1))) :
    selectorMUHoffGateCoeffP (p := bgpParamsNW w)
        (paper3HeadlineSolFamNW w) w τ ≤
      Real.exp (200 * (bgpScaleW w : ℝ) * τ) := by
  have hτ0 : 0 ≤ τ := by
    have hz0 : 0 ≤ selectorMUZOffEnd j := by unfold selectorMUZOffEnd; positivity
    exact le_trans hz0 hτ.1
  have hsin := paper3Hoff_rightCross_sin_le_sqrt2 j hτ
  have hsqrt0 := Real.sqrt_nonneg 2
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt : Real.sqrt 2 / 2 ≤ (4 / 5 : ℝ) := by nlinarith
  have hr : (1 / 10 : ℝ) ≤ ((1 - Real.sin τ) / 2) ^ 1 := by
    rw [pow_one]
    linarith
  have hα := paper3HeadlineSolFamNW_alpha w w hτ0
  have hμ := paper3HeadlineSolFamNW_mu w w hτ0
  unfold selectorMUHoffGateCoeffP
  rw [hα, hμ, bgpParamsNW_A_eq, one_mul, bgpParamsNW_L_eq]
  unfold bGateZ rPulse
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [bgpParamsNW_cα_def, bgpParamsNW_cμ_def]
  have hS0 := (bgpScaleWR_pos w).le
  nlinarith [mul_le_mul_of_nonneg_left hr
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1000) hS0) hτ0)]

private theorem paper3Hoff_right_bad_pointwise_NW
    (w j : ℕ) {τ : ℝ}
    (hτ : τ ∈ Icc (selectorMUZOffEnd j)
      (selectorMUEarlyWriteSubStart (j + 1))) :
    selectorMUHoffGateCoeffP (p := bgpParamsNW w)
        (paper3HeadlineSolFamNW w) w τ * paper3HoffBadPairNW w j τ ≤
      paper3S4bLoserCoeffNW w j *
        Real.exp (-(100 * (bgpScaleW w : ℝ) * τ)) := by
  let S : ℝ := (bgpScaleW w : ℝ)
  let k : ℝ := selectorMUHoffGateCoeffP (p := bgpParamsNW w)
    (paper3HeadlineSolFamNW w) w τ
  let B : ℝ := paper3HoffBadPairNW w j τ
  let L : ℝ := paper3S4bLoserCoeffNW w j
  have hτ0 : 0 ≤ τ := by
    have ha0 : 0 ≤ selectorMUZOffEnd j := by unfold selectorMUZOffEnd; positivity
    exact le_trans ha0 hτ.1
  have hk0 : 0 ≤ k := by
    dsimp [k, selectorMUHoffGateCoeffP]
    exact paper3NW4_zKernel_nonneg w w hτ0
  have hB0 : 0 ≤ B := by
    dsimp [B, paper3HoffBadPairNW]
    exact Finset.sum_nonneg fun v _ => paper3NW_lam_nonneg_forward w w v τ hτ0
  have hk : k ≤ Real.exp (200 * S * τ) := by
    exact paper3Hoff_rightCross_gate_le_exp200_NW w j hτ
  have hB : B ≤ L * Real.exp (-((bgpParamsNW w).cα * τ)) := by
    exact (paper3HoffBadPair_le_newLoser_NW w j hτ0).trans
      (paper3S4b_loser_mass_timelocal_NW w j τ ⟨hτ.1, by
        calc
          τ ≤ selectorMUEarlyWriteSubStart (j + 1) := hτ.2
          _ ≤ selectorMUNextWriteStart j := by
            unfold selectorMUEarlyWriteSubStart selectorMUNextWriteStart
              selectorMUWriteHoldTime
            push_cast
            linarith [Real.pi_pos]⟩)
  have hprod : k * B ≤ Real.exp (200 * S * τ) *
      (L * Real.exp (-((bgpParamsNW w).cα * τ))) :=
    mul_le_mul hk hB hB0 (Real.exp_pos _).le
  calc
    selectorMUHoffGateCoeffP (p := bgpParamsNW w)
        (paper3HeadlineSolFamNW w) w τ * paper3HoffBadPairNW w j τ
        = k * B := rfl
    _ ≤ Real.exp (200 * S * τ) *
        (L * Real.exp (-((bgpParamsNW w).cα * τ))) := hprod
    _ = L * Real.exp (-(100 * S * τ)) := by
      have hcα : (bgpParamsNW w).cα = 300 * S := by
        dsimp only [S]
        exact bgpParamsNW_cα_def w
      rw [hcα]
      calc
        Real.exp (200 * S * τ) * (L * Real.exp (-(300 * S * τ))) =
            L * (Real.exp (200 * S * τ) * Real.exp (-(300 * S * τ))) := by ring
        _ = L * Real.exp (200 * S * τ + -(300 * S * τ)) := by
          rw [Real.exp_add]
        _ = L * Real.exp (-(100 * S * τ)) := by congr 2 <;> ring

private theorem paper3S4bLoserCoeffNW_le_exp_currency (w j : ℕ) :
    paper3S4bLoserCoeffNW w j ≤
      Real.exp (100 * (bgpScaleW w : ℝ) + 1000) := by
  let S : ℝ := (bgpScaleW w : ℝ)
  let card : ℝ := (Fintype.card UniversalLocalView : ℝ)
  have hcard : (1 : ℝ) ≤ card := by
    dsimp only [card]
    exact_mod_cast Fintype.card_pos_iff.mpr
      (⟨defaultLocalViewU⟩ : Nonempty UniversalLocalView)
  have hI := paper3S4bInitialCoeffNW_le_one w j
  have hR := paper3S4bResetCoeffNW_le_one w
  have hL : paper3S4bLoserCoeffNW w j ≤ 2 * card ^ 2 := by
    unfold paper3S4bLoserCoeffNW
    have hin : card * paper3S4bInitialCoeffNW w j + paper3S4bResetCoeffNW w ≤
        card + 1 := by
      nlinarith [mul_le_mul_of_nonneg_left hI (by linarith : 0 ≤ card)]
    have hm1 : 0 ≤ card - 1 := by linarith
    calc
      (card - 1) * (card * paper3S4bInitialCoeffNW w j + paper3S4bResetCoeffNW w)
          ≤ (card - 1) * (card + 1) := mul_le_mul_of_nonneg_left hin hm1
      _ ≤ 2 * card ^ 2 := by nlinarith [sq_nonneg card]
  have hcard' : card ≤ Real.exp (6 * S) := by
    dsimp only [card, S]
    exact paper3NW4_card_le_exp w
  have hcard2 : card ^ 2 ≤ Real.exp (12 * S) := by
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ card) hcard' 2
    exact hp.trans_eq (by rw [← Real.exp_nat_mul]; ring)
  have hS0 : 0 ≤ S := by dsimp only [S]; exact (bgpScaleWR_pos w).le
  calc
    paper3S4bLoserCoeffNW w j ≤ 2 * card ^ 2 := hL
    _ ≤ 2 * Real.exp (12 * S) := mul_le_mul_of_nonneg_left hcard2 (by norm_num)
    _ ≤ Real.exp (100 * S + 1000) := by
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      calc
        2 * Real.exp (12 * S) ≤ Real.exp 1 * Real.exp (12 * S) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
        _ = Real.exp (1 + 12 * S) := by rw [← Real.exp_add]
        _ ≤ Real.exp (100 * S + 1000) := Real.exp_le_exp.mpr (by nlinarith)

private theorem paper3Hoff_right_badIntegral_le_budget_div_32_NW
    (w j : ℕ) :
    (∫ τ in (selectorMUZOffEnd j)..(selectorMUEarlyWriteSubStart (j + 1)),
      selectorMUHoffGateCoeffP (p := bgpParamsNW w)
        (paper3HeadlineSolFamNW w) w τ * paper3HoffBadPairNW w j τ) ≤
      selectorMUHoffEdgeBudget3992 j / 32 := by
  let a : ℝ := selectorMUZOffEnd j
  let b : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let S : ℝ := (bgpScaleW w : ℝ)
  let K : ℝ := paper3S4bLoserCoeffNW w j
  let F : ℝ → ℝ := fun τ => selectorMUHoffGateCoeffP
    (p := bgpParamsNW w) (paper3HeadlineSolFamNW w) w τ *
      paper3HoffBadPairNW w j τ
  have hab : a ≤ b := by
    dsimp only [a, b]
    exact selectorMUZOffEnd_le_earlyWriteSubStart_succ j
  have hr : 0 < 100 * S := by dsimp [S]; nlinarith [bgpScaleWR_pos w]
  have hK0 : 0 ≤ K := paper3S4bLoserCoeffNW_nonneg w j
  have hFcont : Continuous F := by
    apply Continuous.mul
    · simpa [F] using selectorMUHoffGateCoeffP_continuous
        (p := bgpParamsNW w) (sol := paper3HeadlineSolFamNW w) w
    · dsimp [F, paper3HoffBadPairNW]
      exact continuous_finsetSum _ (fun v _ => ((paper3HeadlineSolFamNW w) w).cont_lam v)
  have hEcont : Continuous fun τ : ℝ => K * Real.exp (-(100 * S * τ)) := by fun_prop
  have hmono : (∫ τ in a..b, F τ) ≤
      ∫ τ in a..b, K * Real.exp (-(100 * S * τ)) := by
    apply intervalIntegral.integral_mono_on hab
      (hFcont.intervalIntegrable a b) (hEcont.intervalIntegrable a b)
    intro τ hτ
    change selectorMUHoffGateCoeffP (p := bgpParamsNW w)
      (paper3HeadlineSolFamNW w) w τ * paper3HoffBadPairNW w j τ ≤
        paper3S4bLoserCoeffNW w j * Real.exp (-(100 * (bgpScaleW w : ℝ) * τ))
    exact paper3Hoff_right_bad_pointwise_NW w j hτ
  have htail := integral_const_mul_exp_neg_le_left
    (r := 100 * S) (C := K) (a := a) (b := b) hr hK0 hab
  have hK : K ≤ Real.exp (100 * S + 1000) := by
    dsimp only [K, S]
    exact paper3S4bLoserCoeffNW_le_exp_currency w j
  let T : ℝ := 2 * Real.pi * (j : ℝ) + Real.pi
  have hS4 : (4 : ℝ) ≤ S := by dsimp only [S]; exact bgpScaleWR_ge_four w
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hmargin : 100 * S + 1000 + 200 * T ≤ 100 * S * a := by
    dsimp only [T, a]
    unfold selectorMUZOffEnd
    have hpi := Real.pi_gt_three
    have hS0 : 0 ≤ S := by linarith
    nlinarith [mul_nonneg hj Real.pi_pos.le,
      mul_nonneg (mul_nonneg hS0 hj) Real.pi_pos.le,
      mul_nonneg hS0 Real.pi_pos.le]
  have hKexp : K * Real.exp (-(100 * S * a)) ≤ Real.exp (-(200 * T)) := by
    calc
      K * Real.exp (-(100 * S * a)) ≤
          Real.exp (100 * S + 1000) * Real.exp (-(100 * S * a)) :=
        mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le
      _ = Real.exp (100 * S + 1000 - 100 * S * a) := by
        rw [← Real.exp_add]
        ring_nf
      _ ≤ Real.exp (-(200 * T)) := Real.exp_le_exp.mpr (by linarith)
  have hcoef : 1 / (100 * S) ≤ (7 : ℝ) / 32 := by
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num : (0 : ℝ) < 32)]
    nlinarith
  have hleft : (K / (100 * S)) * Real.exp (-(100 * S * a)) ≤
      (7 / 32) * Real.exp (-(200 * T)) := by
    calc
      (K / (100 * S)) * Real.exp (-(100 * S * a)) =
          (1 / (100 * S)) * (K * Real.exp (-(100 * S * a))) := by ring
      _ ≤ (1 / (100 * S)) * Real.exp (-(200 * T)) :=
        mul_le_mul_of_nonneg_left hKexp (by positivity)
      _ ≤ (7 / 32) * Real.exp (-(200 * T)) :=
        mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
  have hbudgetCoeff : (7 : ℝ) ≤ selectorMUHoffEdgeBudgetCoeff := by
    unfold selectorMUHoffEdgeBudgetCoeff
    linarith [selectorReplicatorHoldEnvelopeCoeff_ge_eight]
  have hcurrency : (K / (100 * S)) * Real.exp (-(100 * S * a)) ≤
      selectorMUHoffEdgeBudget3992 j / 32 := by
    unfold selectorMUHoffEdgeBudget3992 selectorMUHoffEdgeBudget
    rw [show bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L -
      bgpParams38.cα = 200 by norm_num [bgpParams38]]
    change (K / (100 * S)) * Real.exp (-(100 * S * a)) ≤
      (selectorMUHoffEdgeBudgetCoeff * Real.exp (-(200 * T))) / 32
    calc
      (K / (100 * S)) * Real.exp (-(100 * S * a)) ≤
          (7 / 32) * Real.exp (-(200 * T)) := hleft
      _ ≤ (selectorMUHoffEdgeBudgetCoeff / 32) * Real.exp (-(200 * T)) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hbudgetCoeff (by norm_num))
          (Real.exp_pos _).le
      _ = (selectorMUHoffEdgeBudgetCoeff * Real.exp (-(200 * T))) / 32 := by ring
  exact hmono.trans (htail.trans hcurrency)

/-! ## Right active-suffix forcing mass -/

private noncomputable def paper3S4bForcingCoeffNW
    (w j : ℕ) (_v : UniversalLocalView) : ℝ :=
  ((paper3WarmGainQNW w : ℚ) : ℝ) * (paper3S4bLoserCoeffNW w j) ^ 2

private theorem paper3S4bForcingCoeffNW_nonneg
    (w j : ℕ) (v : UniversalLocalView) :
    0 ≤ paper3S4bForcingCoeffNW w j v := by
  unfold paper3S4bForcingCoeffNW
  exact mul_nonneg (paper3WarmGainQNW_nonneg_real w) (sq_nonneg _)

private theorem paper3S4b_forcing_pointwise_exp_NW
    (w j : ℕ) (v : UniversalLocalView)
    (hv : v ≠ localViewU (solMUReplStaticCfg w (j + 1)))
    (τ : ℝ)
    (hτ : τ ∈ Icc (selectorMUEarlyWriteSubStart (j + 1))
      (selectorMUNextWriteStart j)) :
    |selectorMU_activeCgP (p := bgpParamsNW w) paper3HeadlineM
          (paper3WarmGainQNW w) τ *
        (∑ x : UniversalLocalView,
          ((paper3HeadlineSolFamNW w) w).lam x τ *
            (universalPval paper3HeadlineEta paper3HeadlineEta_pos
                (localViewU (solMUReplStaticCfg w (j + 1)))
                (((paper3HeadlineSolFamNW w) w).u τ) -
              universalPval paper3HeadlineEta paper3HeadlineEta_pos x
                (((paper3HeadlineSolFamNW w) w).u τ))) *
        ((paper3HeadlineSolFamNW w) w).lam v τ| ≤
      paper3S4bForcingCoeffNW w j v *
        Real.exp (-((bgpParamsNW w).cα * τ)) := by
  classical
  let sol := (paper3HeadlineSolFamNW w) w
  let cview : UniversalLocalView := localViewU (solMUReplStaticCfg w (j + 1))
  let lam : UniversalLocalView → ℝ := fun x => sol.lam x τ
  let gapf : UniversalLocalView → ℝ := fun x =>
    universalPval paper3HeadlineEta paper3HeadlineEta_pos cview (sol.u τ) -
      universalPval paper3HeadlineEta paper3HeadlineEta_pos x (sol.u τ)
  let cg : ℝ := selectorMU_activeCgP (p := bgpParamsNW w)
    paper3HeadlineM (paper3WarmGainQNW w) τ
  let Sbad : Finset UniversalLocalView :=
    Finset.univ.filter (fun x : UniversalLocalView => x ≠ cview)
  let Bmass : ℝ := Sbad.sum lam
  have hτfull : τ ∈ Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j) :=
    ⟨le_trans (selectorMUZOffEnd_le_earlyWriteSubStart_succ j) hτ.1, hτ.2⟩
  have hτ0 : 0 ≤ τ := by
    exact le_trans (by unfold selectorMUZOffEnd; positivity) hτfull.1
  have hlam0 : ∀ x : UniversalLocalView, 0 ≤ lam x := fun x =>
    paper3NW_lam_nonneg_forward w w x τ hτ0
  have hcg0 : 0 ≤ cg := by
    dsimp [cg, selectorMU_activeCgP]
    exact mul_nonneg
      (pow_nonneg (by nlinarith [Real.neg_one_le_sin τ]) _)
      (mul_nonneg (paper3WarmGainQNW_nonneg_real w) (Real.exp_pos _).le)
  have hgap0 : ∀ x : UniversalLocalView, 0 ≤ gapf x := by
    intro x
    by_cases hx : x = cview
    · subst x; simp [gapf]
    · have hfloor := paper3S4b_gapFloor_NW w j x
        (by simpa [cview] using hx) τ hτfull
      dsimp [gapf, cview, sol]
      linarith
  have hgap_self : gapf cview = 0 := by simp [gapf]
  have hgap_upper : ∀ x : UniversalLocalView, x ≠ cview → gapf x ≤ 1 := by
    intro x hx
    have hut := paper3S4b_right_edge_tube_persist_NW w j τ hτfull
    exact paper3Headline_universalPval_sub_le_one_of_utube
      (fun i => hut i) cview x
  have hsum := paper3_filtered_forcing_pointwise_le_delta_loser_square
    cview lam gapf cg (1 : ℝ) hlam0 hcg0 hgap0 hgap_self hgap_upper
  have hvS : v ∈ Sbad := Finset.mem_filter.mpr
    ⟨Finset.mem_univ v, by simpa [cview] using hv⟩
  have hsingle : |cg * (∑ x : UniversalLocalView, lam x * gapf x) * lam v| ≤
      Sbad.sum (fun x => |cg * (∑ y : UniversalLocalView,
        lam y * gapf y) * lam x|) :=
    Finset.single_le_sum
      (fun x _hx => abs_nonneg
        (cg * (∑ y : UniversalLocalView, lam y * gapf y) * lam x)) hvS
  have hforcing :
      |cg * (∑ x : UniversalLocalView, lam x * gapf x) * lam v| ≤
        cg * Bmass ^ 2 := by
    exact hsingle.trans (by simpa [Sbad, Bmass] using hsum)
  have hB := paper3S4b_loser_mass_timelocal_NW w j τ hτfull
  have hB' : Bmass ≤ paper3S4bLoserCoeffNW w j *
      Real.exp (-((bgpParamsNW w).cα * τ)) := by
    simpa [Bmass, Sbad, lam, cview, sol] using hB
  have hB0 : 0 ≤ Bmass := by
    dsimp [Bmass, Sbad]
    exact Finset.sum_nonneg (fun x _ => hlam0 x)
  have hBsq : Bmass ^ 2 ≤
      (paper3S4bLoserCoeffNW w j *
        Real.exp (-((bgpParamsNW w).cα * τ))) ^ 2 :=
    pow_le_pow_left₀ hB0 hB' 2
  have hcg_le : cg ≤ ((paper3WarmGainQNW w : ℚ) : ℝ) *
      Real.exp ((bgpParamsNW w).cα * τ) := by
    have habs := selectorMU_activeCg_abs_le_exp_gainP
      (p := bgpParamsNW w) paper3HeadlineM (paper3WarmGainQNW w) τ
    rw [abs_of_nonneg hcg0,
      abs_of_nonneg (paper3WarmGainQNW_nonneg_real w)] at habs
    exact habs
  have hprod : cg * Bmass ^ 2 ≤
      (((paper3WarmGainQNW w : ℚ) : ℝ) *
        Real.exp ((bgpParamsNW w).cα * τ)) *
      (paper3S4bLoserCoeffNW w j *
        Real.exp (-((bgpParamsNW w).cα * τ))) ^ 2 :=
    mul_le_mul hcg_le hBsq (sq_nonneg _)
      (mul_nonneg (paper3WarmGainQNW_nonneg_real w) (Real.exp_pos _).le)
  have hexpc : Real.exp ((bgpParamsNW w).cα * τ) *
      Real.exp (-((bgpParamsNW w).cα * τ)) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    |selectorMU_activeCgP (p := bgpParamsNW w) paper3HeadlineM
          (paper3WarmGainQNW w) τ *
        (∑ x : UniversalLocalView, sol.lam x τ *
          (universalPval paper3HeadlineEta paper3HeadlineEta_pos cview (sol.u τ) -
            universalPval paper3HeadlineEta paper3HeadlineEta_pos x (sol.u τ))) *
        sol.lam v τ|
        = |cg * (∑ x : UniversalLocalView, lam x * gapf x) * lam v| := by rfl
    _ ≤ cg * Bmass ^ 2 := hforcing
    _ ≤ (((paper3WarmGainQNW w : ℚ) : ℝ) *
          Real.exp ((bgpParamsNW w).cα * τ)) *
        (paper3S4bLoserCoeffNW w j *
          Real.exp (-((bgpParamsNW w).cα * τ))) ^ 2 := hprod
    _ = paper3S4bForcingCoeffNW w j v *
          Real.exp (-((bgpParamsNW w).cα * τ)) := by
      unfold paper3S4bForcingCoeffNW
      calc
        (((paper3WarmGainQNW w : ℚ) : ℝ) *
              Real.exp ((bgpParamsNW w).cα * τ)) *
            (paper3S4bLoserCoeffNW w j *
              Real.exp (-((bgpParamsNW w).cα * τ))) ^ 2 =
          (((paper3WarmGainQNW w : ℚ) : ℝ) *
              (paper3S4bLoserCoeffNW w j) ^ 2) *
            (Real.exp ((bgpParamsNW w).cα * τ) *
              Real.exp (-((bgpParamsNW w).cα * τ))) *
            Real.exp (-((bgpParamsNW w).cα * τ)) := by ring
        _ = _ := by rw [hexpc]; ring

private theorem paper3S4b_forcing_coeff_sum_le (w j : ℕ) :
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
        (fun v => paper3S4bForcingCoeffNW w j v) ≤
      (2 : ℝ) ^ 86 * (Fintype.card UniversalLocalView : ℝ) ^ 4 := by
  classical
  let card : ℝ := (Fintype.card UniversalLocalView : ℝ)
  let g : ℝ := ((paper3WarmGainQNW w : ℚ) : ℝ)
  let bad : Finset UniversalLocalView := Finset.univ.filter
    (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))
  have hcard0 : 0 < card := by
    dsimp [card]
    exact_mod_cast Fintype.card_pos_iff.mpr
      (⟨defaultLocalViewU⟩ : Nonempty UniversalLocalView)
  have hg : 0 < g := by dsimp [g]; exact paper3WarmGainQNW_pos_real w
  have hcardg : card ≤ g := by
    simpa [card, g] using paper3S4_card_le_gain_NW w
  have hL := paper3S4bLoserCoeffNW_le_card_sq_reset w j
  have hL0 := paper3S4bLoserCoeffNW_nonneg w j
  have hLsq : (paper3S4bLoserCoeffNW w j) ^ 2 ≤
      (card ^ 2 * paper3S4bResetCoeffNW w) ^ 2 :=
    pow_le_pow_left₀ hL0 (by simpa [card] using hL) 2
  have hK : ∀ v : UniversalLocalView,
      paper3S4bForcingCoeffNW w j v ≤ (2 : ℝ) ^ 86 * card ^ 3 := by
    intro v
    have hmul := mul_le_mul_of_nonneg_left hLsq hg.le
    have hcancel :
        g * (card ^ 2 * paper3S4bResetCoeffNW w) ^ 2 =
          (2 : ℝ) ^ 86 * card ^ 4 / g := by
      rw [paper3S4bResetCoeffNW]
      norm_num [paper3HeadlineM]
      dsimp only [g]
      field_simp [paper3WarmGainQNW_pos_real w |>.ne']
      ring
    have hdiv : (2 : ℝ) ^ 86 * card ^ 4 / g ≤
        (2 : ℝ) ^ 86 * card ^ 3 := by
      rw [div_le_iff₀ hg]
      have hpow0 : 0 ≤ (2 : ℝ) ^ 86 * card ^ 3 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hcardg hpow0]
    unfold paper3S4bForcingCoeffNW
    exact hmul.trans (hcancel.le.trans hdiv)
  calc
    bad.sum (fun v => paper3S4bForcingCoeffNW w j v)
        ≤ bad.sum (fun _v => (2 : ℝ) ^ 86 * card ^ 3) :=
      Finset.sum_le_sum (fun v _hv => hK v)
    _ = (bad.card : ℝ) * ((2 : ℝ) ^ 86 * card ^ 3) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ card * ((2 : ℝ) ^ 86 * card ^ 3) := by
      apply mul_le_mul_of_nonneg_right
      · change (bad.card : ℝ) ≤ (Fintype.card UniversalLocalView : ℝ)
        exact_mod_cast Finset.card_le_univ bad
      · positivity
    _ = (2 : ℝ) ^ 86 * card ^ 4 := by ring

private theorem paper3S4b_forcing_exp_budget_NW (w j : ℕ) :
    let bad := Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))
    let r : ℝ := 300 * (bgpScaleW w : ℝ)
    let a : ℝ := selectorMUEarlyWriteSubStart (j + 1)
    2 * (((bad.sum (fun v => paper3S4bForcingCoeffNW w j v)) / r) *
      Real.exp (-(r * a))) ≤ selectorMUHoffEdgeBudget3992 j / 32 := by
  classical
  dsimp
  let S : ℝ := (bgpScaleW w : ℝ)
  let card : ℝ := (Fintype.card UniversalLocalView : ℝ)
  let r : ℝ := 300 * S
  let a : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let Ksum : ℝ :=
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
      (fun v => paper3S4bForcingCoeffNW w j v)
  have hS : (5184 : ℝ) ≤ S := by dsimp [S]; exact paper3NW4_S_ge w
  have hS0 : 0 < S := by dsimp [S]; exact bgpScaleWR_pos w
  have hr : 1 ≤ r := by dsimp [r]; nlinarith
  have hK0 : 0 ≤ Ksum := by
    dsimp [Ksum]
    exact Finset.sum_nonneg (fun v _ => paper3S4bForcingCoeffNW_nonneg w j v)
  have hK : Ksum ≤ (2 : ℝ) ^ 86 * card ^ 4 := by
    dsimp only [Ksum, card]
    exact paper3S4b_forcing_coeff_sum_le w j
  have hdiv : Ksum / r ≤ (2 : ℝ) ^ 86 * card ^ 4 := by
    calc
      Ksum / r ≤ Ksum := by
        rw [div_le_iff₀ (by linarith : 0 < r)]
        nlinarith
      _ ≤ _ := hK
  have hcard := paper3NW4_card_le_exp w
  have hcard4 : card ^ 4 ≤ Real.exp (24 * S) := by
    have hcard' : card ≤ Real.exp (6 * S) := by
      dsimp only [card, S]
      exact hcard
    have hp := pow_le_pow_left₀
      (by dsimp only [card]; exact Nat.cast_nonneg _) hcard' 4
    calc card ^ 4 ≤ Real.exp (6 * S) ^ 4 := hp
      _ = Real.exp (24 * S) := by rw [← Real.exp_nat_mul]; ring
  have htwo : (2 : ℝ) ^ 87 ≤ Real.exp (87 * S) := by
    have h2e : (2 : ℝ) ≤ Real.exp S := by
      have := Real.add_one_le_exp S
      linarith
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2e 87
    calc (2 : ℝ) ^ 87 ≤ Real.exp S ^ 87 := hp
      _ = Real.exp (87 * S) := by rw [← Real.exp_nat_mul]; ring
  have hpoly : (2 : ℝ) ^ 87 * card ^ 4 ≤ Real.exp (111 * S) := by
    calc
      (2 : ℝ) ^ 87 * card ^ 4 ≤
          Real.exp (87 * S) * Real.exp (24 * S) :=
        mul_le_mul htwo hcard4
          (pow_nonneg (Nat.cast_nonneg _) 4) (Real.exp_pos _).le
      _ = Real.exp (111 * S) := by rw [← Real.exp_add]; ring
  have hscalar : 2 * (Ksum / r) * Real.exp (-(r * a)) ≤
      Real.exp (111 * S - r * a) := by
    have hleft : 2 * (Ksum / r) ≤ (2 : ℝ) ^ 87 * card ^ 4 := by
      nlinarith [hdiv]
    calc
      2 * (Ksum / r) * Real.exp (-(r * a)) ≤
          ((2 : ℝ) ^ 87 * card ^ 4) * Real.exp (-(r * a)) :=
        mul_le_mul_of_nonneg_right hleft (Real.exp_pos _).le
      _ ≤ Real.exp (111 * S) * Real.exp (-(r * a)) :=
        mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
      _ = Real.exp (111 * S - r * a) := by rw [← Real.exp_add]; ring
  have hexponent : 111 * S - r * a ≤
      -(200 * Real.pi * (2 * (j : ℝ) + 1)) := by
    dsimp only [r, a]
    unfold selectorMUEarlyWriteSubStart
    push_cast
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hpij : 0 ≤ Real.pi * (j : ℝ) := mul_nonneg Real.pi_pos.le hj
    have hjpart : 400 * Real.pi * (j : ℝ) ≤
        600 * S * Real.pi * (j : ℝ) := by
      have hc : (400 : ℝ) ≤ 600 * S := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hc hpij]
    have hconst : 111 * S + 200 * Real.pi ≤ 675 * S * Real.pi := by
      have hpiS : 3 * S ≤ Real.pi * S :=
        mul_le_mul_of_nonneg_right Real.pi_gt_three.le hS0.le
      have hpi4 := Real.pi_lt_four.le
      nlinarith
    nlinarith
  have hsmall := hscalar.trans
    (Real.exp_le_exp.mpr hexponent)
  refine paper3S13_three_rate_le_budget_div_32 j ?_
  change 2 * (Ksum / r * Real.exp (-(r * a))) ≤ _
  have hpos := Real.exp_pos (-(200 * Real.pi * (2 * (j : ℝ) + 1)))
  nlinarith

private theorem paper3S4b_forcingMass_le_NW (w j : ℕ) :
    2 * (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
      (fun v =>
        ∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
            (selectorMUNextWriteStart j),
          |selectorMU_activeCgP (p := bgpParamsNW w) paper3HeadlineM
              (paper3WarmGainQNW w) τ *
            (∑ x : UniversalLocalView,
              ((paper3HeadlineSolFamNW w) w).lam x τ *
                (universalPval paper3HeadlineEta paper3HeadlineEta_pos
                    (localViewU (solMUReplStaticCfg w (j + 1)))
                    (((paper3HeadlineSolFamNW w) w).u τ) -
                  universalPval paper3HeadlineEta paper3HeadlineEta_pos x
                    (((paper3HeadlineSolFamNW w) w).u τ))) *
            ((paper3HeadlineSolFamNW w) w).lam v τ|) ≤
      selectorMUHoffEdgeBudget3992 j / 32 := by
  classical
  let bad : Finset UniversalLocalView := Finset.univ.filter
    (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))
  let a : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let b : ℝ := selectorMUNextWriteStart j
  let r : ℝ := 300 * (bgpScaleW w : ℝ)
  let F : UniversalLocalView → ℝ → ℝ := fun v τ =>
    selectorMU_activeCgP (p := bgpParamsNW w) paper3HeadlineM
        (paper3WarmGainQNW w) τ *
      (∑ x : UniversalLocalView,
        ((paper3HeadlineSolFamNW w) w).lam x τ *
          (universalPval paper3HeadlineEta paper3HeadlineEta_pos
              (localViewU (solMUReplStaticCfg w (j + 1)))
              (((paper3HeadlineSolFamNW w) w).u τ) -
            universalPval paper3HeadlineEta paper3HeadlineEta_pos x
              (((paper3HeadlineSolFamNW w) w).u τ))) *
      ((paper3HeadlineSolFamNW w) w).lam v τ
  let K : UniversalLocalView → ℝ := fun v => paper3S4bForcingCoeffNW w j v
  have hab : a ≤ b := by
    dsimp [a, b]
    unfold selectorMUEarlyWriteSubStart selectorMUNextWriteStart
      selectorMUWriteHoldTime
    push_cast
    linarith [Real.pi_pos]
  have hr : 0 < r := by dsimp [r]; nlinarith [bgpScaleWR_pos w]
  have hK0 : ∀ v ∈ bad, 0 ≤ K v := by
    intro v _; exact paper3S4bForcingCoeffNW_nonneg w j v
  have hF_cont : ∀ v ∈ bad, ContinuousOn (F v) (Icc a b) := by
    intro v _
    have hcg := selectorMU_activeCg_continuousP
      (p := bgpParamsNW w) paper3HeadlineM (paper3WarmGainQNW w)
    have hmean : Continuous fun τ : ℝ =>
        ∑ x : UniversalLocalView,
          ((paper3HeadlineSolFamNW w) w).lam x τ *
            (universalPval paper3HeadlineEta paper3HeadlineEta_pos
                (localViewU (solMUReplStaticCfg w (j + 1)))
                (((paper3HeadlineSolFamNW w) w).u τ) -
              universalPval paper3HeadlineEta paper3HeadlineEta_pos x
                (((paper3HeadlineSolFamNW w) w).u τ)) := by
      refine continuous_finsetSum Finset.univ ?_
      intro x _
      exact (((paper3HeadlineSolFamNW w) w).cont_lam x).mul
        ((universalPval_continuous_of_cont_u paper3HeadlineEta
            paper3HeadlineEta_pos _
            (fun i => ((paper3HeadlineSolFamNW w) w).cont_u i)).sub
          (universalPval_continuous_of_cont_u paper3HeadlineEta
            paper3HeadlineEta_pos x
            (fun i => ((paper3HeadlineSolFamNW w) w).cont_u i)))
    simpa [F] using
      ((hcg.mul hmean).mul (((paper3HeadlineSolFamNW w) w).cont_lam v)).continuousOn
  have hpoint : ∀ v ∈ bad, ∀ τ ∈ Icc a b,
      |F v τ| ≤ K v * Real.exp (-(r * τ)) := by
    intro v hv τ hτ
    have hvNew := (Finset.mem_filter.mp hv).2.2
    have hp := paper3S4b_forcing_pointwise_exp_NW w j v hvNew τ
      (by simpa [a, b] using hτ)
    have hc : (bgpParamsNW w).cα = r := by
      dsimp [r]
      exact bgpParamsNW_cα_def w
    simpa [F, K, hc] using hp
  have hbudget : 2 * (((bad.sum K) / r) * Real.exp (-(r * a))) ≤
      selectorMUHoffEdgeBudget3992 j / 32 := by
    simpa only [bad, K, r, a] using paper3S4b_forcing_exp_budget_NW w j
  have hsum := two_mul_finset_sum_integral_abs_le_exp_decay_budget
    bad (F := F) (C := K) (r := r) (a := a) (b := b)
    hr hab hK0 hF_cont hpoint hbudget
  simpa [bad, F, K, r, a, b] using hsum

/-! ## P-generic active-QSS slaving, specialized to the NW right suffix -/

private theorem paper3NW_lam_hasDerivAt_gapTracking
    (w : ℕ) {τ : ℝ} (hτ0 : 0 ≤ τ)
    (c v : UniversalLocalView) :
    HasDerivAt (((paper3HeadlineSolFamNW w) w).lam v)
      (selectorMU_activeCr paper3HeadlineM paper3HeadlineKappa τ *
          (Fintype.card UniversalLocalView : ℝ)⁻¹ -
        selectorMU_activeSinkP paper3HeadlineEta paper3HeadlineEta_pos
            (paper3HeadlineSolFamNW w) w c v τ *
          ((paper3HeadlineSolFamNW w) w).lam v τ +
        selectorMU_activeCgP (p := bgpParamsNW w) paper3HeadlineM
            (paper3WarmGainQNW w) τ *
          (∑ x : UniversalLocalView,
            ((paper3HeadlineSolFamNW w) w).lam x τ *
              (universalPval paper3HeadlineEta paper3HeadlineEta_pos c
                  (((paper3HeadlineSolFamNW w) w).u τ) -
                universalPval paper3HeadlineEta paper3HeadlineEta_pos x
                  (((paper3HeadlineSolFamNW w) w).u τ))) *
          ((paper3HeadlineSolFamNW w) w).lam v τ) τ := by
  classical
  let sol := (paper3HeadlineSolFamNW w) w
  let cr : ℝ := selectorMU_activeCr paper3HeadlineM paper3HeadlineKappa τ
  let cg : ℝ := selectorMU_activeCgP (p := bgpParamsNW w)
    paper3HeadlineM (paper3WarmGainQNW w) τ
  let P : UniversalLocalView → ℝ := fun u =>
    universalPval paper3HeadlineEta paper3HeadlineEta_pos u (sol.u τ)
  let lam : UniversalLocalView → ℝ := fun u => sol.lam u τ
  have hrewrite :=
    SelectorDynSol.replicatorLamRHS_eq_gapTrackingResidual_add_meanGap
      (V := UniversalLocalView) (lam := lam) (P := P)
      (cr := cr) (cg := cg) (c := c) (v := v)
      (by simpa [lam, sol] using paper3NW_lam_sum_forward w w τ hτ0)
  have hbase := sol.lam_hasDeriv v τ
    (selectorSchedule_domain_of_nonneg_structural τ hτ0)
  convert hbase using 1
  simpa [cr, cg, P, lam, sol, selectorMU_activeCr,
    selectorMU_activeCgP, selectorMU_activeSinkP, one_div,
    mul_assoc, mul_left_comm, mul_comm] using hrewrite.symm

private theorem paper3NW_mixTargetDerivRHS_halt_centered
    (w : ℕ) {τ : ℝ} (hτ0 : 0 ≤ τ) (c : UniversalLocalView) :
    SelectorReplicatorDynSol.mixTargetDerivRHS
        ((paper3HeadlineSolFamNW w) w) τ haltCoordU =
      ∑ v : UniversalLocalView,
        (((selectorMU_activeCr paper3HeadlineM paper3HeadlineKappa τ *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSinkP paper3HeadlineEta paper3HeadlineEta_pos
                (paper3HeadlineSolFamNW w) w c v τ *
              ((paper3HeadlineSolFamNW w) w).lam v τ +
            selectorMU_activeCgP (p := bgpParamsNW w) paper3HeadlineM
                (paper3WarmGainQNW w) τ *
              (∑ x : UniversalLocalView,
                ((paper3HeadlineSolFamNW w) w).lam x τ *
                  (universalPval paper3HeadlineEta paper3HeadlineEta_pos c
                      (((paper3HeadlineSolFamNW w) w).u τ) -
                    universalPval paper3HeadlineEta paper3HeadlineEta_pos x
                      (((paper3HeadlineSolFamNW w) w).u τ))) *
              ((paper3HeadlineSolFamNW w) w).lam v τ) *
          (BranchData.evalBranch (branchU v)
              (((paper3HeadlineSolFamNW w) w).u τ) haltCoordU -
            BranchData.evalBranch (branchU c)
              (((paper3HeadlineSolFamNW w) w).u τ) haltCoordU))) := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨c⟩
  have hcenter := SelectorReplicatorDynSol.mixTargetDerivRHS_eq_centered
    (sol := ((paper3HeadlineSolFamNW w) w)) τ haltCoordU c
    (paper3NW_lam_sum_forward w w τ hτ0)
  have hraw : ∀ v : UniversalLocalView,
      HasDerivAt (((paper3HeadlineSolFamNW w) w).lam v)
        (((((1 + Real.cos τ) / 2) ^ paper3HeadlineM *
              (paper3HeadlineKappa : ℝ)) *
            (1 / (Fintype.card UniversalLocalView : ℝ) -
              ((paper3HeadlineSolFamNW w) w).lam v τ) +
          (((1 + Real.sin τ) / 2) ^ paper3HeadlineM *
              (((paper3WarmGainQNW w : ℚ) : ℝ) *
                Real.exp ((bgpParamsNW w).cα * τ))) *
            ((paper3HeadlineSolFamNW w) w).lam v τ *
              (universalPval paper3HeadlineEta paper3HeadlineEta_pos v
                  (((paper3HeadlineSolFamNW w) w).u τ) -
                ∑ x : UniversalLocalView,
                  ((paper3HeadlineSolFamNW w) w).lam x τ *
                    universalPval paper3HeadlineEta paper3HeadlineEta_pos x
                      (((paper3HeadlineSolFamNW w) w).u τ)))) τ := by
    intro v
    simpa [selectorSchedule] using
      ((paper3HeadlineSolFamNW w) w).lam_hasDeriv v τ
        (by simpa [selectorSchedule] using hτ0)
  have hgap := paper3NW_lam_hasDerivAt_gapTracking w hτ0 c
  rw [hcenter]
  simp only [MachineInstance.branchU_halt_scale_eq_zero, Rat.cast_zero,
    zero_mul, mul_zero, sub_self, add_zero, zero_add]
  apply Finset.sum_congr rfl
  intro v _
  rw [(hraw v).unique (hgap v)]

private theorem paper3S4b_absRHS_le_badPair_sum_NW
    (w j : ℕ)
    (henc : selectorMUHaltEncConst (solMUReplStaticCfg w) j)
    {τ : ℝ} (hτ0 : 0 ≤ τ) :
    |SelectorReplicatorDynSol.mixTargetDerivRHS
        ((paper3HeadlineSolFamNW w) w) τ haltCoordU| ≤
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j) ∧
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
        (fun v =>
          |selectorMU_activeCr paper3HeadlineM paper3HeadlineKappa τ *
                (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSinkP paper3HeadlineEta paper3HeadlineEta_pos
                (paper3HeadlineSolFamNW w) w
                (localViewU (solMUReplStaticCfg w (j + 1))) v τ *
              ((paper3HeadlineSolFamNW w) w).lam v τ +
            selectorMU_activeCgP (p := bgpParamsNW w) paper3HeadlineM
                (paper3WarmGainQNW w) τ *
              (∑ x : UniversalLocalView,
                ((paper3HeadlineSolFamNW w) w).lam x τ *
                  (universalPval paper3HeadlineEta paper3HeadlineEta_pos
                      (localViewU (solMUReplStaticCfg w (j + 1)))
                      (((paper3HeadlineSolFamNW w) w).u τ) -
                    universalPval paper3HeadlineEta paper3HeadlineEta_pos x
                      (((paper3HeadlineSolFamNW w) w).u τ))) *
              ((paper3HeadlineSolFamNW w) w).lam v τ|) := by
  classical
  let c := localViewU (solMUReplStaticCfg w (j + 1))
  have hM : stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU =
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU := by
    simpa [selectorMUHaltEncConst] using henc
  have hBeq :
      BranchData.evalBranch (branchU (localViewU (solMUReplStaticCfg w j)))
          (((paper3HeadlineSolFamNW w) w).u τ) haltCoordU =
        BranchData.evalBranch (branchU c)
          (((paper3HeadlineSolFamNW w) w).u τ) haltCoordU := by
    dsimp [c]
    rw [branchU_haltCoord_exact_independent, branchU_haltCoord_exact_independent,
      solMUReplStaticCfg_step, solMUReplStaticCfg_step]
    exact hM.symm
  have hkill : ∀ v : UniversalLocalView,
      (v = localViewU (solMUReplStaticCfg w j) ∨ v = c) →
      BranchData.evalBranch (branchU v)
          (((paper3HeadlineSolFamNW w) w).u τ) haltCoordU -
        BranchData.evalBranch (branchU c)
          (((paper3HeadlineSolFamNW w) w).u τ) haltCoordU = 0 := by
    intro v hv
    rcases hv with rfl | rfl
    · exact sub_eq_zero_of_eq hBeq
    · exact sub_self _
  rw [paper3NW_mixTargetDerivRHS_halt_centered w hτ0 c]
  calc
    |∑ v : UniversalLocalView,
        ((selectorMU_activeCr paper3HeadlineM paper3HeadlineKappa τ *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSinkP paper3HeadlineEta paper3HeadlineEta_pos
                (paper3HeadlineSolFamNW w) w c v τ *
              ((paper3HeadlineSolFamNW w) w).lam v τ +
            selectorMU_activeCgP (p := bgpParamsNW w) paper3HeadlineM
                (paper3WarmGainQNW w) τ *
              (∑ x : UniversalLocalView,
                ((paper3HeadlineSolFamNW w) w).lam x τ *
                  (universalPval paper3HeadlineEta paper3HeadlineEta_pos c
                      (((paper3HeadlineSolFamNW w) w).u τ) -
                    universalPval paper3HeadlineEta paper3HeadlineEta_pos x
                      (((paper3HeadlineSolFamNW w) w).u τ))) *
              ((paper3HeadlineSolFamNW w) w).lam v τ) *
          (BranchData.evalBranch (branchU v)
              (((paper3HeadlineSolFamNW w) w).u τ) haltCoordU -
            BranchData.evalBranch (branchU c)
              (((paper3HeadlineSolFamNW w) w).u τ) haltCoordU))|
      ≤ ∑ v : UniversalLocalView,
          |(selectorMU_activeCr paper3HeadlineM paper3HeadlineKappa τ *
                (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSinkP paper3HeadlineEta paper3HeadlineEta_pos
                (paper3HeadlineSolFamNW w) w c v τ *
              ((paper3HeadlineSolFamNW w) w).lam v τ +
            selectorMU_activeCgP (p := bgpParamsNW w) paper3HeadlineM
                (paper3WarmGainQNW w) τ *
              (∑ x : UniversalLocalView,
                ((paper3HeadlineSolFamNW w) w).lam x τ *
                  (universalPval paper3HeadlineEta paper3HeadlineEta_pos c
                      (((paper3HeadlineSolFamNW w) w).u τ) -
                    universalPval paper3HeadlineEta paper3HeadlineEta_pos x
                      (((paper3HeadlineSolFamNW w) w).u τ))) *
              ((paper3HeadlineSolFamNW w) w).lam v τ) *
            (BranchData.evalBranch (branchU v)
                (((paper3HeadlineSolFamNW w) w).u τ) haltCoordU -
              BranchData.evalBranch (branchU c)
                (((paper3HeadlineSolFamNW w) w).u τ) haltCoordU)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧ v ≠ c)).sum
          (fun v => |(selectorMU_activeCr paper3HeadlineM paper3HeadlineKappa τ *
                (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSinkP paper3HeadlineEta paper3HeadlineEta_pos
                (paper3HeadlineSolFamNW w) w c v τ *
              ((paper3HeadlineSolFamNW w) w).lam v τ +
            selectorMU_activeCgP (p := bgpParamsNW w) paper3HeadlineM
                (paper3WarmGainQNW w) τ *
              (∑ x : UniversalLocalView,
                ((paper3HeadlineSolFamNW w) w).lam x τ *
                  (universalPval paper3HeadlineEta paper3HeadlineEta_pos c
                      (((paper3HeadlineSolFamNW w) w).u τ) -
                    universalPval paper3HeadlineEta paper3HeadlineEta_pos x
                      (((paper3HeadlineSolFamNW w) w).u τ))) *
              ((paper3HeadlineSolFamNW w) w).lam v τ) *
            (BranchData.evalBranch (branchU v)
                (((paper3HeadlineSolFamNW w) w).u τ) haltCoordU -
              BranchData.evalBranch (branchU c)
                (((paper3HeadlineSolFamNW w) w).u τ) haltCoordU)|) := by
      refine (Finset.sum_filter_of_ne ?_).symm
      intro v _ hne
      constructor
      · rintro rfl
        exact hne (by rw [hkill _ (Or.inl rfl), mul_zero, abs_zero])
      · rintro rfl
        exact hne (by rw [hkill _ (Or.inr rfl), mul_zero, abs_zero])
    _ ≤ (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧ v ≠ c)).sum
          (fun v => |selectorMU_activeCr paper3HeadlineM paper3HeadlineKappa τ *
                (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSinkP paper3HeadlineEta paper3HeadlineEta_pos
                (paper3HeadlineSolFamNW w) w c v τ *
              ((paper3HeadlineSolFamNW w) w).lam v τ +
            selectorMU_activeCgP (p := bgpParamsNW w) paper3HeadlineM
                (paper3WarmGainQNW w) τ *
              (∑ x : UniversalLocalView,
                ((paper3HeadlineSolFamNW w) w).lam x τ *
                  (universalPval paper3HeadlineEta paper3HeadlineEta_pos c
                      (((paper3HeadlineSolFamNW w) w).u τ) -
                    universalPval paper3HeadlineEta paper3HeadlineEta_pos x
                      (((paper3HeadlineSolFamNW w) w).u τ))) *
              ((paper3HeadlineSolFamNW w) w).lam v τ|) := by
      refine Finset.sum_le_sum ?_
      intro v _
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _)
        (branchU_haltCoord_spread_le_one v c
          (((paper3HeadlineSolFamNW w) w).u τ))
    _ = _ := by simp [c]

private noncomputable def paper3S4bForceNW
    (w j : ℕ) (v : UniversalLocalView) (τ : ℝ) : ℝ :=
  selectorMU_activeCgP (p := bgpParamsNW w) paper3HeadlineM
      (paper3WarmGainQNW w) τ *
    (∑ x : UniversalLocalView,
      ((paper3HeadlineSolFamNW w) w).lam x τ *
        (universalPval paper3HeadlineEta paper3HeadlineEta_pos
            (localViewU (solMUReplStaticCfg w (j + 1)))
            (((paper3HeadlineSolFamNW w) w).u τ) -
          universalPval paper3HeadlineEta paper3HeadlineEta_pos x
            (((paper3HeadlineSolFamNW w) w).u τ))) *
    ((paper3HeadlineSolFamNW w) w).lam v τ

private noncomputable def paper3S4bDefectNW
    (w j : ℕ) (v : UniversalLocalView) (τ : ℝ) : ℝ :=
  selectorMU_activeCr paper3HeadlineM paper3HeadlineKappa τ *
      (Fintype.card UniversalLocalView : ℝ)⁻¹ -
    selectorMU_activeSinkP paper3HeadlineEta paper3HeadlineEta_pos
        (paper3HeadlineSolFamNW w) w
        (localViewU (solMUReplStaticCfg w (j + 1))) v τ *
      ((paper3HeadlineSolFamNW w) w).lam v τ +
    paper3S4bForceNW w j v τ

private theorem paper3S4b_perView_TV_le_NW
    (w j : ℕ) (v : UniversalLocalView)
    (hv : v ≠ localViewU (solMUReplStaticCfg w (j + 1))) :
    (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUNextWriteStart j), |paper3S4bDefectNW w j v τ|) ≤
      |selectorMU_activeQSSP paper3HeadlineEta paper3HeadlineEta_pos
          (paper3HeadlineSolFamNW w) w
          (localViewU (solMUReplStaticCfg w (j + 1))) v
          (selectorMUEarlyWriteSubStart (j + 1)) -
        ((paper3HeadlineSolFamNW w) w).lam v
          (selectorMUEarlyWriteSubStart (j + 1))| +
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUNextWriteStart j),
        |selectorMU_activeQSSDerivRHSP paper3HeadlineEta
          paper3HeadlineEta_pos (paper3HeadlineSolFamNW w) w
          (localViewU (solMUReplStaticCfg w (j + 1))) v τ|) +
      2 * (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUNextWriteStart j), |paper3S4bForceNW w j v τ|) := by
  classical
  let a : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let b : ℝ := selectorMUNextWriteStart j
  let cview : UniversalLocalView := localViewU (solMUReplStaticCfg w (j + 1))
  let k : ℝ → ℝ := fun τ => selectorMU_activeSinkP
    paper3HeadlineEta paper3HeadlineEta_pos (paper3HeadlineSolFamNW w) w cview v τ
  let r : ℝ → ℝ := fun τ =>
    selectorMU_activeCr paper3HeadlineM paper3HeadlineKappa τ *
      (Fintype.card UniversalLocalView : ℝ)⁻¹
  let f : ℝ → ℝ := paper3S4bForceNW w j v
  let m' : ℝ → ℝ := fun τ => selectorMU_activeQSSDerivRHSP
    paper3HeadlineEta paper3HeadlineEta_pos (paper3HeadlineSolFamNW w) w cview v τ
  have hab : a ≤ b := by
    dsimp [a, b]
    unfold selectorMUEarlyWriteSubStart selectorMUNextWriteStart
      selectorMUWriteHoldTime
    push_cast
    linarith [Real.pi_pos]
  have ha0 : 0 ≤ a := by dsimp [a]; unfold selectorMUEarlyWriteSubStart; positivity
  have hfull : ∀ τ ∈ Icc a b,
      τ ∈ Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j) := by
    intro τ hτ
    exact ⟨le_trans (selectorMUZOffEnd_le_earlyWriteSubStart_succ j)
      (by simpa [a] using hτ.1), by simpa [b] using hτ.2⟩
  have hgap : ∀ τ ∈ Icc a b,
      0 ≤ universalPval paper3HeadlineEta paper3HeadlineEta_pos cview
          (((paper3HeadlineSolFamNW w) w).u τ) -
        universalPval paper3HeadlineEta paper3HeadlineEta_pos v
          (((paper3HeadlineSolFamNW w) w).u τ) := by
    intro τ hτ
    have hg := paper3S4b_gapFloor_NW w j v
      (by simpa [cview] using hv) τ (hfull τ hτ)
    linarith
  have hsink : ∀ τ ∈ Icc a b, 0 < k τ := by
    intro τ hτ
    have hτsuffix : τ ∈ Icc (selectorMUEarlyWriteSubStart (j + 1))
        (selectorMUWriteHoldTime (j + 1)) := by
      simpa [a, b, selectorMUNextWriteStart] using hτ
    simpa [k, cview, selectorMU_activeSinkP, selectorMU_activeCgP] using
      selectorMU_activeSuffix_sinkCoeff_pos_of_gap_nonnegP
        (p := bgpParamsNW w) (Mcy := paper3HeadlineM)
        (κ₀ := paper3HeadlineKappa) (g₀ := paper3WarmGainQNW w)
        (by norm_num [paper3HeadlineKappa])
        (paper3WarmGainQNW_nonneg_real w) (j + 1) hτsuffix (hgap τ hτ)
  have hk_cont : Continuous k := by
    simpa [k] using selectorMU_activeSink_continuousP
      paper3HeadlineEta paper3HeadlineEta_pos (paper3HeadlineSolFamNW w) w cview v
  have hr_cont : Continuous r := by
    simpa [r] using (selectorMU_activeCr_continuous paper3HeadlineM
      paper3HeadlineKappa).mul continuous_const
  have hlam_cont : Continuous (((paper3HeadlineSolFamNW w) w).lam v) :=
    ((paper3HeadlineSolFamNW w) w).cont_lam v
  have hmean_cont : Continuous fun τ : ℝ =>
      ∑ x : UniversalLocalView,
        ((paper3HeadlineSolFamNW w) w).lam x τ *
          (universalPval paper3HeadlineEta paper3HeadlineEta_pos cview
              (((paper3HeadlineSolFamNW w) w).u τ) -
            universalPval paper3HeadlineEta paper3HeadlineEta_pos x
              (((paper3HeadlineSolFamNW w) w).u τ)) := by
    refine continuous_finsetSum Finset.univ ?_
    intro x _
    exact (((paper3HeadlineSolFamNW w) w).cont_lam x).mul
      (((paper3HeadlineBoxInputsNW w).hP_cont w cview).sub
        ((paper3HeadlineBoxInputsNW w).hP_cont w x))
  have hf_cont : Continuous f := by
    simpa [f, paper3S4bForceNW, cview] using
      ((selectorMU_activeCg_continuousP (p := bgpParamsNW w)
        paper3HeadlineM (paper3WarmGainQNW w)).mul hmean_cont).mul hlam_cont
  have hm_cont : ContinuousOn (fun τ => r τ / k τ) (Icc a b) :=
    hr_cont.continuousOn.div hk_cont.continuousOn
      (fun τ hτ => ne_of_gt (hsink τ hτ))
  have hm'_cont : ContinuousOn m' (Icc a b) := by
    simpa [m'] using selectorMU_activeQSSDerivRHS_continuousOn_of_sink_posP
      (p := bgpParamsNW w) (sol := paper3HeadlineSolFamNW w) w cview v hsink
  have hy_ode : ∀ τ ∈ Ioo a b,
      HasDerivAt (((paper3HeadlineSolFamNW w) w).lam v)
        (k τ * (r τ / k τ - ((paper3HeadlineSolFamNW w) w).lam v τ) + f τ) τ := by
    intro τ hτ
    have hτIcc : τ ∈ Icc a b := ⟨hτ.1.le, hτ.2.le⟩
    have hk_ne : k τ ≠ 0 := ne_of_gt (hsink τ hτIcc)
    have hlin := paper3NW_lam_hasDerivAt_gapTracking w
      (le_trans ha0 hτIcc.1) cview v
    have hcancel : k τ * (r τ / k τ) = r τ := by
      rw [mul_comm, div_mul_cancel₀ _ hk_ne]
    have heq : k τ * (r τ / k τ - ((paper3HeadlineSolFamNW w) w).lam v τ) +
          f τ = r τ - k τ * ((paper3HeadlineSolFamNW w) w).lam v τ + f τ := by
      rw [mul_sub, hcancel]
    rw [heq]
    simpa [k, r, f, cview, paper3S4bForceNW] using hlin
  have hm_deriv : ∀ τ ∈ Ioo a b,
      HasDerivAt (fun t => r t / k t) (m' τ) τ := by
    intro τ hτ
    have hτIcc : τ ∈ Icc a b := ⟨hτ.1.le, hτ.2.le⟩
    have hτsuffix : τ ∈ Icc (selectorMUEarlyWriteSubStart (j + 1))
        (selectorMUWriteHoldTime (j + 1)) := by
      simpa [a, b, selectorMUNextWriteStart] using hτIcc
    have hq := selectorMU_activeQSS_hasDerivAt_of_sol_u_hasDerivAtP
      (p := bgpParamsNW w) (sol := paper3HeadlineSolFamNW w)
      (by norm_num [paper3HeadlineKappa]) (paper3WarmGainQNW_nonneg_real w)
      w (j + 1) cview v hτsuffix (hgap τ hτIcc)
    simpa [k, r, m', selectorMU_activeQSSP] using hq
  have hstack :=
    stack_write_linear_defect_integral_le_initial_tracking_add_target_deriv_add_forcing_on
      (((paper3HeadlineSolFamNW w) w).lam v) k r f m' a b hab
      hk_cont.continuousOn (fun τ hτ => (hsink τ hτ).le) hsink
      hlam_cont.continuousOn hm_cont hf_cont.continuousOn hm'_cont
      hy_ode hm_deriv
  have hcont_rk : Continuous fun τ : ℝ =>
      r τ - k τ * ((paper3HeadlineSolFamNW w) w).lam v τ :=
    hr_cont.sub (hk_cont.mul hlam_cont)
  have hpt : ∀ τ ∈ Icc a b,
      |r τ - k τ * ((paper3HeadlineSolFamNW w) w).lam v τ + f τ| ≤
        |r τ - k τ * ((paper3HeadlineSolFamNW w) w).lam v τ| + |f τ| :=
    fun τ _ => abs_add_le _ _
  have hint1 : (∫ τ in a..b,
      |r τ - k τ * ((paper3HeadlineSolFamNW w) w).lam v τ + f τ|) ≤
      ∫ τ in a..b,
        (|r τ - k τ * ((paper3HeadlineSolFamNW w) w).lam v τ| + |f τ|) :=
    intervalIntegral.integral_mono_on hab
      (((hcont_rk.add hf_cont).abs).intervalIntegrable a b)
      ((hcont_rk.abs.add hf_cont.abs).intervalIntegrable a b) hpt
  have hint2 : (∫ τ in a..b,
      (|r τ - k τ * ((paper3HeadlineSolFamNW w) w).lam v τ| + |f τ|)) =
      (∫ τ in a..b, |r τ - k τ * ((paper3HeadlineSolFamNW w) w).lam v τ|) +
        ∫ τ in a..b, |f τ| :=
    intervalIntegral.integral_add
      (hcont_rk.abs.intervalIntegrable a b) (hf_cont.abs.intervalIntegrable a b)
  change (∫ τ in a..b,
      |r τ - k τ * ((paper3HeadlineSolFamNW w) w).lam v τ + f τ|) ≤
    |r a / k a - ((paper3HeadlineSolFamNW w) w).lam v a| +
      (∫ τ in a..b, |m' τ|) + 2 * ∫ τ in a..b, |f τ|
  linarith [hint1, hint2, hstack]

private theorem paper3S4b_TV_le_badPair_integralSum_NW
    (w j : ℕ) (henc : selectorMUHaltEncConst (solMUReplStaticCfg w) j) :
    (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUNextWriteStart j),
      |SelectorReplicatorDynSol.mixTargetDerivRHS
        ((paper3HeadlineSolFamNW w) w) τ haltCoordU|) ≤
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j) ∧
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
        (fun v => ∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUNextWriteStart j), |paper3S4bDefectNW w j v τ|) := by
  classical
  let a : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let b : ℝ := selectorMUNextWriteStart j
  let bad : Finset UniversalLocalView := Finset.univ.filter
    (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))
  have hab : a ≤ b := by
    dsimp [a, b]
    unfold selectorMUEarlyWriteSubStart selectorMUNextWriteStart
      selectorMUWriteHoldTime
    push_cast
    linarith [Real.pi_pos]
  have ha0 : 0 ≤ a := by dsimp [a]; unfold selectorMUEarlyWriteSubStart; positivity
  have hdef_cont : ∀ v, Continuous fun τ => paper3S4bDefectNW w j v τ := by
    intro v
    have hmean : Continuous fun τ : ℝ =>
        ∑ x : UniversalLocalView,
          ((paper3HeadlineSolFamNW w) w).lam x τ *
            (universalPval paper3HeadlineEta paper3HeadlineEta_pos
                (localViewU (solMUReplStaticCfg w (j + 1)))
                (((paper3HeadlineSolFamNW w) w).u τ) -
              universalPval paper3HeadlineEta paper3HeadlineEta_pos x
                (((paper3HeadlineSolFamNW w) w).u τ)) := by
      refine continuous_finsetSum Finset.univ ?_
      intro x _
      exact (((paper3HeadlineSolFamNW w) w).cont_lam x).mul
        (((paper3HeadlineBoxInputsNW w).hP_cont w _).sub
          ((paper3HeadlineBoxInputsNW w).hP_cont w x))
    have hcr := selectorMU_activeCr_continuous paper3HeadlineM paper3HeadlineKappa
    have hsink := selectorMU_activeSink_continuousP paper3HeadlineEta
      paper3HeadlineEta_pos (paper3HeadlineSolFamNW w) w
      (localViewU (solMUReplStaticCfg w (j + 1))) v
    have hcg := selectorMU_activeCg_continuousP (p := bgpParamsNW w)
      paper3HeadlineM (paper3WarmGainQNW w)
    simpa [paper3S4bDefectNW, paper3S4bForceNW] using
      ((hcr.mul continuous_const).sub
        (hsink.mul (((paper3HeadlineSolFamNW w) w).cont_lam v))).add
      ((hcg.mul hmean).mul (((paper3HeadlineSolFamNW w) w).cont_lam v))
  have hsum_cont : Continuous fun τ => bad.sum
      (fun v => |paper3S4bDefectNW w j v τ|) :=
    continuous_finsetSum _ (fun v _ => (hdef_cont v).abs)
  have hmono := intervalIntegral.integral_mono_on hab
    ((selectorMU_mixTargetDerivRHS_continuous_for_edgeP
      (sol := paper3HeadlineSolFamNW w) w haltCoordU).abs.intervalIntegrable a b)
    (hsum_cont.intervalIntegrable (μ := MeasureTheory.volume) a b)
    (fun τ hτ => by
      have hp := paper3S4b_absRHS_le_badPair_sum_NW w j henc
        (le_trans ha0 hτ.1)
      simpa [bad, paper3S4bDefectNW, paper3S4bForceNW] using hp)
  have hswap := intervalIntegral.integral_finsetSum
    (s := bad) (f := fun v τ => |paper3S4bDefectNW w j v τ|)
    (fun v _ => (hdef_cont v).abs.intervalIntegrable
      (μ := MeasureTheory.volume) a b)
  calc
    (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUNextWriteStart j),
      |SelectorReplicatorDynSol.mixTargetDerivRHS
        ((paper3HeadlineSolFamNW w) w) τ haltCoordU|)
      ≤ ∫ τ in a..b, bad.sum (fun v => |paper3S4bDefectNW w j v τ|) := by
        simpa [a, b] using hmono
    _ = bad.sum (fun v => ∫ τ in a..b, |paper3S4bDefectNW w j v τ|) := hswap
    _ = _ := by simp [bad, a, b]

/-! ## Right suffix anchor currencies -/

private theorem paper3Hoff_early_exp_currency_le_budget_div_32_NW
    (w j : ℕ) {K : ℝ}
    (hK : K ≤ Real.exp (100 * (bgpScaleW w : ℝ) + 1000)) :
    K * Real.exp (-((bgpParamsNW w).cα *
        selectorMUEarlyWriteSubStart (j + 1))) ≤
      selectorMUHoffEdgeBudget3992 j / 32 := by
  let S : ℝ := (bgpScaleW w : ℝ)
  let a : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let T : ℝ := 2 * Real.pi * (j : ℝ) + Real.pi
  have hS : (5184 : ℝ) ≤ S := by dsimp [S]; exact paper3NW4_S_ge w
  have hS0 : 0 < S := by dsimp [S]; exact bgpScaleWR_pos w
  have hc : (bgpParamsNW w).cα = 300 * S := by
    dsimp [S]
    exact bgpParamsNW_cα_def w
  have hmargin : 100 * S + 1000 + 200 * T ≤ 300 * S * a := by
    dsimp only [T, a]
    unfold selectorMUEarlyWriteSubStart
    push_cast
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hpij : 0 ≤ Real.pi * (j : ℝ) := mul_nonneg Real.pi_pos.le hj
    have hjpart : 400 * Real.pi * (j : ℝ) ≤
        600 * S * Real.pi * (j : ℝ) := by
      have hcoef : (400 : ℝ) ≤ 600 * S := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hcoef hpij]
    have hconst : 100 * S + 1000 + 200 * Real.pi ≤
        675 * S * Real.pi := by
      have hpiS : 3 * S ≤ Real.pi * S :=
        mul_le_mul_of_nonneg_right Real.pi_gt_three.le hS0.le
      have hpi4 := Real.pi_lt_four.le
      nlinarith
    nlinarith
  have hrate : K * Real.exp (-(300 * S * a)) ≤ Real.exp (-(200 * T)) := by
    calc
      K * Real.exp (-(300 * S * a)) ≤
          Real.exp (100 * S + 1000) * Real.exp (-(300 * S * a)) :=
        mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le
      _ = Real.exp (100 * S + 1000 - 300 * S * a) := by
        rw [← Real.exp_add]
        ring
      _ ≤ Real.exp (-(200 * T)) := Real.exp_le_exp.mpr (by linarith)
  have hcoeff : (32 : ℝ) ≤ selectorMUHoffEdgeBudgetCoeff := by
    unfold selectorMUHoffEdgeBudgetCoeff
    linarith [selectorReplicatorHoldEnvelopeCoeff_ge_4000]
  rw [hc]
  unfold selectorMUHoffEdgeBudget3992 selectorMUHoffEdgeBudget
  rw [show bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L -
      bgpParams38.cα = 200 by norm_num [bgpParams38]]
  change K * Real.exp (-(300 * S * a)) ≤
    (selectorMUHoffEdgeBudgetCoeff * Real.exp (-(200 * T))) / 32
  calc
    K * Real.exp (-(300 * S * a)) ≤ Real.exp (-(200 * T)) := hrate
    _ ≤ (selectorMUHoffEdgeBudgetCoeff / 32) * Real.exp (-(200 * T)) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (show (1 : ℝ) ≤ selectorMUHoffEdgeBudgetCoeff / 32 by
          rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 32)]
          simpa using hcoeff) (Real.exp_pos (-(200 * T))).le
    _ = (selectorMUHoffEdgeBudgetCoeff * Real.exp (-(200 * T))) / 32 := by ring

private theorem paper3S4b_badMass_early_le_budget_div_32_NW (w j : ℕ) :
    paper3HoffBadPairNW w j (selectorMUEarlyWriteSubStart (j + 1)) ≤
      selectorMUHoffEdgeBudget3992 j / 32 := by
  let a : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  have ha0 : 0 ≤ a := by dsimp [a]; unfold selectorMUEarlyWriteSubStart; positivity
  have haFull : a ∈ Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j) := by
    constructor
    · dsimp [a]; exact selectorMUZOffEnd_le_earlyWriteSubStart_succ j
    · dsimp [a]
      unfold selectorMUEarlyWriteSubStart selectorMUNextWriteStart
        selectorMUWriteHoldTime
      push_cast
      linarith [Real.pi_pos]
  have hmass := (paper3HoffBadPair_le_newLoser_NW w j ha0).trans
    (paper3S4b_loser_mass_timelocal_NW w j a haFull)
  have hcurrency := paper3Hoff_early_exp_currency_le_budget_div_32_NW w j
    (paper3S4bLoserCoeffNW_le_exp_currency w j)
  exact hmass.trans (by simpa [a] using hcurrency)

private theorem paper3S4b_qssAnchor_early_le_budget_div_32_NW (w j : ℕ) :
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
      (fun v =>
        |selectorMU_activeQSSP paper3HeadlineEta paper3HeadlineEta_pos
          (paper3HeadlineSolFamNW w) w
          (localViewU (solMUReplStaticCfg w (j + 1))) v
          (selectorMUEarlyWriteSubStart (j + 1))|) ≤
      selectorMUHoffEdgeBudget3992 j / 32 := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  let a : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let cview : UniversalLocalView := localViewU (solMUReplStaticCfg w (j + 1))
  let g : ℝ := ((paper3WarmGainQNW w : ℚ) : ℝ)
  let card : ℝ := (Fintype.card UniversalLocalView : ℝ)
  let floor : ℝ := (1 / 2 : ℝ) ^ paper3HeadlineM *
    (g * Real.exp ((bgpParamsNW w).cα * a)) * (1 / 2)
  let B : ℝ := card⁻¹ / floor
  have haFull : a ∈ Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j) := by
    constructor
    · dsimp [a]; exact selectorMUZOffEnd_le_earlyWriteSubStart_succ j
    · dsimp [a]
      unfold selectorMUEarlyWriteSubStart selectorMUNextWriteStart
        selectorMUWriteHoldTime
      push_cast
      linarith [Real.pi_pos]
  have hg : 0 < g := by dsimp [g]; exact paper3WarmGainQNW_pos_real w
  have hcard : 0 < card := by dsimp [card]; exact_mod_cast Fintype.card_pos
  have hfloor : 0 < floor := by dsimp [floor]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hsin : 0 ≤ Real.sin a := by
    apply paper3S4b_sin_nonneg j haFull.1 haFull.2
  have hview : ∀ v ∈ (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))),
      |selectorMU_activeQSSP paper3HeadlineEta paper3HeadlineEta_pos
        (paper3HeadlineSolFamNW w) w cview v a| ≤ B := by
    intro v hv
    have hvNew := (Finset.mem_filter.mp hv).2.2
    have hgap := paper3S4b_gapFloor_NW w j v hvNew a haFull
    have hsink_ge := paper3S4_sink_ge_of_gap_half_NW w cview v hsin hgap
    have hsink_pos : 0 < selectorMU_activeSinkP
        paper3HeadlineEta paper3HeadlineEta_pos (paper3HeadlineSolFamNW w) w
          cview v a := lt_of_lt_of_le (by simpa [floor, g] using hfloor) hsink_ge
    have hcr0 : 0 ≤ selectorMU_activeCr paper3HeadlineM paper3HeadlineKappa a := by
      unfold selectorMU_activeCr
      exact mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_cos a]) _)
        (by norm_num [paper3HeadlineKappa])
    have hcr1 : selectorMU_activeCr paper3HeadlineM paper3HeadlineKappa a ≤ 1 := by
      unfold selectorMU_activeCr
      rw [show ((paper3HeadlineKappa : ℚ) : ℝ) = 1 by
        norm_num [paper3HeadlineKappa], mul_one]
      exact pow_le_one₀ (by nlinarith [Real.neg_one_le_cos a])
        (by nlinarith [Real.cos_le_one a])
    unfold selectorMU_activeQSSP
    rw [abs_of_nonneg (div_nonneg
      (mul_nonneg hcr0 (inv_nonneg.mpr hcard.le)) hsink_pos.le)]
    rw [div_le_iff₀ hsink_pos]
    have hBfloor : B * floor = card⁻¹ := by
      dsimp [B]
      exact div_mul_cancel₀ _ hfloor.ne'
    calc
      selectorMU_activeCr paper3HeadlineM paper3HeadlineKappa a * card⁻¹
          ≤ 1 * card⁻¹ := mul_le_mul_of_nonneg_right hcr1 (inv_nonneg.mpr hcard.le)
      _ = card⁻¹ := one_mul _
      _ = B * floor := hBfloor.symm
      _ ≤ B * selectorMU_activeSinkP paper3HeadlineEta paper3HeadlineEta_pos
          (paper3HeadlineSolFamNW w) w cview v a := by
        apply mul_le_mul_of_nonneg_left _ hB0
        simpa [floor, g] using hsink_ge
  have hsum : (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
      (fun v => |selectorMU_activeQSSP paper3HeadlineEta paper3HeadlineEta_pos
        (paper3HeadlineSolFamNW w) w cview v a|) ≤ card * B := by
    calc
      _ ≤ (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum (fun _ => B) :=
        Finset.sum_le_sum hview
      _ = ((Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).card : ℝ) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ card * B := by
        apply mul_le_mul_of_nonneg_right _ hB0
        change ((Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j) ∧
            v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).card : ℝ) ≤
              (Fintype.card UniversalLocalView : ℝ)
        exact_mod_cast Finset.card_le_univ _
  have hcardB : card * B =
      (2097152 / g) * Real.exp (-((bgpParamsNW w).cα * a)) := by
    dsimp [B, floor]
    have hpow : ((1 : ℝ) / 2) ^ paper3HeadlineM = 1 / 1048576 := by
      norm_num [paper3HeadlineM]
    rw [hpow, ← mul_div_assoc, mul_inv_cancel₀ hcard.ne',
      show (1 : ℝ) / 1048576 *
          (g * Real.exp ((bgpParamsNW w).cα * a)) * (1 / 2) =
        (g * Real.exp ((bgpParamsNW w).cα * a)) / 2097152 by ring,
      one_div_div]
    field_simp [hg.ne']
    rw [← Real.exp_add]
    ring_nf
    simp
  have hK : 2097152 / g ≤ Real.exp (100 * (bgpScaleW w : ℝ) + 1000) := by
    have hg1 : (1 : ℝ) ≤ g := by
      dsimp [g]
      linarith [paper3WarmGainQNW_ge_base w]
    have hdiv : 2097152 / g ≤ (2097152 : ℝ) := by
      rw [div_le_iff₀ hg]
      nlinarith
    have hpowexp : (2097152 : ℝ) ≤
        Real.exp (21 * (bgpScaleW w : ℝ)) := by
      have h2e : (2 : ℝ) ≤ Real.exp (bgpScaleW w : ℝ) := by
        have := Real.add_one_le_exp (bgpScaleW w : ℝ)
        nlinarith [paper3NW4_S_ge w]
      have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2e 21
      have hnum : (2097152 : ℝ) = (2 : ℝ) ^ 21 := by norm_num
      rw [hnum]
      calc
        (2 : ℝ) ^ 21 ≤ Real.exp (bgpScaleW w : ℝ) ^ 21 := hp
        _ = Real.exp (21 * (bgpScaleW w : ℝ)) := by
          rw [← Real.exp_nat_mul]
          ring
    exact hdiv.trans (hpowexp.trans (Real.exp_le_exp.mpr (by
      nlinarith [paper3NW4_S_ge w])))
  have hcurrency := paper3Hoff_early_exp_currency_le_budget_div_32_NW w j hK
  calc
    _ ≤ card * B := by simpa [a, cview] using hsum
    _ = (2097152 / g) * Real.exp (-((bgpParamsNW w).cα * a)) := hcardB
    _ ≤ selectorMUHoffEdgeBudget3992 j / 32 := by simpa [a] using hcurrency

private theorem paper3S4b_qssDerivMass_suffix_le_NW (w j : ℕ) :
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
      (fun v => ∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUNextWriteStart j),
        |selectorMU_activeQSSDerivRHSP paper3HeadlineEta
          paper3HeadlineEta_pos (paper3HeadlineSolFamNW w) w
          (localViewU (solMUReplStaticCfg w (j + 1))) v τ|) ≤
      selectorMUHoffEdgeBudget3992 j / 32 := by
  classical
  let bad : Finset UniversalLocalView := Finset.univ.filter
    (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))
  let Z : ℝ := selectorMUZOffEnd j
  let E : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let H : ℝ := selectorMUNextWriteStart j
  have hZE : Z ≤ E := by simpa [Z, E] using selectorMUZOffEnd_le_earlyWriteSubStart_succ j
  have hEH : E ≤ H := by
    dsimp [E, H]
    unfold selectorMUEarlyWriteSubStart selectorMUNextWriteStart
      selectorMUWriteHoldTime
    push_cast
    linarith [Real.pi_pos]
  have hsub : bad.sum (fun v => ∫ τ in E..H,
      |selectorMU_activeQSSDerivRHSP paper3HeadlineEta
        paper3HeadlineEta_pos (paper3HeadlineSolFamNW w) w
        (localViewU (solMUReplStaticCfg w (j + 1))) v τ|) ≤
      bad.sum (fun v => ∫ τ in Z..H,
      |selectorMU_activeQSSDerivRHSP paper3HeadlineEta
        paper3HeadlineEta_pos (paper3HeadlineSolFamNW w) w
        (localViewU (solMUReplStaticCfg w (j + 1))) v τ|) := by
    apply Finset.sum_le_sum
    intro v hv
    have hvNew := (Finset.mem_filter.mp hv).2.2
    let F : ℝ → ℝ := fun τ =>
      |selectorMU_activeQSSDerivRHSP paper3HeadlineEta
        paper3HeadlineEta_pos (paper3HeadlineSolFamNW w) w
        (localViewU (solMUReplStaticCfg w (j + 1))) v τ|
    have hsink : ∀ τ ∈ Icc Z H,
        0 < selectorMU_activeSinkP paper3HeadlineEta paper3HeadlineEta_pos
          (paper3HeadlineSolFamNW w) w
          (localViewU (solMUReplStaticCfg w (j + 1))) v τ := by
      intro τ hτ
      have hτ' : τ ∈ Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j) :=
        by simpa [Z, H] using hτ
      have hsin := paper3S4b_sin_nonneg j hτ'.1 hτ'.2
      have hgap := paper3S4b_gapFloor_NW w j v hvNew τ hτ'
      have hf := paper3S4_sink_ge_of_gap_half_NW w _ v hsin hgap
      have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ paper3HeadlineM *
          (((paper3WarmGainQNW w : ℚ) : ℝ) *
            Real.exp ((bgpParamsNW w).cα * τ)) * (1 / 2) :=
        mul_pos (mul_pos (pow_pos (by norm_num) _)
          (mul_pos (paper3WarmGainQNW_pos_real w) (Real.exp_pos _)))
          (by norm_num)
      exact lt_of_lt_of_le hpos hf
    have hcont := selectorMU_activeQSSDerivRHS_continuousOn_of_sink_posP
      (p := bgpParamsNW w) (sol := paper3HeadlineSolFamNW w) w
      (localViewU (solMUReplStaticCfg w (j + 1))) v hsink
    apply intervalIntegral.integral_mono_interval hZE hEH le_rfl
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with τ hτ
      exact abs_nonneg _
    · exact hcont.abs.intervalIntegrable_of_Icc
        (le_trans hZE hEH)
  have hsub' := hsub
  simp only [bad, Z, E, H] at hsub'
  exact hsub'.trans (paper3S4b_qssDerivMass_le_NW w j)

private theorem paper3S4b_suffixTV_le_budget_div_8_NW
    (w j : ℕ) (henc : selectorMUHaltEncConst (solMUReplStaticCfg w) j) :
    (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUNextWriteStart j),
      |SelectorReplicatorDynSol.mixTargetDerivRHS
        ((paper3HeadlineSolFamNW w) w) τ haltCoordU|) ≤
      selectorMUHoffEdgeBudget3992 j / 8 := by
  classical
  let bad : Finset UniversalLocalView := Finset.univ.filter
    (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))
  let a : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  have hred := paper3S4b_TV_le_badPair_integralSum_NW w j henc
  have hsum := Finset.sum_le_sum
    (fun v (hv : v ∈ bad) =>
      paper3S4b_perView_TV_le_NW w j v (Finset.mem_filter.mp hv).2.2)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hanchor := Finset.sum_le_sum
    (fun v (_hv : v ∈ bad) => by
      have hlam : 0 ≤ ((paper3HeadlineSolFamNW w) w).lam v a := by
        apply paper3NW_lam_nonneg_forward w w v a
        dsimp [a]
        unfold selectorMUEarlyWriteSubStart
        positivity
      calc
        |selectorMU_activeQSSP paper3HeadlineEta paper3HeadlineEta_pos
            (paper3HeadlineSolFamNW w) w
            (localViewU (solMUReplStaticCfg w (j + 1))) v a -
          ((paper3HeadlineSolFamNW w) w).lam v a|
          ≤ |selectorMU_activeQSSP paper3HeadlineEta paper3HeadlineEta_pos
              (paper3HeadlineSolFamNW w) w
              (localViewU (solMUReplStaticCfg w (j + 1))) v a| +
            |(-((paper3HeadlineSolFamNW w) w).lam v a)| := by
              simpa [sub_eq_add_neg] using abs_add_le
                (selectorMU_activeQSSP paper3HeadlineEta paper3HeadlineEta_pos
                  (paper3HeadlineSolFamNW w) w
                  (localViewU (solMUReplStaticCfg w (j + 1))) v a)
                (-((paper3HeadlineSolFamNW w) w).lam v a)
        _ = |selectorMU_activeQSSP paper3HeadlineEta paper3HeadlineEta_pos
              (paper3HeadlineSolFamNW w) w
              (localViewU (solMUReplStaticCfg w (j + 1))) v a| +
            ((paper3HeadlineSolFamNW w) w).lam v a := by
              rw [abs_neg, abs_of_nonneg hlam])
  rw [Finset.sum_add_distrib] at hanchor
  have hqssA := paper3S4b_qssAnchor_early_le_budget_div_32_NW w j
  have hlamA := paper3S4b_badMass_early_le_budget_div_32_NW w j
  have hqssD := paper3S4b_qssDerivMass_suffix_le_NW w j
  have hforce := paper3S4b_forcingMass_le_NW w j
  have hforce' : 2 * (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
      (fun v => ∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUNextWriteStart j), |paper3S4bForceNW w j v τ|) ≤
      selectorMUHoffEdgeBudget3992 j / 32 := by
    simpa only [paper3S4bForceNW] using hforce
  have hmassEq : bad.sum (fun v =>
      ((paper3HeadlineSolFamNW w) w).lam v a) = paper3HoffBadPairNW w j a := by
    rfl
  rw [hmassEq] at hanchor
  have hb0 := paper3HeadlineHoff_edgeBudget3992_nonneg j
  dsimp only [bad, a] at hsum hanchor
  linarith [hred, hsum, hanchor, hqssA, hlamA, hqssD, hforce', hb0]

/-! ## Settled read endpoint -/

private theorem paper3Hoff_zGateMass_ge_NW (w j : ℕ) :
    Real.pi / 24 * Real.exp (50 * (bgpScaleW w : ℝ) * paper3S13Mid j) ≤
      ∫ τ in (paper3S13Mid j)..(selectorMUWriteReadTime j),
        (bgpParamsNW w).A * ((paper3HeadlineSolFamNW w) w).α τ *
          bGateZ (bgpParamsNW w).L (((paper3HeadlineSolFamNW w) w).μ τ) τ := by
  have hab := paper3S13_mid_le_read j
  have ha0 := paper3S13_mid_nonneg j
  have hpoint : ∀ τ ∈ Icc (paper3S13Mid j) (selectorMUWriteReadTime j),
      Real.exp (50 * (bgpScaleW w : ℝ) * paper3S13Mid j) ≤
        (bgpParamsNW w).A * ((paper3HeadlineSolFamNW w) w).α τ *
          bGateZ (bgpParamsNW w).L (((paper3HeadlineSolFamNW w) w).μ τ) τ := by
    intro τ hτ
    have hτ0 := le_trans ha0 hτ.1
    have hsin : (1 / 2 : ℝ) ≤ Real.sin τ :=
      paper3S13_sin_ge_half j
        (le_trans (le_trans (paper3S13_selectStart_le_subEnd j)
          (paper3S13_subEnd_le_mid j)) hτ.1) hτ.2
    exact (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hτ.1
        (mul_nonneg (by norm_num) (bgpScaleWR_pos w).le))).trans
      (paper3NW4_zKernel_ge_of_sin_ge_half w w hτ0 hsin)
  have hmono := intervalIntegral.integral_mono_on hab
    (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) _ _)
    ((paper3NW4_zKernel_continuous w w).intervalIntegrable
      (μ := MeasureTheory.volume) _ _) hpoint
  have hlen : selectorMUWriteReadTime j - paper3S13Mid j = Real.pi / 24 := by
    unfold selectorMUWriteReadTime paper3S13Mid
    ring
  rw [intervalIntegral.integral_const, smul_eq_mul, hlen] at hmono
  exact hmono

private theorem paper3Hoff_z_readStart_le_budget_div_32_NW
    (w j : ℕ) :
    |((paper3HeadlineSolFamNW w) w).z (selectorMUInterReadStart j) haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤
      selectorMUHoffEdgeBudget3992 j / 32 := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  let a : ℝ := paper3S13Mid j
  let b : ℝ := selectorMUWriteReadTime j
  let S : ℝ := (bgpScaleW w : ℝ)
  let T : ℝ := 2 * Real.pi * (j : ℝ) + Real.pi
  let rate : ℝ := Real.exp (-(200 * T))
  let K : ℝ := paper3S4aLoserCoeffNW w j
  have hab : a ≤ b := by simpa [a, b] using paper3S13_mid_le_read j
  have ha0 : 0 ≤ a := by simpa [a] using paper3S13_mid_nonneg j
  have hS : (5184 : ℝ) ≤ S := by dsimp [S]; exact paper3NW4_S_ge w
  have hS0 : 0 < S := by dsimp [S]; exact bgpScaleWR_pos w
  have hK := paper3S4aLoserCoeffNW_le_exp_currency w j
  have hmargin : 100 * S + 1000 + 200 * T ≤ 300 * S * a := by
    dsimp only [T, a]
    unfold paper3S13Mid
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hpij : 0 ≤ Real.pi * (j : ℝ) := mul_nonneg Real.pi_pos.le hj
    have hjpart : 400 * Real.pi * (j : ℝ) ≤
        600 * S * Real.pi * (j : ℝ) := by
      have hc : (400 : ℝ) ≤ 600 * S := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hc hpij]
    have hconst : 100 * S + 1000 + 200 * Real.pi ≤
        300 * S * (19 * Real.pi / 24) := by
      have hpiS : 3 * S ≤ Real.pi * S :=
        mul_le_mul_of_nonneg_right Real.pi_gt_three.le hS0.le
      have hpi4 := Real.pi_lt_four.le
      nlinarith
    nlinarith
  have hloser : ∀ t ∈ Icc a b,
      paper3HoffOldLoserNW w j t ≤ rate := by
    intro t ht
    have ht0 := le_trans ha0 ht.1
    have hhold : selectorMUWriteHoldTime j ≤ a := by
      dsimp [a]
      unfold selectorMUWriteHoldTime paper3S13Mid
      linarith [Real.pi_pos]
    have htz : b ≤ selectorMUZOffStart j := by
      dsimp [b]
      unfold selectorMUWriteReadTime selectorMUZOffStart
      linarith [Real.pi_pos]
    have hmass := paper3S4a_loser_mass_timelocal_NW w j t
      ⟨le_trans hhold ht.1, le_trans ht.2 htz⟩
    have hexp : K * Real.exp (-((bgpParamsNW w).cα * t)) ≤ rate := by
      have hc : (bgpParamsNW w).cα = 300 * S := by
        dsimp [S]; exact bgpParamsNW_cα_def w
      rw [hc]
      calc
        K * Real.exp (-(300 * S * t)) ≤
            Real.exp (100 * S + 1000) * Real.exp (-(300 * S * t)) :=
          mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le
        _ = Real.exp (100 * S + 1000 - 300 * S * t) := by
          rw [← Real.exp_add]
          ring
        _ ≤ Real.exp (-(200 * T)) := by
          apply Real.exp_le_exp.mpr
          have hcoef : 0 ≤ 300 * S := mul_nonneg (by norm_num) hS0.le
          have hSa : 300 * S * a ≤ 300 * S * t :=
            mul_le_mul_of_nonneg_left ht.1 hcoef
          linarith
        _ = rate := rfl
    have hmass' : paper3HoffOldLoserNW w j t ≤
        K * Real.exp (-((bgpParamsNW w).cα * t)) := by
      simpa only [paper3HoffOldLoserNW, K] using hmass
    exact hmass'.trans hexp
  have hmix : ∀ t ∈ Icc a b,
      |selectorMixTarget branchU ((paper3HeadlineSolFamNW w) w).u
          ((paper3HeadlineSolFamNW w) w).lam t haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤
        rate := by
    intro t ht
    exact (paper3Hoff_mix_pointwise_le_oldLoser_NW w j
      (le_trans ha0 ht.1)).trans (hloser t ht)
  have hdom : ∀ t ∈ Icc a b, t ∈ selectorSchedule.domain := fun t ht =>
    selectorSchedule_domain_of_nonneg_structural t (le_trans ha0 ht.1)
  have hk0 : ∀ t ∈ Icc a b,
      0 ≤ (bgpParamsNW w).A * ((paper3HeadlineSolFamNW w) w).α t *
        bGateZ (bgpParamsNW w).L (((paper3HeadlineSolFamNW w) w).μ t) t :=
    fun t ht => paper3NW4_zKernel_nonneg w w (le_trans ha0 ht.1)
  have hzero : ∀ t ∈ Icc b b,
      |((paper3HeadlineSolFamNW w) w).z t haltCoordU -
        ((paper3HeadlineSolFamNW w) w).z b haltCoordU| ≤ (0 : ℝ) := by
    intro t ht
    have ht' : t = b := le_antisymm ht.2 ht.1
    subst t
    simp
  have hzraw := z_after_write_bound_repl
    (sol := (paper3HeadlineSolFamNW w) w) (s := haltCoordU)
    (a := a) (m := b) (b := b)
    (M := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU)
    (δw := rate) (δzh := 0) hab hdom
    (paper3NW4_zKernel_continuous w w) hk0 hmix hzero b ⟨le_rfl, le_rfl⟩
  let I : ℝ := ∫ t in a..b,
      (bgpParamsNW w).A * ((paper3HeadlineSolFamNW w) w).α t *
        bGateZ (bgpParamsNW w).L (((paper3HeadlineSolFamNW w) w).μ t) t
  have hmass := paper3Hoff_zGateMass_ge_NW w j
  have hx0 : 0 ≤ 50 * S * a := by positivity
  have hexplin : 1 + 50 * S * a ≤ Real.exp (50 * S * a) := by
    simpa [add_comm] using Real.add_one_le_exp (50 * S * a)
  have hpi8 : (1 / 8 : ℝ) ≤ Real.pi / 24 := by
    nlinarith [Real.pi_gt_three]
  have hlinear : 200 * T ≤ (1 / 8 : ℝ) * (1 + 50 * S * a) := by
    dsimp only [T, a]
    unfold paper3S13Mid
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hpij : 0 ≤ Real.pi * (j : ℝ) := mul_nonneg Real.pi_pos.le hj
    have hjpart : 3200 * Real.pi * (j : ℝ) ≤
        100 * S * Real.pi * (j : ℝ) := by
      have hc : (3200 : ℝ) ≤ 100 * S := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hc hpij]
    have hconst : 1600 * Real.pi ≤ 1 + 50 * S * (19 * Real.pi / 24) := by
      have hpiS : 3 * S ≤ Real.pi * S :=
        mul_le_mul_of_nonneg_right Real.pi_gt_three.le hS0.le
      nlinarith
    nlinarith
  have hI : 200 * T ≤ I := by
    have hchain : (1 / 8 : ℝ) * (1 + 50 * S * a) ≤
        Real.pi / 24 * Real.exp (50 * S * a) := by
      calc
        (1 / 8 : ℝ) * (1 + 50 * S * a) ≤
            (1 / 8 : ℝ) * Real.exp (50 * S * a) :=
          mul_le_mul_of_nonneg_left hexplin (by norm_num)
        _ ≤ Real.pi / 24 * Real.exp (50 * S * a) :=
          mul_le_mul_of_nonneg_right hpi8 (Real.exp_pos _).le
    have hmass' : Real.pi / 24 * Real.exp (50 * S * a) ≤ I := by
      dsimp only [I, S, a, b]
      exact hmass
    exact hlinear.trans (hchain.trans hmass')
  have hexpI : Real.exp (-I) ≤ rate := by
    apply Real.exp_le_exp.mpr
    dsimp [rate]
    linarith
  have hMunit := paper3_enc_haltCoordU_mem_unit (solMUReplStaticCfg w (j + 1))
  have hzunit := (paper3HeadlineBoxInputsNW w).halt_z_mem_Icc
    (by rw [bgpParamsNW_A_eq]; norm_num) w a ha0
  have hinit : |((paper3HeadlineSolFamNW w) w).z a haltCoordU -
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤ 1 :=
    paper3_abs_sub_le_one_of_unit_interval_pair hzunit hMunit
  have hctr : Real.exp (-I) *
      |((paper3HeadlineSolFamNW w) w).z a haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤
      rate := by
    exact (mul_le_mul_of_nonneg_left hinit (Real.exp_pos _).le).trans
      (by simpa using hexpI)
  have hz : |((paper3HeadlineSolFamNW w) w).z b haltCoordU -
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤
      2 * rate := by
    have hzraw' := hzraw
    dsimp only [I] at hctr
    dsimp only [rate] at hzraw' ⊢
    linarith
  have hcoeff : (64 : ℝ) ≤ selectorMUHoffEdgeBudgetCoeff := by
    unfold selectorMUHoffEdgeBudgetCoeff
    linarith [selectorReplicatorHoldEnvelopeCoeff_ge_4000]
  unfold selectorMUHoffEdgeBudget3992 selectorMUHoffEdgeBudget
  rw [show bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L -
      bgpParams38.cα = 200 by norm_num [bgpParams38]]
  change |((paper3HeadlineSolFamNW w) w).z b haltCoordU -
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤
    (selectorMUHoffEdgeBudgetCoeff * Real.exp (-(200 * T))) / 32
  have hrate0 : 0 ≤ rate := (Real.exp_pos _).le
  calc
    _ ≤ 2 * rate := hz
    _ ≤ (selectorMUHoffEdgeBudgetCoeff / 32) * rate := by
      apply mul_le_mul_of_nonneg_right _ hrate0
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 32)]
      nlinarith [hcoeff]
    _ = (selectorMUHoffEdgeBudgetCoeff * Real.exp (-(200 * T))) / 32 := by
      dsimp [rate]
      ring

private theorem paper3Hoff_z_drift_read_to_zOffEnd_NW (w j : ℕ) :
    |((paper3HeadlineSolFamNW w) w).z (selectorMUZOffEnd j) haltCoordU -
        ((paper3HeadlineSolFamNW w) w).z (selectorMUInterReadStart j) haltCoordU| ≤
      paper3HeadlineHoffCapLeftFieldNW w j +
        selectorMUHoffMiddleEnvelopeFullCapNW w j := by
  let sol := paper3HeadlineSolFamNW w
  let a : ℝ := selectorMUInterReadStart j
  let b : ℝ := selectorMUZOffStart j
  let c : ℝ := selectorMUZOffEnd j
  let y : ℝ → ℝ := fun τ => (sol w).z τ haltCoordU
  let m : ℝ → ℝ := fun τ =>
    selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU
  let k : ℝ → ℝ := fun τ => selectorMUHoffGateCoeffP
    (p := bgpParamsNW w) sol w τ
  have hab : a ≤ b := by simpa [a, b] using selectorMUInterReadStart_le_zOffStart j
  have hbc : b ≤ c := by simpa [b, c] using selectorMUZOffStart_le_zOffEnd j
  have hac : a ≤ c := le_trans hab hbc
  have ha0 : 0 ≤ a := by
    simp [a, selectorMUInterReadStart, selectorMUWriteReadTime]
    positivity
  have hk_cont : Continuous k := by
    simpa [k] using selectorMUHoffGateCoeffP_continuous
      (p := bgpParamsNW w) (sol := sol) w
  have hm_cont : Continuous m := by simpa [m] using (sol w).cont_mixTarget haltCoordU
  have hy_cont : Continuous y := by simpa [y] using (sol w).cont_z haltCoordU
  have hy_ode : ∀ τ ∈ uIcc a c,
      HasDerivAt y (k τ * (m τ - y τ)) τ := by
    intro τ hτ
    rw [uIcc_of_le hac] at hτ
    have hτ0 := le_trans ha0 hτ.1
    simpa [y, m, k, selectorMUHoffGateCoeffP] using
      (sol w).z_hasDeriv τ
        (selectorSchedule_domain_of_nonneg_structural τ hτ0) haltCoordU
  have hftc : (∫ τ in a..c, k τ * (m τ - y τ)) = y c - y a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hy_ode
      ((hk_cont.mul (hm_cont.sub hy_cont)).intervalIntegrable a c)
  have hInt : ∀ x x' : ℝ, IntervalIntegrable
      (fun τ => paper3HeadlineHoffIntegrandNW w τ) MeasureTheory.volume x x' :=
    fun x x' => (selectorMUHoffIntegrandP_continuous
      (p := bgpParamsNW w) (sol := sol) w).intervalIntegrable x x'
  have habs_eq : ∀ τ,
      |k τ * (m τ - y τ)| = paper3HeadlineHoffIntegrandNW w τ := by
    intro τ
    simp [paper3HeadlineHoffIntegrandNW, selectorMUHoffIntegrandP,
      selectorMUHoffGateCoeffP, k, m, y, sol, mul_assoc]
  have habs : |y c - y a| ≤ ∫ τ in a..c, paper3HeadlineHoffIntegrandNW w τ := by
    rw [← hftc]
    refine (intervalIntegral.abs_integral_le_integral_abs hac).trans ?_
    exact le_of_eq (intervalIntegral.integral_congr
      (fun τ _ => habs_eq τ))
  have hsplit : (∫ τ in a..c, paper3HeadlineHoffIntegrandNW w τ) =
      (∫ τ in a..b, paper3HeadlineHoffIntegrandNW w τ) +
        ∫ τ in b..c, paper3HeadlineHoffIntegrandNW w τ :=
    (intervalIntegral.integral_add_adjacent_intervals (hInt a b) (hInt b c)).symm
  have hmid := paper3HeadlineHoff_middle_fieldIntegral_NW
    paper3HeadlineBoxInputsNW w j c ⟨by simpa [b, c] using hbc, le_rfl⟩
  calc
    |((paper3HeadlineSolFamNW w) w).z (selectorMUZOffEnd j) haltCoordU -
        ((paper3HeadlineSolFamNW w) w).z (selectorMUInterReadStart j) haltCoordU|
      = |y c - y a| := rfl
    _ ≤ ∫ τ in a..c, paper3HeadlineHoffIntegrandNW w τ := habs
    _ = (∫ τ in a..b, paper3HeadlineHoffIntegrandNW w τ) +
        ∫ τ in b..c, paper3HeadlineHoffIntegrandNW w τ := hsplit
    _ ≤ paper3HeadlineHoffCapLeftFieldNW w j +
        selectorMUHoffMiddleEnvelopeFullCapNW w j := by
      exact add_le_add le_rfl (by simpa [b, c] using hmid)

private theorem paper3Hoff_zoff_exp_currency_le_budget_div_32_NW
    (w j : ℕ) {K : ℝ}
    (hK : K ≤ Real.exp (100 * (bgpScaleW w : ℝ) + 1000)) :
    K * Real.exp (-((bgpParamsNW w).cα * selectorMUZOffEnd j)) ≤
      selectorMUHoffEdgeBudget3992 j / 32 := by
  let S : ℝ := (bgpScaleW w : ℝ)
  let Z : ℝ := selectorMUZOffEnd j
  let T : ℝ := 2 * Real.pi * (j : ℝ) + Real.pi
  have hS : (5184 : ℝ) ≤ S := by dsimp [S]; exact paper3NW4_S_ge w
  have hS0 : 0 < S := by dsimp [S]; exact bgpScaleWR_pos w
  have hc : (bgpParamsNW w).cα = 300 * S := by
    dsimp [S]; exact bgpParamsNW_cα_def w
  have hmargin : 100 * S + 1000 + 200 * T ≤ 300 * S * Z := by
    dsimp only [T, Z]
    unfold selectorMUZOffEnd
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hpij : 0 ≤ Real.pi * (j : ℝ) := mul_nonneg Real.pi_pos.le hj
    have hjpart : 400 * Real.pi * (j : ℝ) ≤
        600 * S * Real.pi * (j : ℝ) := by
      have hcoef : (400 : ℝ) ≤ 600 * S := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hcoef hpij]
    have hconst : 100 * S + 1000 + 200 * Real.pi ≤ 600 * S * Real.pi := by
      have hpiS : 3 * S ≤ Real.pi * S :=
        mul_le_mul_of_nonneg_right Real.pi_gt_three.le hS0.le
      have hpi4 := Real.pi_lt_four.le
      nlinarith
    nlinarith
  have hrate : K * Real.exp (-(300 * S * Z)) ≤ Real.exp (-(200 * T)) := by
    calc
      K * Real.exp (-(300 * S * Z)) ≤
          Real.exp (100 * S + 1000) * Real.exp (-(300 * S * Z)) :=
        mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le
      _ = Real.exp (100 * S + 1000 - 300 * S * Z) := by
        rw [← Real.exp_add]
        ring
      _ ≤ Real.exp (-(200 * T)) := Real.exp_le_exp.mpr (by linarith)
  have hcoeff : (32 : ℝ) ≤ selectorMUHoffEdgeBudgetCoeff := by
    unfold selectorMUHoffEdgeBudgetCoeff
    linarith [selectorReplicatorHoldEnvelopeCoeff_ge_4000]
  rw [hc]
  unfold selectorMUHoffEdgeBudget3992 selectorMUHoffEdgeBudget
  rw [show bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L -
      bgpParams38.cα = 200 by norm_num [bgpParams38]]
  change K * Real.exp (-(300 * S * Z)) ≤
    (selectorMUHoffEdgeBudgetCoeff * Real.exp (-(200 * T))) / 32
  calc
    K * Real.exp (-(300 * S * Z)) ≤ Real.exp (-(200 * T)) := hrate
    _ ≤ (selectorMUHoffEdgeBudgetCoeff / 32) * Real.exp (-(200 * T)) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (show (1 : ℝ) ≤ selectorMUHoffEdgeBudgetCoeff / 32 by
          rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 32)]
          simpa using hcoeff) (Real.exp_pos _).le
    _ = _ := by ring

private theorem paper3S4b_badMass_right_le_budget_div_32_NW
    (w j : ℕ) {t : ℝ}
    (ht : t ∈ Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j)) :
    paper3HoffBadPairNW w j t ≤ selectorMUHoffEdgeBudget3992 j / 32 := by
  have ht0 : 0 ≤ t := le_trans (by unfold selectorMUZOffEnd; positivity) ht.1
  have hmass := (paper3HoffBadPair_le_newLoser_NW w j ht0).trans
    (paper3S4b_loser_mass_timelocal_NW w j t ht)
  have hmono : paper3S4bLoserCoeffNW w j *
      Real.exp (-((bgpParamsNW w).cα * t)) ≤
      paper3S4bLoserCoeffNW w j *
        Real.exp (-((bgpParamsNW w).cα * selectorMUZOffEnd j)) := by
    apply mul_le_mul_of_nonneg_left _ (paper3S4bLoserCoeffNW_nonneg w j)
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_left ht.1 (bgpParamsNW_cα_pos w).le)
  exact hmass.trans (hmono.trans
    (paper3Hoff_zoff_exp_currency_le_budget_div_32_NW w j
      (paper3S4bLoserCoeffNW_le_exp_currency w j)))

private theorem paper3Hoff_z_early_le_zoff_add_budget_div_32_NW
    (w j : ℕ) (henc : selectorMUHaltEncConst (solMUReplStaticCfg w) j) :
    |((paper3HeadlineSolFamNW w) w).z (selectorMUEarlyWriteSubStart (j + 1))
          haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤
      |((paper3HeadlineSolFamNW w) w).z (selectorMUZOffEnd j) haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| +
      selectorMUHoffEdgeBudget3992 j / 32 := by
  let Z : ℝ := selectorMUZOffEnd j
  let E : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let sol := (paper3HeadlineSolFamNW w) w
  let y : ℝ → ℝ := fun t => sol.z t haltCoordU
  let m : ℝ → ℝ := fun t => selectorMixTarget branchU sol.u sol.lam t haltCoordU
  let k : ℝ → ℝ := fun t => (bgpParamsNW w).A * sol.α t *
    bGateZ (bgpParamsNW w).L (sol.μ t) t
  let M : ℝ := stackMachineEncodingU.enc
    (solMUReplStaticCfg w (j + 1)) haltCoordU
  let δ : ℝ := selectorMUHoffEdgeBudget3992 j / 32
  have hZE : Z ≤ E := by simpa [Z, E] using selectorMUZOffEnd_le_earlyWriteSubStart_succ j
  have hZ0 : 0 ≤ Z := by dsimp [Z]; unfold selectorMUZOffEnd; positivity
  have hkcont : Continuous k := by simpa [k, sol] using paper3NW4_zKernel_continuous w w
  have hk0 : ∀ t ∈ Icc Z E, 0 ≤ k t := by
    intro t ht
    simpa [k, sol] using paper3NW4_zKernel_nonneg w w (le_trans hZ0 ht.1)
  have hmcont : Continuous m := by simpa [m] using sol.cont_mixTarget haltCoordU
  have hyode : ∀ t ∈ Icc Z E, HasDerivAt y (k t * (m t - y t)) t := by
    intro t ht
    have ht0 := le_trans hZ0 ht.1
    simpa [y, m, k, sol] using sol.z_hasDeriv t
      (selectorSchedule_domain_of_nonneg_structural t ht0) haltCoordU
  have hmsup : ∀ t ∈ Icc Z E, |m t - M| ≤ δ := by
    intro t ht
    have htfull : t ∈ Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j) :=
      ⟨by simpa [Z] using ht.1, le_trans (by simpa [E] using ht.2) (by
        unfold selectorMUEarlyWriteSubStart selectorMUNextWriteStart
          selectorMUWriteHoldTime
        push_cast
        linarith [Real.pi_pos])⟩
    exact (paper3Hoff_mix_pointwise_le_badPair_NW w j
      (le_trans hZ0 ht.1) henc).trans
      (paper3S4b_badMass_right_le_budget_div_32_NW w j htfull)
  have hgron := stack_write_gronwall_sup_bound y m k M Z E hZE
    hkcont hk0 hmcont hyode hmsup
  have hmass0 : 0 ≤ ∫ t in Z..E, k t := by
    apply intervalIntegral.integral_nonneg hZE
    intro t ht
    exact hk0 t ht
  have hexp0 : 0 ≤ Real.exp (-(∫ t in Z..E, k t)) := Real.exp_nonneg _
  have hexp1 : Real.exp (-(∫ t in Z..E, k t)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hδ0 : 0 ≤ δ := by
    dsimp [δ]
    exact div_nonneg (paper3HeadlineHoff_edgeBudget3992_nonneg j) (by norm_num)
  have hfirst : Real.exp (-(∫ t in Z..E, k t)) * |y Z - M| ≤ |y Z - M| := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp1 (abs_nonneg _)
  have hsecond : δ * (1 - Real.exp (-(∫ t in Z..E, k t))) ≤ δ := by
    have hle : 1 - Real.exp (-(∫ t in Z..E, k t)) ≤ 1 := by linarith
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hle hδ0
  dsimp only [y, M, Z, E, sol] at hgron ⊢
  dsimp only [δ] at hgron
  dsimp only [y, M, Z, E, sol] at hfirst
  dsimp only [δ, Z, E] at hsecond
  linarith

private theorem paper3Hoff_suffixField_le_initial_add_TV_NW (w j : ℕ) :
    (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUNextWriteStart j), paper3HeadlineHoffIntegrandNW w τ) ≤
      |selectorMixTarget branchU ((paper3HeadlineSolFamNW w) w).u
          ((paper3HeadlineSolFamNW w) w).lam
          (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU -
        ((paper3HeadlineSolFamNW w) w).z
          (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU| +
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUNextWriteStart j),
        |SelectorReplicatorDynSol.mixTargetDerivRHS
          ((paper3HeadlineSolFamNW w) w) τ haltCoordU|) := by
  let a : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let b : ℝ := selectorMUNextWriteStart j
  let sol := paper3HeadlineSolFamNW w
  let y : ℝ → ℝ := fun τ => (sol w).z τ haltCoordU
  let m : ℝ → ℝ := fun τ => selectorMixTarget branchU
    (sol w).u (sol w).lam τ haltCoordU
  let k : ℝ → ℝ := fun τ => selectorMUHoffGateCoeffP
    (p := bgpParamsNW w) sol w τ
  let mdot : ℝ → ℝ := fun τ =>
    SelectorReplicatorDynSol.mixTargetDerivRHS (sol w) τ haltCoordU
  have hab : a ≤ b := by
    dsimp [a, b]
    unfold selectorMUEarlyWriteSubStart selectorMUNextWriteStart
      selectorMUWriteHoldTime
    push_cast
    linarith [Real.pi_pos]
  have ha0 : 0 ≤ a := by dsimp [a]; unfold selectorMUEarlyWriteSubStart; positivity
  have hkcont : Continuous k := by
    simpa [k] using selectorMUHoffGateCoeffP_continuous
      (p := bgpParamsNW w) (sol := sol) w
  have hmcont : Continuous m := by simpa [m] using (sol w).cont_mixTarget haltCoordU
  have hycont : Continuous y := by simpa [y] using (sol w).cont_z haltCoordU
  have hmdotcont : Continuous mdot := by
    simpa [mdot] using selectorMU_mixTargetDerivRHS_continuous_for_edgeP
      (sol := sol) w haltCoordU
  have hk0 : ∀ τ ∈ Icc a b, 0 ≤ k τ := by
    intro τ hτ
    simpa [k, sol, selectorMUHoffGateCoeffP] using
      paper3NW4_zKernel_nonneg w w (le_trans ha0 hτ.1)
  have hmderiv : ∀ τ ∈ Icc a b, HasDerivAt m (mdot τ) τ := by
    intro τ hτ
    have ht0 := le_trans ha0 hτ.1
    simpa [m, mdot] using
      SelectorReplicatorDynSol.mixTarget_hasDerivAt_ode (sol w)
        (selectorSchedule_domain_of_nonneg_structural τ ht0) haltCoordU
  have hyode : ∀ τ ∈ Icc a b,
      HasDerivAt y (k τ * (m τ - y τ)) τ := by
    intro τ hτ
    have ht0 := le_trans ha0 hτ.1
    simpa [y, m, k, selectorMUHoffGateCoeffP] using
      (sol w).z_hasDeriv τ
        (selectorSchedule_domain_of_nonneg_structural τ ht0) haltCoordU
  have hscalar := stack_write_tracking_total_variation_le y m k mdot hab
    hkcont hk0 hmcont hmdotcont hmderiv hyode
  have hcap : (∫ τ in a..b, paper3HeadlineHoffIntegrandNW w τ) ≤
      ∫ τ in a..b, k τ * |m τ - y τ| := by
    apply intervalIntegral.integral_mono_on hab
      ((selectorMUHoffIntegrandP_continuous
        (p := bgpParamsNW w) (sol := sol) w).intervalIntegrable a b)
      ((hkcont.mul ((hmcont.sub hycont).abs)).intervalIntegrable a b)
    intro τ hτ
    change selectorMUHoffIntegrandP sol w τ ≤ k τ * |m τ - y τ|
    rw [show selectorMUHoffIntegrandP sol w τ = |k τ * (m τ - y τ)| by
      simp [selectorMUHoffIntegrandP, selectorMUHoffGateCoeffP, k, m, y, sol],
      abs_mul, abs_of_nonneg (hk0 τ hτ)]
  exact hcap.trans (by simpa [a, b, y, m, k, mdot, sol] using hscalar)

/-! ## Cap assembly -/

private theorem paper3Hoff_middleCapNW_le_budget_div_32 (w j : ℕ) :
    selectorMUHoffMiddleEnvelopeFullCapNW w j ≤
      selectorMUHoffEdgeBudget3992 j / 32 :=
  (selectorMUHoffMiddleEnvelopeFullCapNW_le_old_middle_budget w j).trans
    (paper3HeadlineHoff_middleFullCap_le_edgeBudget_div_32 j)

private theorem paper3Hoff_capLeft_le_three_budget_div_32 (w j : ℕ) :
    paper3HeadlineHoffCapLeftFieldNW w j ≤
      3 * (selectorMUHoffEdgeBudget3992 j / 32) := by
  have hab := selectorMUInterReadStart_le_zOffStart j
  have ha0 : 0 ≤ selectorMUInterReadStart j := by
    unfold selectorMUInterReadStart selectorMUWriteReadTime
    positivity
  let k : ℝ → ℝ := fun τ => selectorMUHoffGateCoeffP
    (p := bgpParamsNW w) (paper3HeadlineSolFamNW w) w τ
  let e : ℝ → ℝ := fun τ =>
    |selectorMixTarget branchU ((paper3HeadlineSolFamNW w) w).u
        ((paper3HeadlineSolFamNW w) w).lam τ haltCoordU -
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU|
  let loser : ℝ → ℝ := paper3HoffOldLoserNW w j
  have hkcont : Continuous k := by
    simpa [k] using selectorMUHoffGateCoeffP_continuous
      (p := bgpParamsNW w) (sol := paper3HeadlineSolFamNW w) w
  have hecont : Continuous e :=
    (((paper3HeadlineSolFamNW w) w).cont_mixTarget haltCoordU).sub
      continuous_const |>.abs
  have hlcont : Continuous loser := by
    dsimp [loser, paper3HoffOldLoserNW]
    exact continuous_finsetSum _ (fun v _ =>
      ((paper3HeadlineSolFamNW w) w).cont_lam v)
  have hk0 : ∀ τ ∈ Icc (selectorMUInterReadStart j) (selectorMUZOffStart j),
      0 ≤ k τ := by
    intro τ hτ
    simpa [k, selectorMUHoffGateCoeffP] using
      paper3NW4_zKernel_nonneg w w (le_trans ha0 hτ.1)
  have hmono : (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
      k τ * e τ) ≤
      ∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
        k τ * loser τ := by
    apply intervalIntegral.integral_mono_on hab
      ((hkcont.mul hecont).intervalIntegrable _ _)
      ((hkcont.mul hlcont).intervalIntegrable _ _)
    intro τ hτ
    exact mul_le_mul_of_nonneg_left
      (paper3Hoff_mix_pointwise_le_oldLoser_NW w j (le_trans ha0 hτ.1))
      (hk0 τ hτ)
  have hbase := selectorMUHoff_fieldIntegral_le_initial_add_targetP
    (p := bgpParamsNW w) (sol := paper3HeadlineSolFamNW w)
    (by rw [bgpParamsNW_A_eq]; norm_num) w hab ha0
    (M := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU)
  have hz := paper3Hoff_z_readStart_le_budget_div_32_NW w j
  have hbad := paper3Hoff_left_oldLoserIntegral_le_budget_div_32_NW w j
  have hbase' : paper3HeadlineHoffCapLeftFieldNW w j ≤
      |((paper3HeadlineSolFamNW w) w).z (selectorMUInterReadStart j) haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| +
      2 * (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
        k τ * e τ) := by
    simpa [paper3HeadlineHoffCapLeftFieldNW,
      paper3HeadlineHoffIntegrandNW, k, e] using hbase
  have hmono' : (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
      k τ * e τ) ≤ selectorMUHoffEdgeBudget3992 j / 32 := by
    exact hmono.trans (by simpa [k, loser] using hbad)
  linarith

private theorem paper3Hoff_zoff_error_le_five_budget_div_32_NW
    (w j : ℕ) (henc : selectorMUHaltEncConst (solMUReplStaticCfg w) j) :
    |((paper3HeadlineSolFamNW w) w).z (selectorMUZOffEnd j) haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤
      5 * (selectorMUHoffEdgeBudget3992 j / 32) := by
  have hread := paper3Hoff_z_readStart_le_budget_div_32_NW w j
  have hdrift := paper3Hoff_z_drift_read_to_zOffEnd_NW w j
  have hleft := paper3Hoff_capLeft_le_three_budget_div_32 w j
  have hmid := paper3Hoff_middleCapNW_le_budget_div_32 w j
  have htri := abs_sub_le
    (((paper3HeadlineSolFamNW w) w).z (selectorMUZOffEnd j) haltCoordU)
    (((paper3HeadlineSolFamNW w) w).z (selectorMUInterReadStart j) haltCoordU)
    (stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU)
  linarith

private theorem paper3Hoff_early_mix_z_le_seven_budget_div_32_NW
    (w j : ℕ) (henc : selectorMUHaltEncConst (solMUReplStaticCfg w) j) :
    |selectorMixTarget branchU ((paper3HeadlineSolFamNW w) w).u
        ((paper3HeadlineSolFamNW w) w).lam
        (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU -
      ((paper3HeadlineSolFamNW w) w).z
        (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU| ≤
      7 * (selectorMUHoffEdgeBudget3992 j / 32) := by
  let E : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let M : ℝ := stackMachineEncodingU.enc
    (solMUReplStaticCfg w (j + 1)) haltCoordU
  have hZ := paper3Hoff_zoff_error_le_five_budget_div_32_NW w j henc
  have hzE := paper3Hoff_z_early_le_zoff_add_budget_div_32_NW w j henc
  have hE0 : 0 ≤ E := by dsimp [E]; unfold selectorMUEarlyWriteSubStart; positivity
  have hmix := (paper3Hoff_mix_pointwise_le_badPair_NW w j hE0 henc).trans
    (paper3S4b_badMass_early_le_budget_div_32_NW w j)
  have htri := abs_sub_le
    (selectorMixTarget branchU ((paper3HeadlineSolFamNW w) w).u
      ((paper3HeadlineSolFamNW w) w).lam E haltCoordU) M
    (((paper3HeadlineSolFamNW w) w).z E haltCoordU)
  have hcomm := abs_sub_comm M
    (((paper3HeadlineSolFamNW w) w).z E haltCoordU)
  dsimp only [E, M] at hmix htri hcomm ⊢
  linarith

private theorem paper3Hoff_capRight_le_eighteen_budget_div_32_NW
    (w j : ℕ) (henc : selectorMUHaltEncConst (solMUReplStaticCfg w) j) :
    paper3HeadlineHoffCapRightFieldNW w j ≤
      18 * (selectorMUHoffEdgeBudget3992 j / 32) := by
  let Z : ℝ := selectorMUZOffEnd j
  let E : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let H : ℝ := selectorMUNextWriteStart j
  have hZE : Z ≤ E := by simpa [Z, E] using selectorMUZOffEnd_le_earlyWriteSubStart_succ j
  have hEH : E ≤ H := by
    dsimp [E, H]
    unfold selectorMUEarlyWriteSubStart selectorMUNextWriteStart selectorMUWriteHoldTime
    push_cast
    linarith [Real.pi_pos]
  have hZ0 : 0 ≤ Z := by dsimp [Z]; unfold selectorMUZOffEnd; positivity
  have hcross := paper3Hoff_fieldCap_le_readError_add_badIntegral_NW
    w j hZE hZ0 henc
  have hzZ := paper3Hoff_zoff_error_le_five_budget_div_32_NW w j henc
  have hbad := paper3Hoff_right_badIntegral_le_budget_div_32_NW w j
  have hcrossCap : (∫ τ in Z..E, paper3HeadlineHoffIntegrandNW w τ) ≤
      7 * (selectorMUHoffEdgeBudget3992 j / 32) := by
    dsimp only [Z, E] at hcross hzZ hbad ⊢
    linarith
  have hsuffix := paper3Hoff_suffixField_le_initial_add_TV_NW w j
  have hmixz := paper3Hoff_early_mix_z_le_seven_budget_div_32_NW w j henc
  have htv := paper3S4b_suffixTV_le_budget_div_8_NW w j henc
  have hsuffixCap : (∫ τ in E..H, paper3HeadlineHoffIntegrandNW w τ) ≤
      11 * (selectorMUHoffEdgeBudget3992 j / 32) := by
    have hb0 := paper3HeadlineHoff_edgeBudget3992_nonneg j
    dsimp only [E, H] at hsuffix hmixz htv ⊢
    linarith
  have hcont := selectorMUHoffIntegrandP_continuous
    (p := bgpParamsNW w) (sol := paper3HeadlineSolFamNW w) w
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) Z E)
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) E H)
  unfold paper3HeadlineHoffCapRightFieldNW
  change (∫ τ in Z..H, paper3HeadlineHoffIntegrandNW w τ) ≤ _
  have heq : (∫ τ in Z..H, paper3HeadlineHoffIntegrandNW w τ) =
      (∫ τ in Z..E, paper3HeadlineHoffIntegrandNW w τ) +
        ∫ τ in E..H, paper3HeadlineHoffIntegrandNW w τ := hsplit.symm
  rw [heq]
  linarith

private theorem paper3Hoff_capLeft_le_half_NW
    (w j : ℕ) :
    paper3HeadlineHoffCapLeftFieldNW w j ≤
      selectorMUHoffEdgeBudget3992 j / 2 := by
  have h := paper3Hoff_capLeft_le_three_budget_div_32 w j
  have hb0 := paper3HeadlineHoff_edgeBudget3992_nonneg j
  linarith

private theorem paper3Hoff_capRight_le_nineteen_budget_div_32_NW
    (w j : ℕ) (henc : selectorMUHaltEncConst (solMUReplStaticCfg w) j) :
    paper3HeadlineHoffCapRightFieldNW w j ≤
      19 * (selectorMUHoffEdgeBudget3992 j / 32) := by
  exact (paper3Hoff_capRight_le_eighteen_budget_div_32_NW w j henc).trans
    (by have hb0 := paper3HeadlineHoff_edgeBudget3992_nonneg j; linarith)

def paper3HeadlineHoffResidualNW : Paper3HeadlineHoffFieldIntegralResidualNW :=
  paper3HeadlineHoffFieldIntegralResidualNW_of_caps
    paper3HeadlineBoxInputsNW
    (fun w j => 3 * (selectorMUHoffEdgeBudget3992 j / 32))
    (fun w j => 19 * (selectorMUHoffEdgeBudget3992 j / 32))
    paper3Hoff_capLeft_le_three_budget_div_32
    paper3Hoff_capRight_le_nineteen_budget_div_32_NW
    (fun w j henc => by
      have hb0 := paper3HeadlineHoff_edgeBudget3992_nonneg j
      linarith)

end Ripple.BoundedUniversality.BGP
