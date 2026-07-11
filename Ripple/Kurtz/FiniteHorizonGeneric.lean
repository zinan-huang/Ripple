/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/

import Ripple.CTMC.DensityDependentAbsorbing
import Ripple.Kurtz.GronwallEventInclusion

/-!
# Dimension-generic finite-horizon Kurtz backbone

This file abstracts the finite-horizon convergence proof pattern for canonical
frozen density-dependent CTMCs.  System-specific inputs are isolated as
hypotheses: absorbing-state drift compatibility, conservative jumps, a uniform
continuous-time Doob L2 bound, a uniform instantaneous-QV bound, and elementary
regularity/boundedness facts for the mean-field solution.
-/

namespace Ripple

open MeasureTheory MeasureTheory.Measure Topology

namespace CTMC
namespace DensityDepCTMC

variable {d : ℕ}

/-- The canonical frozen initial condition equals the scaled lattice initial
state almost surely. -/
theorem canonical_frozenInitialCondition_eq_scaledState_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      M.frozenInitialCondition M.canonicalPathMap records =
        fun i => (↑(x₀ i) : ℝ) / ↑M.N := by
  filter_upwards
    [M.toQMatrix.canonicalRecordMeasure_record_zero_eq_init_ae x₀,
      M.toQMatrix.canonicalRecordMeasure_all_next_holdingTime_pos_ae_of_nonabsorbing x₀,
      M.toQMatrix.canonicalRecordMeasure_all_next_state_eq_current_ae_of_absorbing x₀]
    with records hrecord0 hpos hstay
  have hrecord0_eq : records 0 = (0, x₀) := by
    simpa using hrecord0
  have hrecord0_state : (records 0).2 = x₀ := by
    simpa using congrArg Prod.snd hrecord0_eq
  have hpos_all :
      ∀ n,
        ¬M.toQMatrix.IsAbsorbing
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) →
          0 < (records (n + 1)).1 := by
    simpa using hpos
  have hstay_all :
      ∀ n,
        M.toQMatrix.IsAbsorbing
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) →
          (records (n + 1)).2 =
            QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records) := by
    simpa using hstay
  have hfreeze : (M.canonicalPathMap records).frozenStateAt 0 = x₀ := by
    by_cases hAbs : M.toQMatrix.IsAbsorbing x₀
    · have hseq : ∀ n, (M.canonicalPathMap records).stateSeq n = x₀ := by
        intro n
        induction n with
        | zero =>
            simpa [DensityDepCTMC.canonicalPathMap,
              QMatrix.recordTrajectoryToPath_stateSeq] using hrecord0_state
        | succ n ih =>
            have hcur :
                QMatrix.currentStateFromHistory
                    (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records) = x₀ := by
              simpa [DensityDepCTMC.canonicalPathMap,
                QMatrix.currentStateFromHistory_frestrictLe] using ih
            have hnext := hstay_all n (by simpa [hcur] using hAbs)
            have hnext_state : (records (n + 1)).2 = x₀ := by
              simpa [hcur] using hnext
            simpa [DensityDepCTMC.canonicalPathMap,
              QMatrix.recordTrajectoryToPath_stateSeq] using hnext_state
      let path := M.canonicalPathMap records
      have hseq_path : ∀ n, path.stateSeq n = x₀ := hseq
      by_cases hex : ∃ n, (0 : ℝ) < path.times n
      · let n := Nat.find hex
        have hmin : ∀ k ∈ Finset.range n, ¬ (0 : ℝ) < path.times k := by
          intro k hk
          exact Nat.find_min hex (Finset.mem_range.mp hk)
        rw [path.frozenStateAt_eq_stateSeq_of_first_time_gt 0 n
          (Nat.find_spec hex) hmin, hseq_path n]
      · have hno : ∀ n, ¬ (0 : ℝ) < path.times n := by
          intro n hn
          exact hex ⟨n, hn⟩
        have hstable : path.stateSeq 0 = path.stateSeq (0 + 1) := by
          rw [hseq_path 0, hseq_path 1]
        have hmin : ∀ k ∈ Finset.range 0,
            path.stateSeq k ≠ path.stateSeq (k + 1) := by
          intro k hk
          simp at hk
        rw [path.frozenStateAt_eq_stateSeq_of_first_stable 0 0 hno hstable hmin,
          hseq_path 0]
    · have hcur0 :
          QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) 0 (Preorder.frestrictLe 0 records) = x₀ := by
        simpa [QMatrix.currentStateFromHistory] using hrecord0_state
      have hhold : 0 < (records 1).1 := hpos_all 0 (by simpa [hcur0] using hAbs)
      have htime0 : 0 < (M.canonicalPathMap records).times 0 := by
        simpa [DensityDepCTMC.canonicalPathMap,
          QMatrix.recordTrajectoryToPath_times_zero] using hhold
      rw [(M.canonicalPathMap records).frozenStateAt_before_first 0 htime0]
      simpa [DensityDepCTMC.canonicalPathMap,
        QMatrix.recordTrajectoryToPath_init] using hrecord0_state
  ext i
  simp [DensityDepCTMC.frozenInitialCondition, DensityDepCTMC.frozenDensityProcess, hfreeze]

end DensityDepCTMC
end CTMC

namespace Kurtz

open Set

private lemma setIntegral_Icc_eq_intervalIntegral_of_le
    {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    (∫ s in Set.Icc a b, f s) = ∫ s in a..b, f s := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]

variable {d : ℕ} {Γ : RateSpec d}

/-- Uniform continuous-time Doob L2 input for the frozen canonical martingale. -/
def FrozenDoobL2 (Γ : RateSpec d) (A : ℝ) : Prop :=
  ∀ (N : ℕ) (hN : 0 < N)
    (x₀ : Fin d → Fin (N + 1))
    (_hinit : (CTMC.DensityDepCTMC.mk N hN Γ).InSimplex x₀),
    ∀ T > 0,
      let M : CTMC.DensityDepCTMC d := CTMC.DensityDepCTMC.mk N hN Γ
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      A * ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
        ∂M.canonicalRecordMeasure x₀

/-- Uniform `O(T/N)` frozen martingale bound from a Doob L2 hypothesis and a
uniform instantaneous-QV rate bound. -/
theorem frozen_martingale_qv_bound_uniform_of_doob
    (Γ : RateSpec d) {A : ℝ} (hA_pos : 0 < A)
    (hDoob : FrozenDoobL2 Γ A)
    (hQVRate : ∃ C₀ > 0, ∀ (N : ℕ) (hN : 0 < N)
      (x : Fin d → Fin (N + 1)),
        (CTMC.DensityDepCTMC.mk N hN Γ).instantQVRate x ≤ C₀ / (N : ℝ))
    {T : ℝ} (hT : 0 < T) :
    ∃ C_qv > 0, ∀ (N : ℕ) (hN : 0 < N)
      (x₀ : Fin d → Fin (N + 1))
      (_hinit : (CTMC.DensityDepCTMC.mk N hN Γ).InSimplex x₀),
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖(CTMC.DensityDepCTMC.mk N hN Γ).frozenMartingalePart
          (CTMC.DensityDepCTMC.mk N hN Γ).canonicalPathMap s records‖ ^ 2
      ∂(CTMC.DensityDepCTMC.mk N hN Γ).canonicalRecordMeasure x₀
      ≤ C_qv * T / ↑N := by
  obtain ⟨C₀, hC₀_pos, hqv_rate⟩ := hQVRate
  refine ⟨A * C₀, mul_pos hA_pos hC₀_pos, ?_⟩
  intro N hN x₀ hinit
  let M : CTMC.DensityDepCTMC d := CTMC.DensityDepCTMC.mk N hN Γ
  have h_pointwise : ∀ records : M.canonicalRecordΩ,
      ∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s)
      ≤ C₀ / ↑N * T := by
    intro records
    have h_vol : MeasureTheory.volume.real (Set.Icc (0 : ℝ) T) = T := by
      rw [_root_.MeasureTheory.Measure.real_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ T - 0)]
      ring
    calc
      ∫ s in Set.Icc (0 : ℝ) T,
          M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s)
        ≤ ‖∫ s in Set.Icc (0 : ℝ) T,
            M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s)‖ :=
          le_abs_self _
      _ ≤ C₀ / ↑N * MeasureTheory.volume.real (Set.Icc (0 : ℝ) T) :=
          MeasureTheory.norm_setIntegral_le_of_norm_le_const
            measure_Icc_lt_top (fun s _hs => by
              rw [Real.norm_eq_abs, abs_of_nonneg (M.instantQVRate_nonneg _)]
              exact hqv_rate N hN _)
      _ = C₀ / ↑N * T := by rw [h_vol]
  have h_expect_bound :
      ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
        ∂M.canonicalRecordMeasure x₀ ≤ C₀ / ↑N * T := by
    calc
      ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
        ∂M.canonicalRecordMeasure x₀
          ≤ ∫ _records, (C₀ / ↑N * T) ∂M.canonicalRecordMeasure x₀ :=
            MeasureTheory.integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun records =>
                MeasureTheory.setIntegral_nonneg measurableSet_Icc
                  fun s _hs => M.instantQVRate_nonneg _)
              (_root_.MeasureTheory.integrable_const _)
              (Filter.Eventually.of_forall h_pointwise)
      _ = C₀ / ↑N * T := by simp [MeasureTheory.integral_const]
  have hdoobN := hDoob N hN x₀ hinit T hT
  calc
    ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖(CTMC.DensityDepCTMC.mk N hN Γ).frozenMartingalePart
          (CTMC.DensityDepCTMC.mk N hN Γ).canonicalPathMap s records‖ ^ 2
        ∂(CTMC.DensityDepCTMC.mk N hN Γ).canonicalRecordMeasure x₀
        = ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
            ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2
            ∂M.canonicalRecordMeasure x₀ := by
          simp [M]
    _ ≤ A * ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
        ∂M.canonicalRecordMeasure x₀ := hdoobN
    _ ≤ A * (C₀ / ↑N * T) :=
        mul_le_mul_of_nonneg_left h_expect_bound (le_of_lt hA_pos)
    _ = A * C₀ * T / ↑N := by ring

/-- Componentwise fundamental theorem of calculus for a mean-field solution,
assuming interval integrability of the drift component on `[0,t]`. -/
theorem meanField_component_sub_eq_integral
    (mf : MeanFieldSolution d Γ)
    (hInt : ∀ i : Fin d, ∀ {t : ℝ}, 0 ≤ t →
      IntervalIntegrable
        (fun s : ℝ => (Γ.drift (mf.sol s)) i)
        MeasureTheory.volume (0 : ℝ) t)
    (i : Fin d) {t : ℝ} (ht : 0 ≤ t) :
    mf.sol t i - mf.sol 0 i =
      ∫ s in (0 : ℝ)..t, (Γ.drift (mf.sol s)) i := by
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hasDerivAt_pi.mp
      (mf.sol_ode s ((by simpa [Set.uIcc_of_le ht] using hs : s ∈ Set.Icc 0 t).1)) i)
    (hInt i ht)).symm

set_option maxHeartbeats 800000 in
-- The generic bounded-integrability proof unfolds measurability of finite product
-- paths and norm bounds; the half-exp specialization already needs this budget.
/-- Integrability of the frozen-process error integrand on a finite horizon. -/
theorem integrableOn_frozen_error_mul_lipschitz_generic
    (M : CTMC.DensityDepCTMC d) (mf : MeanFieldSolution d M.rateSpec)
    (hSolMeas : Measurable mf.sol)
    (hSolBound : ∀ t : ℝ, 0 ≤ t → ‖mf.sol t‖ ≤ 1)
    (L : ℝ) (hL_nn : 0 ≤ L)
    {T : ℝ} (hT : 0 < T)
    (ω : M.canonicalRecordΩ) :
    MeasureTheory.IntegrableOn
      (fun s => L * ‖M.frozenDensityProcess M.canonicalPathMap s ω - mf.sol s‖)
      (Set.uIcc (0 : ℝ) T) MeasureTheory.volume := by
  rw [Set.uIcc_of_le (le_of_lt hT)]
  have hpair : Measurable (fun s : ℝ => ((s, ω) : ℝ × M.canonicalRecordΩ)) :=
    Measurable.prodMk measurable_id measurable_const
  have hX_raw : Measurable (fun s : ℝ =>
      M.frozenDensityProcess M.canonicalPathMap s ω) :=
    M.measurable_prod_canonicalFrozenDensityProcess.comp hpair
  have hdiff_meas : Measurable (fun s : ℝ =>
      M.frozenDensityProcess M.canonicalPathMap s ω - mf.sol s) := by
    rw [measurable_pi_iff]
    intro i
    exact ((measurable_pi_apply i).comp hX_raw).sub
      ((measurable_pi_apply i).comp hSolMeas)
  have hg_meas : Measurable (fun s : ℝ =>
      L * ‖M.frozenDensityProcess M.canonicalPathMap s ω - mf.sol s‖) :=
    (measurable_norm.comp hdiff_meas).const_mul L
  refine MeasureTheory.IntegrableOn.of_bound measure_Icc_lt_top
    hg_meas.aestronglyMeasurable (L * 2) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hL_nn (norm_nonneg _))]
  have h1 := M.frozenDensityProcess_norm_le M.canonicalPathMap s ω
  have h2 := hSolBound s hs.1
  have h3 := norm_sub_le (M.frozenDensityProcess M.canonicalPathMap s ω) (mf.sol s)
  nlinarith

set_option maxHeartbeats 800000 in
-- The pathwise inclusion packages the full componentwise Gronwall estimate in
-- arbitrary dimension; elaboration is comparable to the original concrete proof.
/-- Uniform pathwise Gronwall event inclusion for canonical frozen density
processes. -/
theorem frozen_event_inclusion_generic
    (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (hDriftZero : ∀ (N : ℕ) (hN : 0 < N),
      (CTMC.DensityDepCTMC.mk N hN Γ).DriftZeroAtAbsorbingOnSimplex)
    (hConservative : ∀ (N : ℕ) (hN : 0 < N),
      (CTMC.DensityDepCTMC.mk N hN Γ).ConservativeJumps)
    (hSolBound : ∀ t : ℝ, 0 ≤ t → ‖mf.sol t‖ ≤ 1)
    (hSolMeas : Measurable mf.sol)
    (hSolDriftInt : ∀ i : Fin d, ∀ {t : ℝ}, 0 ≤ t →
      IntervalIntegrable
        (fun s : ℝ => (Γ.drift (mf.sol s)) i)
        MeasureTheory.volume (0 : ℝ) t)
    {T : ℝ} (hT : 0 < T) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (N : ℕ) (hN : 0 < N)
      (x₀ : Fin d → Fin (N + 1))
      (hinit : (CTMC.DensityDepCTMC.mk N hN Γ).InSimplex x₀),
      let M_ctmc : CTMC.DensityDepCTMC d := CTMC.DensityDepCTMC.mk N hN Γ
      let dp := M_ctmc.toFrozenDensityProcess x₀
        (hDriftZero N hN) (hConservative N hN) hinit
      ∀ᵐ ω ∂M_ctmc.canonicalRecordMeasure x₀,
        (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
            ‖dp.process t ω - mf.sol t‖ ≥ ε) →
          (‖dp.init ω - mf.x₀‖ ≥ δ) ∨
          (δ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
            ‖dp.martingale_part s ω‖ ^ 2) := by
  obtain ⟨L, hL_pos, hLip⟩ := Γ.drift_lipschitz_on_ball 1 one_pos
  have hL_nn : 0 ≤ L := le_of_lt hL_pos
  set C_exp := Real.exp (L * T)
  have hCexp_pos : 0 < C_exp := Real.exp_pos _
  set δ := ε / (2 * C_exp)
  have hδ_pos : 0 < δ := div_pos hε (mul_pos two_pos hCexp_pos)
  refine ⟨δ, hδ_pos, ?_⟩
  intro N hN x₀ hinit
  let M_ctmc : CTMC.DensityDepCTMC d := CTMC.DensityDepCTMC.mk N hN Γ
  let dp := M_ctmc.toFrozenDensityProcess x₀
    (hDriftZero N hN) (hConservative N hN) hinit
  have hrcont_ae :=
    M_ctmc.canonical_frozenDensityProcess_forall_continuousWithinAt_Ici_ae x₀
  obtain ⟨K_mart, _hK_pos, hK_bound⟩ :=
    M_ctmc.exists_frozenMartingalePart_norm_bound M_ctmc.canonicalPathMap T (le_of_lt hT)
  filter_upwards [hrcont_ae] with ω hrcont hsup
  have hint_uIcc : MeasureTheory.IntegrableOn
      (fun s => L * ‖dp.process s ω - mf.sol s‖)
      (Set.uIcc (0 : ℝ) T) MeasureTheory.volume := by
    simpa [M_ctmc, dp, CTMC.DensityDepCTMC.toFrozenDensityProcess] using
      integrableOn_frozen_error_mul_lipschitz_generic
        M_ctmc mf hSolMeas hSolBound L hL_nn hT ω
  have hint_Icc : MeasureTheory.IntegrableOn
      (fun s => L * ‖dp.process s ω - mf.sol s‖)
      (Set.Icc (0 : ℝ) T) MeasureTheory.volume := by
    rwa [Set.uIcc_of_le (le_of_lt hT)] at hint_uIcc
  exact gronwall_event_inclusion_pathwise_rightContinuous
    mf hT hL_nn
    (fun t => dp.process t ω)
    (dp.init ω)
    (fun t => dp.martingale_part t ω)
    (by
      intro x hx
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1).mpr
        (hint_Icc.mono_set (Set.Ioc_subset_Icc_self.trans
          (Set.Icc_subset_Icc_right (le_of_lt hx.2)))))
    (by
      intro x hx
      exact (((hrcont x).mono Set.Ioi_subset_Ici_self).sub
        (mf.sol_ode x hx.1).continuousAt.continuousWithinAt).norm.const_mul L)
    (by
      intro x hx
      exact ⟨Set.Icc 0 T, Icc_mem_nhdsGT_of_mem hx,
        hint_Icc.aestronglyMeasurable⟩)
    (by
      have hprim := intervalIntegral.continuousOn_primitive_interval hint_uIcc
      rwa [Set.uIcc_of_le (le_of_lt hT)] at hprim)
    (by
      intro t ht
      have hinner_bdd : BddAbove (Set.range fun _ : 0 ≤ t ∧ t ≤ T =>
          ‖dp.martingale_part t ω‖ ^ 2) :=
        ⟨K_mart ^ 2, by
          rintro y ⟨ht, rfl⟩
          have hb := hK_bound t ω ht.1 ht.2
          have : ‖dp.martingale_part t ω‖ ≤ K_mart := by
            simpa [M_ctmc, dp, CTMC.DensityDepCTMC.toFrozenDensityProcess] using hb
          nlinarith [norm_nonneg (dp.martingale_part t ω)]⟩
      have houter_bdd : BddAbove (Set.range fun s : ℝ =>
          ⨆ (_ : 0 ≤ s ∧ s ≤ T), ‖dp.martingale_part s ω‖ ^ 2) :=
        ⟨K_mart ^ 2, by
          rintro y ⟨s, rfl⟩
          exact Real.iSup_le (fun hs => by
            have hb := hK_bound s ω hs.1 hs.2
            have : ‖dp.martingale_part s ω‖ ≤ K_mart := by
              simpa [M_ctmc, dp, CTMC.DensityDepCTMC.toFrozenDensityProcess] using hb
            nlinarith [norm_nonneg (dp.martingale_part s ω)])
            (by positivity)⟩
      exact le_trans (le_ciSup hinner_bdd ⟨ht.1, ht.2⟩)
        (le_ciSup houter_bdd t))
    hε
    (by
      change
        ((∀ t₁ ∈ Set.Icc (0 : ℝ) T, ‖dp.martingale_part t₁ ω‖ ≤ δ) →
          ∀ t₁ ∈ Set.Icc (0 : ℝ) T,
            ‖dp.process t₁ ω - mf.sol t₁‖ ≤
              (‖dp.init ω - mf.x₀‖ + δ) +
                ∫ s in (0 : ℝ)..t₁, L * ‖dp.process s ω - mf.sol s‖)
      intro hM_bound t₁ ht₁
      apply (pi_norm_le_iff_of_nonneg (add_nonneg (add_nonneg (norm_nonneg _)
        (le_of_lt hδ_pos)) (intervalIntegral.integral_nonneg ht₁.1
          fun s _hs => mul_nonneg hL_nn (norm_nonneg _)))).mpr
      intro i
      have hmpart_def : dp.martingale_part t₁ ω i =
          dp.process t₁ ω i - dp.init ω i -
          (∫ s in Set.Icc (0 : ℝ) t₁,
            (Γ.drift (dp.process s ω)) i) := by
        rfl
      have hode_sub := meanField_component_sub_eq_integral mf hSolDriftInt i ht₁.1
      have hinit_eq := congr_fun mf.sol_init i
      have hconv := setIntegral_Icc_eq_intervalIntegral_of_le ht₁.1
        (fun s => (Γ.drift (dp.process s ω)) i)
      have herr : (dp.process t₁ ω - mf.sol t₁) i =
          (dp.init ω i - mf.x₀ i) +
          ((∫ s in (0 : ℝ)..t₁, (Γ.drift (dp.process s ω)) i) -
           (∫ s in (0 : ℝ)..t₁, (Γ.drift (mf.sol s)) i)) +
          dp.martingale_part t₁ ω i := by
        simp only [Pi.sub_apply]
        have hmpart_interval : dp.martingale_part t₁ ω i =
            dp.process t₁ ω i - dp.init ω i -
            (∫ s in (0 : ℝ)..t₁, (Γ.drift (dp.process s ω)) i) := by
          rw [hmpart_def, hconv]
        have hinit_eq' : mf.sol 0 i = mf.x₀ i := by
          simpa using hinit_eq
        have hode_sub' : mf.sol t₁ i - mf.x₀ i =
            ∫ s in (0 : ℝ)..t₁, (Γ.drift (mf.sol s)) i := by
          linarith
        linarith
      rw [Real.norm_eq_abs, herr]
      have htri1 := abs_add_le
        ((dp.init ω i - mf.x₀ i) +
          ((∫ s in (0 : ℝ)..t₁, (Γ.drift (dp.process s ω)) i) -
           (∫ s in (0 : ℝ)..t₁, (Γ.drift (mf.sol s)) i)))
        (dp.martingale_part t₁ ω i)
      have htri2 := abs_add_le
        (dp.init ω i - mf.x₀ i)
        ((∫ s in (0 : ℝ)..t₁, (Γ.drift (dp.process s ω)) i) -
         (∫ s in (0 : ℝ)..t₁, (Γ.drift (mf.sol s)) i))
      have h_init_bound : |dp.init ω i - mf.x₀ i| ≤ ‖dp.init ω - mf.x₀‖ := by
        rw [← Pi.sub_apply, ← Real.norm_eq_abs]
        exact norm_le_pi_norm _ i
      have h_mart_bound : |dp.martingale_part t₁ ω i| ≤ δ := by
        calc |dp.martingale_part t₁ ω i|
            = ‖dp.martingale_part t₁ ω i‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖dp.martingale_part t₁ ω‖ := norm_le_pi_norm _ i
          _ ≤ δ := hM_bound t₁ ht₁
      have hint_X_i : IntervalIntegrable
          (fun s => (Γ.drift (dp.process s ω)) i)
          MeasureTheory.volume (0 : ℝ) t₁ := by
        have hmeas : Measurable (fun s : ℝ =>
            (Γ.drift (dp.process s ω)) i) := by
          simpa [M_ctmc, dp, CTMC.DensityDepCTMC.toFrozenDensityProcess] using
            M_ctmc.measurable_canonicalFrozenDrift_component_section ω i
        obtain ⟨C, _hC, hbound⟩ := Γ.exists_drift_bound_on_ball 1 zero_lt_one
        have hIcc : MeasureTheory.IntegrableOn
            (fun s => (Γ.drift (dp.process s ω)) i)
            (Set.Icc (0 : ℝ) t₁) MeasureTheory.volume := by
          refine MeasureTheory.IntegrableOn.of_bound measure_Icc_lt_top
            hmeas.aestronglyMeasurable C ?_
          filter_upwards with s
          exact (norm_le_pi_norm (Γ.drift (dp.process s ω)) i).trans
            (hbound (dp.process s ω) (dp.process_norm_le_one s ω))
        exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht₁.1).mpr
          (hIcc.mono_set Set.Ioc_subset_Icc_self)
      have hint_sol_i := hSolDriftInt i ht₁.1
      have h_drift_bound :
          |(∫ s in (0 : ℝ)..t₁, (Γ.drift (dp.process s ω)) i) -
           (∫ s in (0 : ℝ)..t₁, (Γ.drift (mf.sol s)) i)| ≤
          ∫ s in (0 : ℝ)..t₁, L * ‖dp.process s ω - mf.sol s‖ := by
        have hdiff_int : IntervalIntegrable
            (fun s =>
              (Γ.drift (dp.process s ω)) i -
                (Γ.drift (mf.sol s)) i)
            MeasureTheory.volume (0 : ℝ) t₁ :=
          hint_X_i.sub hint_sol_i
        have h_abs_int : IntervalIntegrable
            (fun s =>
              |(Γ.drift (dp.process s ω)) i -
                (Γ.drift (mf.sol s)) i|)
            MeasureTheory.volume (0 : ℝ) t₁ :=
          hdiff_int.abs
        have hint_rhs : IntervalIntegrable
            (fun s => L * ‖dp.process s ω - mf.sol s‖)
            MeasureTheory.volume (0 : ℝ) t₁ := by
          exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht₁.1).mpr
            (hint_Icc.mono_set (Set.Ioc_subset_Icc_self.trans
              (Set.Icc_subset_Icc_right ht₁.2)))
        calc
          |(∫ s in (0 : ℝ)..t₁, (Γ.drift (dp.process s ω)) i) -
            (∫ s in (0 : ℝ)..t₁, (Γ.drift (mf.sol s)) i)|
              = |∫ s in (0 : ℝ)..t₁,
                  ((Γ.drift (dp.process s ω)) i -
                    (Γ.drift (mf.sol s)) i)| := by
                rw [intervalIntegral.integral_sub hint_X_i hint_sol_i]
          _ ≤ ∫ s in (0 : ℝ)..t₁,
                |(Γ.drift (dp.process s ω)) i -
                  (Γ.drift (mf.sol s)) i| :=
              intervalIntegral.abs_integral_le_integral_abs ht₁.1
          _ ≤ ∫ s in (0 : ℝ)..t₁, L * ‖dp.process s ω - mf.sol s‖ := by
              apply intervalIntegral.integral_mono_on ht₁.1 h_abs_int hint_rhs
              intro s hs
              have hcoord :
                  |(Γ.drift (dp.process s ω)) i -
                    (Γ.drift (mf.sol s)) i| ≤
                    ‖Γ.drift (dp.process s ω) - Γ.drift (mf.sol s)‖ := by
                rw [← Real.norm_eq_abs]
                convert norm_le_pi_norm
                  (Γ.drift (dp.process s ω) - Γ.drift (mf.sol s)) i using 1
              exact hcoord.trans
                (hLip (dp.process s ω) (mf.sol s)
                  (dp.process_norm_le_one s ω)
                  (hSolBound s hs.1))
      linarith [htri1, htri2, h_init_bound, h_mart_bound, h_drift_bound])
    hsup

set_option maxHeartbeats 800000 in
-- This theorem assembles the generic event inclusion, Markov step, and canonical
-- initial-condition ae argument; the quantified CTMC types make elaboration heavy.
/-- Generic finite-horizon Kurtz convergence for canonical frozen
density-dependent CTMCs. -/
theorem kurtz_finite_horizon_generic
    (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (hDriftZero : ∀ (N : ℕ) (hN : 0 < N),
      (CTMC.DensityDepCTMC.mk N hN Γ).DriftZeroAtAbsorbingOnSimplex)
    (hConservative : ∀ (N : ℕ) (hN : 0 < N),
      (CTMC.DensityDepCTMC.mk N hN Γ).ConservativeJumps)
    (hSolBound : ∀ t : ℝ, 0 ≤ t → ‖mf.sol t‖ ≤ 1)
    (hSolMeas : Measurable mf.sol)
    (hSolDriftInt : ∀ i : Fin d, ∀ {t : ℝ}, 0 ≤ t →
      IntervalIntegrable
        (fun s : ℝ => (Γ.drift (mf.sol s)) i)
        MeasureTheory.volume (0 : ℝ) t)
    {A_doob : ℝ} (hA_doob_pos : 0 < A_doob)
    (hDoob : FrozenDoobL2 Γ A_doob)
    (hQVRate : ∃ C₀ > 0, ∀ (N : ℕ) (hN : 0 < N)
      (x : Fin d → Fin (N + 1)),
        (CTMC.DensityDepCTMC.mk N hN Γ).instantQVRate x ≤ C₀ / (N : ℝ))
    {T : ℝ} (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (hN : 0 < N)
    (x₀ : Fin d → Fin (N + 1))
    (hinit : (CTMC.DensityDepCTMC.mk N hN Γ).InSimplex x₀)
    (_hinit_close :
      ‖(fun i => (↑(x₀ i) : ℝ) / ↑N) - mf.x₀‖ ≤ 1 / ↑N),
    (CTMC.DensityDepCTMC.mk N hN Γ).canonicalRecordMeasure x₀
      {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        ‖((CTMC.DensityDepCTMC.mk N hN Γ).toFrozenDensityProcess x₀
            (hDriftZero N hN) (hConservative N hN) hinit).process t ω -
          mf.sol t‖ > ε} ≤ ENNReal.ofReal η := by
  obtain ⟨C_qv, hC_qv_pos, hqv⟩ :=
    frozen_martingale_qv_bound_uniform_of_doob Γ hA_doob_pos hDoob hQVRate hT
  obtain ⟨δ, hδ_pos, h_event⟩ :=
    frozen_event_inclusion_generic Γ mf hDriftZero hConservative hSolBound
      hSolMeas hSolDriftInt hT hε
  refine ⟨max (Nat.ceil (1 / δ) + 1)
    (Nat.ceil (C_qv * T / (η * δ ^ 2)) + 1), ?_⟩
  intro N hN_ge hN x₀ hinit hinit_close
  set M_ctmc : CTMC.DensityDepCTMC d := CTMC.DensityDepCTMC.mk N hN Γ
  set dp := M_ctmc.toFrozenDensityProcess x₀
    (hDriftZero N hN) (hConservative N hN) hinit
  set μ := M_ctmc.canonicalRecordMeasure x₀
  let E : Set M_ctmc.canonicalRecordΩ :=
    {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        ‖dp.process t ω - mf.sol t‖ > ε}
  let I : Set M_ctmc.canonicalRecordΩ :=
    {ω | ‖dp.init ω - mf.x₀‖ ≥ δ}
  let A : Set M_ctmc.canonicalRecordΩ :=
    {ω | δ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖dp.martingale_part s ω‖ ^ 2}
  have hN_delta_nat : Nat.ceil (1 / δ) + 1 ≤ N :=
    (le_max_left _ _).trans hN_ge
  have hN_markov_nat : Nat.ceil (C_qv * T / (η * δ ^ 2)) + 1 ≤ N :=
    (le_max_right _ _).trans hN_ge
  have hN_pos_real : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hδ_sq_pos : 0 < δ ^ 2 := sq_pos_of_pos hδ_pos
  have hN_delta_real : 1 / δ < (N : ℝ) := by
    calc
      1 / δ ≤ (Nat.ceil (1 / δ) : ℝ) := Nat.le_ceil _
      _ < (Nat.ceil (1 / δ) + 1 : ℕ) := by
        exact_mod_cast Nat.lt_succ_self (Nat.ceil (1 / δ))
      _ ≤ (N : ℝ) := by
        exact_mod_cast hN_delta_nat
  have h_invN_lt_delta : 1 / (N : ℝ) < δ :=
    (one_div_lt hN_pos_real hδ_pos).2 hN_delta_real
  have hN_markov_real : C_qv * T / (η * δ ^ 2) < (N : ℝ) := by
    calc
      C_qv * T / (η * δ ^ 2)
          ≤ (Nat.ceil (C_qv * T / (η * δ ^ 2)) : ℝ) := Nat.le_ceil _
      _ < (Nat.ceil (C_qv * T / (η * δ ^ 2)) + 1 : ℕ) := by
        exact_mod_cast Nat.lt_succ_self (Nat.ceil (C_qv * T / (η * δ ^ (2 : ℕ))))
      _ ≤ (N : ℝ) := by
        exact_mod_cast hN_markov_nat
  have h_markov_real_target :
      C_qv * T / ((N : ℝ) * δ ^ 2) ≤ η := by
    have hden_pos : 0 < η * δ ^ 2 := mul_pos hη hδ_sq_pos
    have hmul : C_qv * T < (N : ℝ) * (η * δ ^ 2) := by
      rwa [div_lt_iff₀ hden_pos] at hN_markov_real
    have hden2_pos : 0 < (N : ℝ) * δ ^ 2 := mul_pos hN_pos_real hδ_sq_pos
    rw [div_le_iff₀ hden2_pos]
    nlinarith
  have h_event_ae : ∀ᵐ ω ∂μ,
      (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
          ‖dp.process t ω - mf.sol t‖ ≥ ε) →
        (‖dp.init ω - mf.x₀‖ ≥ δ) ∨
        (δ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖dp.martingale_part s ω‖ ^ 2) := by
    simpa [μ, M_ctmc, dp] using h_event N hN x₀ hinit
  have hstep1 : μ E ≤ μ I + μ A := by
    have hae : ∀ᵐ ω ∂μ, ω ∈ E → ω ∈ I ∪ A := by
      filter_upwards [h_event_ae] with ω hω hE
      rcases hω (le_of_lt hE) with hinit_bad | hmart_bad
      · exact Or.inl hinit_bad
      · exact Or.inr hmart_bad
    calc
      μ E ≤ μ (I ∪ A) := _root_.MeasureTheory.measure_mono_ae hae
      _ ≤ μ I + μ A := _root_.MeasureTheory.measure_union_le I A
  have hinit_eq_ae : ∀ᵐ ω ∂μ,
      dp.init ω = (fun i => (↑(x₀ i) : ℝ) / ↑N) := by
    have h := M_ctmc.canonical_frozenInitialCondition_eq_scaledState_ae x₀
    simpa [μ, M_ctmc, dp, CTMC.DensityDepCTMC.toFrozenDensityProcess] using h
  have hI_zero : μ I = 0 := by
    rw [_root_.MeasureTheory.measure_eq_zero_iff_ae_notMem]
    filter_upwards [hinit_eq_ae] with ω hω hωI
    have hclose : ‖dp.init ω - mf.x₀‖ ≤ 1 / (N : ℝ) := by
      rw [hω]
      simpa [one_div] using hinit_close
    exact (not_le_of_gt (lt_of_le_of_lt hclose h_invN_lt_delta)) hωI
  have hA_le : μ A ≤ ENNReal.ofReal η := by
    have hmark :=
      _root_.MeasureTheory.mul_meas_ge_le_integral_of_nonneg
        (by simpa [μ, dp, A] using dp.martingale_sup_sq_nonneg T hT)
        (by simpa [μ, dp, A] using dp.martingale_sup_sq_integrable T hT)
        (δ ^ 2)
    have hqvN : ∫ ω, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖dp.martingale_part s ω‖ ^ 2 ∂μ ≤ C_qv * T / ↑N := by
      have hraw := hqv N hN x₀ hinit
      simpa [μ, M_ctmc, dp, CTMC.DensityDepCTMC.toFrozenDensityProcess] using hraw
    have hreal : μ.real A ≤ η := by
      have h1 : δ ^ 2 * μ.real A ≤ C_qv * T / ↑N := by
        simpa [A] using hmark.trans hqvN
      have hA_to_qv : μ.real A ≤ C_qv * T / ((N : ℝ) * δ ^ 2) := by
        rw [le_div_iff₀ (mul_pos hN_pos_real hδ_sq_pos)]
        have h2 : (N : ℝ) * (δ ^ 2 * μ.real A) ≤
            (N : ℝ) * (C_qv * T / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 hN_pos_real.le
        rw [mul_div_cancel₀ _ (ne_of_gt hN_pos_real)] at h2
        linarith [show μ.real A * ((N : ℝ) * δ ^ 2) =
          (N : ℝ) * (δ ^ 2 * μ.real A) by ring]
      exact hA_to_qv.trans h_markov_real_target
    have hA_ne_top : μ A ≠ ⊤ := _root_.MeasureTheory.measure_ne_top μ A
    exact (ENNReal.le_ofReal_iff_toReal_le hA_ne_top hη.le).2 hreal
  calc
    μ E ≤ μ I + μ A := hstep1
    _ = μ A := by rw [hI_zero, zero_add]
    _ ≤ ENNReal.ofReal η := hA_le

set_option maxHeartbeats 800000 in
/-- Generic Kurtz convergence taking a direct martingale sup bound.
Replaces FrozenDoobL2 + QVRate with a single C·T/N bound on
E[sup ‖martingale_part‖²].  Use when FrozenDoobL2 is unavailable
(e.g. boundary-compatibility fails). -/
theorem kurtz_finite_horizon_generic_v2
    (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (hDriftZero : ∀ (N : ℕ) (hN : 0 < N),
      (CTMC.DensityDepCTMC.mk N hN Γ).DriftZeroAtAbsorbingOnSimplex)
    (hConservative : ∀ (N : ℕ) (hN : 0 < N),
      (CTMC.DensityDepCTMC.mk N hN Γ).ConservativeJumps)
    (hSolBound : ∀ t : ℝ, 0 ≤ t → ‖mf.sol t‖ ≤ 1)
    (hSolMeas : Measurable mf.sol)
    (hSolDriftInt : ∀ i : Fin d, ∀ {t : ℝ}, 0 ≤ t →
      IntervalIntegrable
        (fun s : ℝ => (Γ.drift (mf.sol s)) i)
        MeasureTheory.volume (0 : ℝ) t)
    {T : ℝ} (hT : 0 < T)
    {C_qv : ℝ} (hC_qv_pos : 0 < C_qv)
    (hqv : ∀ (N : ℕ) (hN : 0 < N)
      (x₀ : Fin d → Fin (N + 1))
      (_hinit : (CTMC.DensityDepCTMC.mk N hN Γ).InSimplex x₀)
      (_hclose : ‖(fun i => (↑(x₀ i) : ℝ) / ↑N) - mf.x₀‖ ≤ 1 / ↑N),
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖(CTMC.DensityDepCTMC.mk N hN Γ).frozenMartingalePart
          (CTMC.DensityDepCTMC.mk N hN Γ).canonicalPathMap s records‖ ^ 2
      ∂(CTMC.DensityDepCTMC.mk N hN Γ).canonicalRecordMeasure x₀
      ≤ C_qv * T / ↑N)
    (ε : ℝ) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (hN : 0 < N)
    (x₀ : Fin d → Fin (N + 1))
    (hinit : (CTMC.DensityDepCTMC.mk N hN Γ).InSimplex x₀)
    (_hinit_close :
      ‖(fun i => (↑(x₀ i) : ℝ) / ↑N) - mf.x₀‖ ≤ 1 / ↑N),
    (CTMC.DensityDepCTMC.mk N hN Γ).canonicalRecordMeasure x₀
      {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        ‖((CTMC.DensityDepCTMC.mk N hN Γ).toFrozenDensityProcess x₀
            (hDriftZero N hN) (hConservative N hN) hinit).process t ω -
          mf.sol t‖ > ε} ≤ ENNReal.ofReal η := by
  obtain ⟨δ, hδ_pos, h_event⟩ :=
    frozen_event_inclusion_generic Γ mf hDriftZero hConservative hSolBound
      hSolMeas hSolDriftInt hT hε
  refine ⟨max (Nat.ceil (1 / δ) + 1)
    (Nat.ceil (C_qv * T / (η * δ ^ 2)) + 1), ?_⟩
  intro N hN_ge hN x₀ hinit hinit_close
  set M_ctmc : CTMC.DensityDepCTMC d := CTMC.DensityDepCTMC.mk N hN Γ
  set dp := M_ctmc.toFrozenDensityProcess x₀
    (hDriftZero N hN) (hConservative N hN) hinit
  set μ := M_ctmc.canonicalRecordMeasure x₀
  let E : Set M_ctmc.canonicalRecordΩ :=
    {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        ‖dp.process t ω - mf.sol t‖ > ε}
  let I : Set M_ctmc.canonicalRecordΩ :=
    {ω | ‖dp.init ω - mf.x₀‖ ≥ δ}
  let A : Set M_ctmc.canonicalRecordΩ :=
    {ω | δ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖dp.martingale_part s ω‖ ^ 2}
  have hN_delta_nat : Nat.ceil (1 / δ) + 1 ≤ N :=
    (le_max_left _ _).trans hN_ge
  have hN_markov_nat : Nat.ceil (C_qv * T / (η * δ ^ 2)) + 1 ≤ N :=
    (le_max_right _ _).trans hN_ge
  have hN_pos_real : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hδ_sq_pos : 0 < δ ^ 2 := sq_pos_of_pos hδ_pos
  have hN_delta_real : 1 / δ < (N : ℝ) := by
    calc
      1 / δ ≤ (Nat.ceil (1 / δ) : ℝ) := Nat.le_ceil _
      _ < (Nat.ceil (1 / δ) + 1 : ℕ) := by
        exact_mod_cast Nat.lt_succ_self (Nat.ceil (1 / δ))
      _ ≤ (N : ℝ) := by
        exact_mod_cast hN_delta_nat
  have h_invN_lt_delta : 1 / (N : ℝ) < δ :=
    (one_div_lt hN_pos_real hδ_pos).2 hN_delta_real
  have hN_markov_real : C_qv * T / (η * δ ^ 2) < (N : ℝ) := by
    calc
      C_qv * T / (η * δ ^ 2)
          ≤ (Nat.ceil (C_qv * T / (η * δ ^ 2)) : ℝ) := Nat.le_ceil _
      _ < (Nat.ceil (C_qv * T / (η * δ ^ 2)) + 1 : ℕ) := by
        exact_mod_cast Nat.lt_succ_self (Nat.ceil (C_qv * T / (η * δ ^ (2 : ℕ))))
      _ ≤ (N : ℝ) := by
        exact_mod_cast hN_markov_nat
  have h_markov_real_target :
      C_qv * T / ((N : ℝ) * δ ^ 2) ≤ η := by
    have hden_pos : 0 < η * δ ^ 2 := mul_pos hη hδ_sq_pos
    have hmul : C_qv * T < (N : ℝ) * (η * δ ^ 2) := by
      rwa [div_lt_iff₀ hden_pos] at hN_markov_real
    have hden2_pos : 0 < (N : ℝ) * δ ^ 2 := mul_pos hN_pos_real hδ_sq_pos
    rw [div_le_iff₀ hden2_pos]
    nlinarith
  have h_event_ae : ∀ᵐ ω ∂μ,
      (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
          ‖dp.process t ω - mf.sol t‖ ≥ ε) →
        (‖dp.init ω - mf.x₀‖ ≥ δ) ∨
        (δ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖dp.martingale_part s ω‖ ^ 2) := by
    simpa [μ, M_ctmc, dp] using h_event N hN x₀ hinit
  have hstep1 : μ E ≤ μ I + μ A := by
    have hae : ∀ᵐ ω ∂μ, ω ∈ E → ω ∈ I ∪ A := by
      filter_upwards [h_event_ae] with ω hω hE
      rcases hω (le_of_lt hE) with hinit_bad | hmart_bad
      · exact Or.inl hinit_bad
      · exact Or.inr hmart_bad
    calc
      μ E ≤ μ (I ∪ A) := _root_.MeasureTheory.measure_mono_ae hae
      _ ≤ μ I + μ A := _root_.MeasureTheory.measure_union_le I A
  have hinit_eq_ae : ∀ᵐ ω ∂μ,
      dp.init ω = (fun i => (↑(x₀ i) : ℝ) / ↑N) := by
    have h := M_ctmc.canonical_frozenInitialCondition_eq_scaledState_ae x₀
    simpa [μ, M_ctmc, dp, CTMC.DensityDepCTMC.toFrozenDensityProcess] using h
  have hI_zero : μ I = 0 := by
    rw [_root_.MeasureTheory.measure_eq_zero_iff_ae_notMem]
    filter_upwards [hinit_eq_ae] with ω hω hωI
    have hclose : ‖dp.init ω - mf.x₀‖ ≤ 1 / (N : ℝ) := by
      rw [hω]
      simpa [one_div] using hinit_close
    exact (not_le_of_gt (lt_of_le_of_lt hclose h_invN_lt_delta)) hωI
  have hA_le : μ A ≤ ENNReal.ofReal η := by
    have hmark :=
      _root_.MeasureTheory.mul_meas_ge_le_integral_of_nonneg
        (by simpa [μ, dp, A] using dp.martingale_sup_sq_nonneg T hT)
        (by simpa [μ, dp, A] using dp.martingale_sup_sq_integrable T hT)
        (δ ^ 2)
    have hqvN : ∫ ω, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖dp.martingale_part s ω‖ ^ 2 ∂μ ≤ C_qv * T / ↑N := by
      have hraw := hqv N hN x₀ hinit hinit_close
      simpa [μ, M_ctmc, dp, CTMC.DensityDepCTMC.toFrozenDensityProcess] using hraw
    have hreal : μ.real A ≤ η := by
      have h1 : δ ^ 2 * μ.real A ≤ C_qv * T / ↑N := by
        simpa [A] using hmark.trans hqvN
      have hA_to_qv : μ.real A ≤ C_qv * T / ((N : ℝ) * δ ^ 2) := by
        rw [le_div_iff₀ (mul_pos hN_pos_real hδ_sq_pos)]
        have h2 : (N : ℝ) * (δ ^ 2 * μ.real A) ≤
            (N : ℝ) * (C_qv * T / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 hN_pos_real.le
        rw [mul_div_cancel₀ _ (ne_of_gt hN_pos_real)] at h2
        linarith [show μ.real A * ((N : ℝ) * δ ^ 2) =
          (N : ℝ) * (δ ^ 2 * μ.real A) by ring]
      exact hA_to_qv.trans h_markov_real_target
    have hA_ne_top : μ A ≠ ⊤ := _root_.MeasureTheory.measure_ne_top μ A
    exact (ENNReal.le_ofReal_iff_toReal_le hA_ne_top hη.le).2 hreal
  calc
    μ E ≤ μ I + μ A := hstep1
    _ = μ A := by rw [hI_zero, zero_add]
    _ ≤ ENNReal.ofReal η := hA_le

set_option maxHeartbeats 800000 in
/-- Variant of `kurtz_finite_horizon_generic_v2` where the QV bound `hqv`
only needs to hold for initial states x₀ that are close to the mean-field
initial condition (within 1/N). Useful when boundary compatibility fails
but the QV bound can be established for nearby initial states. -/
theorem kurtz_finite_horizon_generic_v3
    (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (hDriftZero : ∀ (N : ℕ) (hN : 0 < N),
      (CTMC.DensityDepCTMC.mk N hN Γ).DriftZeroAtAbsorbingOnSimplex)
    (hConservative : ∀ (N : ℕ) (hN : 0 < N),
      (CTMC.DensityDepCTMC.mk N hN Γ).ConservativeJumps)
    (hSolBound : ∀ t : ℝ, 0 ≤ t → ‖mf.sol t‖ ≤ 1)
    (hSolMeas : Measurable mf.sol)
    (hSolDriftInt : ∀ i : Fin d, ∀ {t : ℝ}, 0 ≤ t →
      IntervalIntegrable
        (fun s : ℝ => (Γ.drift (mf.sol s)) i)
        MeasureTheory.volume (0 : ℝ) t)
    {T : ℝ} (hT : 0 < T)
    {C_qv : ℝ} (hC_qv_pos : 0 < C_qv)
    (hqv : ∀ (N : ℕ) (hN : 0 < N)
      (x₀ : Fin d → Fin (N + 1))
      (_hinit : (CTMC.DensityDepCTMC.mk N hN Γ).InSimplex x₀)
      (_hinit_close : ‖(fun i => (↑(x₀ i) : ℝ) / ↑N) - mf.x₀‖ ≤ 1 / ↑N),
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖(CTMC.DensityDepCTMC.mk N hN Γ).frozenMartingalePart
          (CTMC.DensityDepCTMC.mk N hN Γ).canonicalPathMap s records‖ ^ 2
      ∂(CTMC.DensityDepCTMC.mk N hN Γ).canonicalRecordMeasure x₀
      ≤ C_qv * T / ↑N)
    (ε : ℝ) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (hN : 0 < N)
    (x₀ : Fin d → Fin (N + 1))
    (hinit : (CTMC.DensityDepCTMC.mk N hN Γ).InSimplex x₀)
    (_hinit_close :
      ‖(fun i => (↑(x₀ i) : ℝ) / ↑N) - mf.x₀‖ ≤ 1 / ↑N),
    (CTMC.DensityDepCTMC.mk N hN Γ).canonicalRecordMeasure x₀
      {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        ‖((CTMC.DensityDepCTMC.mk N hN Γ).toFrozenDensityProcess x₀
            (hDriftZero N hN) (hConservative N hN) hinit).process t ω -
          mf.sol t‖ > ε} ≤ ENNReal.ofReal η := by
  obtain ⟨δ, hδ_pos, h_event⟩ :=
    frozen_event_inclusion_generic Γ mf hDriftZero hConservative hSolBound
      hSolMeas hSolDriftInt hT hε
  refine ⟨max (Nat.ceil (1 / δ) + 1)
    (Nat.ceil (C_qv * T / (η * δ ^ 2)) + 1), ?_⟩
  intro N hN_ge hN x₀ hinit hinit_close
  set M_ctmc : CTMC.DensityDepCTMC d := CTMC.DensityDepCTMC.mk N hN Γ
  set dp := M_ctmc.toFrozenDensityProcess x₀
    (hDriftZero N hN) (hConservative N hN) hinit
  set μ := M_ctmc.canonicalRecordMeasure x₀
  let E : Set M_ctmc.canonicalRecordΩ :=
    {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        ‖dp.process t ω - mf.sol t‖ > ε}
  let I : Set M_ctmc.canonicalRecordΩ :=
    {ω | ‖dp.init ω - mf.x₀‖ ≥ δ}
  let A : Set M_ctmc.canonicalRecordΩ :=
    {ω | δ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖dp.martingale_part s ω‖ ^ 2}
  have hN_delta_nat : Nat.ceil (1 / δ) + 1 ≤ N :=
    (le_max_left _ _).trans hN_ge
  have hN_markov_nat : Nat.ceil (C_qv * T / (η * δ ^ 2)) + 1 ≤ N :=
    (le_max_right _ _).trans hN_ge
  have hN_pos_real : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hδ_sq_pos : 0 < δ ^ 2 := sq_pos_of_pos hδ_pos
  have hN_delta_real : 1 / δ < (N : ℝ) := by
    calc
      1 / δ ≤ (Nat.ceil (1 / δ) : ℝ) := Nat.le_ceil _
      _ < (Nat.ceil (1 / δ) + 1 : ℕ) := by
        exact_mod_cast Nat.lt_succ_self (Nat.ceil (1 / δ))
      _ ≤ (N : ℝ) := by
        exact_mod_cast hN_delta_nat
  have h_invN_lt_delta : 1 / (N : ℝ) < δ :=
    (one_div_lt hN_pos_real hδ_pos).2 hN_delta_real
  have hN_markov_real : C_qv * T / (η * δ ^ 2) < (N : ℝ) := by
    calc
      C_qv * T / (η * δ ^ 2)
          ≤ (Nat.ceil (C_qv * T / (η * δ ^ 2)) : ℝ) := Nat.le_ceil _
      _ < (Nat.ceil (C_qv * T / (η * δ ^ 2)) + 1 : ℕ) := by
        exact_mod_cast Nat.lt_succ_self (Nat.ceil (C_qv * T / (η * δ ^ (2 : ℕ))))
      _ ≤ (N : ℝ) := by
        exact_mod_cast hN_markov_nat
  have h_markov_real_target :
      C_qv * T / ((N : ℝ) * δ ^ 2) ≤ η := by
    have hden_pos : 0 < η * δ ^ 2 := mul_pos hη hδ_sq_pos
    have hmul : C_qv * T < (N : ℝ) * (η * δ ^ 2) := by
      rwa [div_lt_iff₀ hden_pos] at hN_markov_real
    have hden2_pos : 0 < (N : ℝ) * δ ^ 2 := mul_pos hN_pos_real hδ_sq_pos
    rw [div_le_iff₀ hden2_pos]
    nlinarith [show μ.real A * ((N : ℝ) * δ ^ 2) =
      (N : ℝ) * (δ ^ 2 * μ.real A) by ring]
  have h_event_ae : ∀ᵐ ω ∂μ,
      (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
          ‖dp.process t ω - mf.sol t‖ ≥ ε) →
        (‖dp.init ω - mf.x₀‖ ≥ δ) ∨
        (δ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖dp.martingale_part s ω‖ ^ 2) := by
    simpa [μ, M_ctmc, dp] using h_event N hN x₀ hinit
  have hstep1 : μ E ≤ μ I + μ A := by
    have hae : ∀ᵐ ω ∂μ, ω ∈ E → ω ∈ I ∪ A := by
      filter_upwards [h_event_ae] with ω hω hE
      rcases hω (le_of_lt hE) with hinit_bad | hmart_bad
      · exact Or.inl hinit_bad
      · exact Or.inr hmart_bad
    calc
      μ E ≤ μ (I ∪ A) := _root_.MeasureTheory.measure_mono_ae hae
      _ ≤ μ I + μ A := _root_.MeasureTheory.measure_union_le I A
  have hinit_eq_ae : ∀ᵐ ω ∂μ,
      dp.init ω = (fun i => (↑(x₀ i) : ℝ) / ↑N) := by
    have h := M_ctmc.canonical_frozenInitialCondition_eq_scaledState_ae x₀
    simpa [μ, M_ctmc, dp, CTMC.DensityDepCTMC.toFrozenDensityProcess] using h
  have hI_zero : μ I = 0 := by
    rw [_root_.MeasureTheory.measure_eq_zero_iff_ae_notMem]
    filter_upwards [hinit_eq_ae] with ω hω hωI
    have hclose : ‖dp.init ω - mf.x₀‖ ≤ 1 / (N : ℝ) := by
      rw [hω]
      simpa [one_div] using hinit_close
    exact (not_le_of_gt (lt_of_le_of_lt hclose h_invN_lt_delta)) hωI
  have hA_le : μ A ≤ ENNReal.ofReal η := by
    have hmark :=
      _root_.MeasureTheory.mul_meas_ge_le_integral_of_nonneg
        (by simpa [μ, dp, A] using dp.martingale_sup_sq_nonneg T hT)
        (by simpa [μ, dp, A] using dp.martingale_sup_sq_integrable T hT)
        (δ ^ 2)
    have hqvN : ∫ ω, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖dp.martingale_part s ω‖ ^ 2 ∂μ ≤ C_qv * T / ↑N := by
      have hraw := hqv N hN x₀ hinit hinit_close
      simpa [μ, M_ctmc, dp, CTMC.DensityDepCTMC.toFrozenDensityProcess] using hraw
    have hreal : μ.real A ≤ η := by
      have h1 : δ ^ 2 * μ.real A ≤ C_qv * T / ↑N := by
        simpa [A] using hmark.trans hqvN
      have hA_to_qv : μ.real A ≤ C_qv * T / ((N : ℝ) * δ ^ 2) := by
        rw [le_div_iff₀ (mul_pos hN_pos_real hδ_sq_pos)]
        have h2 : (N : ℝ) * (δ ^ 2 * μ.real A) ≤
            (N : ℝ) * (C_qv * T / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 hN_pos_real.le
        rw [mul_div_cancel₀ _ (ne_of_gt hN_pos_real)] at h2
        linarith [show μ.real A * ((N : ℝ) * δ ^ 2) =
          (N : ℝ) * (δ ^ 2 * μ.real A) by ring]
      exact hA_to_qv.trans h_markov_real_target
    have hA_ne_top : μ A ≠ ⊤ := _root_.MeasureTheory.measure_ne_top μ A
    exact (ENNReal.le_ofReal_iff_toReal_le hA_ne_top hη.le).2 hreal
  calc
    μ E ≤ μ I + μ A := hstep1
    _ = μ A := by rw [hI_zero, zero_add]
    _ ≤ ENNReal.ofReal η := hA_le

end Kurtz
end Ripple
