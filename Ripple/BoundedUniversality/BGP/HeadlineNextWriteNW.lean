import Ripple.BoundedUniversality.BGP.HeadlineUnconditional
import Ripple.BoundedUniversality.BGP.SelectorReplicatorHoffP

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance UniversalMachine Filter
open scoped BigOperators Topology

/-- Local structural box inputs used only to put the halt z-coordinate and
halt mixture in `[0,1]`.  Keeping this package here avoids a dependency on the
downstream NW flip assembly. -/
private def paper3NextWriteBoxInputsNW (w : ℕ) :
    MUReplicatorBoxInputsP
      (p := bgpParamsNW w)
      paper3HeadlineEta paper3HeadlineEta_pos
      paper3HeadlineM paper3HeadlineKappa (paper3WarmGainQNW w)
      (paper3HeadlineSolFamNW w) := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  refine
  { hcr_cont := by fun_prop
    hcg_cont := by fun_prop
    hP_cont := ?_
    hcr_nonneg := ?_
    hlam_sum0 := ?_
    hlam_init_nonneg := ?_
    hz0 := ?_ }
  · intro w' v
    exact paper3UniversalPval_continuous_of_cont_u v
      (fun i => ((paper3HeadlineSolFamNW w) w').cont_u i)
  · intro t
    exact mul_nonneg
      (pow_nonneg (by nlinarith [Real.neg_one_le_cos t]) paper3HeadlineM)
      (by norm_num [paper3HeadlineKappa])
  · intro w'
    calc
      (∑ v : UniversalLocalView, ((paper3HeadlineSolFamNW w) w').lam v 0)
          = ∑ _v : UniversalLocalView,
              ((1 / (Fintype.card UniversalLocalView : ℚ)) : ℝ) := by
            apply Finset.sum_congr rfl
            intro v _hv
            exact (paper3HeadlineSolFamNW_initial_values w w').2.2.1 v
      _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        norm_num
  · intro w' v
    rw [(paper3HeadlineSolFamNW_initial_values w w').2.2.1 v]
    have hcard_pos_q : (0 : ℚ) < Fintype.card UniversalLocalView := by
      exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance :
        0 < Fintype.card UniversalLocalView)
    exact_mod_cast (div_nonneg zero_le_one hcard_pos_q.le)
  · intro w'
    rw [(paper3HeadlineSolFamNW_initial_values w w').1 haltCoordU,
      selectorInitX0_cast_enc]
    exact paper3_enc_haltCoordU_mem_unit (selectorInitConfig w')

/-! ## Early settled concentration at the weighted-write split -/

/-- Gain mass accumulated from `selectStart` to `earlyWriteSubStart`.
This is the NW analogue of the early shifted-concentration floor used by the
38-family weighted-write construction. -/
noncomputable def paper3NextWriteEarlyDeltaGFloorNW (w j : ℕ) : ℝ :=
  (3 / 4 : ℝ) ^ paper3HeadlineM *
    (((paper3WarmGainQNW w : ℚ) : ℝ) *
      Real.exp ((bgpParamsNW w).cα * selectorMUSelectStartTime j)) *
    (Real.pi / 12 - selectorMURecoveryDelta)

theorem paper3NextWriteEarlyDeltaGFloorNW_nonneg (w j : ℕ) :
    0 ≤ paper3NextWriteEarlyDeltaGFloorNW w j := by
  unfold paper3NextWriteEarlyDeltaGFloorNW
  have hπ := Real.pi_gt_three
  have hΔ : selectorMURecoveryDelta = 1 / 100000 := rfl
  exact mul_nonneg
    (mul_nonneg (by positivity)
      (mul_nonneg (paper3WarmGainQNW_nonneg_real w) (Real.exp_pos _).le))
    (by rw [hΔ]; linarith)

/-- The gain accumulated by `earlyWriteSubStart` dominates the explicit early
floor. -/
theorem paper3NextWriteEarlyDeltaGFloorNW_le (w j : ℕ) {t : ℝ}
    (ht : selectorMUEarlyWriteSubStart j ≤ t) :
    paper3NextWriteEarlyDeltaGFloorNW w j ≤
      ((paper3HeadlineSolFamNW w) w).G t -
        ((paper3HeadlineSolFamNW w) w).G (selectorMUSelectStartTime j) := by
  have hsel0 : 0 ≤ selectorMUSelectStartTime j :=
    le_trans (selectorMUWriteStartTime_nonneg j)
      (selectorMUWriteStart_le_selectStart j)
  have hsel_early : selectorMUSelectStartTime j ≤
      selectorMUEarlyWriteSubStart j := by
    unfold selectorMUSelectStartTime selectorMUEarlyWriteSubStart
      selectorMUWriteStartTime
    have hπ := Real.pi_gt_three
    have hΔ : selectorMURecoveryDelta = 1 / 100000 := rfl
    rw [hΔ]
    linarith
  have hearly0 : 0 ≤ selectorMUEarlyWriteSubStart j :=
    le_trans hsel0 hsel_early
  have h1 := paper3NW4_G_sub_eq w w hsel0 hsel_early
  have h2 := paper3NW4_G_sub_eq w w hearly0 ht
  have h2_nonneg : 0 ≤ ((paper3HeadlineSolFamNW w) w).G t -
      ((paper3HeadlineSolFamNW w) w).G
        (selectorMUEarlyWriteSubStart j) := by
    rw [h2]
    exact intervalIntegral.integral_nonneg ht
      (fun s _ => paper3NW4cg_nonneg w s)
  have hfloor : paper3NextWriteEarlyDeltaGFloorNW w j ≤
      ((paper3HeadlineSolFamNW w) w).G (selectorMUEarlyWriteSubStart j) -
        ((paper3HeadlineSolFamNW w) w).G
          (selectorMUSelectStartTime j) := by
    rw [h1]
    have hpt : ∀ s ∈ Icc (selectorMUSelectStartTime j)
        (selectorMUEarlyWriteSubStart j),
        (3 / 4 : ℝ) ^ paper3HeadlineM *
          (((paper3WarmGainQNW w : ℚ) : ℝ) *
            Real.exp ((bgpParamsNW w).cα *
              selectorMUSelectStartTime j)) ≤ paper3NW4cg w s := by
      intro s hs
      have hsin : (1 : ℝ) / 2 ≤ Real.sin s := by
        apply sin_ge_half_of_gate_window j
        constructor
        · have h := le_trans (selectorMUWriteStart_le_selectStart j) hs.1
          simpa [selectorMUWriteStartTime] using h
        · have h := le_trans hs.2 (selectorMUEarlySubStart_le_writeHold j)
          simpa [selectorMUWriteHoldTime] using h
      have hpow : (3 / 4 : ℝ) ^ paper3HeadlineM ≤
          ((1 + Real.sin s) / 2) ^ paper3HeadlineM := by
        apply pow_le_pow_left₀ (by norm_num)
        linarith
      have hcα : 0 ≤ (bgpParamsNW w).cα :=
        (bgpParamsNW_cα_pos w).le
      have hexp : Real.exp ((bgpParamsNW w).cα *
          selectorMUSelectStartTime j) ≤
          Real.exp ((bgpParamsNW w).cα * s) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hs.1 hcα
      unfold paper3NW4cg
      calc
        (3 / 4 : ℝ) ^ paper3HeadlineM *
            (((paper3WarmGainQNW w : ℚ) : ℝ) *
              Real.exp ((bgpParamsNW w).cα * selectorMUSelectStartTime j))
            ≤ (3 / 4 : ℝ) ^ paper3HeadlineM *
              (((paper3WarmGainQNW w : ℚ) : ℝ) *
                Real.exp ((bgpParamsNW w).cα * s)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_left hexp
                (paper3WarmGainQNW_nonneg_real w)
        _ ≤ ((1 + Real.sin s) / 2) ^ paper3HeadlineM *
              (((paper3WarmGainQNW w : ℚ) : ℝ) *
                Real.exp ((bgpParamsNW w).cα * s)) := by
              apply mul_le_mul_of_nonneg_right hpow
              exact mul_nonneg (paper3WarmGainQNW_nonneg_real w)
                (Real.exp_pos _).le
    have hmono := intervalIntegral.integral_mono_on hsel_early
      (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) _ _)
      ((paper3NW4cg_cont w).intervalIntegrable
        (μ := MeasureTheory.volume) _ _) hpt
    have hlen : selectorMUEarlyWriteSubStart j -
        selectorMUSelectStartTime j =
          Real.pi / 12 - selectorMURecoveryDelta := by
      unfold selectorMUEarlyWriteSubStart selectorMUSelectStartTime
        selectorMUWriteStartTime
      ring
    rw [intervalIntegral.integral_const, smul_eq_mul, hlen] at hmono
    change
      (3 / 4 : ℝ) ^ paper3HeadlineM *
          (((paper3WarmGainQNW w : ℚ) : ℝ) *
            Real.exp ((bgpParamsNW w).cα * selectorMUSelectStartTime j)) *
          (Real.pi / 12 - selectorMURecoveryDelta) ≤ _
    ring_nf at hmono ⊢
    exact hmono
  linarith

theorem paper3NextWriteEarlyDeltaGFloorNW_tendsto_atTop (w : ℕ) :
    Tendsto (paper3NextWriteEarlyDeltaGFloorNW w) atTop atTop := by
  have hscaled : Tendsto
      (fun j : ℕ => (bgpParamsNW w).cα * selectorMUSelectStartTime j)
      atTop atTop :=
    Filter.Tendsto.const_mul_atTop (bgpParamsNW_cα_pos w)
      paper3NW4_selectStart_tendsto_atTop
  have hexp := Real.tendsto_exp_atTop.comp hscaled
  have hwarm : 0 < ((paper3WarmGainQNW w : ℚ) : ℝ) :=
    paper3WarmGainQNW_pos_real w
  have h1 := Filter.Tendsto.const_mul_atTop hwarm hexp
  have hpow : 0 < (3 / 4 : ℝ) ^ paper3HeadlineM := by positivity
  have h2 := Filter.Tendsto.const_mul_atTop hpow h1
  have hwidth : 0 < Real.pi / 12 - selectorMURecoveryDelta := by
    have hπ := Real.pi_gt_three
    have hΔ : selectorMURecoveryDelta = 1 / 100000 := rfl
    rw [hΔ]
    linarith
  have h3 := Filter.Tendsto.atTop_mul_const hwidth h2
  refine Filter.Tendsto.congr (fun j => ?_) h3
  simp only [Function.comp_apply]
  rfl

/-- Uniform early loser radius on `[earlyWriteSubStart, writeHold]`. -/
noncomputable def paper3NextWriteEarlyEpsNW (w j : ℕ) : ℝ :=
  ((Fintype.card UniversalLocalView : ℝ) - 1) *
    ((Fintype.card UniversalLocalView : ℝ) *
      Real.exp (-(15 / 16) * paper3NextWriteEarlyDeltaGFloorNW w j) +
     2 ^ (paper3HeadlineM + 1) *
      Real.exp (-((bgpParamsNW w).cα * selectorMUSelectStartTime j)))

theorem paper3NextWriteEarlyEpsNW_nonneg (w j : ℕ) :
    0 ≤ paper3NextWriteEarlyEpsNW w j := by
  classical
  unfold paper3NextWriteEarlyEpsNW
  have hcard : (1 : ℝ) ≤ Fintype.card UniversalLocalView := by
    exact_mod_cast (Fintype.card_pos_iff.mpr
      (⟨defaultLocalViewU⟩ : Nonempty UniversalLocalView))
  positivity

theorem paper3NextWriteEarlyEpsNW_tendsto_zero (w : ℕ) :
    Tendsto (paper3NextWriteEarlyEpsNW w) atTop (𝓝 0) := by
  classical
  have hfloor := paper3NextWriteEarlyDeltaGFloorNW_tendsto_atTop w
  have hfloor_scaled : Tendsto
      (fun j => (15 / 16 : ℝ) * paper3NextWriteEarlyDeltaGFloorNW w j)
      atTop atTop := Filter.Tendsto.const_mul_atTop (by norm_num) hfloor
  have hdecay1 : Tendsto
      (fun j => Real.exp (-(15 / 16 : ℝ) *
        paper3NextWriteEarlyDeltaGFloorNW w j)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp hfloor_scaled
    simpa only [neg_mul] using h
  have hscaled : Tendsto
      (fun j : ℕ => (bgpParamsNW w).cα * selectorMUSelectStartTime j)
      atTop atTop :=
    Filter.Tendsto.const_mul_atTop (bgpParamsNW_cα_pos w)
      paper3NW4_selectStart_tendsto_atTop
  have hdecay2 : Tendsto
      (fun j => Real.exp (-((bgpParamsNW w).cα *
        selectorMUSelectStartTime j))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hscaled
  have hsum :=
    (hdecay1.const_mul (Fintype.card UniversalLocalView : ℝ)).add
      (hdecay2.const_mul ((2 : ℝ) ^ (paper3HeadlineM + 1)))
  have hfinal := hsum.const_mul
    ((Fintype.card UniversalLocalView : ℝ) - 1)
  change Tendsto
    (fun j => ((Fintype.card UniversalLocalView : ℝ) - 1) *
      ((Fintype.card UniversalLocalView : ℝ) *
        Real.exp (-(15 / 16) * paper3NextWriteEarlyDeltaGFloorNW w j) +
       2 ^ (paper3HeadlineM + 1) *
        Real.exp (-((bgpParamsNW w).cα * selectorMUSelectStartTime j))))
      atTop (𝓝 0)
  simpa only [mul_zero, add_zero] using hfinal

/-- Loser-mass concentration already holds on the late part of the active
write, before the settled window begins. -/
theorem paper3NextWriteEarly_loser_mass_NW (w j : ℕ) :
    ∀ t ∈ Icc (selectorMUEarlyWriteSubStart j)
        (selectorMUWriteHoldTime j),
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j))).sum
          (fun v => ((paper3HeadlineSolFamNW w) w).lam v t) ≤
        paper3NextWriteEarlyEpsNW w j := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  let sol := (paper3HeadlineSolFamNW w) w
  let a := selectorMUSelectStartTime j
  let gap := selectorReplicatorGapVal paper3HeadlineEta paper3HeadlineEta_pos
  intro t ht
  have hsel_early : a ≤ selectorMUEarlyWriteSubStart j := by
    dsimp [a]
    unfold selectorMUSelectStartTime selectorMUEarlyWriteSubStart
      selectorMUWriteStartTime
    have hπ := Real.pi_gt_three
    have hΔ : selectorMURecoveryDelta = 1 / 100000 := rfl
    rw [hΔ]
    linarith
  have hat : a ≤ t := le_trans hsel_early ht.1
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact le_trans (selectorMUWriteStartTime_nonneg j)
      (selectorMUWriteStart_le_selectStart j)
  have hgap0 : 0 < gap := by
    simpa [gap] using
      solMURepl_static_hgap0 paper3HeadlineEta paper3HeadlineEta_pos
        paper3HeadlineHerr
  have hgap1516 : (15 : ℝ) / 16 ≤ gap := by
    have h := paper3RecoveryGap_ge_fifteen_sixteen w j
    simpa [paper3RecoveryGap, gap] using h
  have hcard_pos : (0 : ℝ) < (Fintype.card UniversalLocalView : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr
      (⟨defaultLocalViewU⟩ : Nonempty UniversalLocalView)
  let Kt := ∫ s in a..t,
    Real.exp (gap * (sol.G s - sol.G a)) *
      (((1 + Real.cos s) / 2) ^ paper3HeadlineM *
        ((paper3HeadlineKappa : ℚ) : ℝ))
  have hKt0 : 0 ≤ Kt := by
    dsimp [Kt]
    apply intervalIntegral.integral_nonneg hat
    intro s _
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_cos s]) _)
        (by norm_num [paper3HeadlineKappa]))
  have hutube := paper3SegC_edge_tube_NW w j
  have hfloor := paper3NW4_floor_on_selToZOff w w j hutube
  have hsub_aZ : ∀ s, s ∈ Icc a t →
      s ∈ Icc a (selectorMUZOffStart j) := by
    intro s hs
    exact ⟨hs.1, le_trans hs.2
      (le_trans ht.2
        (le_trans (selectorMUWriteHold_le_read j)
          (paper3NW4_wr_le_zOffStart j)))⟩
  have hsub_wsZ : ∀ s, s ∈ Icc a t →
      s ∈ Icc (selectorMUWriteStartTime j) (selectorMUZOffStart j) := by
    intro s hs
    exact ⟨le_trans (selectorMUWriteStart_le_selectStart j) hs.1,
      (hsub_aZ s hs).2⟩
  have h1 := loser_mass_small_on_settled_window sol
    (localViewU (solMUReplStaticCfg w j))
    (selectStart := a) (writeStart := t) (readStart := t)
    (Lmin := 1 / (Fintype.card UniversalLocalView : ℝ))
    (gap := gap) (R0 := (Fintype.card UniversalLocalView : ℝ))
    (Kreset := Kt)
    hat (le_refl t) (by positivity) hgap0.le hcard_pos.le hKt0
    (fun s hs => selectorSchedule_domain_of_nonneg_structural s
      (le_trans ha0 hs.1))
    ((((continuous_const.add Real.continuous_cos).div_const 2).pow _).mul
      continuous_const)
    (fun s hs => hfloor s (hsub_aZ s hs))
    (fun v s hs => paper3NW_lam_nonneg_forward w w v s
      (le_trans ha0 hs.1))
    (fun s hs => paper3NW_lam_sum_forward w w s (le_trans ha0 hs.1))
    (fun s _hs => by
      exact mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_cos s]) _)
        (by norm_num [paper3HeadlineKappa]))
    (fun s _hs => by
      exact mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_sin s]) _)
        (mul_nonneg (paper3WarmGainQNW_nonneg_real w) (Real.exp_pos _).le))
    (fun v hv s hs => by
      have h := paper3NW4_gap_of_tube w w j hutube v hv s
        (hsub_wsZ s ⟨hs.1, hs.2.le⟩)
      simpa [gap] using h)
    (fun v hv => by
      have hfloor_a : 1 / (Fintype.card UniversalLocalView : ℝ) ≤
          sol.lam (localViewU (solMUReplStaticCfg w j)) a := by
        exact hfloor a
          ⟨le_rfl, paper3NW4_sel_le_zOffStart j⟩
      exact paper3Headline_lam_ratio_card_bound_at
        (lam := fun v' : UniversalLocalView => sol.lam v' a)
        (vstar := localViewU (solMUReplStaticCfg w j))
        (paper3NW_lam_sum_forward w w a ha0)
        (fun v' => paper3NW_lam_nonneg_forward w w v' a ha0)
        hfloor_a v hv)
    (fun t' ht' => by
      have heq : t' = t := le_antisymm ht'.2 ht'.1
      subst t'
      exact le_rfl)
    (fun t' ht' => by
      have heq : t' = t := le_antisymm ht'.2 ht'.1
      subst t'
      exact le_rfl)
  have h2 := h1 t ⟨le_rfl, le_rfl⟩
  rw [epsLamSettled_card_inv] at h2
  have hcard1 : (0 : ℝ) ≤ (Fintype.card UniversalLocalView : ℝ) - 1 := by
    have hcardNat : 1 ≤ Fintype.card UniversalLocalView :=
      (Fintype.card_pos_iff.mpr
        (⟨defaultLocalViewU⟩ : Nonempty UniversalLocalView))
    have hcardReal : (1 : ℝ) ≤ Fintype.card UniversalLocalView := by
      exact_mod_cast hcardNat
    linarith
  have hΔG := paper3NextWriteEarlyDeltaGFloorNW_le w j ht.1
  have hΔGf0 := paper3NextWriteEarlyDeltaGFloorNW_nonneg w j
  have hXle : Real.exp (-(gap * (sol.G t - sol.G a))) ≤
      Real.exp (-(15 / 16) * paper3NextWriteEarlyDeltaGFloorNW w j) := by
    apply Real.exp_le_exp.mpr
    have hΔG0 : 0 ≤ sol.G t - sol.G a := le_trans hΔGf0 hΔG
    nlinarith
  have hKtX : Kt * Real.exp (-(gap * (sol.G t - sol.G a))) ≤
      2 ^ (paper3HeadlineM + 1) *
        Real.exp (-((bgpParamsNW w).cα * a)) := by
    have hkill := paper3NW4_reset_kill w w j (t := t) (gap := gap)
      hat
      (le_trans ht.2
        (le_trans (selectorMUWriteHold_le_read j)
          (paper3NW4_wr_le_zOffStart j))) hgap1516
    have hXeq : Real.exp (-gap * (sol.G t - sol.G a)) =
        Real.exp (-(gap * (sol.G t - sol.G a))) := by
      congr 1
      ring
    rw [hXeq] at hkill
    simpa [Kt] using hkill
  calc
    (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j))).sum
          (fun v => sol.lam v t)
        ≤ ((Fintype.card UniversalLocalView : ℝ) - 1) *
          (((Fintype.card UniversalLocalView : ℝ) + Kt) *
            Real.exp (-(gap * (sol.G t - sol.G a)))) := h2
    _ = ((Fintype.card UniversalLocalView : ℝ) - 1) *
        ((Fintype.card UniversalLocalView : ℝ) *
          Real.exp (-(gap * (sol.G t - sol.G a))) +
         Kt * Real.exp (-(gap * (sol.G t - sol.G a)))) := by ring
    _ ≤ ((Fintype.card UniversalLocalView : ℝ) - 1) *
        ((Fintype.card UniversalLocalView : ℝ) *
          Real.exp (-(15 / 16) * paper3NextWriteEarlyDeltaGFloorNW w j) +
         2 ^ (paper3HeadlineM + 1) *
          Real.exp (-((bgpParamsNW w).cα * a))) := by
      apply mul_le_mul_of_nonneg_left _ hcard1
      have h3 := mul_le_mul_of_nonneg_left hXle hcard_pos.le
      linarith
    _ = paper3NextWriteEarlyEpsNW w j := by
      rw [paper3NextWriteEarlyEpsNW]

/-! ## Weighted active-write contraction -/

/-- Z-gate mass on the late quarter of the active write. -/
noncomputable def paper3NextWriteEarlyMassLowerNW (w j : ℕ) : ℝ :=
  (Real.pi / 4) *
    Real.exp (50 * (bgpScaleW w : ℝ) *
      (2 * Real.pi * (j : ℝ) + Real.pi / 4))

theorem paper3NextWriteEarlyMassLowerNW_le_integral (w j : ℕ) :
    paper3NextWriteEarlyMassLowerNW w j ≤
      ∫ τ in (selectorMUEarlyWriteSubStart j)..(selectorMUWriteHoldTime j),
        (bgpParamsNW w).A * ((paper3HeadlineSolFamNW w) w).α τ *
          bGateZ (bgpParamsNW w).L
            (((paper3HeadlineSolFamNW w) w).μ τ) τ := by
  have hab : selectorMUEarlyWriteSubStart j ≤
      selectorMUWriteHoldTime j := selectorMUEarlySubStart_le_writeHold j
  have ha0 : 0 ≤ selectorMUEarlyWriteSubStart j := by
    unfold selectorMUEarlyWriteSubStart
    positivity
  have hpoint : ∀ τ ∈ Icc (selectorMUEarlyWriteSubStart j)
      (selectorMUWriteHoldTime j),
      Real.exp (50 * (bgpScaleW w : ℝ) *
          (2 * Real.pi * (j : ℝ) + Real.pi / 4)) ≤
        (bgpParamsNW w).A * ((paper3HeadlineSolFamNW w) w).α τ *
          bGateZ (bgpParamsNW w).L
            (((paper3HeadlineSolFamNW w) w).μ τ) τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    have hsin : (1 : ℝ) / 2 ≤ Real.sin τ := by
      apply sin_ge_half_of_write_window j
      constructor
      · have h := le_trans (selectorMUWriteStart_le_earlySubStart j) hτ.1
        simpa [selectorMUWriteStartTime] using h
      · have h := le_trans hτ.2 (selectorMUWriteHold_le_read j)
        simpa [selectorMUWriteReadTime] using h
    calc
      Real.exp (50 * (bgpScaleW w : ℝ) *
          (2 * Real.pi * (j : ℝ) + Real.pi / 4))
          ≤ Real.exp (50 * (bgpScaleW w : ℝ) * τ) := by
            apply Real.exp_le_exp.mpr
            have hS : 0 < (bgpScaleW w : ℝ) := bgpScaleWR_pos w
            have h := hτ.1
            unfold selectorMUEarlyWriteSubStart at h
            nlinarith
      _ ≤ _ := paper3NW4_zKernel_ge_of_sin_ge_half w w hτ0 hsin
  have hmono := intervalIntegral.integral_mono_on hab
    (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) _ _)
    ((paper3NW4_zKernel_continuous w w).intervalIntegrable
      (μ := MeasureTheory.volume) _ _) hpoint
  have hwidth : selectorMUWriteHoldTime j -
      selectorMUEarlyWriteSubStart j = Real.pi / 4 := by
    unfold selectorMUWriteHoldTime selectorMUEarlyWriteSubStart
    ring
  rw [intervalIntegral.integral_const, smul_eq_mul, hwidth] at hmono
  change (Real.pi / 4) * Real.exp
      (50 * (bgpScaleW w : ℝ) *
        (2 * Real.pi * (j : ℝ) + Real.pi / 4)) ≤ _
  nlinarith

theorem paper3NextWriteEarlyMassLowerNW_tendsto_atTop (w : ℕ) :
    Tendsto (paper3NextWriteEarlyMassLowerNW w) atTop atTop := by
  have hlin : Tendsto
      (fun j : ℕ => 2 * Real.pi * (j : ℝ) + Real.pi / 4)
      atTop atTop := by
    have h := Filter.Tendsto.const_mul_atTop
      (by positivity : (0 : ℝ) < 2 * Real.pi)
      tendsto_natCast_atTop_atTop
    exact Filter.tendsto_atTop_add_const_right atTop (Real.pi / 4) h
  have hscaled : Tendsto
      (fun j : ℕ => 50 * (bgpScaleW w : ℝ) *
        (2 * Real.pi * (j : ℝ) + Real.pi / 4)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop
      (mul_pos (by norm_num) (bgpScaleWR_pos w)) hlin
  have hexp := Real.tendsto_exp_atTop.comp hscaled
  have h := Filter.Tendsto.const_mul_atTop
    (show (0 : ℝ) < Real.pi / 4 by positivity) hexp
  refine Filter.Tendsto.congr (fun j => ?_) h
  rfl

/-- The Duhamel-weighted movement of the halt mix before `writeHold`. -/
noncomputable def paper3NextWriteWeightedMixNW (w j : ℕ) : ℝ :=
  Real.exp (-(paper3NextWriteEarlyMassLowerNW w j)) +
    (Fintype.card UniversalLocalView : ℝ) *
      paper3NextWriteEarlyEpsNW w j +
    (Fintype.card UniversalLocalView : ℝ) * paper3NW4EpsLam w j

theorem paper3NextWriteWeightedMixNW_nonneg (w j : ℕ) :
    0 ≤ paper3NextWriteWeightedMixNW w j := by
  unfold paper3NextWriteWeightedMixNW
  exact add_nonneg
    (add_nonneg (Real.exp_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _)
        (paper3NextWriteEarlyEpsNW_nonneg w j)))
    (mul_nonneg (Nat.cast_nonneg _) (paper3NW4EpsLam_nonneg w j))

theorem paper3NextWriteWeightedMixNW_tendsto_zero (w : ℕ) :
    Tendsto (paper3NextWriteWeightedMixNW w) atTop (𝓝 0) := by
  have hmass := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (paper3NextWriteEarlyMassLowerNW_tendsto_atTop w)
  have hearly := (paper3NextWriteEarlyEpsNW_tendsto_zero w).const_mul
    (Fintype.card UniversalLocalView : ℝ)
  have hhold := (paper3NW4EpsLam_tendsto_zero w).const_mul
    (Fintype.card UniversalLocalView : ℝ)
  change Tendsto
    (fun j => Real.exp (-(paper3NextWriteEarlyMassLowerNW w j)) +
      (Fintype.card UniversalLocalView : ℝ) *
        paper3NextWriteEarlyEpsNW w j +
      (Fintype.card UniversalLocalView : ℝ) * paper3NW4EpsLam w j)
    atTop (𝓝 0)
  simpa only [Function.comp_apply, mul_zero, add_zero] using
    (hmass.add hearly).add hhold

theorem paper3NextWrite_weighted_mix_NW (w j : ℕ) :
    (∫ τ in (selectorMUWriteStartTime j)..(selectorMUWriteHoldTime j),
      Real.exp (-(∫ σ in τ..(selectorMUWriteHoldTime j),
        (bgpParamsNW w).A * ((paper3HeadlineSolFamNW w) w).α σ *
          bGateZ (bgpParamsNW w).L
            (((paper3HeadlineSolFamNW w) w).μ σ) σ)) *
      ((bgpParamsNW w).A * ((paper3HeadlineSolFamNW w) w).α τ *
        bGateZ (bgpParamsNW w).L
          (((paper3HeadlineSolFamNW w) w).μ τ) τ) *
      |selectorMixTarget branchU ((paper3HeadlineSolFamNW w) w).u
          ((paper3HeadlineSolFamNW w) w).lam τ haltCoordU -
        selectorMixTarget branchU ((paper3HeadlineSolFamNW w) w).u
          ((paper3HeadlineSolFamNW w) w).lam
            (selectorMUWriteHoldTime j) haltCoordU|) ≤
      paper3NextWriteWeightedMixNW w j := by
  classical
  let sol := (paper3HeadlineSolFamNW w) w
  let W := selectorMUWriteStartTime j
  let E := selectorMUEarlyWriteSubStart j
  let H := selectorMUWriteHoldTime j
  let k : ℝ → ℝ := fun t =>
    (bgpParamsNW w).A * sol.α t * bGateZ (bgpParamsNW w).L (sol.μ t) t
  let d : ℝ → ℝ := fun t =>
    selectorMixTarget branchU sol.u sol.lam t haltCoordU -
      selectorMixTarget branchU sol.u sol.lam H haltCoordU
  let C := (Fintype.card UniversalLocalView : ℝ) *
      paper3NextWriteEarlyEpsNW w j +
    (Fintype.card UniversalLocalView : ℝ) * paper3NW4EpsLam w j
  have hWE : W ≤ E := by
    simpa [W, E] using selectorMUWriteStart_le_earlySubStart j
  have hEH : E ≤ H := by
    simpa [E, H] using selectorMUEarlySubStart_le_writeHold j
  have hk_cont : Continuous k := by
    simpa [k, sol] using paper3NW4_zKernel_continuous w w
  have hd_cont : Continuous d := by
    exact (sol.cont_mixTarget haltCoordU).sub continuous_const
  have hk_nonneg : ∀ t ∈ Icc W H, 0 ≤ k t := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans (selectorMUWriteStartTime_nonneg j)
      (by simpa [W] using ht.1)
    simpa [k, sol] using paper3NW4_zKernel_nonneg w w ht0
  have hH0 : 0 ≤ H := by
    simpa [H] using le_trans (selectorMUWriteStartTime_nonneg j)
      (selectorMUWriteStart_le_hold j)
  have hprefix : ∀ t ∈ Icc W E, |d t| ≤ (1 : ℝ) := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans (selectorMUWriteStartTime_nonneg j)
      (by simpa [W] using ht.1)
    have hmT := (paper3NextWriteBoxInputsNW w).halt_mixTarget_mem_Icc w t ht0
    have hmH := (paper3NextWriteBoxInputsNW w).halt_mixTarget_mem_Icc w H hH0
    exact paper3_abs_sub_le_one_of_unit_interval_pair hmT hmH
  have hsuffix : ∀ t ∈ Icc E H, |d t| ≤ C := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans (selectorMUWriteStartTime_nonneg j)
      (le_trans (selectorMUWriteStart_le_earlySubStart j)
        (by simpa [E] using ht.1))
    have hsumT := paper3NW_lam_sum_forward w w t ht0
    have hsumH := paper3NW_lam_sum_forward w w H hH0
    have hloserT := paper3NextWriteEarly_loser_mass_NW w j t
      (by simpa [E, H] using ht)
    have hloserH := paper3NW4_loser_mass_hold_window w j H
      (by simp [H, selectorMUWriteHold_le_read])
    have h := selectorMixTarget_halt_pair_of_loser_sum
      sol.u sol.lam t H (solMUReplStaticCfg w j)
      hsumT hsumH
      (fun v => paper3NW_lam_nonneg_forward w w v t ht0)
      (fun v => paper3NW_lam_nonneg_forward w w v H hH0)
      hloserT hloserH
    simpa [d, C] using h
  have hC : 0 ≤ C := by
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (paper3NextWriteEarlyEpsNW_nonneg w j))
      (mul_nonneg (Nat.cast_nonneg _) (paper3NW4EpsLam_nonneg w j))
  have hkernel := terminal_kernel_split_abs_bound k d W E H C
    hWE hEH hk_cont hd_cont hk_nonneg hprefix hsuffix hC
  have hmass := paper3NextWriteEarlyMassLowerNW_le_integral w j
  have hexp : Real.exp (-(∫ s in E..H, k s)) ≤
      Real.exp (-(paper3NextWriteEarlyMassLowerNW w j)) := by
    apply Real.exp_le_exp.mpr
    simpa [E, H, k, sol] using neg_le_neg hmass
  calc
    (∫ τ in (selectorMUWriteStartTime j)..(selectorMUWriteHoldTime j),
      Real.exp (-(∫ σ in τ..(selectorMUWriteHoldTime j),
        (bgpParamsNW w).A * ((paper3HeadlineSolFamNW w) w).α σ *
          bGateZ (bgpParamsNW w).L
            (((paper3HeadlineSolFamNW w) w).μ σ) σ)) *
      ((bgpParamsNW w).A * ((paper3HeadlineSolFamNW w) w).α τ *
        bGateZ (bgpParamsNW w).L
          (((paper3HeadlineSolFamNW w) w).μ τ) τ) *
      |selectorMixTarget branchU ((paper3HeadlineSolFamNW w) w).u
          ((paper3HeadlineSolFamNW w) w).lam τ haltCoordU -
        selectorMixTarget branchU ((paper3HeadlineSolFamNW w) w).u
          ((paper3HeadlineSolFamNW w) w).lam
            (selectorMUWriteHoldTime j) haltCoordU|)
        = ∫ τ in W..H, Real.exp (-(∫ σ in τ..H, k σ)) * k τ * |d τ| := by
          simp [W, H, k, d, sol]
    _ ≤ Real.exp (-(∫ s in E..H, k s)) + C := hkernel
    _ ≤ Real.exp (-(paper3NextWriteEarlyMassLowerNW w j)) + C :=
      add_le_add hexp le_rfl
    _ = paper3NextWriteWeightedMixNW w j := by
      unfold paper3NextWriteWeightedMixNW
      dsimp [C]
      ring

/-! ## The `writeHold` endpoint and the whole settled tail -/

/-- Error at `writeHold j`, relative to the freshly written configuration
`cfg (j+1)`. -/
noncomputable def paper3NextWriteStartDeltaNW (w j : ℕ) : ℝ :=
  Real.exp (-(paper3NextWriteEarlyMassLowerNW w j)) +
    paper3NextWriteWeightedMixNW w j + paper3NW4EpsLam w j

theorem paper3NextWriteStartDeltaNW_nonneg (w j : ℕ) :
    0 ≤ paper3NextWriteStartDeltaNW w j := by
  unfold paper3NextWriteStartDeltaNW
  exact add_nonneg
    (add_nonneg (Real.exp_nonneg _)
      (paper3NextWriteWeightedMixNW_nonneg w j))
    (paper3NW4EpsLam_nonneg w j)

theorem paper3NextWriteStartDeltaNW_tendsto_zero (w : ℕ) :
    Tendsto (paper3NextWriteStartDeltaNW w) atTop (𝓝 0) := by
  have hmass := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (paper3NextWriteEarlyMassLowerNW_tendsto_atTop w)
  have hweighted := paper3NextWriteWeightedMixNW_tendsto_zero w
  have hhold := paper3NW4EpsLam_tendsto_zero w
  change Tendsto
    (fun j => Real.exp (-(paper3NextWriteEarlyMassLowerNW w j)) +
      paper3NextWriteWeightedMixNW w j + paper3NW4EpsLam w j)
    atTop (𝓝 0)
  simpa only [Function.comp_apply, add_zero] using
    (hmass.add hweighted).add hhold

/-- The active write has reached the new halt encoding by `writeHold`. -/
theorem paper3NextWrite_start_NW (w j : ℕ) :
    |((paper3HeadlineSolFamNW w) w).z (selectorMUWriteHoldTime j) haltCoordU -
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤
        paper3NextWriteStartDeltaNW w j := by
  classical
  let sol := (paper3HeadlineSolFamNW w) w
  let W := selectorMUWriteStartTime j
  let E := selectorMUEarlyWriteSubStart j
  let H := selectorMUWriteHoldTime j
  let k : ℝ → ℝ := fun t =>
    (bgpParamsNW w).A * sol.α t * bGateZ (bgpParamsNW w).L (sol.μ t) t
  let m : ℝ → ℝ := fun t =>
    selectorMixTarget branchU sol.u sol.lam t haltCoordU
  let M := m H
  have hWH : W ≤ H := by
    simpa [W, H] using selectorMUWriteStart_le_hold j
  have hk_cont : Continuous k := by
    simpa [k, sol] using paper3NW4_zKernel_continuous w w
  have hk_nonneg : ∀ t ∈ Icc W H, 0 ≤ k t := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans (selectorMUWriteStartTime_nonneg j)
      (by simpa [W] using ht.1)
    simpa [k, sol] using paper3NW4_zKernel_nonneg w w ht0
  have hm_cont : Continuous m := by
    simpa [m] using sol.cont_mixTarget haltCoordU
  have hy_ode : ∀ t ∈ Icc W H,
      HasDerivAt (fun τ => sol.z τ haltCoordU)
        (k t * (m t - sol.z t haltCoordU)) t := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans (selectorMUWriteStartTime_nonneg j)
      (by simpa [W] using ht.1)
    simpa [k, m] using sol.z_hasDeriv t
      (selectorSchedule_domain_of_nonneg_structural t ht0) haltCoordU
  have hscalar := stack_write_gronwall_weighted_bound
    (fun t => sol.z t haltCoordU) m k M W H hWH
    hk_cont hk_nonneg hm_cont hy_ode
  have hW0 : 0 ≤ W := by
    simpa [W] using selectorMUWriteStartTime_nonneg j
  have hH0 : 0 ≤ H := by
    exact le_trans hW0 hWH
  have hentry : |sol.z W haltCoordU - M| ≤ (1 : ℝ) := by
    have hz := (paper3NextWriteBoxInputsNW w).halt_z_mem_Icc
      (by rw [bgpParamsNW_A_eq]; norm_num : 0 ≤ (bgpParamsNW w).A)
      w W hW0
    have hmH := (paper3NextWriteBoxInputsNW w).halt_mixTarget_mem_Icc w H hH0
    exact paper3_abs_sub_le_one_of_unit_interval_pair hz hmH
  have hWE : W ≤ E := by
    simpa [W, E] using selectorMUWriteStart_le_earlySubStart j
  have hEH : E ≤ H := by
    simpa [E, H] using selectorMUEarlySubStart_le_writeHold j
  have hpref_nonneg : 0 ≤ ∫ t in W..E, k t := by
    apply intervalIntegral.integral_nonneg hWE
    intro t ht
    exact hk_nonneg t ⟨ht.1, le_trans ht.2 hEH⟩
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hk_cont.intervalIntegrable (μ := MeasureTheory.volume) W E)
    (hk_cont.intervalIntegrable (μ := MeasureTheory.volume) E H)
  have hearlyMass := paper3NextWriteEarlyMassLowerNW_le_integral w j
  have hfullMass : paper3NextWriteEarlyMassLowerNW w j ≤
      ∫ t in W..H, k t := by
    have hearlyMass' : paper3NextWriteEarlyMassLowerNW w j ≤
        ∫ t in E..H, k t := by
      simpa [E, H, k, sol] using hearlyMass
    linarith
  have hctr : Real.exp (-(∫ t in W..H, k t)) *
      |sol.z W haltCoordU - M| ≤
        Real.exp (-(paper3NextWriteEarlyMassLowerNW w j)) := by
    have h := exp_neg_mul_abs_le_exp_neg_lbd_mul hfullMass hentry
    simpa using h
  have hweighted :
      (∫ t in W..H,
        Real.exp (-(∫ s in t..H, k s)) * k t * |m t - M|) ≤
          paper3NextWriteWeightedMixNW w j := by
    simpa [W, H, k, m, M, sol] using
      paper3NextWrite_weighted_mix_NW w j
  have hzM : |sol.z H haltCoordU - M| ≤
      Real.exp (-(paper3NextWriteEarlyMassLowerNW w j)) +
        paper3NextWriteWeightedMixNW w j := by
    exact hscalar.trans (add_le_add hctr hweighted)
  have hloser := paper3NW4_loser_mass_hold_window w j H
    (by simp [H, selectorMUWriteHold_le_read])
  have hmix : |m H -
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤
        paper3NW4EpsLam w j := by
    have hraw := selectorMixTarget_halt_to_next_of_loser_sum_sharp
      sol.u sol.lam H (solMUReplStaticCfg w j)
      (paper3NW_lam_sum_forward w w H hH0)
      (fun v => paper3NW_lam_nonneg_forward w w v H hH0) hloser
    simpa [m, solMUReplStaticCfg_step w j] using hraw
  calc
    |((paper3HeadlineSolFamNW w) w).z (selectorMUWriteHoldTime j)
        haltCoordU -
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU|
        ≤ |sol.z H haltCoordU - M| +
          |M - stackMachineEncodingU.enc
            (solMUReplStaticCfg w (j + 1)) haltCoordU| := by
              simpa [sol, H] using abs_sub_le
                (sol.z H haltCoordU) M
                (stackMachineEncodingU.enc
                  (solMUReplStaticCfg w (j + 1)) haltCoordU)
    _ ≤ (Real.exp (-(paper3NextWriteEarlyMassLowerNW w j)) +
          paper3NextWriteWeightedMixNW w j) + paper3NW4EpsLam w j :=
      add_le_add hzM hmix
    _ = paper3NextWriteStartDeltaNW w j := by
      rfl

/-- Final per-word next-write radius, shifted to cycle `j+1`. -/
noncomputable def paper3HeadlineNextWriteDeltaNW (w j : ℕ) : ℝ :=
  paper3NextWriteStartDeltaNW w (j + 1) + paper3NW4EpsLam w (j + 1)

theorem paper3HeadlineNextWriteDeltaNW_nonneg (w j : ℕ) :
    0 ≤ paper3HeadlineNextWriteDeltaNW w j := by
  unfold paper3HeadlineNextWriteDeltaNW
  exact add_nonneg (paper3NextWriteStartDeltaNW_nonneg w (j + 1))
    (paper3NW4EpsLam_nonneg w (j + 1))

theorem paper3HeadlineNextWriteDeltaNW_tendsto_zero (w : ℕ) :
    Tendsto (paper3HeadlineNextWriteDeltaNW w) atTop (𝓝 0) := by
  have hstart := (paper3NextWriteStartDeltaNW_tendsto_zero w).comp
    (Filter.tendsto_add_atTop_nat 1)
  have hmix := (paper3NW4EpsLam_tendsto_zero w).comp
    (Filter.tendsto_add_atTop_nat 1)
  change Tendsto
    (fun j => paper3NextWriteStartDeltaNW w (j + 1) +
      paper3NW4EpsLam w (j + 1)) atTop (𝓝 0)
  simpa only [add_zero] using hstart.add hmix

/-- Pointwise propagation of the new halt encoding over the complete next
settled-write window. -/
theorem paper3HeadlineNextWrite_bound_NW (w j : ℕ) :
    ∀ t ∈ Icc (selectorMUNextWriteStart j) (selectorMUNextRead j),
      |((paper3HeadlineSolFamNW w) w).z t haltCoordU -
        stackMachineEncodingU.enc
          (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤
        paper3HeadlineNextWriteDeltaNW w j := by
  classical
  let n := j + 1
  let sol := (paper3HeadlineSolFamNW w) w
  let H := selectorMUWriteHoldTime n
  let R := selectorMUWriteReadTime n
  let target := stackMachineEncodingU.enc
    (solMUReplStaticCfg w (n + 1)) haltCoordU
  intro t ht
  have ht' : t ∈ Icc H R := by
    simpa [n, H, R, selectorMUNextWriteStart, selectorMUNextRead,
      Nat.add_assoc] using ht
  have hH0 : 0 ≤ H := by
    dsimp [H]
    exact le_trans (selectorMUWriteStartTime_nonneg n)
      (selectorMUWriteStart_le_hold n)
  have hdom : ∀ τ ∈ Icc H t, τ ∈ selectorSchedule.domain := by
    intro τ hτ
    exact selectorSchedule_domain_of_nonneg_structural τ
      (le_trans hH0 hτ.1)
  have hg_cont : Continuous fun τ =>
      (bgpParamsNW w).A * sol.α τ *
        bGateZ (bgpParamsNW w).L (sol.μ τ) τ := by
    simpa [sol] using paper3NW4_zKernel_continuous w w
  have hg0 : ∀ τ ∈ Icc H t,
      0 ≤ (bgpParamsNW w).A * sol.α τ *
        bGateZ (bgpParamsNW w).L (sol.μ τ) τ := by
    intro τ hτ
    simpa [sol] using paper3NW4_zKernel_nonneg w w
      (le_trans hH0 hτ.1)
  have hmix : ∀ τ ∈ Icc H t,
      |selectorMixTarget branchU sol.u sol.lam τ haltCoordU - target| ≤
        paper3NW4EpsLam w n := by
    intro τ hτ
    have hτfull : τ ∈ Icc (selectorMUWriteHoldTime n)
        (selectorMUWriteReadTime n) := by
      exact ⟨by simpa [H] using hτ.1,
        le_trans hτ.2 ht'.2⟩
    have hτ0 : 0 ≤ τ := le_trans hH0 (by simpa [H] using hτ.1)
    have hloser := paper3NW4_loser_mass_hold_window w n τ hτfull
    have hraw := selectorMixTarget_halt_to_next_of_loser_sum_sharp
      sol.u sol.lam τ (solMUReplStaticCfg w n)
      (paper3NW_lam_sum_forward w w τ hτ0)
      (fun v => paper3NW_lam_nonneg_forward w w v τ hτ0) hloser
    simpa [target, solMUReplStaticCfg_step w n] using hraw
  have hzero : ∀ τ ∈ Icc t t,
      |sol.z τ haltCoordU - sol.z t haltCoordU| ≤ (0 : ℝ) := by
    intro τ hτ
    have hτeq : τ = t := le_antisymm hτ.2 hτ.1
    subst τ
    simp
  have hafter := z_after_write_bound_repl
    (sol := sol) (s := haltCoordU)
    (a := H) (m := t) (b := t) (M := target)
    (δw := paper3NW4EpsLam w n) (δzh := 0)
    ht'.1 hdom hg_cont hg0 hmix hzero
  have hraw := hafter t ⟨le_rfl, le_rfl⟩
  have hmass : 0 ≤ ∫ τ in H..t,
      (bgpParamsNW w).A * sol.α τ *
        bGateZ (bgpParamsNW w).L (sol.μ τ) τ := by
    apply intervalIntegral.integral_nonneg ht'.1
    intro τ hτ
    exact hg0 τ hτ
  have hexp : Real.exp (-(∫ τ in H..t,
      (bgpParamsNW w).A * sol.α τ *
        bGateZ (bgpParamsNW w).L (sol.μ τ) τ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hstart : |sol.z H haltCoordU - target| ≤
      paper3NextWriteStartDeltaNW w n := by
    simpa [sol, H, target, Nat.add_assoc] using
      paper3NextWrite_start_NW w n
  have hterm : Real.exp (-(∫ τ in H..t,
      (bgpParamsNW w).A * sol.α τ *
        bGateZ (bgpParamsNW w).L (sol.μ τ) τ)) *
      |sol.z H haltCoordU - target| ≤
        paper3NextWriteStartDeltaNW w n := by
    have h := mul_le_mul hexp hstart (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  have hfinal : |sol.z t haltCoordU - target| ≤
      paper3NextWriteStartDeltaNW w n + paper3NW4EpsLam w n := by
    have hraw' : |sol.z t haltCoordU - target| ≤
        Real.exp (-(∫ τ in H..t,
          (bgpParamsNW w).A * sol.α τ *
            bGateZ (bgpParamsNW w).L (sol.μ τ) τ)) *
          |sol.z H haltCoordU - target| + paper3NW4EpsLam w n := by
      simpa only [sub_self, abs_zero, zero_add] using hraw
    exact hraw'.trans (add_le_add hterm le_rfl)
  simpa [paper3HeadlineNextWriteDeltaNW, n, sol, target,
    Nat.add_assoc] using hfinal

/-- **NW NextWrite capstone.**  This is exactly the diagonal supplier required
by `paper3AnalyticResidualDischargeNW_of_diagonal`. -/
def paper3HeadlineNextWriteNW (w : ℕ) :
    ∃ δ : ℕ → ℝ,
      Tendsto δ atTop (𝓝 0) ∧
      (∀ j, 0 ≤ δ j) ∧
      (∀ j, ∀ t ∈ Icc (selectorMUNextWriteStart j)
          (selectorMUNextRead j),
        |((paper3HeadlineSolFamNW w) w).z t haltCoordU -
          stackMachineEncodingU.enc
            (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤ δ j) := by
  exact ⟨paper3HeadlineNextWriteDeltaNW w,
    paper3HeadlineNextWriteDeltaNW_tendsto_zero w,
    paper3HeadlineNextWriteDeltaNW_nonneg w,
    paper3HeadlineNextWrite_bound_NW w⟩

end Ripple.BoundedUniversality.BGP
