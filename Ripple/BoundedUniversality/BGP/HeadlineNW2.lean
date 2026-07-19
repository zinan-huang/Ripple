import Ripple.BoundedUniversality.BGP.HeadlineUnconditional
import Ripple.BoundedUniversality.BGP.BernsteinSlope
import Ripple.BoundedUniversality.BGP.S4LeafToolkit

/-!
# NW S4 extension (split out of HeadlineUnconditional for fast iteration)

This file holds the new S4a-QSS / S4b / flip work.  It imports the stable
`HeadlineUnconditional` base (whose declarations were un-privatised so this
file can reference them) and compiles in seconds against the base olean.
Semantic reorganisation is deferred until everything is green.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance UniversalMachine Filter
open scoped BigOperators Topology
set_option maxRecDepth 8000
set_option maxHeartbeats 300000

private noncomputable def bgpS4GammaInvFactor : ℝ :=
  (2 : ℝ) ^ (bgpHeadlineM + 1)

private noncomputable def bgpS4PGapCoeffNW : ℝ :=
  2 * (Fintype.card (Fin d_U) : ℝ) *
    BernsteinSlope.bgpHeadlineSelectorSlopeConst *
    bgpS4EdgeZUBoundNW

/-- A uniform coefficient; `j` and `v` are retained only to match the dossier API. -/
private noncomputable def bgpS4aQSSDerivCoeffNW
    (w j : ℕ) (v : UniversalLocalView) : ℝ :=
  (bgpHeadlineM : ℝ) * bgpS4GammaInvFactor +
    ((bgpHeadlineM : ℝ) + 300 * (bgpScaleW w : ℝ) +
      bgpS4PGapCoeffNW) * bgpS4GammaInvFactor ^ 2

private theorem bgpS4EdgeZUBoundNW_nonneg :
    0 ≤ bgpS4EdgeZUBoundNW := by
  have hD : 0 ≤ D_U := D_U_nonneg
  have hC : 0 ≤ bgpF1CwinDefN := bgpF1CwinDefN_nonneg
  have hlin : 0 ≤ 5 * D_U + 2 := by
    nlinarith
  have hprod : 0 ≤ 4000 * D_U * (5 * D_U + 2) :=
    mul_nonneg (mul_nonneg (by norm_num) hD) hlin
  unfold bgpS4EdgeZUBoundNW
  nlinarith

private theorem bgpS4GammaInvFactor_pos :
    0 < bgpS4GammaInvFactor := by
  unfold bgpS4GammaInvFactor
  exact pow_pos (by norm_num) _

private theorem bgpS4PGapCoeffNW_nonneg :
    0 ≤ bgpS4PGapCoeffNW := by
  have hcard : 0 ≤ (Fintype.card (Fin d_U) : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card (Fin d_U))
  have hslope :
      0 ≤ BernsteinSlope.bgpHeadlineSelectorSlopeConst :=
    BernsteinSlope.bgpHeadlineSelectorSlopeConst_nonneg
  unfold bgpS4PGapCoeffNW
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) hcard)
      hslope)
    bgpS4EdgeZUBoundNW_nonneg

private theorem bgpS4aQSSDerivCoeffNW_nonneg
    (w j : ℕ) (v : UniversalLocalView) :
    0 ≤ bgpS4aQSSDerivCoeffNW w j v := by
  have hM : 0 ≤ (bgpHeadlineM : ℝ) := Nat.cast_nonneg _
  have hS : 0 ≤ (bgpScaleW w : ℝ) := (bgpScaleWR_pos w).le
  have hA : 0 ≤ bgpS4GammaInvFactor := bgpS4GammaInvFactor_pos.le
  have hP : 0 ≤ bgpS4PGapCoeffNW := bgpS4PGapCoeffNW_nonneg
  have hsum :
      0 ≤ (bgpHeadlineM : ℝ) + 300 * (bgpScaleW w : ℝ) +
        bgpS4PGapCoeffNW :=
    add_nonneg (add_nonneg hM (mul_nonneg (by norm_num) hS)) hP
  unfold bgpS4aQSSDerivCoeffNW
  exact add_nonneg
    (mul_nonneg hM hA)
    (mul_nonneg hsum (sq_nonneg bgpS4GammaInvFactor))

/-- Exact quotient cancellation used by the QSS derivative leaf. -/
private theorem bgpS4_qss_scalar_cancel
    {N g E A M r P cr CgD cg PGapD gamma : ℝ}
    (hN : 1 ≤ N)
    (hg : 1 ≤ g)
    (hE : 0 < E)
    (hA : 0 < A)
    (hM : 0 ≤ M)
    (hr : 0 ≤ r)
    (hP : 0 ≤ P)
    (hcr : 0 ≤ cr ∧ cr ≤ 1)
    (hCgD : 0 ≤ CgD ∧ CgD ≤ (M + r) * (g * E))
    (hcg : 0 ≤ cg ∧ cg ≤ g * E)
    (hPGapD : 0 ≤ PGapD ∧ PGapD ≤ P)
    (hgamma : gamma = g * E / A) :
    (1 / N) *
        (M / gamma + cr * (CgD + cg * PGapD) / gamma ^ 2) ≤
      (M * A + (M + r + P) * A ^ 2) / E := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hgpos : 0 < g := lt_of_lt_of_le zero_lt_one hg
  have hGEpos : 0 < g * E := mul_pos hgpos hE
  have hgammaPos : 0 < gamma := by
    rw [hgamma]
    exact div_pos hGEpos hA
  have hMrP : 0 ≤ M + r + P := by
    linarith
  have hCgP0 : 0 ≤ CgD + cg * PGapD :=
    add_nonneg hCgD.1 (mul_nonneg hcg.1 hPGapD.1)
  have hnum :
      cr * (CgD + cg * PGapD) ≤ (M + r + P) * (g * E) := by
    calc
      cr * (CgD + cg * PGapD)
          ≤ CgD + cg * PGapD := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hcr.2 hCgP0
      _ ≤ (M + r) * (g * E) + (g * E) * P := by
        have hcgP : cg * PGapD ≤ (g * E) * P := by
          calc
            cg * PGapD ≤ (g * E) * PGapD :=
              mul_le_mul_of_nonneg_right hcg.2 hPGapD.1
            _ ≤ (g * E) * P :=
              mul_le_mul_of_nonneg_left hPGapD.2 hGEpos.le
        exact add_le_add hCgD.2 hcgP
      _ = (M + r + P) * (g * E) := by
        ring
  have hMA0 : 0 ≤ M * A := mul_nonneg hM hA.le
  have hMPA0 : 0 ≤ (M + r + P) * A ^ 2 :=
    mul_nonneg hMrP (sq_nonneg A)
  have htermM : M / gamma ≤ (M * A) / E := by
    rw [hgamma]
    calc
      M / (g * E / A) = (M * A / g) / E := by
        field_simp [hgpos.ne', hE.ne', hA.ne'] <;> ring
      _ ≤ (M * A) / E :=
        div_le_div_of_nonneg_right (div_le_self hMA0 hg) hE.le
  have htermQ :
      cr * (CgD + cg * PGapD) / gamma ^ 2 ≤
        ((M + r + P) * A ^ 2) / E := by
    rw [hgamma]
    calc
      cr * (CgD + cg * PGapD) / (g * E / A) ^ 2
          ≤ ((M + r + P) * (g * E)) / (g * E / A) ^ 2 :=
            div_le_div_of_nonneg_right hnum (sq_nonneg _)
      _ = (((M + r + P) * A ^ 2) / g) / E := by
        field_simp [hgpos.ne', hE.ne', hA.ne'] <;> ring
      _ ≤ ((M + r + P) * A ^ 2) / E :=
        div_le_div_of_nonneg_right (div_le_self hMPA0 hg) hE.le
  have hinside0 :
      0 ≤ M / gamma + cr * (CgD + cg * PGapD) / gamma ^ 2 :=
    add_nonneg
      (div_nonneg hM hgammaPos.le)
      (div_nonneg (mul_nonneg hcr.1 hCgP0) (sq_nonneg gamma))
  have hNinv : 1 / N ≤ 1 := by
    rw [div_le_one hNpos]
    exact hN
  calc
    (1 / N) *
        (M / gamma + cr * (CgD + cg * PGapD) / gamma ^ 2)
        ≤ M / gamma + cr * (CgD + cg * PGapD) / gamma ^ 2 := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hNinv hinside0
    _ ≤ (M * A) / E + ((M + r + P) * A ^ 2) / E :=
      add_le_add htermM htermQ
    _ = (M * A + (M + r + P) * A ^ 2) / E := by
      ring

set_option maxRecDepth 4000 in
private theorem bgpS4_qssDeriv_pointwise_exp_of_edge_data_NW
    (w j : ℕ) (cfg : UConf) (c v : UniversalLocalView) {τ : ℝ}
    (hτ0 : 0 ≤ τ)
    (hsin : 0 ≤ Real.sin τ)
    (hutube :
      UTube r_LE_U cfg
        (((bgpHeadlineSolFamNW w) w).u τ))
    (hzu : ∀ i : Fin d_U,
      |((bgpHeadlineSolFamNW w) w).z τ i -
        ((bgpHeadlineSolFamNW w) w).u τ i| ≤
          bgpS4EdgeZUBoundNW)
    (hgap :
      (1 / 2 : ℝ) ≤
        universalPval bgpHeadlineEta bgpHeadlineEta_pos c
            (((bgpHeadlineSolFamNW w) w).u τ) -
          universalPval bgpHeadlineEta bgpHeadlineEta_pos v
            (((bgpHeadlineSolFamNW w) w).u τ)) :
    |selectorMU_activeQSSDerivRHSP
        bgpHeadlineEta bgpHeadlineEta_pos
        (bgpHeadlineSolFamNW w) w c v τ| ≤
      bgpS4aQSSDerivCoeffNW w j v *
        Real.exp (-(300 * (bgpScaleW w : ℝ) * τ)) := by
  classical
  let S : ℝ := (bgpScaleW w : ℝ)
  let r : ℝ := 300 * S
  let g : ℝ := ((bgpWarmGainQNW w : ℚ) : ℝ)
  let E : ℝ := Real.exp (r * τ)
  let A : ℝ := bgpS4GammaInvFactor
  let P : ℝ := bgpS4PGapCoeffNW
  let gamma : ℝ :=
    ((1 / 2 : ℝ) ^ bgpHeadlineM * (g * E)) * (1 / 2)
  let sol := bgpHeadlineSolFamNW w

  have hSpos : 0 < S := by
    simpa only [S] using bgpScaleWR_pos w
  have hr0 : 0 ≤ r := by
    dsimp only [r]
    exact mul_nonneg (by norm_num) hSpos.le
  have hEpos : 0 < E := Real.exp_pos _
  have hg1 : 1 ≤ g := by
    dsimp only [g]
    linarith [bgpWarmGainQNW_ge_base w]
  have hgpos : 0 < g := lt_of_lt_of_le zero_lt_one hg1
  have hApos : 0 < A := by
    simpa only [A] using bgpS4GammaInvFactor_pos
  have hP0 : 0 ≤ P := by
    simpa only [P] using bgpS4PGapCoeffNW_nonneg

  have hbase0 : 0 ≤ (1 + Real.sin τ) / 2 := by
    nlinarith [Real.neg_one_le_sin τ]
  have hbaseHalf : (1 / 2 : ℝ) ≤ (1 + Real.sin τ) / 2 := by
    linarith
  have hpowFloor :
      (1 / 2 : ℝ) ^ bgpHeadlineM ≤
        ((1 + Real.sin τ) / 2) ^ bgpHeadlineM :=
    pow_le_pow_left₀ (by norm_num) hbaseHalf bgpHeadlineM

  have hcg0 :
      0 ≤ selectorMU_activeCgP (p := bgpParamsNW w)
        bgpHeadlineM (bgpWarmGainQNW w) τ := by
    unfold selectorMU_activeCgP
    exact mul_nonneg
      (pow_nonneg hbase0 _)
      (mul_nonneg (bgpWarmGainQNW_pos_real w).le
        (Real.exp_pos _).le)

  have hgainEq :
      ((bgpWarmGainQNW w : ℚ) : ℝ) *
          Real.exp ((bgpParamsNW w).cα * τ) = g * E := by
    dsimp only [g, E, r, S]
    rw [bgpParamsNW_cα_def]

  have hcgUpper :
      selectorMU_activeCgP (p := bgpParamsNW w)
          bgpHeadlineM (bgpWarmGainQNW w) τ ≤ g * E := by
    have habs := selectorMU_activeCg_abs_le_exp_gainP
      (p := bgpParamsNW w) bgpHeadlineM (bgpWarmGainQNW w) τ
    rw [abs_of_nonneg hcg0, abs_of_pos (bgpWarmGainQNW_pos_real w)] at habs
    calc
      selectorMU_activeCgP (p := bgpParamsNW w)
          bgpHeadlineM (bgpWarmGainQNW w) τ
          ≤ ((bgpWarmGainQNW w : ℚ) : ℝ) *
              Real.exp ((bgpParamsNW w).cα * τ) := habs
      _ = g * E := hgainEq

  have hcgFloor :
      (1 / 2 : ℝ) ^ bgpHeadlineM * (g * E) ≤
        selectorMU_activeCgP (p := bgpParamsNW w)
          bgpHeadlineM (bgpWarmGainQNW w) τ := by
    unfold selectorMU_activeCgP
    rw [hgainEq]
    exact mul_le_mul_of_nonneg_right hpowFloor
      (mul_nonneg hgpos.le hEpos.le)

  have hgammaFloor :
      gamma ≤ selectorMU_activeCgP (p := bgpParamsNW w)
        bgpHeadlineM (bgpWarmGainQNW w) τ *
          (universalPval bgpHeadlineEta bgpHeadlineEta_pos c
              (((bgpHeadlineSolFamNW w) w).u τ) -
            universalPval bgpHeadlineEta bgpHeadlineEta_pos v
              (((bgpHeadlineSolFamNW w) w).u τ)) := by
    dsimp only [gamma]
    calc
      ((1 / 2 : ℝ) ^ bgpHeadlineM * (g * E)) * (1 / 2)
          ≤ selectorMU_activeCgP (p := bgpParamsNW w)
              bgpHeadlineM (bgpWarmGainQNW w) τ * (1 / 2) :=
        mul_le_mul_of_nonneg_right hcgFloor (by norm_num)
      _ ≤ selectorMU_activeCgP (p := bgpParamsNW w)
              bgpHeadlineM (bgpWarmGainQNW w) τ *
            (universalPval bgpHeadlineEta bgpHeadlineEta_pos c
                (((bgpHeadlineSolFamNW w) w).u τ) -
              universalPval bgpHeadlineEta bgpHeadlineEta_pos v
                (((bgpHeadlineSolFamNW w) w).u τ)) :=
        mul_le_mul_of_nonneg_left hgap hcg0

  have hgammaPos : 0 < gamma := by
    dsimp only [gamma]
    exact mul_pos
      (mul_pos (pow_pos (by norm_num) _)
        (mul_pos hgpos hEpos))
      (by norm_num)

  have hgammaEq : gamma = g * E / A := by
    dsimp only [gamma, A]
    unfold bgpS4GammaInvFactor
    norm_num [bgpHeadlineM]
    ring

  have hcr0 :
      0 ≤ selectorMU_activeCr bgpHeadlineM bgpHeadlineKappa τ := by
    unfold selectorMU_activeCr bgpHeadlineKappa
    have hbase : (0:ℝ) ≤ (1 + Real.cos τ) / 2 := by
      nlinarith [Real.neg_one_le_cos τ]
    positivity
  have hcr1 :
      selectorMU_activeCr bgpHeadlineM bgpHeadlineKappa τ ≤ 1 := by
    have hc0 : 0 ≤ (1 + Real.cos τ) / 2 := by
      nlinarith [Real.neg_one_le_cos τ]
    have hc1 : (1 + Real.cos τ) / 2 ≤ 1 := by
      nlinarith [Real.cos_le_one τ]
    have hp : ((1 + Real.cos τ) / 2) ^ bgpHeadlineM ≤ 1 :=
      pow_le_one₀ hc0 hc1
    simpa only [selectorMU_activeCr, bgpHeadlineKappa,
      Rat.cast_one, mul_one] using hp

  have hCrD :
      |selectorMU_activeCrDeriv
          bgpHeadlineM bgpHeadlineKappa τ| ≤
        (bgpHeadlineM : ℝ) := by
    simpa only [bgpHeadlineKappa, Rat.cast_one, abs_one, mul_one] using
      selectorMU_activeCrDeriv_abs_le
        bgpHeadlineM bgpHeadlineKappa τ

  let CgD : ℝ := ((bgpHeadlineM : ℝ) + r) * (g * E)
  have hCgD0 : 0 ≤ CgD := by
    dsimp only [CgD]
    exact mul_nonneg
      (add_nonneg (Nat.cast_nonneg _) hr0)
      (mul_nonneg hgpos.le hEpos.le)
  have hCgD :
      |selectorMU_activeCgDerivP (p := bgpParamsNW w)
        bgpHeadlineM (bgpWarmGainQNW w) τ| ≤ CgD := by
    have h := selectorMU_activeCgDeriv_abs_le_exp_gainP
      (p := bgpParamsNW w) bgpHeadlineM (bgpWarmGainQNW w) τ
    rw [abs_of_pos (bgpParamsNW_cα_pos w),
      abs_of_pos (bgpWarmGainQNW_pos_real w)] at h
    calc
      |selectorMU_activeCgDerivP (p := bgpParamsNW w)
          bgpHeadlineM (bgpWarmGainQNW w) τ|
          ≤ ((bgpHeadlineM : ℝ) + (bgpParamsNW w).cα) *
              (((bgpWarmGainQNW w : ℚ) : ℝ) *
                Real.exp ((bgpParamsNW w).cα * τ)) := h
      _ = CgD := by
        dsimp only [CgD, r, S, g, E]
        rw [bgpParamsNW_cα_def]

  have hgapB :
      |universalPval bgpHeadlineEta bgpHeadlineEta_pos c
          (((bgpHeadlineSolFamNW w) w).u τ) -
        universalPval bgpHeadlineEta bgpHeadlineEta_pos v
          (((bgpHeadlineSolFamNW w) w).u τ)| ≤ 1 := by
    rw [abs_le]
    constructor
    · have hrev := bgpHeadline_universalPval_sub_le_one_of_utube
        (eta := bgpHeadlineEta) (heta := bgpHeadlineEta_pos) hutube v c
      linarith
    · exact bgpHeadline_universalPval_sub_le_one_of_utube hutube c v

  have huRHS : ∀ i : Fin d_U,
      |selectorMU_uDerivRHSP sol w τ i| ≤ bgpS4EdgeZUBoundNW := by
    intro i
    have hk0 := bgpNW4_uKernel_nonneg w w hτ0
    have hk := bgpNW4_uKernel_le_of_sin_nonneg w w hτ0 hsin
    have hdec : Real.exp (-(200 * S * τ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith
    unfold selectorMU_uDerivRHSP
    rw [abs_mul, abs_of_nonneg hk0]
    calc
      (bgpParamsNW w).A * ((bgpHeadlineSolFamNW w) w).α τ *
          bGateU (bgpParamsNW w).L
            (((bgpHeadlineSolFamNW w) w).μ τ) τ *
        |((bgpHeadlineSolFamNW w) w).z τ i -
          ((bgpHeadlineSolFamNW w) w).u τ i|
          ≤ Real.exp (-(200 * S * τ)) * bgpS4EdgeZUBoundNW :=
        mul_le_mul hk (hzu i) (abs_nonneg _) (Real.exp_pos _).le
      _ ≤ bgpS4EdgeZUBoundNW := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hdec bgpS4EdgeZUBoundNW_nonneg

  have hpGapD :
      |selectorMU_universalPvalDerivRHSP
          bgpHeadlineEta bgpHeadlineEta_pos sol w c τ -
        selectorMU_universalPvalDerivRHSP
          bgpHeadlineEta bgpHeadlineEta_pos sol w v τ| ≤ P := by
    have hp :=
      BernsteinSlope.selectorMU_universalPvalGapDerivRHS_abs_le_selectorSlopeP
        (p := bgpParamsNW w) (sol := sol)
        w c v τ cfg hutube huRHS
    have hp' :
        |selectorMU_universalPvalDerivRHSP
            bgpHeadlineEta bgpHeadlineEta_pos sol w c τ -
          selectorMU_universalPvalDerivRHSP
            bgpHeadlineEta bgpHeadlineEta_pos sol w v τ| ≤
          (2 * ((Fintype.card (Fin d_U) : ℝ) *
            BernsteinSlope.bgpHeadlineSelectorSlopeConst)) *
              bgpS4EdgeZUBoundNW := by
      simpa only [bgpHeadlineEta, BernsteinSlope.bgpSlopeEta] using hp
    calc
      |selectorMU_universalPvalDerivRHSP
          bgpHeadlineEta bgpHeadlineEta_pos sol w c τ -
        selectorMU_universalPvalDerivRHSP
          bgpHeadlineEta bgpHeadlineEta_pos sol w v τ|
          ≤ (2 * ((Fintype.card (Fin d_U) : ℝ) *
              BernsteinSlope.bgpHeadlineSelectorSlopeConst)) *
                bgpS4EdgeZUBoundNW := hp'
      _ = P := by
        dsimp only [P]
        unfold bgpS4PGapCoeffNW
        ring

  have hmaster :=
    selectorMU_activeQSSDerivRHS_abs_le_of_gap_and_pvalDeriv_boundsP
      bgpHeadlineEta bgpHeadlineEta_pos
      (p := bgpParamsNW w) (sol := sol)
      w c v τ
      (gamma := gamma)
      (CrD := (bgpHeadlineM : ℝ))
      (CgD := CgD)
      (GapB := 1)
      (PGapD := P)
      hgammaPos hcr0 hcg0 hgammaFloor hCrD hCgD hgapB hpGapD

  have hcard : (1 : ℝ) ≤ Fintype.card UniversalLocalView := by
    exact_mod_cast le_trans (by norm_num : 1 ≤ 2) bgpHeadlineHCardTwo
  have hscalar := bgpS4_qss_scalar_cancel
    (N := (Fintype.card UniversalLocalView : ℝ))
    (g := g) (E := E) (A := A)
    (M := (bgpHeadlineM : ℝ)) (r := r) (P := P)
    (cr := selectorMU_activeCr bgpHeadlineM bgpHeadlineKappa τ)
    (CgD := CgD)
    (cg := selectorMU_activeCgP (p := bgpParamsNW w)
      bgpHeadlineM (bgpWarmGainQNW w) τ)
    (PGapD := P) (gamma := gamma)
    hcard hg1 hEpos hApos (Nat.cast_nonneg _) hr0 hP0
    ⟨hcr0, hcr1⟩
    ⟨hCgD0, le_rfl⟩
    ⟨hcg0, hcgUpper⟩
    ⟨hP0, le_rfl⟩ hgammaEq

  calc
    |selectorMU_activeQSSDerivRHSP
        bgpHeadlineEta bgpHeadlineEta_pos sol w c v τ|
        ≤ (1 / (Fintype.card UniversalLocalView : ℝ)) *
          ((bgpHeadlineM : ℝ) / gamma +
            selectorMU_activeCr bgpHeadlineM bgpHeadlineKappa τ *
              (CgD * 1 +
                selectorMU_activeCgP (p := bgpParamsNW w)
                  bgpHeadlineM (bgpWarmGainQNW w) τ * P) /
                gamma ^ 2) := hmaster
    _ ≤ ((bgpHeadlineM : ℝ) * A +
          ((bgpHeadlineM : ℝ) + r + P) * A ^ 2) / E := by
      simpa only [mul_one] using hscalar
    _ = bgpS4aQSSDerivCoeffNW w j v *
        Real.exp (-(300 * (bgpScaleW w : ℝ) * τ)) := by
      dsimp only [A, P, r, S, E]
      unfold bgpS4aQSSDerivCoeffNW
      rw [div_eq_mul_inv, Real.exp_neg]

private theorem bgpS4a_qssDeriv_pointwise_exp_NW
    (w j : ℕ) (v : UniversalLocalView)
    (hv : v ≠ localViewU (solMUReplStaticCfg w j))
    (τ : ℝ)
    (hτ : τ ∈ Icc (selectorMUInterReadStart j)
      (selectorMUZOffStart j)) :
    |selectorMU_activeQSSDerivRHSP
        bgpHeadlineEta bgpHeadlineEta_pos
        (bgpHeadlineSolFamNW w) w
        (localViewU (solMUReplStaticCfg w j)) v τ| ≤
      bgpS4aQSSDerivCoeffNW w j v *
        Real.exp (-(300 * (bgpScaleW w : ℝ) * τ)) := by
  have hτ0 : 0 ≤ τ := by
    have ha0 : 0 ≤ selectorMUInterReadStart j := by
      unfold selectorMUInterReadStart selectorMUWriteReadTime
      positivity
    exact le_trans ha0 hτ.1
  have hsin : 0 ≤ Real.sin τ :=
    sin_nonneg_on_handoff_piece1 j
      (by simpa only [selectorMUInterReadStart, selectorMUWriteReadTime] using hτ.1)
      (by simpa only [selectorMUZOffStart] using hτ.2)
  have htube :
      UTube r_LE_U (bgpF1Cfg w j)
        (((bgpHeadlineSolFamNW w) w).u τ) :=
    bgpSegC_edge_tube_NW w j τ
      ⟨le_trans (selectorMUWriteStart_le_read j) hτ.1, hτ.2⟩
  have hzu : ∀ i : Fin d_U,
      |((bgpHeadlineSolFamNW w) w).z τ i -
        ((bgpHeadlineSolFamNW w) w).u τ i| ≤
          bgpS4EdgeZUBoundNW := by
    intro i
    exact bgpS4_edge_zu_envelope_NW w j i τ
      (by simpa only [selectorMUInterReadStart, selectorMUWriteReadTime] using hτ)
  have hgap := bgpS4a_gapFloor_NW w j v hv τ hτ
  exact bgpS4_qssDeriv_pointwise_exp_of_edge_data_NW
    w j (bgpF1Cfg w j) (localViewU (solMUReplStaticCfg w j)) v
    hτ0 hsin htube hzu hgap

/-! ### Shallow exponential-currency helpers -/

private theorem bgpS4_two_le_exp_one :
    (2 : ℝ) ≤ Real.exp 1 := by
  have h := Real.add_one_le_exp (1 : ℝ)
  norm_num at h ⊢
  exact h

private theorem bgpS4_three_le_exp_two :
    (3 : ℝ) ≤ Real.exp 2 := by
  have hsplit : Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  rw [hsplit]
  nlinarith [bgpS4_two_le_exp_one, Real.exp_pos (1 : ℝ)]

private theorem bgpS4_three_hundred_le_exp_six :
    (300 : ℝ) ≤ Real.exp 6 := by
  have h20 := bgpNW4_exp_three_ge
  have hsplit : Real.exp (6 : ℝ) = Real.exp 3 * Real.exp 3 := by
    rw [show (6 : ℝ) = 3 + 3 by norm_num, Real.exp_add]
  rw [hsplit]
  nlinarith [h20, Real.exp_pos (3 : ℝ)]

private theorem bgpS4_one_hundred_thousand_le_exp_twelve :
    (100000 : ℝ) ≤ Real.exp 12 := by
  have h20 := bgpNW4_exp_three_ge
  have hE3 : 0 < Real.exp (3 : ℝ) := Real.exp_pos _
  have h6 : (400 : ℝ) ≤ Real.exp 3 * Real.exp 3 := by
    nlinarith
  have h9 : (8000 : ℝ) ≤ Real.exp 3 * Real.exp 3 * Real.exp 3 := by
    nlinarith
  have h12 : (160000 : ℝ) ≤
      Real.exp 3 * Real.exp 3 * Real.exp 3 * Real.exp 3 := by
    nlinarith
  have hsplit : Real.exp (12 : ℝ) =
      Real.exp 3 * Real.exp 3 * Real.exp 3 * Real.exp 3 := by
    rw [show (12 : ℝ) = 3 + 3 + 3 + 3 by norm_num,
      Real.exp_add, Real.exp_add, Real.exp_add]
  rw [hsplit]
  linarith

private theorem bgpS4_pow_le_exp_nat_mul
    {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x ^ n ≤ Real.exp ((n : ℝ) * x) := by
  have hxexp : x ≤ Real.exp x := by
    have h := Real.add_one_le_exp x
    linarith
  calc
    x ^ n ≤ (Real.exp x) ^ n :=
      pow_le_pow_left₀ hx hxexp n
    _ = Real.exp ((n : ℝ) * x) :=
      (Real.exp_nat_mul x n).symm

private theorem bgpS4GammaInvFactor_le_exp_21 :
    bgpS4GammaInvFactor ≤ Real.exp 21 := by
  have hp : (2 : ℝ) ^ 21 ≤ (Real.exp 1) ^ 21 :=
    pow_le_pow_left₀ (by norm_num) bgpS4_two_le_exp_one 21
  have hexp : (Real.exp 1) ^ 21 = Real.exp 21 := by
    simpa using (Real.exp_nat_mul (1 : ℝ) 21).symm
  unfold bgpS4GammaInvFactor
  norm_num [bgpHeadlineM]
  have h221 : (2097152 : ℝ) = (2:ℝ)^21 := by norm_num
  rw [h221]
  exact hp.trans_eq hexp

private theorem bgpS4GammaInvFactor_sq_le_exp_42 :
    bgpS4GammaInvFactor ^ 2 ≤ Real.exp 42 := by
  have hp := pow_le_pow_left₀ bgpS4GammaInvFactor_pos.le
    bgpS4GammaInvFactor_le_exp_21 2
  calc
    bgpS4GammaInvFactor ^ 2 ≤ (Real.exp 21) ^ 2 := hp
    _ = Real.exp 42 := by
      rw [← Real.exp_nat_mul]; norm_num

private theorem bgpS4EdgeZUBoundNW_le_exp_currency
    (w : ℕ) :
    bgpS4EdgeZUBoundNW ≤
      Real.exp (20 * (bgpScaleW w : ℝ) + 220) := by
  let S : ℝ := (bgpScaleW w : ℝ)
  have hS4 : (4 : ℝ) ≤ S := by
    simpa only [S] using bgpScaleWR_ge_four w
  have hS1 : (1 : ℝ) ≤ S := le_trans (by norm_num) hS4
  have hS0 : 0 ≤ S := le_trans (by norm_num) hS4
  have hD : D_U ≤ 2 * S := by
    simpa only [S] using D_U_le_two_bgpScaleW w
  have hD0 : 0 ≤ D_U := D_U_nonneg
  have h4000D : 4000 * D_U ≤ 8000 * S := by
    nlinarith
  have h5D : 5 * D_U + 2 ≤ 10 * S + 2 := by
    nlinarith
  have hprod :
      4000 * D_U * (5 * D_U + 2) ≤
        (8000 * S) * (10 * S + 2) := by
    exact mul_le_mul h4000D h5D
      (by nlinarith [hD0]) (by nlinarith [hS0])
  have hSleS2 : S ≤ S ^ 2 := by
    have hmul : 0 ≤ S * (S - 1) :=
      mul_nonneg hS0 (sub_nonneg.mpr hS1)
    nlinarith [sq_nonneg S]
  have h1leS2 : (1 : ℝ) ≤ S ^ 2 := by
    nlinarith
  have hpoly :
      (2 * D_U + 4000 * D_U * (5 * D_U + 2)) +
          4 * D_U + 2 ≤ 100000 * S ^ 2 := by
    nlinarith
  have hbaseScale : (bgpScale : ℝ) ≤ S := by
    simpa only [S] using bgpScaleR_le_bgpScaleWR w
  have hCwin : bgpF1CwinDefN ≤ S * Real.exp 200 := by
    exact le_trans bgpF1CwinDefN_le_scale_exp200
      (mul_le_mul_of_nonneg_right hbaseScale (Real.exp_pos _).le)
  have hraw :
      bgpS4EdgeZUBoundNW ≤
        100000 * S ^ 2 + S * Real.exp 200 := by
    unfold bgpS4EdgeZUBoundNW
    nlinarith
  have hS2exp : S ^ 2 ≤ Real.exp (2 * S) := by
    simpa using bgpS4_pow_le_exp_nat_mul hS0 2
  have hpolyExp :
      100000 * S ^ 2 ≤ Real.exp (2 * S + 12) := by
    calc
      100000 * S ^ 2 ≤ Real.exp 12 * Real.exp (2 * S) :=
        mul_le_mul bgpS4_one_hundred_thousand_le_exp_twelve
          hS2exp (sq_nonneg S) (Real.exp_pos _).le
      _ = Real.exp (2 * S + 12) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hSexp : S ≤ Real.exp S := by
    have h := Real.add_one_le_exp S
    linarith
  have hCexp : S * Real.exp 200 ≤ Real.exp (S + 200) := by
    calc
      S * Real.exp 200 ≤ Real.exp S * Real.exp 200 :=
        mul_le_mul_of_nonneg_right hSexp (Real.exp_pos _).le
      _ = Real.exp (S + 200) := by
        rw [← Real.exp_add]
  let X : ℝ := 20 * S + 219
  have hpolyX : Real.exp (2 * S + 12) ≤ Real.exp X := by
    apply Real.exp_le_exp.mpr
    dsimp only [X]
    nlinarith
  have hCX : Real.exp (S + 200) ≤ Real.exp X := by
    apply Real.exp_le_exp.mpr
    dsimp only [X]
    nlinarith
  calc
    bgpS4EdgeZUBoundNW
        ≤ 100000 * S ^ 2 + S * Real.exp 200 := hraw
    _ ≤ Real.exp (2 * S + 12) + Real.exp (S + 200) :=
      add_le_add hpolyExp hCexp
    _ ≤ Real.exp X + Real.exp X :=
      add_le_add hpolyX hCX
    _ = 2 * Real.exp X := by ring
    _ ≤ Real.exp 1 * Real.exp X :=
      mul_le_mul_of_nonneg_right bgpS4_two_le_exp_one
        (Real.exp_pos _).le
    _ = Real.exp (20 * S + 220) := by
      rw [← Real.exp_add]
      dsimp only [X]
      congr 1
      ring

private theorem bgpS4PGapCoeffNW_le_exp_currency
    (w : ℕ) :
    bgpS4PGapCoeffNW ≤
      Real.exp (40 * (bgpScaleW w : ℝ) + 423) := by
  let S : ℝ := (bgpScaleW w : ℝ)
  have h12 : (12 : ℝ) ≤ Real.exp 3 := by
    linarith [bgpNW4_exp_three_ge]
  have hslope :=
    BernsteinSlope.bgpHeadlineSelectorSlopeConst_le_exp_currency_NW w
  have hedge := bgpS4EdgeZUBoundNW_le_exp_currency w
  have hdef :
      bgpS4PGapCoeffNW =
        12 * BernsteinSlope.bgpHeadlineSelectorSlopeConst *
          bgpS4EdgeZUBoundNW := by
    unfold bgpS4PGapCoeffNW
    norm_num [d_U]
  rw [hdef]
  calc
    12 * BernsteinSlope.bgpHeadlineSelectorSlopeConst *
        bgpS4EdgeZUBoundNW
        ≤ Real.exp 3 *
            Real.exp (20 * S + 200) *
              Real.exp (20 * S + 220) := by
      exact mul_le_mul
        (mul_le_mul h12 (by simpa only [S] using hslope)
          BernsteinSlope.bgpHeadlineSelectorSlopeConst_nonneg
          (Real.exp_pos _).le)
        (by simpa only [S] using hedge)
        bgpS4EdgeZUBoundNW_nonneg
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = Real.exp (40 * S + 423) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

private theorem bgpS4aQSSDerivCoeffNW_le_exp_currency
    (w j : ℕ) (v : UniversalLocalView) :
    bgpS4aQSSDerivCoeffNW w j v ≤
      Real.exp (40 * (bgpScaleW w : ℝ) + 468) := by
  set S : ℝ := (bgpScaleW w : ℝ) with hS
  clear_value S
  let X : ℝ := 40 * S + 423
  let Y : ℝ := 40 * S + 467
  have hS4 : (4 : ℝ) ≤ S := by
    simpa only [hS] using bgpScaleWR_ge_four w
  have hS0 : 0 ≤ S := le_trans (by norm_num) hS4
  have hM3 : (bgpHeadlineM : ℝ) ≤ Real.exp 3 := by
    simpa only [bgpHeadlineM] using bgpNW4_exp_three_ge
  have hSexp : S ≤ Real.exp S := by
    have h := Real.add_one_le_exp S
    linarith
  have hrExp : 300 * S ≤ Real.exp (S + 6) := by
    calc
      300 * S ≤ Real.exp 6 * Real.exp S :=
        mul_le_mul bgpS4_three_hundred_le_exp_six
          hSexp hS0 (Real.exp_pos _).le
      _ = Real.exp (S + 6) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hP := bgpS4PGapCoeffNW_le_exp_currency w
  have hM_X : (bgpHeadlineM : ℝ) ≤ Real.exp X := by
    exact le_trans hM3 (Real.exp_le_exp.mpr (by dsimp only [X]; nlinarith))
  have hr_X : 300 * S ≤ Real.exp X := by
    exact le_trans hrExp
      (Real.exp_le_exp.mpr (by dsimp only [X]; nlinarith))
  have hP_X : bgpS4PGapCoeffNW ≤ Real.exp X := by
    simpa only [X, hS] using hP
  have hsum :
      (bgpHeadlineM : ℝ) + 300 * S + bgpS4PGapCoeffNW ≤
        3 * Real.exp X := by
    nlinarith
  have hsumExp :
      (bgpHeadlineM : ℝ) + 300 * S + bgpS4PGapCoeffNW ≤
        Real.exp (X + 2) := by
    calc
      (bgpHeadlineM : ℝ) + 300 * S + bgpS4PGapCoeffNW
          ≤ 3 * Real.exp X := hsum
      _ ≤ Real.exp 2 * Real.exp X :=
        mul_le_mul_of_nonneg_right bgpS4_three_le_exp_two
          (Real.exp_pos _).le
      _ = Real.exp (X + 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hA0 : 0 ≤ bgpS4GammaInvFactor := bgpS4GammaInvFactor_pos.le
  have hA21 := bgpS4GammaInvFactor_le_exp_21
  have hA42 := bgpS4GammaInvFactor_sq_le_exp_42
  have hfirst :
      (bgpHeadlineM : ℝ) * bgpS4GammaInvFactor ≤ Real.exp Y := by
    calc
      (bgpHeadlineM : ℝ) * bgpS4GammaInvFactor
          ≤ Real.exp 3 * Real.exp 21 :=
        mul_le_mul hM3 hA21 hA0 (Real.exp_pos _).le
      _ = Real.exp 24 := by
        rw [← Real.exp_add]
        norm_num
      _ ≤ Real.exp Y :=
        Real.exp_le_exp.mpr (by dsimp only [Y]; nlinarith)
  have hsecond :
      ((bgpHeadlineM : ℝ) + 300 * S + bgpS4PGapCoeffNW) *
          bgpS4GammaInvFactor ^ 2 ≤ Real.exp Y := by
    calc
      ((bgpHeadlineM : ℝ) + 300 * S + bgpS4PGapCoeffNW) *
          bgpS4GammaInvFactor ^ 2
          ≤ Real.exp (X + 2) * Real.exp 42 :=
        mul_le_mul hsumExp hA42 (sq_nonneg _) (Real.exp_pos _).le
      _ = Real.exp Y := by
        rw [← Real.exp_add]
        dsimp only [X, Y]
        congr 1
        ring
  unfold bgpS4aQSSDerivCoeffNW
  rw [← hS]
  calc
    (bgpHeadlineM : ℝ) * bgpS4GammaInvFactor +
        ((bgpHeadlineM : ℝ) + 300 * S + bgpS4PGapCoeffNW) *
          bgpS4GammaInvFactor ^ 2
        ≤ Real.exp Y + Real.exp Y := add_le_add hfirst hsecond
    _ = 2 * Real.exp Y := by ring
    _ ≤ Real.exp 1 * Real.exp Y :=
      mul_le_mul_of_nonneg_right bgpS4_two_le_exp_one
        (Real.exp_pos _).le
    _ = Real.exp (40 * S + 468) := by
      rw [← Real.exp_add]
      dsimp only [Y]
      congr 1
      ring

private theorem bgpS4a_qssCoeff_sum_le_exp_currency_NW
    (w j : ℕ) :
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => bgpS4aQSSDerivCoeffNW w j v) ≤
      Real.exp (100 * (bgpScaleW w : ℝ) + 1000) := by
  classical
  set S : ℝ := (bgpScaleW w : ℝ) with hS
  clear_value S
  let bad : Finset UniversalLocalView :=
    Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))
  have hcard : (bad.card : ℝ) ≤ S ^ 6 := by
    have h1 : bad.card ≤ Fintype.card UniversalLocalView := by
      simpa only [Finset.card_univ] using
        Finset.card_le_card (Finset.filter_subset
          (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w j) ∧
              v ≠ localViewU (solMUReplStaticCfg w (j + 1)))
          Finset.univ)
    have h2 := cardUniversalLocalView_le_bgpScale_pow_six
    have h3 : bgpScale ^ 6 ≤ bgpScaleW w ^ 6 :=
      Nat.pow_le_pow_left (bgpScale_le_bgpScaleW w) 6
    rw [hS]
    exact_mod_cast le_trans h1 (le_trans h2 h3)
  have hS0 : 0 ≤ S := by
    simpa only [hS] using (bgpScaleWR_pos w).le
  have hS6 : S ^ 6 ≤ Real.exp (6 * S) := by
    simpa using bgpS4_pow_le_exp_nat_mul hS0 6
  have hterm : ∀ v : UniversalLocalView,
      bgpS4aQSSDerivCoeffNW w j v ≤ Real.exp (40 * S + 468) := by
    intro v
    simpa only [hS] using bgpS4aQSSDerivCoeffNW_le_exp_currency w j v
  change bad.sum (fun v => bgpS4aQSSDerivCoeffNW w j v) ≤
    Real.exp (100 * S + 1000)
  calc
    bad.sum (fun v => bgpS4aQSSDerivCoeffNW w j v)
        ≤ bad.sum (fun _ => Real.exp (40 * S + 468)) := by
      exact Finset.sum_le_sum fun v _hv => hterm v
    _ = (bad.card : ℝ) * Real.exp (40 * S + 468) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ S ^ 6 * Real.exp (40 * S + 468) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ ≤ Real.exp (6 * S) * Real.exp (40 * S + 468) :=
      mul_le_mul_of_nonneg_right hS6 (Real.exp_pos _).le
    _ = Real.exp (46 * S + 468) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (100 * S + 1000) := by
      apply Real.exp_le_exp.mpr
      nlinarith

private theorem selectorMUHoffEdgeBudgetCoeff_ge_seven :
    (7 : ℝ) ≤ selectorMUHoffEdgeBudgetCoeff := by
  unfold selectorMUHoffEdgeBudgetCoeff
  linarith [selectorReplicatorHoldEnvelopeCoeff_ge_eight]

/-- A coefficient bounded by `exp (100*S+1000)` fits the unchanged edge budget. -/
private theorem bgpS4a_exp_currency_le_budget_div_32_NW
    (w j : ℕ) {K : ℝ}
    (hK : K ≤ Real.exp (100 * (bgpScaleW w : ℝ) + 1000)) :
    (K / (300 * (bgpScaleW w : ℝ))) *
      Real.exp (-(300 * (bgpScaleW w : ℝ) *
        selectorMUInterReadStart j)) ≤
      selectorMUHoffEdgeBudget3992 j / 32 := by
  let S : ℝ := (bgpScaleW w : ℝ)
  let a : ℝ := selectorMUInterReadStart j
  let T : ℝ := 2 * Real.pi * (j : ℝ) + Real.pi
  have hS4 : (4 : ℝ) ≤ S := by
    simpa only [S] using bgpScaleWR_ge_four w
  have hSpos : 0 < S := lt_of_lt_of_le (by norm_num) hS4
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hmargin :
      100 * S + 1000 + 200 * T ≤ 300 * S * a := by
    dsimp only [a, T]
    unfold selectorMUInterReadStart selectorMUWriteReadTime
    have hpi := Real.pi_gt_three
    have hS4 := bgpScaleWR_ge_four w
    have hS0 : (0:ℝ) ≤ (bgpScaleW w : ℝ) := le_trans (by norm_num) hS4
    have hj := (Nat.cast_nonneg j : (0:ℝ) ≤ (j:ℝ))
    nlinarith [hpi, hS4, hS0, hj, mul_nonneg hj Real.pi_pos.le, mul_nonneg (mul_nonneg hS0 hj) Real.pi_pos.le, mul_nonneg hS0 Real.pi_pos.le]
  have hKexp :
      K * Real.exp (-(300 * S * a)) ≤ Real.exp (-(200 * T)) := by
    calc
      K * Real.exp (-(300 * S * a))
          ≤ Real.exp (100 * S + 1000) *
              Real.exp (-(300 * S * a)) :=
        mul_le_mul_of_nonneg_right
          (by simpa only [S] using hK) (Real.exp_pos _).le
      _ = Real.exp (100 * S + 1000 - 300 * S * a) := by
        rw [← Real.exp_add]
        ring_nf
      _ ≤ Real.exp (-(200 * T)) := by
        apply Real.exp_le_exp.mpr
        linarith
  have hcoef : 1 / (300 * S) ≤ (7 : ℝ) / 32 := by
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num : (0 : ℝ) < 32)]
    nlinarith
  have hleft :
      (K / (300 * S)) * Real.exp (-(300 * S * a)) ≤
        (7 / 32) * Real.exp (-(200 * T)) := by
    calc
      (K / (300 * S)) * Real.exp (-(300 * S * a))
          = (1 / (300 * S)) *
              (K * Real.exp (-(300 * S * a))) := by ring
      _ ≤ (1 / (300 * S)) * Real.exp (-(200 * T)) :=
        mul_le_mul_of_nonneg_left hKexp (by positivity)
      _ ≤ (7 / 32) * Real.exp (-(200 * T)) :=
        mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
  unfold selectorMUHoffEdgeBudget3992 selectorMUHoffEdgeBudget
  rw [show bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L -
      bgpParams38.cα = 200 by norm_num [bgpParams38]]
  change (K / (300 * S)) * Real.exp (-(300 * S * a)) ≤
    (selectorMUHoffEdgeBudgetCoeff * Real.exp (-(200 * T))) / 32
  calc
    (K / (300 * S)) * Real.exp (-(300 * S * a))
        ≤ (7 / 32) * Real.exp (-(200 * T)) := hleft
    _ ≤ (selectorMUHoffEdgeBudgetCoeff / 32) *
          Real.exp (-(200 * T)) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right selectorMUHoffEdgeBudgetCoeff_ge_seven
          (by norm_num))
        (Real.exp_pos _).le
    _ = (selectorMUHoffEdgeBudgetCoeff * Real.exp (-(200 * T))) / 32 := by
      ring

private theorem bgpS4a_qssDeriv_exp_budget_NW (w j : ℕ) :
    ((((Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => bgpS4aQSSDerivCoeffNW w j v)) /
        (300 * (bgpScaleW w : ℝ))) *
      Real.exp (-(300 * (bgpScaleW w : ℝ) *
        selectorMUInterReadStart j))) ≤
      selectorMUHoffEdgeBudget3992 j / 32 := by
  exact bgpS4a_exp_currency_le_budget_div_32_NW w j
    (bgpS4a_qssCoeff_sum_le_exp_currency_NW w j)

private theorem bgpS4a_activeSink_pos_NW
    (w j : ℕ) (v : UniversalLocalView)
    (hv : v ≠ localViewU (solMUReplStaticCfg w j))
    {τ : ℝ}
    (hτ : τ ∈ Icc (selectorMUInterReadStart j)
      (selectorMUZOffStart j)) :
    0 < selectorMU_activeSinkP
      bgpHeadlineEta bgpHeadlineEta_pos
      (bgpHeadlineSolFamNW w) w
      (localViewU (solMUReplStaticCfg w j)) v τ := by
  have hsin : 0 ≤ Real.sin τ :=
    sin_nonneg_on_handoff_piece1 j
      (by simpa only [selectorMUInterReadStart, selectorMUWriteReadTime] using hτ.1)
      (by simpa only [selectorMUZOffStart] using hτ.2)
  have hgap := bgpS4a_gapFloor_NW w j v hv τ hτ
  have hfloor := bgpS4_sink_ge_of_gap_half_NW w
    (localViewU (solMUReplStaticCfg w j)) v hsin hgap
  have hpow : 0 < (1 / 2 : ℝ) ^ bgpHeadlineM :=
    pow_pos (by norm_num) _
  have hgain :
      0 < ((bgpWarmGainQNW w : ℚ) : ℝ) *
        Real.exp ((bgpParamsNW w).cα * τ) :=
    mul_pos (bgpWarmGainQNW_pos_real w) (Real.exp_pos _)
  have hbasePos :
      0 < (1 / 2 : ℝ) ^ bgpHeadlineM *
        (((bgpWarmGainQNW w : ℚ) : ℝ) *
          Real.exp ((bgpParamsNW w).cα * τ)) * (1 / 2) :=
    mul_pos (mul_pos hpow hgain) (by norm_num)
  exact lt_of_lt_of_le hbasePos hfloor

/-- Dossier statement: no leading factor `2`. -/
theorem bgpS4a_qssDerivMass_le_NW (w j : ℕ) :
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
      (fun v =>
        ∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
          |selectorMU_activeQSSDerivRHSP
            bgpHeadlineEta bgpHeadlineEta_pos
            (bgpHeadlineSolFamNW w) w
            (localViewU (solMUReplStaticCfg w j)) v τ|) ≤
      selectorMUHoffEdgeBudget3992 j / 32 := by
  classical
  let sol := bgpHeadlineSolFamNW w
  let c : UniversalLocalView := localViewU (solMUReplStaticCfg w j)
  let a : ℝ := selectorMUInterReadStart j
  let b : ℝ := selectorMUZOffStart j
  let S : ℝ := (bgpScaleW w : ℝ)
  let r : ℝ := 300 * S
  let bad : Finset UniversalLocalView :=
    Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))
  let K : UniversalLocalView → ℝ :=
    fun v => bgpS4aQSSDerivCoeffNW w j v
  have hab : a ≤ b := by
    simpa only [a, b] using selectorMUInterReadStart_le_zOffStart j
  have hr : 0 < r := by
    dsimp only [r, S]
    nlinarith [bgpScaleWR_pos w]
  have hK0 : ∀ v ∈ bad, 0 ≤ K v := by
    intro v _hv
    exact bgpS4aQSSDerivCoeffNW_nonneg w j v
  have hsink : ∀ v ∈ bad, ∀ τ ∈ Icc a b,
      0 < selectorMU_activeSinkP
        bgpHeadlineEta bgpHeadlineEta_pos sol w c v τ := by
    intro v hv τ hτ
    have hvOld := (Finset.mem_filter.mp hv).2.1
    exact bgpS4a_activeSink_pos_NW w j v hvOld
      (by simpa only [a, b, c] using hτ)
  have hcont : ∀ v ∈ bad,
      ContinuousOn
        (fun τ => selectorMU_activeQSSDerivRHSP
          bgpHeadlineEta bgpHeadlineEta_pos sol w c v τ)
        (Icc a b) := by
    intro v hv
    exact selectorMU_activeQSSDerivRHS_continuousOn_of_sink_posP
      (p := bgpParamsNW w) (sol := sol) w c v (hsink v hv)
  have hpoint : ∀ v ∈ bad, ∀ τ ∈ Icc a b,
      |selectorMU_activeQSSDerivRHSP
        bgpHeadlineEta bgpHeadlineEta_pos sol w c v τ| ≤
        K v * Real.exp (-(r * τ)) := by
    intro v hv τ hτ
    have hvOld := (Finset.mem_filter.mp hv).2.1
    have hp := bgpS4a_qssDeriv_pointwise_exp_NW
      w j v hvOld τ (by simpa only [a, b] using hτ)
    simpa only [sol, c, K, r, S] using hp
  have hbudget :
      ((bad.sum K) / r) * Real.exp (-(r * a)) ≤
        selectorMUHoffEdgeBudget3992 j / 32 := by
    simpa only [bad, K, r, S, a] using
      bgpS4a_qssDeriv_exp_budget_NW w j
  have hsum :=
    finset_sum_integral_abs_le_exp_decay_budget
      bad
      (F := fun v τ =>
        selectorMU_activeQSSDerivRHSP
          bgpHeadlineEta bgpHeadlineEta_pos sol w c v τ)
      (C := K) (r := r) (a := a) (b := b)
      hr hab hK0 hcont hpoint hbudget
  simpa only [sol, c, a, b, bad, K, r, S] using hsum

/-! ### S4b bridge tube + gap floor (right edge, new center `cfg (j+1)`)

The S4b analytic leaves are the `j → j+1` twins of the S4a leaves, with the
winner center on the *new* configuration `solMUReplStaticCfg w (j+1)` and the
window shifted to the right edge `[zOffEnd j, nextWriteStart j] =
[2π(j+1), 2π(j+1)+π/2]`.  Q4175 verified that the entire twin family reduces to
the single bridge tube below; once it lands, every S4b leaf is the S4a proof
with `k := j+1`. -/

/-- **S4b bridge: the right-edge new-center `u`-tube persists across the full
S4b window** `[zOffEnd j, nextWriteStart j] = [2π(j+1), 2π(j+1)+π/2]`.

ROUTE: the window splits at `writeStart (j+1) = 2π(j+1)+π/6`.
* Prewrite gap `[2π(j+1), ws (j+1)]` — the S2 copy/trapping proof gives the
  new-center tube at `zOffEnd` with the sharper radius `19r/20`.  The landed
  NW tail third-tube bounds `|z-u|` by `4D_U+3`; the off-phase u-kernel then
  moves `u` by at most the tail currency, sharpened here to `r/20`.
* Write prefix `[ws (j+1), 2π(j+1)+π/2] ⊆ [ws (j+1), wr (j+1)]` — Seg C edge
  tube at `j+1` (`bgpSegC_edge_tube_NW w (j+1)`). -/
theorem bgpS4b_right_edge_tube_persist_NW (w j : ℕ) :
    ∀ t ∈ Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j),
      UTube r_LE_U (solMUReplStaticCfg w (j + 1))
        (((bgpHeadlineSolFamNW w) w).u t) := by
  let sol := (bgpHeadlineSolFamNW w) w
  let cfg := solMUReplStaticCfg w (j + 1)
  let a : ℝ := selectorMUZOffEnd j
  let b : ℝ := selectorMUWriteStartTime (j + 1)

  have hdelta0 : 0 ≤ 9 * r_LE_U / 20 := by
    norm_num [r_LE_U]
  rcases bgpS2_handoff_entry_NW w j with ⟨hzEntry, huEntry⟩
  have box := bgpS2_window_firstExit_box_NW w j
    hdelta0 (le_refl (9 * r_LE_U / 20)) hzEntry huEntry
  have hzT := bgpS2_z_tube_lower_half_NW w j box hzEntry
  have hHcap : bgpS2LowerHalfZDriftNW w j ≤ r_LE_U / 4 := by
    unfold bgpS2LowerHalfZDriftNW
    exact bgpS2_firstExit_z_drift_cap_NW w j

  have hcopy_entry : ∀ i : Fin d_U,
      |sol.u (2 * Real.pi * (j : ℝ) + 4 * Real.pi / 3) i -
        stackMachineEncodingU.enc cfg i| ≤ 4 * D_U + 2 := by
    intro i
    have hcmem : (2 * Real.pi * (j : ℝ) + 4 * Real.pi / 3) ∈
        Icc (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6)
          (2 * Real.pi * (j : ℝ) + 2 * Real.pi) := by
      constructor <;> linarith [Real.pi_pos]
    have hu := box.hu _ hcmem i
    have henc := bgpNW4_enc_abs cfg i
    have htri := abs_sub
      (sol.u (2 * Real.pi * (j : ℝ) + 4 * Real.pi / 3) i)
      (stackMachineEncodingU.enc cfg i)
    dsimp only [sol, cfg] at hu htri ⊢
    unfold bgpS2GuardCu at hu
    linarith

  have hdeltaZ0 : 0 ≤ 9 * r_LE_U / 20 + bgpS2LowerHalfZDriftNW w j :=
    add_nonneg hdelta0 (bgpS2LowerHalfZDriftNW_nonneg w j)
  have hcopy : ∀ i : Fin d_U,
      |sol.u (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 3) i -
        stackMachineEncodingU.enc cfg i| ≤
          Real.exp (-bgpS2CopyMassLowerNW w j) * (4 * D_U + 2) +
            (9 * r_LE_U / 20 + bgpS2LowerHalfZDriftNW w j) := by
    intro i
    simpa only [sol, cfg] using
      bgpS2_u_copy_contract_NW w w j i hdeltaZ0 (hcopy_entry i)
        (fun t ht => hzT t
          ⟨le_trans (by linarith [Real.pi_pos]) ht.1,
            le_trans ht.2 (by linarith [Real.pi_pos])⟩ i)

  have hpost : ∀ i : Fin d_U, ∀ t ∈ Icc
      (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 3)
      (2 * Real.pi * (j : ℝ) + 2 * Real.pi),
      |sol.u t i - stackMachineEncodingU.enc cfg i| ≤
        Real.exp (-bgpS2CopyMassLowerNW w j) * (4 * D_U + 2) +
          (9 * r_LE_U / 20 + bgpS2LowerHalfZDriftNW w j) := by
    intro i
    have hde : 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 3 ≤
        2 * Real.pi * (j : ℝ) + 2 * Real.pi := by
      linarith [Real.pi_pos]
    have hd0 : 0 ≤ 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 3 := by
      positivity
    have hG0 : 0 ≤
        Real.exp (-bgpS2CopyMassLowerNW w j) * (4 * D_U + 2) :=
      mul_nonneg (Real.exp_pos _).le (by nlinarith [D_U_nonneg])
    exact relax_abs_trap
      (fun τ => sol.u τ i) (fun τ => sol.z τ i)
      (fun τ => (bgpParamsNW w).A * sol.α τ *
        bGateU (bgpParamsNW w).L (sol.μ τ) τ)
      (M := stackMachineEncodingU.enc cfg i)
      (δ := Real.exp (-bgpS2CopyMassLowerNW w j) * (4 * D_U + 2) +
        (9 * r_LE_U / 20 + bgpS2LowerHalfZDriftNW w j))
      hde (by simpa only [sol] using bgpNW4_uKernel_continuous w w)
      (sol.cont_z i)
      (fun t ht => sol.u_hasDeriv t
        (selectorSchedule_domain_of_nonneg_structural t
          (le_trans hd0 ht.1)) i)
      (fun t ht => by
        simpa only [sol] using bgpNW4_uKernel_nonneg w w
          (le_trans hd0 ht.1))
      (hcopy i)
      (fun t ht => by
        have hz := hzT t ⟨by linarith [ht.1], ht.2⟩ i
        linarith)

  have hGcap :
      Real.exp (-bgpS2CopyMassLowerNW w j) * (4 * D_U + 2) ≤
        r_LE_U / 4 := by
    have h := bgpS2_copy_D0_exp_neg_mass_le_quarter_NW w j
    nlinarith
  have ha_slack : ∀ i : Fin d_U,
      |sol.u a i - stackMachineEncodingU.enc cfg i| ≤ 19 * r_LE_U / 20 := by
    intro i
    have hmem : a ∈ Icc
        (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 3)
        (2 * Real.pi * (j : ℝ) + 2 * Real.pi) := by
      dsimp only [a]
      unfold selectorMUZOffEnd
      constructor <;> linarith [Real.pi_pos]
    have h := hpost i a hmem
    linarith [hGcap, hHcap]

  rcases bgpF1_joint_step_core_NW w with ⟨core, hcore⟩
  have hje := bgpF1_joint_tube_and_endpoint_NW w core
  have htube0 : ∀ i : Fin d_U,
      |sol.u (selectorMUWriteStartTime j) i -
        stackMachineEncodingU.enc (bgpF1Cfg w j) i| ≤
          bgpF1TubeRadiusN bgpF1CwinDefN := by
    intro i
    have h := (hje j).1 i
    rw [hcore] at h
    simpa only [sol] using h
  have hwin : ∀ i : Fin d_U, ∀ t ∈ Icc
      (selectorMUWriteStartTime j) (selectorMUWriteReadTime j),
      |sol.z t i - sol.u t i| ≤ bgpF1CwinDefN := by
    intro i t ht
    have h := core.hwin_of j (hje j).1 (hje j).2 i t ht
    rw [hcore] at h
    simpa only [sol] using h
  have htail : ∀ t ∈ Icc a b, ∀ i : Fin d_U,
      |sol.u t i - stackMachineEncodingU.enc cfg i| ≤ 1 / 3 := by
    simpa only [sol, cfg, a, b, bgpF1Cfg] using
      bgpNW4_tail_tube w w j htube0 hwin

  have ha0 : 0 ≤ a := by
    dsimp only [a]
    unfold selectorMUZOffEnd
    positivity
  have hab : a ≤ b := by
    simpa only [a, b] using bgpNW4_zOffEnd_le_ws_succ j
  have hz_a_abs : ∀ i : Fin d_U, |sol.z a i| ≤ 2 * D_U + 1 := by
    intro i
    have ha_lower : 2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6 ≤ a := by
      dsimp only [a]
      unfold selectorMUZOffEnd
      linarith [Real.pi_pos]
    have ha_upper : a ≤ 2 * Real.pi * (j : ℝ) + 2 * Real.pi := by
      dsimp only [a]
      unfold selectorMUZOffEnd
      linarith
    have hz := hzT a ⟨ha_lower, ha_upper⟩ i
    have henc := bgpNW4_enc_abs cfg i
    have htri : |sol.z a i| ≤
        |sol.z a i - stackMachineEncodingU.enc cfg i| +
          |stackMachineEncodingU.enc cfg i| := by
      have h := abs_sub_le (sol.z a i)
        (stackMachineEncodingU.enc cfg i) 0
      simpa using h
    have hr : r_LE_U = (1 : ℝ) / 1000 := rfl
    rw [hr] at hz hHcap
    linarith

  have hzu_tail : ∀ t ∈ Icc a b, ∀ i : Fin d_U,
      |sol.z t i - sol.u t i| ≤ 4 * D_U + 3 := by
    intro t ht i
    have hmix : ∀ s ∈ Icc a t, ∀ k : Fin d_U,
        |selectorMixTarget branchU sol.u sol.lam s k| ≤ 2 * D_U := by
      intro s hs k
      have hs0 : 0 ≤ s := le_trans ha0 hs.1
      simpa only [sol] using
        bgpNW_mixTarget_abs_le_of_branch_abs w w hs0
          (fun i' v => branchU_evalBranch_abs_le_two_D_U_of_third_tube
            (fun k' => htail s ⟨hs.1, le_trans hs.2 ht.2⟩ k') v i') k
    have hztrap : sol.z t i ∈ Icc
        (min (sol.z a i) (-(2 * D_U)))
        (max (sol.z a i) (2 * D_U)) := by
      exact bgpN_trapping_on_Icc
        (fun s => sol.z s i)
        (fun s => selectorMixTarget branchU sol.u sol.lam s i)
        (fun s => (bgpParamsNW w).A * sol.α s *
          bGateZ (bgpParamsNW w).L (sol.μ s) s)
        ht.1
        (by simpa only [sol] using bgpNW4_zKernel_continuous w w)
        (sol.cont_mixTarget i)
        (fun s hs => sol.z_hasDeriv s
          (selectorSchedule_domain_of_nonneg_structural s
            (le_trans ha0 hs.1)) i)
        (fun s hs => by
          simpa only [sol] using bgpNW4_zKernel_nonneg w w
            (le_trans ha0 hs.1))
        (fun s hs => by
          have hm := hmix s hs i
          rw [abs_le] at hm
          exact ⟨le_trans (min_le_right _ _) hm.1,
            le_trans hm.2 (le_max_right _ _)⟩)
        ⟨min_le_left _ _, le_max_left _ _⟩
    have hza := abs_le.mp (hz_a_abs i)
    have hz_abs : |sol.z t i| ≤ 2 * D_U + 1 := by
      rw [abs_le]
      constructor
      · have hmin : -(2 * D_U + 1) ≤
            min (sol.z a i) (-(2 * D_U)) := by
          rcases min_cases (sol.z a i) (-(2 * D_U)) with h | h
          · rw [h.1]; exact hza.1
          · rw [h.1]; linarith
        exact le_trans hmin hztrap.1
      · have hmax : max (sol.z a i) (2 * D_U) ≤ 2 * D_U + 1 := by
          rcases max_cases (sol.z a i) (2 * D_U) with h | h
          · rw [h.1]; exact hza.2
          · rw [h.1]; linarith
        exact le_trans hztrap.2 hmax
    have hu_tube := htail t ht i
    have henc := bgpNW4_enc_abs cfg i
    have hu_tri : |sol.u t i| ≤
        |sol.u t i - stackMachineEncodingU.enc cfg i| +
          |stackMachineEncodingU.enc cfg i| := by
      have h := abs_sub_le (sol.u t i)
        (stackMachineEncodingU.enc cfg i) 0
      simpa using h
    have hu_abs : |sol.u t i| ≤ 2 * D_U + 1 := by
      linarith
    have htri := abs_sub (sol.z t i) (sol.u t i)
    linarith

  have htail_small :
      (4 * D_U + 3) * Real.exp (-(200 * (bgpScaleW w : ℝ) * a)) /
          (200 * (bgpScaleW w : ℝ)) ≤ r_LE_U / 20 := by
    set S : ℝ := (bgpScaleW w : ℝ) with hS
    clear_value S
    have hleg :
        (4 * D_U + 3) * Real.exp (-(200 * S * selectorMUZOffEnd j)) /
            (200 * S) ≤
          Real.exp (-(2 * (j : ℝ))) * Real.exp (-(20 * S)) := by
      simpa only [hS] using bgpNW4_leg_tail w j
    have hS4 : (4 : ℝ) ≤ S := by
      simpa only [hS] using bgpScaleWR_ge_four w
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hej : Real.exp (-(2 * (j : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    have heS : Real.exp (-(20 * S)) ≤ Real.exp (-(80 : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith [hS4])
    have h80 : (20000 : ℝ) ≤ Real.exp (80 : ℝ) := by
      have h10 : (11 : ℝ) ≤ Real.exp (10 : ℝ) := by
        linarith [Real.add_one_le_exp (10 : ℝ)]
      have hpow : (11 : ℝ) ^ (8 : ℕ) ≤ (Real.exp (10 : ℝ)) ^ (8 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) h10 8
      have hexp8 : Real.exp (80 : ℝ) = (Real.exp (10 : ℝ)) ^ (8 : ℕ) := by
        rw [← Real.exp_nat_mul]
        norm_num
      rw [hexp8]
      nlinarith [hpow]
    have hcap : Real.exp (-(80 : ℝ)) ≤ r_LE_U / 20 := by
      have heneg : Real.exp (-(80 : ℝ)) = 1 / Real.exp (80 : ℝ) := by
        rw [Real.exp_neg]
        simp only [one_div]
      have hrecip : 1 / Real.exp 80 ≤ 1 / 20000 :=
        one_div_le_one_div_of_le (by norm_num) h80
      rw [heneg]
      norm_num [r_LE_U] at hrecip ⊢
      exact hrecip
    have hprod : Real.exp (-(2 * (j : ℝ))) *
        Real.exp (-(20 * S)) ≤ Real.exp (-(80 : ℝ)) := by
      calc
        _ ≤ 1 * Real.exp (-(20 * S)) :=
          mul_le_mul_of_nonneg_right hej (Real.exp_pos _).le
        _ ≤ Real.exp (-(80 : ℝ)) := by simpa using heS
    simpa only [a, hS] using hleg.trans (hprod.trans hcap)

  intro t ht
  by_cases htb : t ≤ b
  · intro i
    have ht' : t ∈ Icc a b := ⟨ht.1, htb⟩
    have hdrift := bgpNW4_u_drift_of_sin_nonneg w w i
      (by nlinarith [D_U_nonneg] : 0 ≤ 4 * D_U + 3) ha0
      (fun s hs => bgpNW4_sin_nonneg_prewriteTail j hs.1 hs.2)
      hzu_tail t ht'
    have htri : |sol.u t i - stackMachineEncodingU.enc cfg i| ≤
        |sol.u t i - sol.u a i| +
          |sol.u a i - stackMachineEncodingU.enc cfg i| :=
      abs_sub_le _ _ _
    have ha_i := ha_slack i
    change |sol.u t i - stackMachineEncodingU.enc cfg i| ≤ r_LE_U
    exact le_trans htri (by linarith [hdrift, htail_small, ha_i])
  · have hbt : b ≤ t := le_of_not_ge htb
    have ht_right : t ∈ Icc (selectorMUWriteStartTime (j + 1))
        (selectorMUZOffStart (j + 1)) := by
      refine ⟨by simpa only [b] using hbt, ?_⟩
      have hnext : selectorMUNextWriteStart j =
          selectorMUWriteHoldTime (j + 1) := rfl
      have hhold_z : selectorMUWriteHoldTime (j + 1) ≤
          selectorMUZOffStart (j + 1) := by
        unfold selectorMUWriteHoldTime selectorMUZOffStart
        linarith [Real.pi_pos]
      exact le_trans (by simpa only [hnext] using ht.2) hhold_z
    intro i
    simpa only [sol, cfg, bgpF1Cfg] using
      bgpSegC_edge_tube_NW w (j + 1) t ht_right i

/-- **S4b left-edge payoff-gap floor (NW)**: the `j → j+1` twin of
`bgpS4a_gapFloor_NW`.  On the right-edge window the *new* winner keeps the
pairwise payoff gap `≥ 1/2` over every other view, from the persisting
new-center tube via the center-generic `bgpSegC_pairwiseGap_of_single_tube_NW`
at `k := j+1`. -/
theorem bgpS4b_gapFloor_NW (w j : ℕ) :
    ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w (j + 1)) →
    ∀ τ ∈ Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j),
      (1 / 2 : ℝ) ≤
        universalPval bgpHeadlineEta bgpHeadlineEta_pos
            (localViewU (solMUReplStaticCfg w (j + 1)))
            (((bgpHeadlineSolFamNW w) w).u τ) -
          universalPval bgpHeadlineEta bgpHeadlineEta_pos v
            (((bgpHeadlineSolFamNW w) w).u τ) := by
  intro v hv τ hτ
  have hgap := bgpSegC_pairwiseGap_of_single_tube_NW w (j + 1)
    (bgpS4b_right_edge_tube_persist_NW w j) τ hτ v hv
  have hhalf := bgpS13_gapVal_ge_half
  linarith

/-! ### S4b analytic leaves (right edge, new center) -/

/-- Crude all-coordinate `|z-u|` envelope on the S4b right edge. -/
theorem bgpS4b_edge_zu_envelope_NW (w j : ℕ) (i : Fin d_U) :
    ∀ t ∈ Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j),
      |((bgpHeadlineSolFamNW w) w).z t i -
        ((bgpHeadlineSolFamNW w) w).u t i| ≤ bgpS4EdgeZUBoundNW := by
  let sol := (bgpHeadlineSolFamNW w) w
  let cfg := solMUReplStaticCfg w (j + 1)
  let a : ℝ := selectorMUZOffEnd j
  let b : ℝ := selectorMUNextWriteStart j
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    unfold selectorMUZOffEnd
    positivity
  have hab : a ≤ b := by
    simpa only [a, b] using selectorMUZOffEnd_le_nextWriteStart j
  have hD0 := D_U_nonneg
  have hr : r_LE_U = 1 / 1000 := rfl
  have hu_lvl : ∀ t ∈ Icc a b, ∀ k : Fin d_U,
      |sol.u t k| ≤ 2 * D_U + 1 := by
    intro t ht k
    have htube := bgpS4b_right_edge_tube_persist_NW w j t
      (by simpa only [a, b] using ht) k
    change |sol.u t k - stackMachineEncodingU.enc cfg k| ≤ r_LE_U at htube
    have henc := bgpNW4_enc_abs cfg k
    have hsplit : |sol.u t k| ≤
        |sol.u t k - stackMachineEncodingU.enc cfg k| +
          |stackMachineEncodingU.enc cfg k| := by
      have h := abs_sub_le (sol.u t k)
        (stackMachineEncodingU.enc cfg k) (0 : ℝ)
      simpa using h
    rw [hr] at htube
    linarith
  have hmix_lvl : ∀ t ∈ Icc a b,
      |selectorMixTarget branchU sol.u sol.lam t i| ≤
        2 * D_U + 4000 * D_U * (5 * D_U + 2) := by
    intro t ht
    have hbr : ∀ (i' : Fin d_U) (v : UniversalLocalView),
        |BranchData.evalBranch (branchU v) (sol.u t) i'| ≤
          2 * D_U + 4000 * D_U * (5 * D_U + 2) := by
      intro i' v
      have htube := bgpS4b_right_edge_tube_persist_NW w j t
        (by simpa only [a, b] using ht) i'
      change |sol.u t i' - stackMachineEncodingU.enc cfg i'| ≤ r_LE_U at htube
      have hx : |sol.u t i' - stackMachineEncodingU.enc cfg i'| ≤
          5 * D_U + 2 := by
        rw [hr] at htube
        linarith
      exact bgpNW4_eval_abs_of_coord_bound v i' cfg hx
    simpa only [sol] using
      bgpNW_mixTarget_abs_le_of_branch_abs w w
        (le_trans ha0 ht.1) hbr i
  have hz_entry : |sol.z a i| ≤ 2 * D_U + 1 := by
    have hdelta0 : 0 ≤ 9 * r_LE_U / 20 := by
      norm_num [r_LE_U]
    rcases bgpS2_handoff_entry_NW w j with ⟨hzEntry, huEntry⟩
    have box := bgpS2_window_firstExit_box_NW w j
      hdelta0 (le_refl (9 * r_LE_U / 20)) hzEntry huEntry
    have hzT := bgpS2_z_tube_lower_half_NW w j box hzEntry
    have hmem : a ∈ Icc
        (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + 2 * Real.pi) := by
      dsimp only [a]
      unfold selectorMUZOffEnd
      constructor <;> linarith [Real.pi_pos]
    have hz := hzT a hmem i
    have hHcap : bgpS2LowerHalfZDriftNW w j ≤ r_LE_U / 4 := by
      unfold bgpS2LowerHalfZDriftNW
      exact bgpS2_firstExit_z_drift_cap_NW w j
    have henc := bgpNW4_enc_abs cfg i
    have hsplit : |sol.z a i| ≤
        |sol.z a i - stackMachineEncodingU.enc cfg i| +
          |stackMachineEncodingU.enc cfg i| := by
      have h := abs_sub_le (sol.z a i)
        (stackMachineEncodingU.enc cfg i) (0 : ℝ)
      simpa using h
    dsimp only [sol, cfg] at hz hsplit ⊢
    rw [hr] at hz hHcap
    linarith
  have hz_lvl : ∀ t ∈ Icc a b,
      |sol.z t i| ≤
        (2 * D_U + 4000 * D_U * (5 * D_U + 2)) + 2 * D_U + 1 := by
    have hbr0 : (0 : ℝ) ≤
        2 * D_U + 4000 * D_U * (5 * D_U + 2) := by
      nlinarith
    have htrap := relax_abs_trap
      (fun τ => sol.z τ i)
      (fun τ => selectorMixTarget branchU sol.u sol.lam τ i)
      (fun τ => (bgpParamsNW w).A * sol.α τ *
        bGateZ (bgpParamsNW w).L (sol.μ τ) τ)
      (M := (0 : ℝ))
      (δ := (2 * D_U + 4000 * D_U * (5 * D_U + 2)) + 2 * D_U + 1)
      hab
      (by simpa only [sol] using bgpNW4_zKernel_continuous w w)
      (sol.cont_mixTarget i)
      (fun t ht => sol.z_hasDeriv t
        (selectorSchedule_domain_of_nonneg_structural t
          (le_trans ha0 ht.1)) i)
      (fun t ht => by
        simpa only [sol] using bgpNW4_zKernel_nonneg w w
          (le_trans ha0 ht.1))
      (by
        simp only [sub_zero]
        exact hz_entry.trans (by linarith))
      (fun t ht => by
        simp only [sub_zero]
        exact (hmix_lvl t ht).trans (by linarith))
    intro t ht
    simpa using htrap t ht
  intro t ht
  have ht' : t ∈ Icc a b := by simpa only [a, b] using ht
  have hz := hz_lvl t ht'
  have hu := hu_lvl t ht' i
  have hsplit : |sol.z t i - sol.u t i| ≤ |sol.z t i| + |sol.u t i| :=
    abs_sub (sol.z t i) (sol.u t i)
  unfold bgpS4EdgeZUBoundNW
  linarith [bgpF1CwinDefN_nonneg]

private theorem bgpS4b_qssDeriv_pointwise_exp_NW
    (w j : ℕ) (v : UniversalLocalView)
    (hv : v ≠ localViewU (solMUReplStaticCfg w (j + 1)))
    (τ : ℝ)
    (hτ : τ ∈ Icc (selectorMUZOffEnd j)
      (selectorMUNextWriteStart j)) :
    |selectorMU_activeQSSDerivRHSP
        bgpHeadlineEta bgpHeadlineEta_pos
        (bgpHeadlineSolFamNW w) w
        (localViewU (solMUReplStaticCfg w (j + 1))) v τ| ≤
      bgpS4aQSSDerivCoeffNW w j v *
        Real.exp (-(300 * (bgpScaleW w : ℝ) * τ)) := by
  have hτ0 : 0 ≤ τ := by
    have ha0 : 0 ≤ selectorMUZOffEnd j := by
      unfold selectorMUZOffEnd
      positivity
    exact le_trans ha0 hτ.1
  have hsin : 0 ≤ Real.sin τ :=
    bgpS4b_sin_nonneg j hτ.1 hτ.2
  have htube : UTube r_LE_U (solMUReplStaticCfg w (j + 1))
      (((bgpHeadlineSolFamNW w) w).u τ) :=
    bgpS4b_right_edge_tube_persist_NW w j τ hτ
  have hzu : ∀ i : Fin d_U,
      |((bgpHeadlineSolFamNW w) w).z τ i -
        ((bgpHeadlineSolFamNW w) w).u τ i| ≤ bgpS4EdgeZUBoundNW := by
    intro i
    exact bgpS4b_edge_zu_envelope_NW w j i τ hτ
  have hgap := bgpS4b_gapFloor_NW w j v hv τ hτ
  exact bgpS4_qssDeriv_pointwise_exp_of_edge_data_NW
    w j (solMUReplStaticCfg w (j + 1))
    (localViewU (solMUReplStaticCfg w (j + 1))) v
    hτ0 hsin htube hzu hgap

private theorem bgpS4b_qssDeriv_exp_budget_NW (w j : ℕ) :
    ((((Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => bgpS4aQSSDerivCoeffNW w j v)) /
        (300 * (bgpScaleW w : ℝ))) *
      Real.exp (-(300 * (bgpScaleW w : ℝ) *
        selectorMUZOffEnd j))) ≤
      selectorMUHoffEdgeBudget3992 j / 32 := by
  set S : ℝ := (bgpScaleW w : ℝ) with hS
  clear_value S
  let K : ℝ :=
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
        (fun v => bgpS4aQSSDerivCoeffNW w j v)
  have hS0 : 0 < S := by simpa only [hS] using bgpScaleWR_pos w
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    exact Finset.sum_nonneg fun v _ => bgpS4aQSSDerivCoeffNW_nonneg w j v
  have ha : selectorMUInterReadStart j ≤ selectorMUZOffEnd j :=
    le_trans (selectorMUInterReadStart_le_zOffStart j)
      (selectorMUZOffStart_le_zOffEnd j)
  have hexp :
      Real.exp (-(300 * S * selectorMUZOffEnd j)) ≤
        Real.exp (-(300 * S * selectorMUInterReadStart j)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hmono :
      (K / (300 * S)) * Real.exp (-(300 * S * selectorMUZOffEnd j)) ≤
        (K / (300 * S)) *
          Real.exp (-(300 * S * selectorMUInterReadStart j)) :=
    mul_le_mul_of_nonneg_left hexp (div_nonneg hK0 (by positivity))
  have hold := bgpS4a_qssDeriv_exp_budget_NW w j
  change (K / (300 * S)) * Real.exp (-(300 * S * selectorMUZOffEnd j)) ≤ _
  exact hmono.trans (by simpa only [K, hS] using hold)

private theorem bgpS4b_activeSink_pos_NW
    (w j : ℕ) (v : UniversalLocalView)
    (hv : v ≠ localViewU (solMUReplStaticCfg w (j + 1)))
    {τ : ℝ}
    (hτ : τ ∈ Icc (selectorMUZOffEnd j)
      (selectorMUNextWriteStart j)) :
    0 < selectorMU_activeSinkP
      bgpHeadlineEta bgpHeadlineEta_pos
      (bgpHeadlineSolFamNW w) w
      (localViewU (solMUReplStaticCfg w (j + 1))) v τ := by
  have hsin : 0 ≤ Real.sin τ := bgpS4b_sin_nonneg j hτ.1 hτ.2
  have hgap := bgpS4b_gapFloor_NW w j v hv τ hτ
  have hfloor := bgpS4_sink_ge_of_gap_half_NW w
    (localViewU (solMUReplStaticCfg w (j + 1))) v hsin hgap
  have hpow : 0 < (1 / 2 : ℝ) ^ bgpHeadlineM :=
    pow_pos (by norm_num) _
  have hgain :
      0 < ((bgpWarmGainQNW w : ℚ) : ℝ) *
        Real.exp ((bgpParamsNW w).cα * τ) :=
    mul_pos (bgpWarmGainQNW_pos_real w) (Real.exp_pos _)
  have hbasePos :
      0 < (1 / 2 : ℝ) ^ bgpHeadlineM *
        (((bgpWarmGainQNW w : ℚ) : ℝ) *
          Real.exp ((bgpParamsNW w).cα * τ)) * (1 / 2) :=
    mul_pos (mul_pos hpow hgain) (by norm_num)
  exact lt_of_lt_of_le hbasePos hfloor

/-- S4b QSS derivative mass on the right edge, with the new configuration as
the active center. -/
theorem bgpS4b_qssDerivMass_le_NW (w j : ℕ) :
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
      (fun v =>
        ∫ τ in (selectorMUZOffEnd j)..(selectorMUNextWriteStart j),
          |selectorMU_activeQSSDerivRHSP
            bgpHeadlineEta bgpHeadlineEta_pos
            (bgpHeadlineSolFamNW w) w
            (localViewU (solMUReplStaticCfg w (j + 1))) v τ|) ≤
      selectorMUHoffEdgeBudget3992 j / 32 := by
  classical
  let sol := bgpHeadlineSolFamNW w
  let c : UniversalLocalView := localViewU (solMUReplStaticCfg w (j + 1))
  let a : ℝ := selectorMUZOffEnd j
  let b : ℝ := selectorMUNextWriteStart j
  let S : ℝ := (bgpScaleW w : ℝ)
  let r : ℝ := 300 * S
  let bad : Finset UniversalLocalView :=
    Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j) ∧
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))
  let K : UniversalLocalView → ℝ := fun v => bgpS4aQSSDerivCoeffNW w j v
  have hab : a ≤ b := by
    simpa only [a, b] using selectorMUZOffEnd_le_nextWriteStart j
  have hr : 0 < r := by
    dsimp only [r, S]
    nlinarith [bgpScaleWR_pos w]
  have hK0 : ∀ v ∈ bad, 0 ≤ K v := by
    intro v _hv
    exact bgpS4aQSSDerivCoeffNW_nonneg w j v
  have hsink : ∀ v ∈ bad, ∀ τ ∈ Icc a b,
      0 < selectorMU_activeSinkP
        bgpHeadlineEta bgpHeadlineEta_pos sol w c v τ := by
    intro v hv τ hτ
    have hvNew := (Finset.mem_filter.mp hv).2.2
    exact bgpS4b_activeSink_pos_NW w j v hvNew
      (by simpa only [a, b, c] using hτ)
  have hcont : ∀ v ∈ bad,
      ContinuousOn
        (fun τ => selectorMU_activeQSSDerivRHSP
          bgpHeadlineEta bgpHeadlineEta_pos sol w c v τ)
        (Icc a b) := by
    intro v hv
    exact selectorMU_activeQSSDerivRHS_continuousOn_of_sink_posP
      (p := bgpParamsNW w) (sol := sol) w c v (hsink v hv)
  have hpoint : ∀ v ∈ bad, ∀ τ ∈ Icc a b,
      |selectorMU_activeQSSDerivRHSP
        bgpHeadlineEta bgpHeadlineEta_pos sol w c v τ| ≤
        K v * Real.exp (-(r * τ)) := by
    intro v hv τ hτ
    have hvNew := (Finset.mem_filter.mp hv).2.2
    have hp := bgpS4b_qssDeriv_pointwise_exp_NW
      w j v hvNew τ (by simpa only [a, b] using hτ)
    simpa only [sol, c, K, r, S] using hp
  have hbudget :
      ((bad.sum K) / r) * Real.exp (-(r * a)) ≤
        selectorMUHoffEdgeBudget3992 j / 32 := by
    simpa only [bad, K, r, S, a] using
      bgpS4b_qssDeriv_exp_budget_NW w j
  have hsum :=
    finset_sum_integral_abs_le_exp_decay_budget
      bad
      (F := fun v τ =>
        selectorMU_activeQSSDerivRHSP
          bgpHeadlineEta bgpHeadlineEta_pos sol w c v τ)
      (C := K) (r := r) (a := a) (b := b)
      hr hab hK0 hcont hpoint hbudget
  simpa only [sol, c, a, b, bad, K, r, S] using hsum

/-! #### S4b loser-mass preparation -/

/-- Instantiate the conditional S2 post-copy tube with the landed handoff
entry. -/
theorem bgpS4b_s2_new_tube_NW (w j : ℕ) :
    ∀ t ∈ Icc (bgpS2RecStart j) (selectorMUZOffEnd j),
      UTube r_LE_U (solMUReplStaticCfg w (j + 1))
        (((bgpHeadlineSolFamNW w) w).u t) := by
  have hdelta0 : 0 ≤ 9 * r_LE_U / 20 := by
    norm_num [r_LE_U]
  rcases bgpS2_handoff_entry_NW w j with ⟨hzEntry, huEntry⟩
  intro t ht
  apply bgpS2_interRead_new_tube_NW w j
    hdelta0 (le_refl (9 * r_LE_U / 20)) hzEntry huEntry t
  constructor
  · simpa only [bgpS2RecStart] using ht.1
  · calc
      t ≤ 2 * Real.pi * ((j : ℝ) + 1) := by
        simpa only [selectorMUZOffEnd] using ht.2
      _ = 2 * Real.pi * (j : ℝ) + 2 * Real.pi := by ring

/-- The new-center tube from the late S2 recovery anchor through the whole
S4b right edge. -/
theorem bgpS4b_mid_to_right_tube_NW (w j : ℕ) :
    ∀ t ∈ Icc (bgpS2Mid j) (selectorMUNextWriteStart j),
      UTube r_LE_U (solMUReplStaticCfg w (j + 1))
        (((bgpHeadlineSolFamNW w) w).u t) := by
  intro t ht
  by_cases htz : t ≤ selectorMUZOffEnd j
  · exact bgpS4b_s2_new_tube_NW w j t
      ⟨le_trans (bgpS2_recStart_le_mid j) ht.1, htz⟩
  · exact bgpS4b_right_edge_tube_persist_NW w j t
      ⟨le_of_not_ge htz, ht.2⟩

/-- Reset recovery regenerates the new-view winner floor at the S2 midpoint,
now for the word-coupled NW clock. -/
theorem bgpS4b_newWinner_recovery_floor_NW (w j : ℕ) :
    1 / (Fintype.card UniversalLocalView : ℝ) ≤
      ((bgpHeadlineSolFamNW w) w).lam
        (localViewU (solMUReplStaticCfg w (j + 1))) (bgpS2Mid j) := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hπd4 : Real.pi < 3.1416 := Real.pi_lt_d4
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hrec0 : 0 ≤ bgpS2RecStart j := bgpS2_recStart_nonneg j
  have hst : bgpS2RecStart j ≤ bgpS2Mid j := bgpS2_recStart_le_mid j
  have hgap_half := bgpS13_gapVal_ge_half
  have hg0_pos := bgpWarmGainQNW_pos_real w
  have htube := bgpS4b_s2_new_tube_NW w j
  have hpairgap := bgpSegC_pairwiseGap_of_single_tube_NW w (j + 1)
    htube
  set cgMin : ℝ := Real.exp (600 * Real.pi * (j : ℝ) + 525 * Real.pi)
    with hcgMin_def
  have hcgMin_pos : (0 : ℝ) < cgMin := by
    rw [hcgMin_def]
    exact Real.exp_pos _
  have hcgMin_ge16 : (16 : ℝ) ≤ cgMin := by
    rw [hcgMin_def]
    have h4 : ((4 : ℕ) : ℝ) ≤ 600 * Real.pi * (j : ℝ) + 525 * Real.pi := by
      push_cast
      nlinarith [mul_nonneg hπ.le hj0]
    have h := bgpS13_exp_pow_ge h4
    norm_num at h
    linarith
  have hsplitcg : cgMin =
      Real.exp (600 * Real.pi * (j : ℝ)) * Real.exp (525 * Real.pi) := by
    rw [hcgMin_def, ← Real.exp_add]
  have hE525 : (1048576 : ℝ) ≤ Real.exp (525 * Real.pi) := by
    have h20 : ((20 : ℕ) : ℝ) ≤ 525 * Real.pi := by
      push_cast
      nlinarith
    have h := bgpS13_exp_pow_ge h20
    norm_num at h
    linarith
  have hEj : 1 + 1800 * (j : ℝ) ≤ Real.exp (600 * Real.pi * (j : ℝ)) := by
    have h := Real.add_one_le_exp (600 * Real.pi * (j : ℝ))
    nlinarith [mul_nonneg hj0 (by linarith : (0 : ℝ) ≤ 600 * Real.pi - 1800)]
  have hcg_lb : 1048576 * (1 + 1800 * (j : ℝ)) ≤ cgMin := by
    rw [hsplitcg]
    calc
      (1048576 : ℝ) * (1 + 1800 * (j : ℝ))
          = (1 + 1800 * (j : ℝ)) * 1048576 := by ring
      _ ≤ Real.exp (600 * Real.pi * (j : ℝ)) * Real.exp (525 * Real.pi) :=
        mul_le_mul hEj hE525 (by norm_num) (Real.exp_pos _).le
  have hb_pos : (0 : ℝ) < cgMin * (1 / 2) / 2 - 1 := by
    linarith
  have hlen : bgpS2Mid j - bgpS2RecStart j = Real.pi / 12 := by
    unfold bgpS2Mid bgpS2RecStart
    ring
  have hbDelta : ((2 * (1886 * j + 1652) : ℕ) : ℝ) ≤
      (cgMin * (1 / 2) / 2 - 1) *
        (bgpS2Mid j - bgpS2RecStart j) := by
    rw [hlen]
    have hKval : ((2 * (1886 * j + 1652) : ℕ) : ℝ) =
        2 * (1886 * (j : ℝ) + 1652) := by
      push_cast
      ring
    rw [hKval]
    have hπ12 : (1 / 4 : ℝ) ≤ Real.pi / 12 := by linarith
    have hmul : (cgMin * (1 / 2) / 2 - 1) * (1 / 4) ≤
        (cgMin * (1 / 2) / 2 - 1) * (Real.pi / 12) :=
      mul_le_mul_of_nonneg_left hπ12 hb_pos.le
    linarith [hmul, hcg_lb]
  have hpow2 : 1 + (cgMin * (1 / 2) / 2 - 1) / (1 / 8 : ℝ) ≤
      (2 : ℝ) ^ (2 * (1886 * j + 1652)) := by
    have h2n : (2 : ℝ) ^ (2 * (1886 * j + 1652)) =
        (4 : ℝ) ^ (1886 * j + 1652) := by
      rw [pow_mul]
      norm_num
    have hjmul : 600 * Real.pi * (j : ℝ) ≤ 1886 * (j : ℝ) := by
      nlinarith [mul_nonneg hj0 (by linarith : (0 : ℝ) ≤ 1886 - 600 * Real.pi)]
    have hxle : 600 * Real.pi * (j : ℝ) + 525 * Real.pi + 1 ≤
        ((1886 * j + 1652 : ℕ) : ℝ) := by
      push_cast
      linarith
    have hexp4 := bgpS2_exp_le_four_pow hxle
    have hE1 : (2 : ℝ) ≤ Real.exp 1 := by
      linarith [Real.add_one_le_exp (1 : ℝ)]
    have h2cg : 2 * cgMin ≤
        Real.exp (600 * Real.pi * (j : ℝ) + 525 * Real.pi + 1) := by
      have hsplit1 :
          Real.exp (600 * Real.pi * (j : ℝ) + 525 * Real.pi + 1) =
            Real.exp (600 * Real.pi * (j : ℝ) + 525 * Real.pi) * Real.exp 1 := by
        rw [← Real.exp_add]
      rw [hsplit1, hcgMin_def]
      have := mul_le_mul_of_nonneg_left hE1
        (Real.exp_pos (600 * Real.pi * (j : ℝ) + 525 * Real.pi)).le
      linarith
    have hb8 : 1 + (cgMin * (1 / 2) / 2 - 1) / (1 / 8 : ℝ) =
        2 * cgMin - 7 := by ring
    rw [hb8, h2n]
    linarith
  exact bgpHeadline_replicator_winner_recovery_at_endpoint
    ((bgpHeadlineSolFamNW w) w)
    (localViewU (solMUReplStaticCfg w (j + 1)))
    (s := bgpS2RecStart j) (t := bgpS2Mid j)
    (crMin := 1 / 8) (crMax := 1) (cgMin := cgMin) (gap := 1 / 2)
    (b := cgMin * (1 / 2) / 2 - 1) (K := 2 * (1886 * j + 1652))
    bgpHeadlineHCardTwo
    (by norm_num)
    (by norm_num)
    hcgMin_pos.le
    (by norm_num)
    rfl
    hb_pos
    hbDelta
    hpow2
    hst
    (fun u hu => selectorSchedule_domain_of_nonneg_structural u
      (le_trans hrec0 hu.1))
    (fun u hu => by
      constructor
      · have h := bgpS2_crF_ge_eighth j hu.1
          (le_trans hu.2 (bgpS2_mid_le_zOffEnd j))
        simpa [bgpS13crF] using h
      · have h := bgpS13crF_le_one u
        simpa [bgpS13crF] using h)
    (fun u hu => by
      show cgMin ≤ ((1 + Real.sin u) / 2) ^ bgpHeadlineM *
        (((bgpWarmGainQNW w : ℚ) : ℝ) *
          Real.exp ((bgpParamsNW w).cα * u))
      have hsin := bgpS2_sin_ge_neg_half j hu.1
        (le_trans hu.2 (bgpS2_mid_le_zOffEnd j))
      have hu0 : 0 ≤ u := le_trans hrec0 hu.1
      have hcαge : (300 : ℝ) ≤ (bgpParamsNW w).cα := by
        rw [bgpParamsNW_cα_def]
        nlinarith [bgpScaleWR_ge_one w]
      have hexp_mono :
          Real.exp (600 * Real.pi * (j : ℝ) + 550 * Real.pi) ≤
            Real.exp ((bgpParamsNW w).cα * u) := by
        apply Real.exp_le_exp.mpr
        have h1 := hu.1
        unfold bgpS2RecStart at h1
        have h300 : 600 * Real.pi * (j : ℝ) + 550 * Real.pi ≤ 300 * u := by
          linarith
        have hcu := mul_le_mul_of_nonneg_right hcαge hu0
        linarith
      have hpow_base : ((1 : ℝ) / 4) ^ bgpHeadlineM ≤
          ((1 + Real.sin u) / 2) ^ bgpHeadlineM :=
        pow_le_pow_left₀ (by norm_num) (by linarith) _
      have h4pow : (4 : ℝ) ^ bgpHeadlineM ≤ Real.exp (25 * Real.pi) := by
        have h40 : ((40 : ℕ) : ℝ) ≤ 25 * Real.pi := by
          push_cast
          nlinarith
        have h := bgpS13_exp_pow_ge h40
        have heq240 : (4 : ℝ) ^ bgpHeadlineM = (2 : ℝ) ^ (40 : ℕ) := by
          norm_num [bgpHeadlineM]
        rw [heq240]
        exact h
      have hg1 : (1 : ℝ) ≤ ((bgpWarmGainQNW w : ℚ) : ℝ) := by
        linarith [bgpWarmGainQNW_ge_base w]
      have hkey : cgMin ≤ ((1 : ℝ) / 4) ^ bgpHeadlineM *
          (((bgpWarmGainQNW w : ℚ) : ℝ) *
            Real.exp (600 * Real.pi * (j : ℝ) + 550 * Real.pi)) := by
        have h4M_pos : (0 : ℝ) < (4 : ℝ) ^ bgpHeadlineM := by positivity
        have hquarter : ((1 : ℝ) / 4) ^ bgpHeadlineM =
            ((4 : ℝ) ^ bgpHeadlineM)⁻¹ := by
          rw [one_div, inv_pow]
        rw [hquarter, inv_mul_eq_div, le_div_iff₀ h4M_pos]
        have hsplit2 : Real.exp (600 * Real.pi * (j : ℝ) + 550 * Real.pi) =
            cgMin * Real.exp (25 * Real.pi) := by
          rw [hcgMin_def, ← Real.exp_add]
          congr 1
          ring
        rw [hsplit2]
        have hstep : cgMin * (4 : ℝ) ^ bgpHeadlineM ≤
            cgMin * (((bgpWarmGainQNW w : ℚ) : ℝ) *
              Real.exp (25 * Real.pi)) := by
          refine mul_le_mul_of_nonneg_left ?_ hcgMin_pos.le
          calc
            (4 : ℝ) ^ bgpHeadlineM ≤ Real.exp (25 * Real.pi) := h4pow
            _ ≤ ((bgpWarmGainQNW w : ℚ) : ℝ) *
                Real.exp (25 * Real.pi) :=
              le_mul_of_one_le_left (Real.exp_pos _).le hg1
        calc
          cgMin * (4 : ℝ) ^ bgpHeadlineM
              ≤ cgMin * (((bgpWarmGainQNW w : ℚ) : ℝ) *
                  Real.exp (25 * Real.pi)) := hstep
          _ = ((bgpWarmGainQNW w : ℚ) : ℝ) *
              (cgMin * Real.exp (25 * Real.pi)) := by ring
      calc
        cgMin ≤ ((1 : ℝ) / 4) ^ bgpHeadlineM *
            (((bgpWarmGainQNW w : ℚ) : ℝ) *
              Real.exp (600 * Real.pi * (j : ℝ) + 550 * Real.pi)) := hkey
        _ ≤ ((1 + Real.sin u) / 2) ^ bgpHeadlineM *
            (((bgpWarmGainQNW w : ℚ) : ℝ) *
              Real.exp ((bgpParamsNW w).cα * u)) :=
          mul_le_mul hpow_base
            (mul_le_mul_of_nonneg_left hexp_mono hg0_pos.le)
            (by positivity)
            (pow_nonneg (by nlinarith [Real.neg_one_le_sin u]) _))
    (fun v hv u hu => by
      have huIcc : u ∈ Icc (bgpS2RecStart j) (selectorMUZOffEnd j) :=
        ⟨hu.1, le_trans (le_of_lt hu.2) (bgpS2_mid_le_zOffEnd j)⟩
      have hle := hpairgap u huIcc v (by simpa using hv)
      linarith)
    (fun u hu => by
      have hu0 : 0 ≤ u := le_trans hrec0 hu.1
      have huIcc : u ∈ Icc (bgpS2RecStart j) (selectorMUZOffEnd j) :=
        ⟨hu.1, le_trans (le_of_lt hu.2) (bgpS2_mid_le_zOffEnd j)⟩
      exact selector_replicator_havg_gap_of_utube
        (eta := bgpHeadlineEta) (heta := bgpHeadlineEta_pos)
        (lam := fun v => ((bgpHeadlineSolFamNW w) w).lam v u)
        (u := ((bgpHeadlineSolFamNW w) w).u u)
        (c := solMUReplStaticCfg w (j + 1))
        (gap := 1 / 2)
        bgpHeadlineHerr (htube u huIcc) hgap_half
        (bgpNW_lam_sum_forward w w u hu0)
        (fun v => bgpNW_lam_nonneg_forward w w v u hu0))
    (fun u hu => bgpNW_lam_sum_forward w w u (le_trans hrec0 hu.1))
    (fun v u hu => bgpNW_lam_nonneg_forward w w v u
      (le_trans hrec0 hu.1))

/-- The recovered new-winner floor persists through the whole S4b right edge. -/
theorem bgpS4b_newWinner_floor_NW (w j : ℕ) :
    ∀ t ∈ Icc (bgpS2Mid j) (selectorMUNextWriteStart j),
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        ((bgpHeadlineSolFamNW w) w).lam
          (localViewU (solMUReplStaticCfg w (j + 1))) t := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hmid0 := bgpS2_mid_nonneg j
  have htube := bgpS4b_mid_to_right_tube_NW w j
  have hgap_floor :
      ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w (j + 1)) →
        ∀ t ∈ Ico (bgpS2Mid j) (selectorMUNextWriteStart j),
          universalPval bgpHeadlineEta bgpHeadlineEta_pos v
              (((bgpHeadlineSolFamNW w) w).u t) -
            universalPval bgpHeadlineEta bgpHeadlineEta_pos
              (localViewU (solMUReplStaticCfg w (j + 1)))
              (((bgpHeadlineSolFamNW w) w).u t) ≤ 0 := by
    intro v hv t ht
    have hgap := bgpSegC_pairwiseGap_of_single_tube_NW w (j + 1)
      htube t (Ico_subset_Icc_self ht) v hv
    linarith [bgpS13_gapVal_pos]
  exact replicator_winner_floor_on_interval
    (sol := (bgpHeadlineSolFamNW w) w)
    (localViewU (solMUReplStaticCfg w (j + 1)))
    (a := bgpS2Mid j) (b := selectorMUNextWriteStart j)
    (le_trans (bgpS2_mid_le_zOffEnd j)
      (selectorMUZOffEnd_le_nextWriteStart j))
    (fun t ht => selectorSchedule_domain_of_nonneg_structural t
      (le_trans hmid0 ht.1))
    (fun t _ht => by
      exact mul_nonneg
        (pow_nonneg (by nlinarith [Real.neg_one_le_cos t]) _)
        (by norm_num [bgpHeadlineKappa]))
    (fun t _ht => by
      exact mul_nonneg
        (pow_nonneg (by nlinarith [Real.neg_one_le_sin t]) _)
        (mul_nonneg (bgpWarmGainQNW_nonneg_real w) (Real.exp_pos _).le))
    hgap_floor
    (fun t ht => bgpNW_lam_sum_forward w w t (le_trans hmid0 ht.1))
    (fun v t ht => bgpNW_lam_nonneg_forward w w v t
      (le_trans hmid0 ht.1))
    (bgpS4b_newWinner_recovery_floor_NW w j)

/-- Larger reset supersolution coefficient needed on the short S2 prefix,
where the active-gain base is only `1/4`. -/
noncomputable def bgpS4bResetCoeffNW (w : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * bgpHeadlineM + 3) /
    ((bgpWarmGainQNW w : ℚ) : ℝ)

theorem bgpS4bResetCoeffNW_nonneg (w : ℕ) :
    0 ≤ bgpS4bResetCoeffNW w := by
  unfold bgpS4bResetCoeffNW
  exact div_nonneg (pow_nonneg (by norm_num) _)
    (bgpWarmGainQNW_nonneg_real w)

theorem bgpS4bResetCoeffNW_le_one (w : ℕ) :
    bgpS4bResetCoeffNW w ≤ 1 := by
  set S : ℝ := (bgpScaleW w : ℝ) with hSdef
  clear_value S
  have hS : (5184 : ℝ) ≤ S := by
    simpa only [hSdef] using bgpNW4_S_ge w
  have hg : 0 < ((bgpWarmGainQNW w : ℚ) : ℝ) :=
    bgpWarmGainQNW_pos_real w
  have hpow6 : (1 : ℝ) ≤ (6 : ℝ) ^ w := one_le_pow₀ (by norm_num)
  have hqscale :
      (1734736490 : ℝ) * S ^ 6 ≤
        ((bgpWarmGainQNW w : ℚ) : ℝ) := by
    rw [hSdef]
    unfold bgpWarmGainQNW bgpWarmGainCNW
    push_cast
    nlinarith [mul_nonneg
      (by positivity : (0 : ℝ) ≤ 1734736490 * (bgpScaleW w : ℝ) ^ 6)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 6) w)]
  rw [bgpS4bResetCoeffNW, div_le_one hg]
  norm_num [bgpHeadlineM]
  have hS6 : (5184 : ℝ) ^ 6 ≤ S ^ 6 :=
    pow_le_pow_left₀ (by norm_num) hS 6
  nlinarith

/-- On `[S2Mid, nextWriteStart]`, the payoff gap times active gain dominates
the physical NW clock rate. -/
theorem bgpS4b_gap_mul_cg_ge_calpha_NW
    (w j : ℕ) {gap s : ℝ}
    (hgap : (15 : ℝ) / 16 ≤ gap)
    (hs : s ∈ Icc (bgpS2Mid j) (selectorMUNextWriteStart j)) :
    (bgpParamsNW w).cα ≤ gap * bgpNW4cg w s := by
  set S : ℝ := (bgpScaleW w : ℝ) with hSdef
  clear_value S
  have hS : (5184 : ℝ) ≤ S := by
    simpa only [hSdef] using bgpNW4_S_ge w
  have hS0 : 0 < S := by linarith
  have hsin : -(1 / 2 : ℝ) ≤ Real.sin s := by
    by_cases hsz : s ≤ selectorMUZOffEnd j
    · exact bgpS2_sin_ge_neg_half j
        (le_trans (bgpS2_recStart_le_mid j) hs.1) hsz
    · have hsright : s ∈ Icc (selectorMUZOffEnd j)
          (selectorMUNextWriteStart j) := ⟨le_of_not_ge hsz, hs.2⟩
      linarith [bgpS4b_sin_nonneg j hsright.1 hsright.2]
  have hpow : (1 / 4 : ℝ) ^ bgpHeadlineM ≤
      ((1 + Real.sin s) / 2) ^ bgpHeadlineM := by
    apply pow_le_pow_left₀ (by norm_num)
    linarith
  have hs0 : 0 ≤ s := le_trans (bgpS2_mid_nonneg j) hs.1
  have hc0 : 0 ≤ (bgpParamsNW w).cα := (bgpParamsNW_cα_pos w).le
  have hexp : 1 ≤ Real.exp ((bgpParamsNW w).cα * s) :=
    Real.one_le_exp (mul_nonneg hc0 hs0)
  have hg0 : 0 ≤ ((bgpWarmGainQNW w : ℚ) : ℝ) :=
    bgpWarmGainQNW_nonneg_real w
  have hcg : (1 / 4 : ℝ) ^ bgpHeadlineM *
        ((bgpWarmGainQNW w : ℚ) : ℝ) ≤ bgpNW4cg w s := by
    unfold bgpNW4cg
    calc
      (1 / 4 : ℝ) ^ bgpHeadlineM *
          ((bgpWarmGainQNW w : ℚ) : ℝ)
          ≤ ((1 + Real.sin s) / 2) ^ bgpHeadlineM *
              ((bgpWarmGainQNW w : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_right hpow hg0
      _ ≤ ((1 + Real.sin s) / 2) ^ bgpHeadlineM *
          (((bgpWarmGainQNW w : ℚ) : ℝ) *
            Real.exp ((bgpParamsNW w).cα * s)) := by
        apply mul_le_mul_of_nonneg_left
        · simpa using mul_le_mul_of_nonneg_left hexp hg0
        · exact pow_nonneg (by linarith [Real.neg_one_le_sin s]) _
  have hqscale :
      (1734736490 : ℝ) * S ^ 6 ≤
        ((bgpWarmGainQNW w : ℚ) : ℝ) := by
    have hpow6 : (1 : ℝ) ≤ (6 : ℝ) ^ w := one_le_pow₀ (by norm_num)
    rw [hSdef]
    unfold bgpWarmGainQNW bgpWarmGainCNW
    push_cast
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤
      1734736490 * (bgpScaleW w : ℝ) ^ 6) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 6) w)]
  have hpow5 : (5184 : ℝ) ^ 5 ≤ S ^ 5 :=
    pow_le_pow_left₀ (by norm_num) hS 5
  have hscale :
      400 * (4 : ℝ) ^ bgpHeadlineM * S ≤
        (1734736490 : ℝ) * S ^ 6 := by
    have hm := mul_le_mul_of_nonneg_left hpow5 hS0.le
    have hnum :
        400 * (4 : ℝ) ^ bgpHeadlineM ≤
          (1734736490 : ℝ) * (5184 : ℝ) ^ 5 := by
      norm_num [bgpHeadlineM]
    calc
      400 * (4 : ℝ) ^ bgpHeadlineM * S
          ≤ ((1734736490 : ℝ) * (5184 : ℝ) ^ 5) * S :=
        mul_le_mul_of_nonneg_right hnum hS0.le
      _ ≤ (1734736490 : ℝ) * S ^ 6 := by
        nlinarith [hm]
  have hbase :
      (bgpParamsNW w).cα ≤ (15 / 16 : ℝ) *
        ((1 / 4 : ℝ) ^ bgpHeadlineM *
          ((bgpWarmGainQNW w : ℚ) : ℝ)) := by
    rw [bgpParamsNW_cα_def]
    have hgain := hscale.trans hqscale
    rw [hSdef] at hgain
    -- hgain : 400 * 4^M * bgpScaleW w ≤ warmgain.  Avoid `norm_num [bgpHeadlineM]`
    -- on the full goal (it whnf-blows up on `warmgain`/`bgpScaleW`); the only
    -- numeric fact needed is `(1/4)^M · 4^M = 1`.
    have hpp : ((1 / 4 : ℝ)) ^ bgpHeadlineM * (4 : ℝ) ^ bgpHeadlineM = 1 := by
      rw [← mul_pow]; norm_num
    have h4M : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ bgpHeadlineM := by positivity
    have hb : (0 : ℝ) ≤ (bgpScaleW w : ℝ) := by positivity
    have hstep : (400 : ℝ) * (bgpScaleW w : ℝ) ≤
        (1 / 4 : ℝ) ^ bgpHeadlineM * ((bgpWarmGainQNW w : ℚ) : ℝ) := by
      calc (400 : ℝ) * (bgpScaleW w : ℝ)
          = (1 / 4 : ℝ) ^ bgpHeadlineM *
              (400 * (4 : ℝ) ^ bgpHeadlineM * (bgpScaleW w : ℝ)) := by
            rw [show (1 / 4 : ℝ) ^ bgpHeadlineM *
                  (400 * (4 : ℝ) ^ bgpHeadlineM * (bgpScaleW w : ℝ))
                = 400 * ((1 / 4 : ℝ) ^ bgpHeadlineM * (4 : ℝ) ^ bgpHeadlineM)
                    * (bgpScaleW w : ℝ) by ring, hpp]; ring
        _ ≤ (1 / 4 : ℝ) ^ bgpHeadlineM * ((bgpWarmGainQNW w : ℚ) : ℝ) :=
            mul_le_mul_of_nonneg_left hgain h4M
    linarith [mul_le_mul_of_nonneg_left hstep (by norm_num : (0 : ℝ) ≤ 15 / 16), hb]
  have hbase0 : 0 ≤ (1 / 4 : ℝ) ^ bgpHeadlineM *
      ((bgpWarmGainQNW w : ℚ) : ℝ) := by positivity
  calc
    (bgpParamsNW w).cα ≤ (15 / 16 : ℝ) *
        ((1 / 4 : ℝ) ^ bgpHeadlineM *
          ((bgpWarmGainQNW w : ℚ) : ℝ)) := hbase
    _ ≤ gap * ((1 / 4 : ℝ) ^ bgpHeadlineM *
          ((bgpWarmGainQNW w : ℚ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hgap hbase0
    _ ≤ gap * bgpNW4cg w s :=
      mul_le_mul_of_nonneg_left hcg (by linarith)

/-- The reset convolution from `S2Mid` retains absolute physical-time decay. -/
theorem bgpS4b_reset_duhamel_timelocal_NW
    (w j : ℕ) {gap t : ℝ}
    (hgap : (15 : ℝ) / 16 ≤ gap)
    (ht : t ∈ Icc (bgpS2Mid j) (selectorMUNextWriteStart j)) :
    (∫ s in (bgpS2Mid j)..t,
        Real.exp (gap *
          (((bgpHeadlineSolFamNW w) w).G s -
            ((bgpHeadlineSolFamNW w) w).G (bgpS2Mid j))) *
          (((1 + Real.cos s) / 2) ^ bgpHeadlineM *
            ((bgpHeadlineKappa : ℚ) : ℝ))) *
        Real.exp (-gap *
          (((bgpHeadlineSolFamNW w) w).G t -
            ((bgpHeadlineSolFamNW w) w).G (bgpS2Mid j))) ≤
      bgpS4bResetCoeffNW w *
        Real.exp (-((bgpParamsNW w).cα * t)) := by
  let sol := (bgpHeadlineSolFamNW w) w
  let a := bgpS2Mid j
  let c := (bgpParamsNW w).cα
  let cg : ℝ → ℝ := bgpNW4cg w
  let reset : ℝ → ℝ := fun s =>
    ((1 + Real.cos s) / 2) ^ bgpHeadlineM *
      ((bgpHeadlineKappa : ℚ) : ℝ)
  have hat : a ≤ t := ht.1
  have hgap0 : 0 < gap := by linarith
  have hc : 0 < c := by simpa [c] using bgpParamsNW_cα_pos w
  have ha0 : 0 ≤ a := bgpS2_mid_nonneg j
  have hmajor : ∀ s ∈ Icc a t,
      reset s ≤ (gap * cg s - c) *
        (bgpS4bResetCoeffNW w * Real.exp (-(c * s))) := by
    intro s hs
    have hswin : s ∈ Icc (bgpS2Mid j)
        (selectorMUNextWriteStart j) := ⟨hs.1, le_trans hs.2 ht.2⟩
    have hgain := bgpS4b_gap_mul_cg_ge_calpha_NW w j hgap hswin
    have hreset_le : reset s ≤ 1 := by
      dsimp [reset]
      norm_num [bgpHeadlineKappa]
      exact pow_le_one₀ (by nlinarith [Real.neg_one_le_cos s])
        (by nlinarith [Real.cos_le_one s])
    have hs_half : (1 / 2 : ℝ) ≤ s := by
      have hmid := hs.1
      dsimp [a] at hmid
      unfold bgpS2Mid at hmid
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      nlinarith [Real.pi_gt_three, mul_nonneg Real.pi_pos.le hj]
    have hcexp : c * Real.exp (-(c * s)) ≤ 1 := by
      have hcs0 : 0 ≤ c * s := mul_nonneg hc.le (by linarith)
      have hmul := Real.mul_exp_neg_le_exp_neg_one (c * s)
      have hexp1 : Real.exp (-(1 : ℝ)) ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_le_comm₀ (by positivity) (by norm_num)]
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      have hleft : c * Real.exp (-(c * s)) ≤
          2 * ((c * s) * Real.exp (-(c * s))) := by
        have hnonneg := mul_nonneg hc.le (Real.exp_pos (-(c * s))).le
        nlinarith [mul_nonneg (sub_nonneg.mpr hs_half) hnonneg]
      linarith
    have hC0 := bgpS4bResetCoeffNW_nonneg w
    have hsub : 1 ≤ (gap * cg s - c) *
        (bgpS4bResetCoeffNW w * Real.exp (-(c * s))) := by
      have hsin : -(1 / 2 : ℝ) ≤ Real.sin s := by
        by_cases hsz : s ≤ selectorMUZOffEnd j
        · exact bgpS2_sin_ge_neg_half j
            (le_trans (bgpS2_recStart_le_mid j) hswin.1) hsz
        · have hsright : s ∈ Icc (selectorMUZOffEnd j)
              (selectorMUNextWriteStart j) := ⟨le_of_not_ge hsz, hswin.2⟩
          linarith [bgpS4b_sin_nonneg j hsright.1 hsright.2]
      have hpow : (1 / 4 : ℝ) ^ bgpHeadlineM ≤
          ((1 + Real.sin s) / 2) ^ bgpHeadlineM := by
        apply pow_le_pow_left₀ (by norm_num)
        linarith
      have hg : 0 < ((bgpWarmGainQNW w : ℚ) : ℝ) :=
        bgpWarmGainQNW_pos_real w
      have hcancel :
          gap * ((1 / 4 : ℝ) ^ bgpHeadlineM *
            (((bgpWarmGainQNW w : ℚ) : ℝ) * Real.exp (c * s))) *
              (bgpS4bResetCoeffNW w * Real.exp (-(c * s))) =
            gap * 8 := by
        rw [bgpS4bResetCoeffNW]
        have hexpc : Real.exp (c * s) * Real.exp (-(c * s)) = 1 := by
          rw [← Real.exp_add]
          simp
        field_simp
        norm_num [bgpHeadlineM]
        calc
          1 / 1099511627776 * Real.exp (c * s) * 8796093022208 *
                Real.exp (-(c * s)) =
              8 * (Real.exp (c * s) * Real.exp (-(c * s))) := by ring
          _ = 8 := by rw [hexpc]; ring
      have hcg_lower : (1 / 4 : ℝ) ^ bgpHeadlineM *
          (((bgpWarmGainQNW w : ℚ) : ℝ) * Real.exp (c * s)) ≤ cg s := by
        unfold cg bgpNW4cg c
        exact mul_le_mul_of_nonneg_right hpow
          (mul_nonneg (bgpWarmGainQNW_nonneg_real w) (Real.exp_pos _).le)
      have hfactor0 : 0 ≤
          bgpS4bResetCoeffNW w * Real.exp (-(c * s)) :=
        mul_nonneg hC0 (Real.exp_pos _).le
      have hmain := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcg_lower hgap0.le) hfactor0
      have hcost : c *
          (bgpS4bResetCoeffNW w * Real.exp (-(c * s))) ≤ 1 := by
        have hCle : bgpS4bResetCoeffNW w ≤ 1 :=
          bgpS4bResetCoeffNW_le_one w
        have hfac0 : 0 ≤ c * Real.exp (-(c * s)) :=
          mul_nonneg hc.le (Real.exp_pos _).le
        have hmul := mul_le_mul_of_nonneg_left hCle hfac0
        calc
          c * (bgpS4bResetCoeffNW w * Real.exp (-(c * s))) =
              (c * Real.exp (-(c * s))) * bgpS4bResetCoeffNW w := by ring
          _ ≤ (c * Real.exp (-(c * s))) * 1 := hmul
          _ ≤ 1 := by simpa using hcexp
      rw [hcancel] at hmain
      nlinarith
    exact hreset_le.trans hsub
  have hsuper :=
    forward_reset_integral_mul_decay_le_exp_supersolution
      (a := a) (t := t) (gap := gap) (c := c)
      (C := bgpS4bResetCoeffNW w)
      (G := sol.G) (cg := cg) (reset := reset)
      hat hgap0 hc (bgpS4bResetCoeffNW_nonneg w)
      sol.cont_G
      (fun s hs => by
        have hs0 : 0 ≤ s := le_trans ha0 hs.1
        simpa [cg, sol] using bgpNW4_G_hasDeriv w w hs0)
      (bgpNW4cg_cont w)
      (by dsimp [reset]; fun_prop)
      hmajor
  simpa [sol, a, c, cg, reset, neg_mul] using hsuper

/-- Exact settled loser envelope from `S2Mid` through the right edge. -/
theorem bgpS4b_loser_mass_exact_NW (w j : ℕ) :
    ∀ t ∈ Icc (bgpS2Mid j) (selectorMUNextWriteStart j),
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => ((bgpHeadlineSolFamNW w) w).lam v t) ≤
      epsLamSettled (V := UniversalLocalView)
        (1 / (Fintype.card UniversalLocalView : ℝ))
        (selectorReplicatorGapVal bgpHeadlineEta bgpHeadlineEta_pos)
        (Fintype.card UniversalLocalView : ℝ)
        (∫ s in (bgpS2Mid j)..t,
          Real.exp
            (selectorReplicatorGapVal bgpHeadlineEta bgpHeadlineEta_pos *
              (((bgpHeadlineSolFamNW w) w).G s -
                ((bgpHeadlineSolFamNW w) w).G (bgpS2Mid j))) *
            (((1 + Real.cos s) / 2) ^ bgpHeadlineM *
              ((bgpHeadlineKappa : ℚ) : ℝ)))
        (((bgpHeadlineSolFamNW w) w).G) (bgpS2Mid j) t := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  set sol := (bgpHeadlineSolFamNW w) w with hsol
  set a := bgpS2Mid j with ha_def
  set gap := selectorReplicatorGapVal bgpHeadlineEta bgpHeadlineEta_pos
    with hgap_def
  intro t ht
  have hat : a ≤ t := by simpa only [a] using ht.1
  have ha0 : 0 ≤ a := by simpa only [a] using bgpS2_mid_nonneg j
  have hgap0 : 0 < gap := by simpa only [gap] using bgpS13_gapVal_pos
  have hcard_pos : (0 : ℝ) < (Fintype.card UniversalLocalView : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr
      (⟨defaultLocalViewU⟩ : Nonempty UniversalLocalView)
  set Kt := ∫ s in a..t,
    Real.exp (gap * (sol.G s - sol.G a)) *
      (((1 + Real.cos s) / 2) ^ bgpHeadlineM *
        ((bgpHeadlineKappa : ℚ) : ℝ)) with hKt_def
  have hKt0 : 0 ≤ Kt := by
    rw [hKt_def]
    apply intervalIntegral.integral_nonneg hat
    intro s _
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_cos s]) _)
        (by norm_num [bgpHeadlineKappa]))
  have htube := bgpS4b_mid_to_right_tube_NW w j
  have hfloor := bgpS4b_newWinner_floor_NW w j
  have hsub : ∀ s, s ∈ Icc a t →
      s ∈ Icc (bgpS2Mid j) (selectorMUNextWriteStart j) :=
    fun s hs => ⟨by simpa only [a] using hs.1, le_trans hs.2 ht.2⟩
  have hraw := loser_mass_small_on_settled_window sol
    (localViewU (solMUReplStaticCfg w (j + 1)))
    (selectStart := a) (writeStart := t) (readStart := t)
    (Lmin := 1 / (Fintype.card UniversalLocalView : ℝ))
    (gap := gap) (R0 := (Fintype.card UniversalLocalView : ℝ))
    (Kreset := Kt)
    hat (le_refl t)
    (by positivity) hgap0.le hcard_pos.le hKt0
    (fun s hs => selectorSchedule_domain_of_nonneg_structural s
      (le_trans ha0 hs.1))
    ((((continuous_const.add Real.continuous_cos).div_const 2).pow _).mul
      continuous_const)
    (fun s hs => hfloor s (hsub s hs))
    (fun v s hs => bgpNW_lam_nonneg_forward w w v s
      (le_trans ha0 hs.1))
    (fun s hs => bgpNW_lam_sum_forward w w s (le_trans ha0 hs.1))
    (fun s hs =>
      mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_cos s]) _)
        (by norm_num [bgpHeadlineKappa]))
    (fun s hs => bgpNW4cg_nonneg w s)
    (fun v hv s hs => by
      have h := bgpSegC_pairwiseGap_of_single_tube_NW w (j + 1)
        htube s (hsub s ⟨hs.1, hs.2.le⟩) v hv
      change universalPval bgpHeadlineEta bgpHeadlineEta_pos v (sol.u s) -
          universalPval bgpHeadlineEta bgpHeadlineEta_pos
            (localViewU (solMUReplStaticCfg w (j + 1))) (sol.u s) ≤ -gap
      change gap ≤ universalPval bgpHeadlineEta bgpHeadlineEta_pos
          (localViewU (solMUReplStaticCfg w (j + 1))) (sol.u s) -
        universalPval bgpHeadlineEta bgpHeadlineEta_pos v (sol.u s) at h
      linarith)
    (fun v hv => by
      have hfloor_a : 1 / (Fintype.card UniversalLocalView : ℝ) ≤
          sol.lam (localViewU (solMUReplStaticCfg w (j + 1))) a :=
        hfloor a (by
          change a ∈ Icc a (selectorMUNextWriteStart j)
          exact ⟨le_rfl, le_trans ht.1 ht.2⟩)
      exact bgpHeadline_lam_ratio_card_bound_at
        (lam := fun v' : UniversalLocalView => sol.lam v' a)
        (vstar := localViewU (solMUReplStaticCfg w (j + 1)))
        (bgpNW_lam_sum_forward w w a ha0)
        (fun v' => bgpNW_lam_nonneg_forward w w v' a ha0)
        hfloor_a v hv)
    (fun t' ht' => by
      have heq : t' = t := le_antisymm ht'.2 ht'.1
      rw [heq, hKt_def])
    (fun t' ht' => by
      have heq : t' = t := le_antisymm ht'.2 ht'.1
      rw [heq])
  have h := hraw t ⟨le_rfl, le_rfl⟩
  simpa [sol, a, gap, Kt, hgap_def, hKt_def, hsol, ha_def] using h

end Ripple.BoundedUniversality.BGP
