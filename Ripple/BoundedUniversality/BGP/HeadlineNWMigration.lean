import Ripple.BoundedUniversality.BGP.HeadlineUnconditional

noncomputable section
namespace Ripple.BoundedUniversality.BGP
open Set MachineInstance
open scoped BigOperators

theorem paper3RecoveryCgMinLeNW (wg j : ℕ) :
    ∀ u ∈ Icc (selectorMUWriteStartTime j) (selectorMUSelectStartTime j),
      paper3RecoveryCgMin wg j ≤
        ((1 + Real.sin u) / 2) ^ paper3HeadlineM *
          (((paper3WarmGainQNW wg : ℚ) : ℝ) *
            Real.exp ((bgpParamsNW wg).cα * u)) := by
  intro u hu
  have hgate : u ∈
      Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + Real.pi / 2) := by
    refine ⟨?_, ?_⟩
    · simpa [selectorMUWriteStartTime] using hu.1
    · have hsel_hold : selectorMUSelectStartTime j ≤ selectorMUWriteHoldTime j :=
        le_of_lt (selectorMUSelectStart_lt_hold j)
      have hright : u ≤ selectorMUWriteHoldTime j := le_trans hu.2 hsel_hold
      simpa [selectorMUWriteHoldTime] using hright
  have hsin : (1 : ℝ) / 2 ≤ Real.sin u :=
    sin_ge_half_of_gate_window j hgate
  have hsin_base : (3 / 4 : ℝ) ≤ (1 + Real.sin u) / 2 := by
    linarith
  have hsin_pow :
      (3 / 4 : ℝ) ^ paper3HeadlineM ≤
        ((1 + Real.sin u) / 2) ^ paper3HeadlineM := by
    simpa [paper3HeadlineM] using
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) hsin_base 20)
  have hC_le_warm :
      ((paper3WarmGainC : ℚ) : ℝ) ≤ ((paper3WarmGainQNW wg : ℚ) : ℝ) := by
    have h1 : (1734736490 : ℚ) ≤ paper3WarmGainCNW wg :=
      paper3WarmGainCNW_ge_base wg
    have h2 : paper3WarmGainCNW wg ≤ paper3WarmGainQNW wg := by
      have hpow : (1 : ℚ) ≤ (6 : ℚ) ^ wg :=
        one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 6)
      have hC0 := paper3WarmGainCNW_nonneg wg
      unfold paper3WarmGainQNW
      nlinarith
    have h3 : (paper3WarmGainC : ℚ) ≤ paper3WarmGainQNW wg := by
      unfold paper3WarmGainC
      linarith
    exact_mod_cast h3
  have hu_nonneg : 0 ≤ u :=
    le_trans (selectorMUWriteStartTime_nonneg j) hu.1
  have hcα_nonneg : 0 ≤ (bgpParamsNW wg).cα := by
    rw [bgpParamsNW_cα_def]
    have := bgpScaleWR_pos wg
    nlinarith
  have hexp_one : (1 : ℝ) ≤ Real.exp ((bgpParamsNW wg).cα * u) :=
    Real.one_le_exp_iff.mpr (mul_nonneg hcα_nonneg hu_nonneg)
  have hwarm_nonneg : 0 ≤ ((paper3WarmGainQNW wg : ℚ) : ℝ) :=
    paper3WarmGainQNW_nonneg_real wg
  have hC_le_warm_exp :
      ((paper3WarmGainC : ℚ) : ℝ) ≤
        ((paper3WarmGainQNW wg : ℚ) : ℝ) *
          Real.exp ((bgpParamsNW wg).cα * u) := by
    calc ((paper3WarmGainC : ℚ) : ℝ)
        ≤ ((paper3WarmGainQNW wg : ℚ) : ℝ) := hC_le_warm
      _ = ((paper3WarmGainQNW wg : ℚ) : ℝ) * 1 := by ring
      _ ≤ ((paper3WarmGainQNW wg : ℚ) : ℝ) *
          Real.exp ((bgpParamsNW wg).cα * u) :=
          mul_le_mul_of_nonneg_left hexp_one hwarm_nonneg
  unfold paper3RecoveryCgMin
  have hpow_nonneg : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ paper3HeadlineM := by
    positivity
  calc (3 / 4 : ℝ) ^ paper3HeadlineM * ((paper3WarmGainC : ℚ) : ℝ)
      ≤ (3 / 4 : ℝ) ^ paper3HeadlineM *
        (((paper3WarmGainQNW wg : ℚ) : ℝ) *
          Real.exp ((bgpParamsNW wg).cα * u)) :=
        mul_le_mul_of_nonneg_left hC_le_warm_exp hpow_nonneg
    _ ≤ ((1 + Real.sin u) / 2) ^ paper3HeadlineM *
        (((paper3WarmGainQNW wg : ℚ) : ℝ) *
          Real.exp ((bgpParamsNW wg).cα * u)) :=
        mul_le_mul_of_nonneg_right hsin_pow
          (mul_nonneg hwarm_nonneg (Real.exp_pos _).le)

end Ripple.BoundedUniversality.BGP
