/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.RelaxedBandErrorConstants

/-!
# Uniform error envelope for the adaptive relaxed schedule

The scalar hypotheses below are independent of the dyadic rung.  They turn
the exact finite error sum into one common exponential envelope per rung.
-/

namespace Tri

open scoped ENNReal

/-- Adaptive rung data together with the three quantitative scalar
certificates needed by the error analysis. -/
structure RelaxedDyadicAdaptiveErrorData
    (r : RelaxedRate) (n P : ℕ) where
  base : RelaxedDyadicAdaptiveData r n P
  hbeta : 1 < base.beta
  hclock :
    (1 : ℝ) ≤ (r.fire : ℝ) * (base.C : ℝ)
  habsorb :
    -Real.log (relaxedDirW base.beta : ℝ) ≤
      32 * (base.R₀ : ℝ) *
        Real.log (relaxedDirEta base.beta : ℝ)
  hrate :
    (1 : ℝ) ≤
      32 * (base.R₀ : ℝ) *
        Real.log (relaxedDirEta base.beta : ℝ)

/-- Common three-term envelope for every rung. -/
noncomputable def relaxedDyadicAdaptiveRungEnvelope
    (r : RelaxedRate) (n P : ℕ)
    (E : RelaxedDyadicAdaptiveErrorData r n P) : ℝ≥0∞ :=
  ENNReal.ofReal
      (Real.exp
        (-((E.base.L : ℝ) *
          Real.log (E.base.beta : ℝ)))) +
    ENNReal.ofReal (Real.exp (-(E.base.L : ℝ))) +
    ENNReal.ofReal (Real.exp (-(E.base.L : ℝ)))

/-- The quantitative scalar hypotheses bound each adaptive rung by the same
buffer-scale exponential envelope. -/
theorem relaxedDyadicAdaptiveRungError_le
    (r : RelaxedRate) (n P j : ℕ)
    (E : RelaxedDyadicAdaptiveErrorData r n P) :
    relaxedDyadicLadderError r n
        (relaxedDyadicAdaptiveRungData r n P E.base) j ≤
      relaxedDyadicAdaptiveRungEnvelope r n P E := by
  let Q := relaxedDyadicActiveScale P j
  let R :=
    relaxedDyadicAdaptiveMultiplier E.base.R₀ E.base.L Q
  have hQ : 1 ≤ Q :=
    relaxedDyadicActiveScale_pos P j
  have hQP : Q ≤ P :=
    relaxedDyadicActiveScale_le P j E.base.hP
  have hroom : 2 * (Q + E.base.L) ≤ n := by
    have := E.base.hroom
    omega
  have hR₀R : E.base.R₀ ≤ R :=
    relaxedDyadicAdaptiveMultiplier_ge_base
      E.base.R₀ E.base.L Q
  have hR : 1 ≤ R := E.base.hR₀.trans hR₀R
  have hlogEta :
      0 ≤ Real.log (relaxedDirEta E.base.beta : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast
      le_of_lt (relaxedDir_eta_gt_one E.hbeta)
  have hscale :
      32 * (E.base.R₀ : ℝ) *
          Real.log (relaxedDirEta E.base.beta : ℝ) ≤
        32 * (R : ℝ) *
          Real.log (relaxedDirEta E.base.beta : ℝ) := by
    have hcast : (E.base.R₀ : ℝ) ≤ (R : ℝ) := by
      exact_mod_cast hR₀R
    gcongr
  have habsorb :
      -Real.log (relaxedDirW E.base.beta : ℝ) ≤
        32 * (R : ℝ) *
          Real.log (relaxedDirEta E.base.beta : ℝ) :=
    E.habsorb.trans hscale
  have hraw :=
    relaxedDyadicBandError_le_exp
      r n Q E.base.L R E.base.C E.base.beta
      hQ E.base.hL hR E.base.hC hroom
      E.hbeta E.hclock habsorb
  have hRQ :
      E.base.R₀ * E.base.L ≤ R * Q := by
    dsimp only [R, Q]
    exact relaxedDyadicAdaptiveMultiplier_mul_scale_ge
      E.base.R₀ E.base.L
        (relaxedDyadicActiveScale P j)
        (relaxedDyadicActiveScale_pos P j)
  have hLleRQ : E.base.L ≤ R * Q := by
    calc
      E.base.L ≤ E.base.R₀ * E.base.L := by
        simpa only [one_mul] using
          Nat.mul_le_mul_right E.base.L E.base.hR₀
      _ ≤ R * Q := hRQ
  have hLleDir :
      (E.base.L : ℝ) ≤
        32 * (R : ℝ) * (Q : ℝ) *
          Real.log (relaxedDirEta E.base.beta : ℝ) := by
    have hrateL :
        (E.base.L : ℝ) ≤
          (E.base.L : ℝ) *
            (32 * (E.base.R₀ : ℝ) *
              Real.log (relaxedDirEta E.base.beta : ℝ)) := by
      have hL0 : (0 : ℝ) ≤ E.base.L := by positivity
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left E.hrate hL0
    have hRQreal :
        ((E.base.R₀ * E.base.L : ℕ) : ℝ) ≤
          ((R * Q : ℕ) : ℝ) := by
      exact_mod_cast hRQ
    have hreward :
        (E.base.L : ℝ) *
            (32 * (E.base.R₀ : ℝ) *
              Real.log (relaxedDirEta E.base.beta : ℝ)) ≤
          32 * (R : ℝ) * (Q : ℝ) *
            Real.log (relaxedDirEta E.base.beta : ℝ) := by
      push_cast at hRQreal
      nlinarith
    exact hrateL.trans hreward
  have hdir :
      ENNReal.ofReal
          (Real.exp
            (-(32 * (R : ℝ) * (Q : ℝ) *
              Real.log (relaxedDirEta E.base.beta : ℝ)))) ≤
        ENNReal.ofReal (Real.exp (-(E.base.L : ℝ))) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    linarith
  have hclock :
      ENNReal.ofReal (Real.exp (-((R * Q : ℕ) : ℝ))) ≤
        ENNReal.ofReal (Real.exp (-(E.base.L : ℝ))) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (by exact_mod_cast hLleRQ)
  change
    relaxedDyadicBandError r n Q E.base.L R
        (E.base.C * R) E.base.beta 0 ≤ _
  exact hraw.trans (add_le_add (add_le_add le_rfl hdir) hclock)

/-- The complete adaptive error sum is the number of dyadic rungs times the
common rung envelope. -/
theorem relaxedDyadicAdaptiveError_le
    (r : RelaxedRate) (n P : ℕ)
    (E : RelaxedDyadicAdaptiveErrorData r n P) :
    relaxedDyadicAdaptiveError r n P E.base ≤
      (relaxedDyadicStageCount P : ℝ≥0∞) *
        relaxedDyadicAdaptiveRungEnvelope r n P E := by
  unfold relaxedDyadicAdaptiveError
  calc
    (∑ j ∈ Finset.range (relaxedDyadicStageCount P),
        relaxedDyadicLadderError r n
          (relaxedDyadicAdaptiveRungData r n P E.base) j) ≤
      ∑ j ∈ Finset.range (relaxedDyadicStageCount P),
        relaxedDyadicAdaptiveRungEnvelope r n P E := by
          gcongr with j hj
          exact relaxedDyadicAdaptiveRungError_le r n P j E
    _ = (relaxedDyadicStageCount P : ℝ≥0∞) *
        relaxedDyadicAdaptiveRungEnvelope r n P E := by
          simp [nsmul_eq_mul]

/-- The physical adaptive schedule reaches exact consensus with the uniform
exponential error envelope. -/
theorem relaxedDyadicAdaptive_raw_consensus_exp
    (r : RelaxedRate) (n P : ℕ)
    (E : RelaxedDyadicAdaptiveErrorData r n P) :
    terminalFailureMass
        (iter
          (freeze (fun x : ℕ => x = n)
            (relaxedTriChain r n))
          (relaxedDyadicAdaptiveHorizon r n P E.base)
          (relaxedDyadicStart n P))
        (fun x : ℕ => x = n) ≤
      (relaxedDyadicStageCount P : ℝ≥0∞) *
        relaxedDyadicAdaptiveRungEnvelope r n P E := by
  exact (relaxedDyadicAdaptive_raw_consensus r n P E.base).trans
    (relaxedDyadicAdaptiveError_le r n P E)

end Tri

#print axioms Tri.relaxedDyadicAdaptiveRungError_le
#print axioms Tri.relaxedDyadicAdaptiveError_le
#print axioms Tri.relaxedDyadicAdaptive_raw_consensus_exp
