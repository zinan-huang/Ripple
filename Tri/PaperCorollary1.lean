/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.PaperLemma3

/-!
# Paper Corollary 1: completion of one phase-1 stage

Paper Lemma 3 doubles the actual signed gap.  A phase-1 stage may start above
its nominal lower checkpoint, so this file transfers that stronger target to
the stage target and then uses the phase-1 square-gap premise to expose the
paper's `exp (-Θ(γ lg n))` error.
-/

namespace Tri

open scoped ENNReal

/-- Completion target for a phase-1 stage whose nominal starting gap is `D`. -/
def Corollary1Target (n D x : ℕ) : Prop :=
  n + 2 * D ≤ 2 * x

noncomputable instance corollary1TargetDecidable
    (n D : ℕ) :
    DecidablePred (Corollary1Target n D) :=
  Classical.decPred _

/-- The literal productive-clock content of paper Corollary 1, before
substituting the phase-1 square-root scale.  The actual starting gap `Δ` may
lie anywhere in the active stage interval `D ≤ Δ < 2D`. -/
theorem corollary1_stage_gap
    {n x₀ y₀ D Δ : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hD0 : 0 < D) (hstart : D ≤ Δ)
    (hactive : Δ < 2 * D) (hcap : 2 * D ≤ n) :
    terminalFailureMass
        (iter
          (freeze (Corollary1Target n D) (productiveTriChain n))
          (2 * n) x₀)
        (Corollary1Target n D) ≤
      (2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-((D : ℝ) ^ 2 / (48 * (n : ℝ))))) := by
  let A : ℕ → Prop := Corollary1Target n D
  let B : ℕ → Prop := Lemma3Target n Δ
  let K : ℕ → PMF ℕ := productiveTriChain n
  have hΔ0 : 0 < Δ := lt_of_lt_of_le hD0 hstart
  have hΔn : Δ < n := lt_of_lt_of_le hactive hcap
  have hBA : ∀ x, B x → A x := by
    intro x hx
    have hthreshold :
        2 * D ≤ min (2 * Δ) n :=
      le_min (by omega) hcap
    unfold A B Corollary1Target Lemma3Target at *
    omega
  have hlazy : IsLazyProjection K (freeze B K) id := by
    intro x
    by_cases hx : B x
    · right
      rw [freeze_of_mem x hx]
      simpa using PMF.map_id (PMF.pure x)
    · left
      rw [freeze_of_not_mem x hx]
      simpa using PMF.map_id (K x)
  have hprojection :=
    targetFreeze_failure_le_lazy_projection
      A K (freeze B K) id hlazy (2 * n) x₀
  have hmono :
      terminalFailureMass
          (iter (freeze B K) (2 * n) x₀) A ≤
        terminalFailureMass
          (iter (freeze B K) (2 * n) x₀) B :=
    terminalFailureMass_mono _ A B hBA
  have hDΔR : (D : ℝ) ≤ Δ := by
    exact_mod_cast hstart
  have hsq :
      (D : ℝ) ^ 2 ≤ (Δ : ℝ) ^ 2 := by
    nlinarith [hDΔR, show (0 : ℝ) ≤ D by positivity,
      show (0 : ℝ) ≤ Δ by positivity]
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_trans hΔ0 hΔn)
  have hfrac :
      (D : ℝ) ^ 2 / (48 * (n : ℝ)) ≤
        (Δ : ℝ) ^ 2 / (48 * (n : ℝ)) :=
    (div_le_div_iff_of_pos_right (by positivity)).2 hsq
  have herr :
      ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 / (48 * (n : ℝ))))) ≤
        ENNReal.ofReal
          (Real.exp
            (-((D : ℝ) ^ 2 / (48 * (n : ℝ))))) :=
    ENNReal.ofReal_le_ofReal <|
      Real.exp_le_exp.mpr (neg_le_neg hfrac)
  calc
    terminalFailureMass
        (iter
          (freeze (Corollary1Target n D) (productiveTriChain n))
          (2 * n) x₀)
        (Corollary1Target n D) ≤
      terminalFailureMass
          (iter (freeze B K) (2 * n) x₀) A := by
      simpa [A, K] using hprojection
    _ ≤ terminalFailureMass
          (iter (freeze B K) (2 * n) x₀) B :=
      hmono
    _ ≤ (2 : ℝ≥0∞) *
          ENNReal.ofReal
            (Real.exp
              (-((Δ : ℝ) ^ 2 / (48 * (n : ℝ))))) := by
      simpa [B, K] using
        lemma3_productive_gap_doubling
          hpop hgap hΔ0 hΔn
    _ ≤ (2 : ℝ≥0∞) *
          ENNReal.ofReal
            (Real.exp
              (-((D : ℝ) ^ 2 / (48 * (n : ℝ))))) := by
      simpa [mul_comm] using
        mul_le_mul_right herr (2 : ℝ≥0∞)

/-- **Paper Corollary 1.** Every active phase-1 stage completes within `2n`
productive reactions.  The integral premise
`γ n lg n ≤ D²` is the subtraction-free form of the paper's
`D ≥ √(γ n lg n)` stage invariant. -/
theorem corollary1
    {n x₀ y₀ D Δ γ : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hD0 : 0 < D) (hstart : D ≤ Δ)
    (hactive : Δ < 2 * D) (hcap : 2 * D ≤ n)
    (hscale : γ * n * Nat.log 2 n ≤ D ^ 2) :
    terminalFailureMass
        (iter
          (freeze (Corollary1Target n D) (productiveTriChain n))
          (2 * n) x₀)
        (Corollary1Target n D) ≤
      (2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-(((γ * Nat.log 2 n : ℕ) : ℝ) / 48))) := by
  have hΔ0 : 0 < Δ := lt_of_lt_of_le hD0 hstart
  have hΔn : Δ < n := lt_of_lt_of_le hactive hcap
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_trans hΔ0 hΔn)
  have hscaleR :
      (γ : ℝ) * (n : ℝ) * (Nat.log 2 n : ℝ) ≤
        (D : ℝ) ^ 2 := by
    exact_mod_cast hscale
  have hfrac :
      ((γ * Nat.log 2 n : ℕ) : ℝ) / 48 ≤
        (D : ℝ) ^ 2 / (48 * (n : ℝ)) := by
    calc
      ((γ * Nat.log 2 n : ℕ) : ℝ) / 48 =
          ((γ : ℝ) * (n : ℝ) * (Nat.log 2 n : ℝ)) /
            (48 * (n : ℝ)) := by
        norm_num only [Nat.cast_mul]
        field_simp
      _ ≤ (D : ℝ) ^ 2 / (48 * (n : ℝ)) :=
        (div_le_div_iff_of_pos_right (by positivity)).2 hscaleR
  have herr :
      ENNReal.ofReal
          (Real.exp
            (-((D : ℝ) ^ 2 / (48 * (n : ℝ))))) ≤
        ENNReal.ofReal
          (Real.exp
            (-(((γ * Nat.log 2 n : ℕ) : ℝ) / 48))) :=
    ENNReal.ofReal_le_ofReal <|
      Real.exp_le_exp.mpr (neg_le_neg hfrac)
  exact
    (corollary1_stage_gap
      hpop hgap hD0 hstart hactive hcap).trans
      (by
        simpa [mul_comm] using
          mul_le_mul_right herr (2 : ℝ≥0∞))

end Tri
