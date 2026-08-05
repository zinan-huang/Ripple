/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveProperStage

/-!
# Arithmetic schedule for proper-stage amplification

The paper repeats the `49/48` proper-stage increment 144 times.  Rather than
iterate nested ceilings, it tracks the simpler lower thresholds

`ceil((48+i) * Δ / 48)`, for `0 ≤ i ≤ 144`.

The final threshold is exactly `4Δ`, and each next threshold is covered by the
capped proper-stage target of the current threshold.
-/

namespace Tri.Multi

open scoped ENNReal

variable {m n : ℕ}

/-- Natural-number ceiling of division by 48. -/
def ceilDiv48 (a : ℕ) : ℕ :=
  (a + 47) / 48

@[simp] theorem ceilDiv48_le_iff
    (a g : ℕ) :
    ceilDiv48 a ≤ g ↔ a ≤ 48 * g := by
  unfold ceilDiv48
  omega

theorem le_mul_ceilDiv48
    (a : ℕ) :
    a ≤ 48 * ceilDiv48 a := by
  exact (ceilDiv48_le_iff a (ceilDiv48 a)).mp le_rfl

/-- The uncapped linear threshold at repetition `i`. -/
def properAmplificationRaw (Δ i : ℕ) : ℕ :=
  ceilDiv48 ((48 + i) * Δ)

/-- The paper's linear threshold capped at the maximum possible gap. -/
def properAmplificationTarget (Δ i n : ℕ) : ℕ :=
  min (properAmplificationRaw Δ i) n

theorem properAmplificationRaw_zero
    (Δ : ℕ) :
    properAmplificationRaw Δ 0 = Δ := by
  unfold properAmplificationRaw ceilDiv48
  omega

theorem properAmplificationTarget_zero
    (Δ n : ℕ) :
    properAmplificationTarget Δ 0 n = min Δ n := by
  rw [properAmplificationTarget, properAmplificationRaw_zero]

theorem properAmplificationRaw_144
    (Δ : ℕ) :
    properAmplificationRaw Δ 144 = 4 * Δ := by
  unfold properAmplificationRaw ceilDiv48
  omega

theorem properAmplificationTarget_144
    (Δ n : ℕ) :
    properAmplificationTarget Δ 144 n = min (4 * Δ) n := by
  rw [properAmplificationTarget, properAmplificationRaw_144]

theorem properAmplificationRaw_mono
    (Δ i j : ℕ) (hij : i ≤ j) :
    properAmplificationRaw Δ i ≤ properAmplificationRaw Δ j := by
  unfold properAmplificationRaw
  rw [ceilDiv48_le_iff]
  have hj := le_mul_ceilDiv48 ((48 + j) * Δ)
  have hnum : (48 + i) * Δ ≤ (48 + j) * Δ :=
    Nat.mul_le_mul_right Δ (Nat.add_le_add_left hij 48)
  exact hnum.trans hj

theorem properAmplificationTarget_mono
    (Δ n i j : ℕ) (hij : i ≤ j) :
    properAmplificationTarget Δ i n ≤
      properAmplificationTarget Δ j n := by
  unfold properAmplificationTarget
  exact min_le_min
    (properAmplificationRaw_mono Δ i j hij) le_rfl

theorem properAmplificationRaw_le_pairTarget
    (Δ i : ℕ) :
    properAmplificationRaw Δ (i + 1) ≤
      properPairTarget (properAmplificationRaw Δ i) := by
  unfold properAmplificationRaw
  rw [ceilDiv48_le_iff]
  have hi :=
    le_mul_ceilDiv48 ((48 + i) * Δ)
  have hpair :
      49 * properAmplificationRaw Δ i ≤
        48 * properPairTarget (properAmplificationRaw Δ i) := by
    exact (properPairTarget_le_iff
      (properAmplificationRaw Δ i)
      (properPairTarget (properAmplificationRaw Δ i))).mp le_rfl
  have hscaled :
      (49 + i) * Δ ≤ 49 * ceilDiv48 ((48 + i) * Δ) := by
    nlinarith [Nat.zero_le (i * Δ)]
  rw [show (48 + (i + 1)) * Δ = (49 + i) * Δ by ring]
  simpa only [properAmplificationRaw] using hscaled.trans hpair

/-- One proper-stage target covers the next threshold in the 144-step linear
schedule.  No restriction on `i` is needed for this arithmetic fact. -/
theorem properAmplificationTarget_succ_le_stageTarget
    (Δ i n : ℕ) :
    properAmplificationTarget Δ (i + 1) n ≤
      properStageTarget (properAmplificationTarget Δ i n) n := by
  unfold properAmplificationTarget properStageTarget
  by_cases hi : properAmplificationRaw Δ i ≤ n
  · rw [min_eq_left hi]
    exact min_le_min
      (properAmplificationRaw_le_pairTarget Δ i) le_rfl
  · have hni : n ≤ properAmplificationRaw Δ i := by omega
    rw [min_eq_right hni]
    have hnPair : n ≤ properPairTarget n :=
      properPairTarget_ge n
    rw [min_eq_right hnPair]
    exact min_le_right _ _

/-- Every scheduled threshold stays below the population cap. -/
theorem properAmplificationTarget_le_population
    (Δ i n : ℕ) :
    properAmplificationTarget Δ i n ≤ n :=
  Nat.min_le_right _ _

/-- Before the cap is reached, every scheduled threshold is at least the base
gap. -/
theorem base_le_properAmplificationTarget
    (Δ i n : ℕ) (hΔn : Δ ≤ n) :
    Δ ≤ properAmplificationTarget Δ i n := by
  unfold properAmplificationTarget
  apply le_min
  · calc
      Δ = properAmplificationRaw Δ 0 :=
        (properAmplificationRaw_zero Δ).symm
      _ ≤ properAmplificationRaw Δ i :=
        properAmplificationRaw_mono Δ 0 i (Nat.zero_le i)
  · exact hΔn

/-- The three one-substage error terms allow one uniform envelope at the
original base-gap scale. -/
theorem properStage_error_le_uniform
    (m n Δ D x0 : ℕ)
    (hn : 0 < n) (hD4 : 4 ≤ D)
    (hΔD : Δ ≤ D) (hDx0 : D ≤ x0) (hx0n : x0 ≤ n) :
    (m : ℝ≥0∞) *
          ENNReal.ofReal
            (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) +
        (m : ℝ≥0∞) *
          ENNReal.ofReal
            (Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ))))) +
        ENNReal.ofReal (Real.exp (-(x0 : ℝ) / 8)) ≤
      ((2 * m + 1 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((Δ : ℝ) ^ 2 / (82944 * (n : ℝ))))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0pos : 0 < x0 := by omega
  have hx0R : (0 : ℝ) < x0 := by exact_mod_cast hx0pos
  have hΔDR : (Δ : ℝ) ≤ D := by exact_mod_cast hΔD
  have hDx0R : (D : ℝ) ≤ x0 := by exact_mod_cast hDx0
  have hx0nR : (x0 : ℝ) ≤ n := by exact_mod_cast hx0n
  have hΔn : Δ ≤ n := hΔD.trans (hDx0.trans hx0n)
  have hsqΔD : (Δ : ℝ) ^ 2 ≤ (D : ℝ) ^ 2 := by
    nlinarith
  have hfracA :
      (Δ : ℝ) ^ 2 / (82944 * (n : ℝ)) ≤
        (D : ℝ) ^ 2 / (18 * (n : ℝ)) := by
    calc
      (Δ : ℝ) ^ 2 / (82944 * (n : ℝ)) ≤
          (D : ℝ) ^ 2 / (82944 * (n : ℝ)) := by
        exact div_le_div_of_nonneg_right hsqΔD (by positivity)
      _ ≤ (D : ℝ) ^ 2 / (18 * (n : ℝ)) := by
        apply div_le_div_of_nonneg_left
        · positivity
        · positivity
        · nlinarith
  have hfracC :
      (Δ : ℝ) ^ 2 / (82944 * (n : ℝ)) ≤
        (D : ℝ) ^ 2 / (82944 * (x0 : ℝ)) := by
    calc
      (Δ : ℝ) ^ 2 / (82944 * (n : ℝ)) ≤
          (D : ℝ) ^ 2 / (82944 * (n : ℝ)) := by
        exact div_le_div_of_nonneg_right hsqΔD (by positivity)
      _ ≤ (D : ℝ) ^ 2 / (82944 * (x0 : ℝ)) := by
        apply div_le_div_of_nonneg_left
        · positivity
        · positivity
        · nlinarith
  have hprodNat : Δ ^ 2 ≤ x0 * n := by
    have hmul := Nat.mul_le_mul hΔD hΔn
    simpa [pow_two] using hmul.trans
      (Nat.mul_le_mul_right n hDx0)
  have hprodR : (Δ : ℝ) ^ 2 ≤ (x0 : ℝ) * n := by
    exact_mod_cast hprodNat
  have hfracB :
      (Δ : ℝ) ^ 2 / (82944 * (n : ℝ)) ≤
        (x0 : ℝ) / 8 := by
    calc
      (Δ : ℝ) ^ 2 / (82944 * (n : ℝ)) ≤
          ((x0 : ℝ) * n) / (82944 * (n : ℝ)) := by
        exact div_le_div_of_nonneg_right hprodR (by positivity)
      _ = (x0 : ℝ) / 82944 := by
        field_simp
      _ ≤ (x0 : ℝ) / 8 := by
        apply div_le_div_of_nonneg_left
        · positivity
        · norm_num
        · norm_num
  let E : ℝ≥0∞ :=
    ENNReal.ofReal
      (Real.exp (-((Δ : ℝ) ^ 2 / (82944 * (n : ℝ)))))
  have hA :
      ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) ≤ E := by
    dsimp only [E]
    exact ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.mpr (neg_le_neg hfracA))
  have hC :
      ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ))))) ≤ E := by
    dsimp only [E]
    exact ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.mpr (neg_le_neg hfracC))
  have hB :
      ENNReal.ofReal (Real.exp (-(x0 : ℝ) / 8)) ≤ E := by
    dsimp only [E]
    exact ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.mpr (by
        have := neg_le_neg hfracB
        convert this using 1 <;> ring))
  calc
    (m : ℝ≥0∞) *
          ENNReal.ofReal
            (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) +
        (m : ℝ≥0∞) *
          ENNReal.ofReal
            (Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ))))) +
        ENNReal.ofReal (Real.exp (-(x0 : ℝ) / 8)) ≤
      (m : ℝ≥0∞) * E + (m : ℝ≥0∞) * E + E :=
        add_le_add (add_le_add
          (mul_le_mul_right hA _) (mul_le_mul_right hC _)) hB
    _ = ((2 * m + 1 : ℕ) : ℝ≥0∞) * E := by
      push_cast
      ring

end Tri.Multi

#print axioms Tri.Multi.properAmplificationTarget_succ_le_stageTarget
#print axioms Tri.Multi.properAmplificationTarget_144
#print axioms Tri.Multi.properStage_error_le_uniform
