/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveProperProgressStop

/-!
# Explicit proper-stage progress exponent

The repaired proper-stage quotient is bounded by
`exp(-D^2/(82944*x0))`.  The proof keeps the target-potential growth and the
relevant-event contraction as separate real exponential terms.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

theorem properPairTarget_pred_ge
    (D : ℕ) :
    D ≤ properPairTarget D - 1 := by
  rw [properPairTarget_eq]
  omega

theorem properPairTarget_excess_le
    (D : ℕ) :
    48 * (properPairTarget D - 1 - D) ≤ D := by
  unfold properPairTarget
  omega

theorem properPairTarget_pred_eq_of_le_48
    (D : ℕ) (hD : 1 ≤ D) (hD48 : D ≤ 48) :
    properPairTarget D - 1 = D := by
  unfold properPairTarget
  omega

theorem properStageScale_lower_seven_fifths
    (x0 : ℕ) (hx04 : 4 ≤ x0) :
    7 * x0 ≤ 5 * properStageScale x0 := by
  unfold properStageScale
  omega

theorem properStageScale_upper_three_halves
    (x0 : ℕ) :
    2 * properStageScale x0 ≤ 3 * x0 := by
  unfold properStageScale
  omega

theorem half_lower_two_fifths
    (D : ℕ) (hD4 : 4 ≤ D) :
    2 * D ≤ 5 * (D / 2) := by
  omega

theorem half_lower_twentyfour_fortynine
    (D : ℕ) (hD49 : 49 ≤ D) :
    24 * D ≤ 49 * (D / 2) := by
  omega

/-- Algebraic separation of target-potential growth and counter
contraction. -/
theorem properProgress_quotient_eq
    (S d D u K : ℕ) (hS : 0 < S) :
    pairProperProgressTilt S d ^ D /
        (pairProperProgressTilt S d ^ u *
          (pairProperProgressFactor S d)⁻¹ ^ K) =
      (pairProperProgressTilt S d ^ D /
          pairProperProgressTilt S d ^ u) *
        pairProperProgressFactor S d ^ K := by
  let w := pairProperProgressTilt S d
  let φ := pairProperProgressFactor S d
  have hw0 : w ≠ 0 := by
    dsimp only [w]
    exact pairProperProgressTilt_ne_zero S d hS
  have hwtop : w ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    dsimp only [w]
    exact pairProperProgressTilt_le_one S d hS
  have hφ0 : φ ≠ 0 := by
    dsimp only [φ]
    exact pairProperProgressFactor_ne_zero S d hS
  have hφtop : φ ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    dsimp only [φ]
    exact pairProperProgressFactor_le_one S d hS
  change w ^ D / (w ^ u * (φ⁻¹) ^ K) =
    (w ^ D / w ^ u) * φ ^ K
  calc
    w ^ D / (w ^ u * (φ⁻¹) ^ K) =
        w ^ D * 1 / (w ^ u * (φ⁻¹) ^ K) := by rw [mul_one]
    _ = (w ^ D / w ^ u) * (1 / (φ⁻¹) ^ K) :=
      ENNReal.mul_div_mul_comm
        (Or.inl (pow_ne_zero _ hw0))
        (Or.inl (ENNReal.pow_ne_top hwtop))
    _ = (w ^ D / w ^ u) * φ ^ K := by
      rw [one_div, ENNReal.inv_pow, inv_inv]

/-- Scalar quotient from the repaired proper-stage progress theorem has the
paper-scale Gaussian exponent. -/
theorem properProgress_quotient_le_exp
    (D x0 : ℕ) (hD4 : 4 ≤ D) (hDx0 : D ≤ x0) :
    pairProperProgressTilt (properStageScale x0) (D / 2) ^ D /
        (pairProperProgressTilt (properStageScale x0) (D / 2) ^
            (properPairTarget D - 1) *
          (pairProperProgressFactor (properStageScale x0) (D / 2))⁻¹ ^
            properInvolvingTarget x0) ≤
      ENNReal.ofReal
        (Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ))))) := by
  let S := properStageScale x0
  let d := D / 2
  let u := properPairTarget D - 1
  let K := properInvolvingTarget x0
  let p := 8 * S + 3 * d
  let q := 8 * S + 4 * d
  let a := 52 * S ^ 2 + d ^ 2
  let b := 52 * S ^ 2
  have hx04 : 4 ≤ x0 := hD4.trans hDx0
  have hx0 : 0 < x0 := by omega
  have hS : 0 < S := by
    dsimp only [S]
    exact properStageScale_pos x0 (by omega)
  have hd0R : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have hSR : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  have hx0R : (0 : ℝ) < (x0 : ℝ) := by exact_mod_cast hx0
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hp : 0 < p := by
    dsimp only [p]
    omega
  have hpq : p ≤ q := by
    dsimp only [p, q]
    omega
  have hb : 0 < b := by
    dsimp only [b]
    positivity
  have hba : b ≤ a := by
    dsimp only [a, b]
    omega
  have hDu : D ≤ u := by
    dsimp only [u]
    exact properPairTarget_pred_ge D
  have hratio :
      pairProperProgressTilt S d ^ D /
          pairProperProgressTilt S d ^ u ≤
        ENNReal.ofReal
          (Real.exp (((u : ℝ) - (D : ℝ)) *
            Real.log ((q : ℝ) / (p : ℝ)))) := by
    simpa only [pairProperProgressTilt, p, q] using
      Tri.base_pow_ratio_le_ofReal_exp p q D u hp hpq hDu
  have hfactor :
      pairProperProgressFactor S d ^ K ≤
        ENNReal.ofReal
          (Real.exp (-(K : ℝ) *
            ((a : ℝ) - (b : ℝ)) / (a : ℝ))) := by
    simpa only [pairProperProgressFactor, a, b] using
      Tri.ratio_pow_le_exp a b K hb hba
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (hp.trans_le hpq)
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hratioPos : (0 : ℝ) < (q : ℝ) / (p : ℝ) :=
    div_pos hqR hpR
  have hratioOne : (1 : ℝ) ≤ (q : ℝ) / (p : ℝ) := by
    rw [le_div_iff₀ hpR]
    norm_num
    exact_mod_cast hpq
  have hlog0 : 0 ≤ Real.log ((q : ℝ) / (p : ℝ)) :=
    Real.log_nonneg hratioOne
  have hlog :
      Real.log ((q : ℝ) / (p : ℝ)) ≤ (d : ℝ) / (8 * (S : ℝ)) := by
    have hlogRaw := Real.log_le_sub_one_of_pos hratioPos
    have hsub :
        (q : ℝ) / (p : ℝ) - 1 = (d : ℝ) / (p : ℝ) := by
      dsimp only [p, q]
      push_cast
      field_simp
      ring
    rw [hsub] at hlogRaw
    refine hlogRaw.trans ?_
    have h8 : (0 : ℝ) < 8 * (S : ℝ) := by positivity
    have hpR' : (0 : ℝ) < (p : ℝ) := hpR
    rw [div_le_div_iff₀ hpR' h8]
    dsimp only [p]
    push_cast
    nlinarith
  have hr :
      ((u : ℝ) - (D : ℝ)) ≤ (D : ℝ) / 48 := by
    have hsubNat : u - D = properPairTarget D - 1 - D := by
      dsimp only [u]
    have hnat := properPairTarget_excess_le D
    rw [← hsubNat] at hnat
    have hcast :
        (48 : ℝ) * ((u - D : ℕ) : ℝ) ≤ (D : ℝ) := by
      exact_mod_cast hnat
    rw [← Nat.cast_sub hDu]
    nlinarith
  have hdUpper :
      (d : ℝ) ≤ (D : ℝ) / 2 := by
    have hnat := Nat.div_mul_le_self D 2
    have hnat' : 2 * d ≤ D := by
      dsimp only [d]
      simpa [mul_comm] using hnat
    have hcast : (2 : ℝ) * d ≤ D := by exact_mod_cast hnat'
    nlinarith
  have hSLower :
      (7 : ℝ) / 5 * (x0 : ℝ) ≤ (S : ℝ) := by
    have hnat := properStageScale_lower_seven_fifths x0 hx04
    change 7 * x0 ≤ 5 * S at hnat
    have hcast : (7 : ℝ) * x0 ≤ 5 * S := by exact_mod_cast hnat
    nlinarith
  have hSUpper :
      (S : ℝ) ≤ (3 : ℝ) / 2 * (x0 : ℝ) := by
    have hnat := properStageScale_upper_three_halves x0
    change 2 * S ≤ 3 * x0 at hnat
    have hcast : (2 : ℝ) * S ≤ 3 * x0 := by exact_mod_cast hnat
    nlinarith
  have hDx0R : (D : ℝ) ≤ (x0 : ℝ) := by exact_mod_cast hDx0
  have hdUpperX :
      (d : ℝ) ≤ (x0 : ℝ) / 2 := hdUpper.trans (by nlinarith)
  have hKLower :
      (x0 : ℝ) / 2 ≤ (K : ℝ) := by
    have hnat : x0 ≤ 2 * K := by
      dsimp only [K]
      unfold properInvolvingTarget
      omega
    have hcast :
        (x0 : ℝ) ≤ 2 * (K : ℝ) := by
      exact_mod_cast hnat
    nlinarith
  have hdenUpper :
      (a : ℝ) ≤ 118 * (x0 : ℝ) ^ 2 := by
    have hS0 : (0 : ℝ) ≤ S := by positivity
    have hx00 : (0 : ℝ) ≤ x0 := by positivity
    have hd0 : (0 : ℝ) ≤ d := by positivity
    have hSsq :
        (S : ℝ) ^ 2 ≤ ((3 : ℝ) / 2 * (x0 : ℝ)) ^ 2 :=
      (sq_le_sq₀ hS0 (by positivity)).mpr hSUpper
    have hdsq :
        (d : ℝ) ^ 2 ≤ ((x0 : ℝ) / 2) ^ 2 :=
      (sq_le_sq₀ hd0 (by positivity)).mpr hdUpperX
    dsimp only [a]
    push_cast
    nlinarith
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (hb.trans_le hba)
  have hgrowth :
      ((u : ℝ) - (D : ℝ)) *
          Real.log ((q : ℝ) / (p : ℝ)) ≤
        5 * (D : ℝ) ^ 2 / (5376 * (x0 : ℝ)) := by
    have hDuR : (D : ℝ) ≤ (u : ℝ) := by exact_mod_cast hDu
    have huD0 : (0 : ℝ) ≤ (u : ℝ) - (D : ℝ) := by linarith
    calc
      ((u : ℝ) - (D : ℝ)) *
          Real.log ((q : ℝ) / (p : ℝ)) ≤
        ((D : ℝ) / 48) * ((d : ℝ) / (8 * (S : ℝ))) :=
          mul_le_mul hr hlog hlog0 (by positivity)
      _ ≤ ((D : ℝ) / 48) *
          (((D : ℝ) / 2) / (8 * ((7 : ℝ) / 5 * (x0 : ℝ)))) := by
        gcongr
      _ = 5 * (D : ℝ) ^ 2 / (5376 * (x0 : ℝ)) := by
        field_simp
        ring
  have hexponent :
      ((u : ℝ) - (D : ℝ)) *
          Real.log ((q : ℝ) / (p : ℝ)) -
        (K : ℝ) * ((a : ℝ) - (b : ℝ)) / (a : ℝ) ≤
      -((D : ℝ) ^ 2 / (82944 * (x0 : ℝ))) := by
    by_cases hD48 : D ≤ 48
    · have huD : u = D := by
        dsimp only [u]
        exact properPairTarget_pred_eq_of_le_48 D (by omega) hD48
      have hdLower :
          (2 : ℝ) / 5 * (D : ℝ) ≤ (d : ℝ) := by
        have hnat := half_lower_two_fifths D hD4
        change 2 * D ≤ 5 * d at hnat
        have hcast : (2 : ℝ) * D ≤ 5 * d := by exact_mod_cast hnat
        nlinarith
      have hdecay :
          (D : ℝ) ^ 2 / (1475 * (x0 : ℝ)) ≤
            (K : ℝ) * ((a : ℝ) - (b : ℝ)) / (a : ℝ) := by
        have hab : ((a : ℝ) - (b : ℝ)) = (d : ℝ) ^ 2 := by
          dsimp only [a, b]
          push_cast
          ring
        rw [hab]
        calc
          (D : ℝ) ^ 2 / (1475 * (x0 : ℝ)) =
              ((x0 : ℝ) / 2) *
                (((2 : ℝ) / 5 * (D : ℝ)) ^ 2) /
                  (118 * (x0 : ℝ) ^ 2) := by
            field_simp
            ring
          _ ≤ (K : ℝ) * (d : ℝ) ^ 2 / (a : ℝ) := by
            gcongr
      rw [huD]
      norm_num
      have htarget :
          (D : ℝ) ^ 2 / (82944 * (x0 : ℝ)) ≤
            (D : ℝ) ^ 2 / (1475 * (x0 : ℝ)) := by
        gcongr
        norm_num
      linarith
    · have hD49 : 49 ≤ D := by omega
      have hdLower :
          (24 : ℝ) / 49 * (D : ℝ) ≤ (d : ℝ) := by
        have hnat := half_lower_twentyfour_fortynine D hD49
        change 24 * D ≤ 49 * d at hnat
        have hcast : (24 : ℝ) * D ≤ 49 * d := by exact_mod_cast hnat
        rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0 : ℝ) < 49)]
        simpa [mul_comm] using hcast
      have hdecay :
          (D : ℝ) ^ 2 / (1024 * (x0 : ℝ)) ≤
            (K : ℝ) * ((a : ℝ) - (b : ℝ)) / (a : ℝ) := by
        have hab : ((a : ℝ) - (b : ℝ)) = (d : ℝ) ^ 2 := by
          dsimp only [a, b]
          push_cast
          ring
        rw [hab]
        calc
          (D : ℝ) ^ 2 / (1024 * (x0 : ℝ)) ≤
              288 * (D : ℝ) ^ 2 / (283318 * (x0 : ℝ)) := by
            have hc : (1 : ℝ) / 1024 ≤ 288 / 283318 := by
              norm_num
            have hs : 0 ≤ (D : ℝ) ^ 2 / (x0 : ℝ) := by positivity
            have hm := mul_le_mul_of_nonneg_right hc hs
            convert hm using 1 <;> field_simp
          _ =
              ((x0 : ℝ) / 2) *
                (((24 : ℝ) / 49 * (D : ℝ)) ^ 2) /
                  (118 * (x0 : ℝ) ^ 2) := by
            field_simp
            ring
          _ ≤ (K : ℝ) * (d : ℝ) ^ 2 / (a : ℝ) := by
            gcongr
      have hconstants :
          (5 : ℝ) / 5376 + 1 / 82944 ≤ 1 / 1024 := by
        norm_num
      have hscale0 : 0 ≤ (D : ℝ) ^ 2 / (x0 : ℝ) := by positivity
      have hscaled := mul_le_mul_of_nonneg_right hconstants hscale0
      have hcombine :
            5 * (D : ℝ) ^ 2 / (5376 * (x0 : ℝ)) +
              (D : ℝ) ^ 2 / (82944 * (x0 : ℝ)) ≤
            (D : ℝ) ^ 2 / (1024 * (x0 : ℝ)) := by
        convert hscaled using 1 <;> field_simp
      linarith
  rw [properProgress_quotient_eq S d D u K hS]
  calc
    (pairProperProgressTilt S d ^ D /
          pairProperProgressTilt S d ^ u) *
        pairProperProgressFactor S d ^ K ≤
      ENNReal.ofReal
          (Real.exp (((u : ℝ) - (D : ℝ)) *
            Real.log ((q : ℝ) / (p : ℝ)))) *
        ENNReal.ofReal
          (Real.exp (-(K : ℝ) *
            ((a : ℝ) - (b : ℝ)) / (a : ℝ))) :=
      mul_le_mul hratio hfactor bot_le bot_le
    _ = ENNReal.ofReal
        (Real.exp (((u : ℝ) - (D : ℝ)) *
            Real.log ((q : ℝ) / (p : ℝ)) -
          (K : ℝ) * ((a : ℝ) - (b : ℝ)) / (a : ℝ))) := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 3
      ring
    _ ≤ ENNReal.ofReal
        (Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ))))) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexponent)

/-- Fixed-competitor completion-(c) failure mass with the explicit repaired
proper-stage exponent. -/
theorem productivePairJointLocalStop_proper_completion_exp_tail
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (D x0 T : ℕ) (hD4 : 4 ≤ D) (hDx0 : D ≤ x0)
    (q0 : ProductivePairJointState m n) (hq0 : q0.CounterInv)
    (hgap0 : pairGapNat q0.config X Y = D)
    (hrelevant0 : q0.relevant = 0) :
    (∑' z : ProductivePairJointState m n,
      if pairGapNat z.config X Y < properPairTarget D ∧
          x0 ≤ 2 * z.involving then
        iter
          (productivePairJointLocalStop h3 X Y
            (properStageScale x0) (D / 2) (properPairTarget D))
          T q0 z
      else 0) ≤
      ENNReal.ofReal
        (Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ))))) := by
  exact
    (productivePairJointLocalStop_proper_completion_tail_fresh
      h3 X Y hXY D x0 T hD4 hDx0 q0 hq0 hgap0 hrelevant0).trans
      (properProgress_quotient_le_exp D x0 hD4 hDx0)

end Tri.Multi

#print axioms Tri.Multi.properProgress_quotient_le_exp
#print axioms Tri.Multi.productivePairJointLocalStop_proper_completion_exp_tail
