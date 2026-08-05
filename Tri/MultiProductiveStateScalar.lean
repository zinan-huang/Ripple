/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveStateDependent

/-!
# Scalar bounds for state-dependent proper-stage errors

Both fixed-pair failure quotients have two sources of decay: the usual
Gaussian term at the minimum stage gap, and an additional term proportional
to the competitor's excess initial gap.  This file makes that second term
explicit and sums the two failure channels under one envelope.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-! ## Fixed-pair geometric decay -/

/-- Factor the excess initial gap out of a geometric quotient. -/
theorem pow_quotient_factor_of_le
    (u : ℝ≥0∞) (a D g : ℕ) (hDg : D ≤ g) :
    u ^ g / u ^ a =
      u ^ (g - D) * (u ^ D / u ^ a) := by
  calc
    u ^ g / u ^ a =
        u ^ ((g - D) + D) / u ^ a := by
      congr 2
      omega
    _ = u ^ (g - D) * (u ^ D / u ^ a) := by
      rw [pow_add, mul_div_assoc]

/-- The local safety quotient at the minimum stage gap has Gaussian decay at
the stage-start plurality scale. -/
theorem properSafety_quotient_le_exp
    (D x0 : ℕ) (hD4 : 4 ≤ D) (hDx0 : D ≤ x0) :
    pairGapLinearBase (properStageScale x0) (D / 2) ^ D /
        pairGapLinearBase (properStageScale x0) (D / 2) ^
          (D / 2 - 1) ≤
      ENNReal.ofReal
        (Real.exp (-((D : ℝ) ^ 2 / (24 * (x0 : ℝ))))) := by
  let S := properStageScale x0
  let d := D / 2
  let b := D - d
  have hx0 : 0 < x0 := by omega
  have hS : 0 < S := by
    dsimp only [S]
    exact properStageScale_pos x0 hx0
  have hd2 : 2 ≤ d := by
    dsimp only [d]
    omega
  have hdb : d + b = D := by
    dsimp only [d, b]
    omega
  have hbase :
      pairGapLinearBase S d ^ D /
          pairGapLinearBase S d ^ (d - 1) =
        pairGapLinearBase S d ^ (b + 1) := by
    rw [show D = (d - 1) + (b + 1) by omega,
      pow_add, mul_comm, mul_div_assoc,
      ENNReal.div_self
        (pow_ne_zero _
          (pairGapLinearBase_ne_zero S d hS))
        (ENNReal.pow_ne_top
          (ne_top_of_le_ne_top ENNReal.one_ne_top
            (pairGapLinearBase_le_one S d hS))),
      mul_one]
  have hpow :=
    pairGapLinearBase_pow_le_exp S d (b + 1) hS
  have hdNat : D ≤ 3 * d := by
    dsimp only [d]
    omega
  have hbNat : D ≤ 2 * (b + 1) := by
    dsimp only [b, d]
    omega
  have hnumNat : D ^ 2 ≤ 6 * (b + 1) * d := by
    have hmul := Nat.mul_le_mul hbNat hdNat
    calc
      D ^ 2 = D * D := by ring
      _ ≤ 2 * (b + 1) * (3 * d) := hmul
      _ = 6 * (b + 1) * d := by ring
  have hSupper : 2 * S ≤ 3 * x0 := by
    dsimp only [S]
    exact properStageScale_upper_three_halves x0
  have hdUpper : 2 * d ≤ x0 := by
    dsimp only [d]
    omega
  have hdenNat : 2 * S + d ≤ 4 * x0 := by omega
  have hx0R : (0 : ℝ) < x0 := by exact_mod_cast hx0
  have hdenR :
      (2 : ℝ) * S + d ≤ 4 * x0 := by
    exact_mod_cast hdenNat
  have hnumR :
      (D : ℝ) ^ 2 ≤ 6 * (b + 1 : ℕ) * d := by
    exact_mod_cast hnumNat
  have hrate :
      (D : ℝ) ^ 2 / (24 * (x0 : ℝ)) ≤
        (b + 1 : ℕ) * (d : ℝ) /
          (2 * (S : ℝ) + (d : ℝ)) := by
    have hdenPos : (0 : ℝ) < 2 * S + d := by positivity
    rw [div_le_div_iff₀ (by positivity) hdenPos]
    nlinarith
  rw [hbase]
  exact hpow.trans <|
    ENNReal.ofReal_le_ofReal <|
      Real.exp_le_exp.mpr (neg_le_neg hrate)

/-- Every power of the proper progress tilt has an explicit excess-gap
exponential envelope. -/
theorem pairProperProgressTilt_pow_le_exp
    (D x0 k : ℕ) (hD4 : 4 ≤ D) (hDx0 : D ≤ x0) :
    pairProperProgressTilt (properStageScale x0) (D / 2) ^ k ≤
      ENNReal.ofReal
        (Real.exp (-((k : ℝ) * (D : ℝ) /
          (40 * (x0 : ℝ))))) := by
  let S := properStageScale x0
  let d := D / 2
  let p := 8 * S + 3 * d
  let q := 8 * S + 4 * d
  have hx0 : 0 < x0 := by omega
  have hS : 0 < S := by
    dsimp only [S]
    exact properStageScale_pos x0 hx0
  have hp : 0 < p := by
    dsimp only [p]
    omega
  have hpq : p ≤ q := by
    dsimp only [p, q]
    omega
  have hraw := Tri.ratio_pow_le_exp q p k hp hpq
  have hSupper : 2 * S ≤ 3 * x0 := by
    dsimp only [S]
    exact properStageScale_upper_three_halves x0
  have hdUpper : 2 * d ≤ x0 := by
    dsimp only [d]
    omega
  have hqNat : q ≤ 14 * x0 := by
    dsimp only [q]
    omega
  have hdNat : 2 * D ≤ 5 * d := by
    dsimp only [d]
    exact half_lower_two_fifths D hD4
  have hx0R : (0 : ℝ) < x0 := by exact_mod_cast hx0
  have hqR : (0 : ℝ) < q := by exact_mod_cast hp.trans_le hpq
  have hqUpper : (q : ℝ) ≤ 14 * x0 := by
    exact_mod_cast hqNat
  have hdLower : (2 : ℝ) * D ≤ 5 * d := by
    exact_mod_cast hdNat
  have hrate :
      (k : ℝ) * (D : ℝ) / (40 * (x0 : ℝ)) ≤
        (k : ℝ) * ((q : ℝ) - (p : ℝ)) / (q : ℝ) := by
    have hdiff : ((q : ℝ) - (p : ℝ)) = (d : ℝ) := by
      dsimp only [p, q]
      push_cast
      ring
    rw [hdiff]
    by_cases hk : k = 0
    · simp [hk]
    · have hkR : (0 : ℝ) < k := by exact_mod_cast (Nat.pos_of_ne_zero hk)
      have hcross :
          (D : ℝ) * (q : ℝ) ≤
            40 * (x0 : ℝ) * (d : ℝ) := by
        calc
          (D : ℝ) * (q : ℝ) ≤
              (D : ℝ) * (14 * (x0 : ℝ)) :=
            mul_le_mul_of_nonneg_left hqUpper (by positivity)
          _ ≤ 40 * (x0 : ℝ) * (d : ℝ) := by
            nlinarith
      rw [div_le_div_iff₀ (by positivity) hqR]
      nlinarith
  simpa only [pairProperProgressTilt, p, q, S, d] using
    hraw.trans
      (ENNReal.ofReal_le_ofReal
        (Real.exp_le_exp.mpr (by
          have hneg := neg_le_neg hrate
          ring_nf at hneg ⊢
          exact hneg)))

/-- The local linear safety base has at least the same excess-gap decay as
the relaxed proper progress tilt. -/
theorem pairGapLocalLinearBase_pow_le_exp
    (D x0 k : ℕ) (hD4 : 4 ≤ D) (hDx0 : D ≤ x0) :
    pairGapLinearBase (properStageScale x0) (D / 2) ^ k ≤
      ENNReal.ofReal
        (Real.exp (-((k : ℝ) * (D : ℝ) /
          (40 * (x0 : ℝ))))) := by
  let S := properStageScale x0
  let d := D / 2
  let p := 2 * S
  let q := 2 * S + d
  have hx0 : 0 < x0 := by omega
  have hS : 0 < S := by
    dsimp only [S]
    exact properStageScale_pos x0 hx0
  have hp : 0 < p := by
    dsimp only [p]
    omega
  have hpq : p ≤ q := by
    dsimp only [p, q]
    omega
  have hraw := Tri.ratio_pow_le_exp q p k hp hpq
  have hSupper : 2 * S ≤ 3 * x0 := by
    dsimp only [S]
    exact properStageScale_upper_three_halves x0
  have hdUpper : 2 * d ≤ x0 := by
    dsimp only [d]
    omega
  have hqNat : q ≤ 4 * x0 := by
    dsimp only [q]
    omega
  have hdNat : 2 * D ≤ 5 * d := by
    dsimp only [d]
    exact half_lower_two_fifths D hD4
  have hqR : (0 : ℝ) < q := by exact_mod_cast hp.trans_le hpq
  have hqUpper : (q : ℝ) ≤ 4 * x0 := by
    exact_mod_cast hqNat
  have hdLower : (2 : ℝ) * D ≤ 5 * d := by
    exact_mod_cast hdNat
  have hrate :
      (k : ℝ) * (D : ℝ) / (40 * (x0 : ℝ)) ≤
        (k : ℝ) * ((q : ℝ) - (p : ℝ)) / (q : ℝ) := by
    have hdiff : ((q : ℝ) - (p : ℝ)) = (d : ℝ) := by
      dsimp only [p, q]
      push_cast
      ring
    rw [hdiff]
    by_cases hk : k = 0
    · simp [hk]
    · have hkR : (0 : ℝ) < k := by exact_mod_cast (Nat.pos_of_ne_zero hk)
      have hcross :
          (D : ℝ) * (q : ℝ) ≤
            40 * (x0 : ℝ) * (d : ℝ) := by
        calc
          (D : ℝ) * (q : ℝ) ≤
              (D : ℝ) * (4 * (x0 : ℝ)) :=
            mul_le_mul_of_nonneg_left hqUpper (by positivity)
          _ ≤ 40 * (x0 : ℝ) * (d : ℝ) := by
            nlinarith
      rw [div_le_div_iff₀ (by positivity) hqR]
      nlinarith
  simpa only [pairGapLinearBase, p, q, S, d] using
    hraw.trans
      (ENNReal.ofReal_le_ofReal
        (Real.exp_le_exp.mpr (by
          have hneg := neg_le_neg hrate
          ring_nf at hneg ⊢
          exact hneg)))

/-! ## A common exact pair envelope -/

/-- Common state-dependent scalar envelope for one fixed competitor and one
failure channel. -/
noncomputable def properPairStateEnvelope
    (D x0 g : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp
      (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ)) +
        (((g - D : ℕ) : ℝ) * (D : ℝ) /
          (40 * (x0 : ℝ))))))

/-- The exact completion-(a) quotient fits the common state-dependent
envelope. -/
theorem properSafety_actual_quotient_le_envelope
    (D x0 g : ℕ) (hD4 : 4 ≤ D) (hDx0 : D ≤ x0)
    (hDg : D ≤ g) :
    pairGapLinearBase (properStageScale x0) (D / 2) ^ g /
        pairGapLinearBase (properStageScale x0) (D / 2) ^
          (D / 2 - 1) ≤
      properPairStateEnvelope D x0 g := by
  let u := pairGapLinearBase (properStageScale x0) (D / 2)
  let E : ℝ :=
    (D : ℝ) ^ 2 / (82944 * (x0 : ℝ))
  let F : ℝ :=
    (((g - D : ℕ) : ℝ) * (D : ℝ) / (40 * (x0 : ℝ)))
  have hextra :
      u ^ (g - D) ≤ ENNReal.ofReal (Real.exp (-F)) := by
    simpa only [u, F] using
      pairGapLocalLinearBase_pow_le_exp D x0 (g - D) hD4 hDx0
  have hbase24 :=
    properSafety_quotient_le_exp D x0 hD4 hDx0
  have hbase :
      u ^ D / u ^ (D / 2 - 1) ≤
        ENNReal.ofReal (Real.exp (-E)) := by
    exact hbase24.trans <|
      ENNReal.ofReal_le_ofReal <|
        Real.exp_le_exp.mpr <| by
          dsimp only [E]
          have hx0 : (0 : ℝ) < x0 := by exact_mod_cast (by omega : 0 < x0)
          have hfrac :
              (D : ℝ) ^ 2 / (82944 * (x0 : ℝ)) ≤
                (D : ℝ) ^ 2 / (24 * (x0 : ℝ)) := by
            apply div_le_div_of_nonneg_left
            · positivity
            · positivity
            · nlinarith
          linarith
  rw [show u ^ g / u ^ (D / 2 - 1) =
      u ^ (g - D) * (u ^ D / u ^ (D / 2 - 1)) by
        exact pow_quotient_factor_of_le u (D / 2 - 1) D g hDg]
  calc
    u ^ (g - D) * (u ^ D / u ^ (D / 2 - 1)) ≤
        ENNReal.ofReal (Real.exp (-F)) *
          ENNReal.ofReal (Real.exp (-E)) :=
      mul_le_mul hextra hbase bot_le bot_le
    _ = properPairStateEnvelope D x0 g := by
      unfold properPairStateEnvelope
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 3
      dsimp only [E, F]
      ring

/-- The exact completion-(c) quotient at the capped target fits the same
state-dependent envelope. -/
theorem properProgress_actual_quotient_le_envelope
    (D x0 target g : ℕ)
    (hD4 : 4 ≤ D) (hDx0 : D ≤ x0)
    (htargetLe : target ≤ properPairTarget D)
    (hDg : D ≤ g) :
    pairProperProgressTilt (properStageScale x0) (D / 2) ^ g /
        (pairProperProgressTilt (properStageScale x0) (D / 2) ^
            (target - 1) *
          (pairProperProgressFactor
            (properStageScale x0) (D / 2))⁻¹ ^
              properInvolvingTarget x0) ≤
      properPairStateEnvelope D x0 g := by
  let w := pairProperProgressTilt (properStageScale x0) (D / 2)
  let φ := pairProperProgressFactor (properStageScale x0) (D / 2)
  let K := properInvolvingTarget x0
  let E : ℝ :=
    (D : ℝ) ^ 2 / (82944 * (x0 : ℝ))
  let F : ℝ :=
    (((g - D : ℕ) : ℝ) * (D : ℝ) / (40 * (x0 : ℝ)))
  have hS : 0 < properStageScale x0 :=
    properStageScale_pos x0 (by omega)
  have hw1 : w ≤ 1 := by
    dsimp only [w]
    exact pairProperProgressTilt_le_one _ _ hS
  have htargetPred :
      target - 1 ≤ properPairTarget D - 1 :=
    Nat.sub_le_sub_right htargetLe 1
  have hpowDen :
      w ^ (properPairTarget D - 1) ≤ w ^ (target - 1) :=
    pow_le_pow_right_of_le_one' hw1 htargetPred
  have hden :
      w ^ (properPairTarget D - 1) * (φ⁻¹) ^ K ≤
        w ^ (target - 1) * (φ⁻¹) ^ K := by
    simpa [mul_comm] using
      (mul_le_mul_right hpowDen ((φ⁻¹) ^ K))
  have hbase :
      w ^ D / (w ^ (target - 1) * (φ⁻¹) ^ K) ≤
        ENNReal.ofReal (Real.exp (-E)) := by
    exact
      (ENNReal.div_le_div_left hden _).trans <| by
        simpa only [w, φ, K, E] using
          properProgress_quotient_le_exp D x0 hD4 hDx0
  have hextra :
      w ^ (g - D) ≤ ENNReal.ofReal (Real.exp (-F)) := by
    simpa only [w, F] using
      pairProperProgressTilt_pow_le_exp D x0 (g - D) hD4 hDx0
  rw [show w ^ g /
      (w ^ (target - 1) * (φ⁻¹) ^ K) =
        w ^ (g - D) *
          (w ^ D / (w ^ (target - 1) * (φ⁻¹) ^ K)) by
        calc
          w ^ g / (w ^ (target - 1) * (φ⁻¹) ^ K) =
              w ^ ((g - D) + D) /
                (w ^ (target - 1) * (φ⁻¹) ^ K) := by
            congr 2
            omega
          _ = w ^ (g - D) *
              (w ^ D / (w ^ (target - 1) * (φ⁻¹) ^ K)) := by
            rw [pow_add, mul_div_assoc]]
  calc
    w ^ (g - D) *
          (w ^ D / (w ^ (target - 1) * (φ⁻¹) ^ K)) ≤
        ENNReal.ofReal (Real.exp (-F)) *
          ENNReal.ofReal (Real.exp (-E)) :=
      mul_le_mul hextra hbase bot_le bot_le
    _ = properPairStateEnvelope D x0 g := by
      unfold properPairStateEnvelope
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 3
      dsimp only [E, F]
      ring

/-- Both all-competitor channels in the exact proper-stage error fit two
copies of the common state-dependent pair envelope. -/
theorem productiveProperStageStateError_le_pair_envelopes
    (X : Species m) (D x0 : ℕ)
    (hD4 : 4 ≤ D) (hDx0 : D ≤ x0)
    (c0 : Config m n)
    (hinit : HasPairwiseGap c0 X D) :
    productiveProperStageStateError X D x0 c0 ≤
      2 * (∑ Y ∈ Finset.univ.erase X,
        properPairStateEnvelope D x0 (pairGapNat c0 X Y)) +
      ENNReal.ofReal (Real.exp (-(x0 : ℝ) / 8)) := by
  have hpair :
      ∀ Y ∈ Finset.univ.erase X,
        D ≤ pairGapNat c0 X Y := by
    intro Y hY
    have hYX : Y ≠ X := (Finset.mem_erase.mp hY).1
    have hg := hinit Y hYX
    unfold pairGapNat
    omega
  unfold productiveProperStageStateError
  have hsafety :
      (∑ Y ∈ Finset.univ.erase X,
        pairGapLinearBase (properStageScale x0) (D / 2) ^
            pairGapNat c0 X Y /
          pairGapLinearBase (properStageScale x0) (D / 2) ^
            (D / 2 - 1)) ≤
        ∑ Y ∈ Finset.univ.erase X,
          properPairStateEnvelope D x0 (pairGapNat c0 X Y) := by
    apply Finset.sum_le_sum
    intro Y hY
    exact properSafety_actual_quotient_le_envelope
      D x0 (pairGapNat c0 X Y) hD4 hDx0 (hpair Y hY)
  have hprogress :
      (∑ Y ∈ Finset.univ.erase X,
        pairProperProgressTilt (properStageScale x0) (D / 2) ^
            pairGapNat c0 X Y /
          (pairProperProgressTilt (properStageScale x0) (D / 2) ^
              (properStageTarget D n - 1) *
            (pairProperProgressFactor
              (properStageScale x0) (D / 2))⁻¹ ^
                properInvolvingTarget x0)) ≤
        ∑ Y ∈ Finset.univ.erase X,
          properPairStateEnvelope D x0 (pairGapNat c0 X Y) := by
    apply Finset.sum_le_sum
    intro Y hY
    exact properProgress_actual_quotient_le_envelope
      D x0 (properStageTarget D n) (pairGapNat c0 X Y)
      hD4 hDx0 (properStageTarget_le_pairTarget D n) (hpair Y hY)
  calc
    _ ≤ (∑ Y ∈ Finset.univ.erase X,
          properPairStateEnvelope D x0 (pairGapNat c0 X Y)) +
        (∑ Y ∈ Finset.univ.erase X,
          properPairStateEnvelope D x0 (pairGapNat c0 X Y)) +
        ENNReal.ofReal (Real.exp (-(x0 : ℝ) / 8)) :=
      add_le_add (add_le_add hsafety hprogress) le_rfl
    _ = 2 * (∑ Y ∈ Finset.univ.erase X,
          properPairStateEnvelope D x0 (pairGapNat c0 X Y)) +
        ENNReal.ofReal (Real.exp (-(x0 : ℝ) / 8)) := by ring

/-! ## Summing over competitors without a species loss

Competitors are split at half the plurality count. There are few large
competitors, while every small competitor gains extra geometric decay. This
replaces the naive factor equal to the total number of species.
-/

/-- Discarding the nonnegative excess-gap exponent gives the common Gaussian
base envelope. -/
theorem properPairStateEnvelope_le_base
    (D x0 g : ℕ) (hx0 : 0 < x0) :
    properPairStateEnvelope D x0 g ≤
      ENNReal.ofReal
        (Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ))))) := by
  unfold properPairStateEnvelope
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hx0R : (0 : ℝ) < x0 := by exact_mod_cast hx0
  have hfar :
      (0 : ℝ) ≤ ((g - D : ℕ) : ℝ) * (D : ℝ) /
        (40 * (x0 : ℝ)) := by positivity
  linarith

/-- A competitor below half the initial plurality count gains an additional
`exp(-D/160)` factor when `4D ≤ x0`. -/
theorem properPairStateEnvelope_le_far
    (c0 : Config m n) (X Y : Species m)
    (D x0 : ℕ) (hx0 : count c0 X = x0)
    (hD4 : 4 ≤ D) (h4D : 4 * D ≤ x0)
    (hsmall : ¬ x0 ≤ 2 * count c0 Y) :
    properPairStateEnvelope D x0 (pairGapNat c0 X Y) ≤
      ENNReal.ofReal
        (Real.exp
          (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ)) +
            (D : ℝ) / 160))) := by
  have hx0pos : 0 < x0 := by omega
  have hexcess :
      x0 ≤ 4 * (pairGapNat c0 X Y - D) := by
    unfold pairGapNat
    omega
  have hx0R : (0 : ℝ) < x0 := by exact_mod_cast hx0pos
  have hexcessR :
      (x0 : ℝ) ≤ 4 * ((pairGapNat c0 X Y - D : ℕ) : ℝ) := by
    exact_mod_cast hexcess
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hrate :
      (D : ℝ) / 160 ≤
        ((pairGapNat c0 X Y - D : ℕ) : ℝ) * (D : ℝ) /
          (40 * (x0 : ℝ)) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 160)
      (by positivity : (0 : ℝ) < 40 * x0)]
    nlinarith
  unfold properPairStateEnvelope
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  linarith

/-- Competitors at least half as populous as `X` are few: their number times
`x0` is at most `2n`. -/
theorem largeCompetitor_card_mul_le
    (c0 : Config m n) (X : Species m) (x0 : ℕ) :
    ((Finset.univ.erase X).filter
        (fun Y => x0 ≤ 2 * count c0 Y)).card * x0 ≤ 2 * n := by
  classical
  let s : Finset (Species m) :=
    (Finset.univ.erase X).filter
      (fun Y => x0 ≤ 2 * count c0 Y)
  have hlower :
      s.card * x0 ≤ ∑ Y ∈ s, 2 * count c0 Y := by
    simpa [nsmul_eq_mul, mul_comm] using
      (Finset.card_nsmul_le_sum s
        (fun Y => 2 * count c0 Y) x0 (by
          intro Y hY
          exact (Finset.mem_filter.mp hY).2))
  have hsum :
      (∑ Y ∈ s, count c0 Y) ≤ n := by
    calc
      (∑ Y ∈ s, count c0 Y) ≤
          ∑ Y ∈ (Finset.univ : Finset (Species m)), count c0 Y :=
        Finset.sum_le_sum_of_subset (by
          intro Y hY
          exact Finset.mem_univ Y)
      _ = n := sum_count c0
  dsimp only [s] at hlower ⊢
  calc
    _ ≤ ∑ Y ∈
        (Finset.univ.erase X).filter
          (fun Y => x0 ≤ 2 * count c0 Y),
        2 * count c0 Y := hlower
    _ = 2 * ∑ Y ∈
        (Finset.univ.erase X).filter
          (fun Y => x0 ≤ 2 * count c0 Y),
        count c0 Y := by
          rw [Finset.mul_sum]
    _ ≤ 2 * n := Nat.mul_le_mul_left 2 hsum

/-- The sum of all fixed-pair envelopes has no naked species factor.  Large
competitors are paid for by population mass; small competitors receive the
extra-gap exponential decay. -/
theorem properPairStateEnvelope_sum_le
    (c0 : Config m n) (X : Species m)
    (D x0 : ℕ) (hx0 : count c0 X = x0)
    (hD4 : 4 ≤ D)
    (h4D : 4 * D ≤ x0) :
    (∑ Y ∈ Finset.univ.erase X,
        properPairStateEnvelope D x0 (pairGapNat c0 X Y)) ≤
      ((2 * n : ℕ) : ℝ≥0∞) / (x0 : ℝ≥0∞) *
          ENNReal.ofReal
            (Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ))))) +
        (m : ℝ≥0∞) *
          ENNReal.ofReal
            (Real.exp
              (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ)) +
                (D : ℝ) / 160))) := by
  classical
  let s : Finset (Species m) := Finset.univ.erase X
  let P : Species m → Prop := fun Y => x0 ≤ 2 * count c0 Y
  let E : ℝ≥0∞ :=
    ENNReal.ofReal
      (Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ)))))
  let F : ℝ≥0∞ :=
    ENNReal.ofReal
      (Real.exp
        (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ)) + (D : ℝ) / 160)))
  have hx0pos : 0 < x0 := by omega
  have hsplit :
      (∑ Y ∈ s,
          properPairStateEnvelope D x0 (pairGapNat c0 X Y)) =
        (∑ Y ∈ s with P Y,
          properPairStateEnvelope D x0 (pairGapNat c0 X Y)) +
        (∑ Y ∈ s with ¬ P Y,
          properPairStateEnvelope D x0 (pairGapNat c0 X Y)) := by
    symm
    exact Finset.sum_filter_add_sum_filter_not s P _
  rw [hsplit]
  have hlarge :
      (∑ Y ∈ s with P Y,
          properPairStateEnvelope D x0 (pairGapNat c0 X Y)) ≤
        ((s.filter P).card : ℝ≥0∞) * E := by
    simpa only [nsmul_eq_mul] using
      (Finset.sum_le_card_nsmul (s.filter P)
        (fun Y => properPairStateEnvelope D x0 (pairGapNat c0 X Y))
        E (by
          intro Y _hY
          exact properPairStateEnvelope_le_base
            D x0 (pairGapNat c0 X Y) hx0pos))
  have hsmall :
      (∑ Y ∈ s with ¬ P Y,
          properPairStateEnvelope D x0 (pairGapNat c0 X Y)) ≤
        ((s.filter (fun Y => ¬ P Y)).card : ℝ≥0∞) * F := by
    simpa only [nsmul_eq_mul] using
      (Finset.sum_le_card_nsmul (s.filter fun Y => ¬ P Y)
        (fun Y => properPairStateEnvelope D x0 (pairGapNat c0 X Y))
        F (by
          intro Y hY
          exact properPairStateEnvelope_le_far
            c0 X Y D x0 hx0 hD4 h4D
              (Finset.mem_filter.mp hY).2))
  have hcardLargeNat :
      (s.filter P).card * x0 ≤ 2 * n := by
    simpa only [s, P] using largeCompetitor_card_mul_le c0 X x0
  have hcardLarge :
      ((s.filter P).card : ℝ≥0∞) ≤
        ((2 * n : ℕ) : ℝ≥0∞) / (x0 : ℝ≥0∞) := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (by exact_mod_cast (Nat.ne_of_gt hx0pos)))
      (Or.inl (ENNReal.natCast_ne_top x0))).2
    exact_mod_cast hcardLargeNat
  have hcardSmall :
      ((s.filter (fun Y => ¬ P Y)).card : ℝ≥0∞) ≤ (m : ℝ≥0∞) := by
    have hcardSmallNat :
        (s.filter (fun Y => ¬ P Y)).card ≤ m := by
      calc
        (s.filter (fun Y => ¬ P Y)).card ≤ s.card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ ≤ (Finset.univ : Finset (Species m)).card :=
          Finset.card_le_card (Finset.erase_subset X _)
        _ = m := Finset.card_fin m
    exact_mod_cast hcardSmallNat
  calc
    (∑ Y ∈ s with P Y,
          properPairStateEnvelope D x0 (pairGapNat c0 X Y)) +
        (∑ Y ∈ s with ¬ P Y,
          properPairStateEnvelope D x0 (pairGapNat c0 X Y)) ≤
      ((s.filter P).card : ℝ≥0∞) * E +
        ((s.filter (fun Y => ¬ P Y)).card : ℝ≥0∞) * F :=
      add_le_add hlarge hsmall
    _ ≤ (((2 * n : ℕ) : ℝ≥0∞) / (x0 : ℝ≥0∞)) * E +
        (m : ℝ≥0∞) * F := by
      exact add_le_add
        (by simpa [mul_comm] using mul_le_mul_right hcardLarge E)
        (by simpa [mul_comm] using mul_le_mul_right hcardSmall F)
    _ = _ := by rfl

/-- A fallback bound used when the plurality count is within a constant
factor of the stage gap. -/
theorem properPairStateEnvelope_sum_le_species
    (c0 : Config m n) (X : Species m)
    (D x0 : ℕ) (hx0 : 0 < x0) :
    (∑ Y ∈ Finset.univ.erase X,
        properPairStateEnvelope D x0 (pairGapNat c0 X Y)) ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ))))) := by
  calc
    (∑ Y ∈ Finset.univ.erase X,
        properPairStateEnvelope D x0 (pairGapNat c0 X Y)) ≤
      (((Finset.univ.erase X).card : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ))))) := by
      simpa only [nsmul_eq_mul] using
        (Finset.sum_le_card_nsmul (Finset.univ.erase X)
          (fun Y => properPairStateEnvelope D x0 (pairGapNat c0 X Y))
          (ENNReal.ofReal
            (Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ))))))
          (by
            intro Y _hY
            exact properPairStateEnvelope_le_base
              D x0 (pairGapNat c0 X Y) hx0))
    _ ≤ (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ))))) := by
      gcongr
      have hcard :
          (Finset.univ.erase X).card ≤ m := by
        calc
          (Finset.univ.erase X).card ≤
              (Finset.univ : Finset (Species m)).card :=
            Finset.card_le_card (Finset.erase_subset X _)
          _ = m := Finset.card_fin m
      exact_mod_cast hcard

/-! ## Uniform asymptotic absorption -/

/-- Denominator of the unconditional one-proper-stage headline exponent. -/
def properStageHeadlineDenominator : ℕ := 663552

/-- A fixed threshold above which all elementary coefficient absorptions used
below hold. -/
def properStageHeadlineThreshold : ℕ := 2000000

/-- The paper assumptions imply that the stage gap dominates the confidence
scale and that the species coefficient is at most a square of their ratio. -/
theorem stage_gap_species_relations
    (m n g Δ D : ℕ)
    (hn : 0 < n)
    (hm : m * g ≤ n)
    (hscale : g * n ≤ Δ ^ 2)
    (hΔD : Δ ≤ D) (hDn : D ≤ n) :
    g ≤ D ∧ m * g ^ 2 ≤ D ^ 2 := by
  have hΔsqD : Δ ^ 2 ≤ D ^ 2 :=
    Nat.pow_le_pow_left hΔD 2
  have hDsqDn : D ^ 2 ≤ D * n := by
    rw [pow_two]
    exact Nat.mul_le_mul_left D hDn
  have hgn : g * n ≤ D * n :=
    hscale.trans (hΔsqD.trans hDsqDn)
  have hgD : g ≤ D :=
    Nat.le_of_mul_le_mul_right hgn hn
  have hmScaled : m * g * g ≤ n * g :=
    Nat.mul_le_mul_right g hm
  have hng : n * g ≤ D ^ 2 := by
    simpa [mul_comm] using hscale.trans hΔsqD
  constructor
  · exact hgD
  · calc
      m * g ^ 2 = m * g * g := by ring
      _ ≤ n * g := hmScaled
      _ ≤ D ^ 2 := hng

/-- A quadratic bound on `m` is absorbed by any sufficiently slow
gap-exponential. -/
theorem two_species_le_exp_gap
    (m g D Q : ℕ)
    (hg : 0 < g) (hQ : 0 < Q) (hgD : g ≤ D)
    (hm : m * g ^ 2 ≤ D ^ 2)
    (hlarge : 3 * Q ≤ g) :
    (2 * m : ℕ) ≤ Real.exp ((D : ℝ) / (Q : ℝ)) := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  let r : ℝ := (D : ℝ) / (g : ℝ)
  have hr1 : (1 : ℝ) ≤ r := by
    dsimp only [r]
    rw [le_div_iff₀ hgR]
    have hgDR : (g : ℝ) ≤ D := by exact_mod_cast hgD
    linarith
  have hmR : (m : ℝ) ≤ r ^ 2 := by
    have hmCast :
        (m : ℝ) * (g : ℝ) ^ 2 ≤ (D : ℝ) ^ 2 := by
      exact_mod_cast hm
    dsimp only [r]
    rw [div_pow]
    rw [le_div_iff₀ (sq_pos_of_pos hgR)]
    simpa [mul_comm] using hmCast
  have htwo : (2 : ℝ) < Real.exp r := by
    exact Real.exp_one_gt_two.trans_le
      (Real.exp_le_exp.mpr hr1)
  have hrExp : r ≤ Real.exp r := by
    exact le_trans (le_add_of_nonneg_right (by norm_num))
      (Real.add_one_le_exp r)
  have hcoeff :
      (2 : ℝ) * (m : ℝ) ≤ Real.exp (3 * r) := by
    calc
      (2 : ℝ) * (m : ℝ) ≤ Real.exp r * r ^ 2 :=
        mul_le_mul htwo.le hmR (by positivity) (by positivity)
      _ ≤ Real.exp r * (Real.exp r) ^ 2 := by
        gcongr
      _ = Real.exp (3 * r) := by
        rw [pow_two, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have hrate : 3 * r ≤ (D : ℝ) / (Q : ℝ) := by
    have hlargeR : (3 : ℝ) * Q ≤ g := by exact_mod_cast hlarge
    dsimp only [r]
    rw [show (3 : ℝ) * ((D : ℝ) / g) =
        ((3 : ℝ) * D) / g by ring]
    rw [div_le_div_iff₀ hgR hQR]
    have hD0 : (0 : ℝ) ≤ D := by positivity
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_right hlargeR hD0
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  exact hcoeff.trans (Real.exp_le_exp.mpr hrate)

/-- Four copies of a scale ratio are absorbed by half of the common
Gaussian exponent. -/
theorem four_ratio_mul_exp_le
    (n g D x0 : ℕ)
    (hx0 : 0 < x0) (hx0n : x0 ≤ n)
    (hscale : g * n ≤ D ^ 2)
    (hlarge : 6 * 82944 ≤ g) :
    (4 * (n : ℝ) / (x0 : ℝ)) *
        Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ)))) ≤
      Real.exp (-((g : ℝ) / properStageHeadlineDenominator)) := by
  let r : ℝ := (n : ℝ) / (x0 : ℝ)
  have hx0R : (0 : ℝ) < x0 := by exact_mod_cast hx0
  have hr1 : (1 : ℝ) ≤ r := by
    dsimp only [r]
    rw [le_div_iff₀ hx0R]
    have hx0nR : (x0 : ℝ) ≤ n := by exact_mod_cast hx0n
    linarith
  have hscaleR :
      (g : ℝ) * (n : ℝ) ≤ (D : ℝ) ^ 2 := by
    exact_mod_cast hscale
  have hlargeR : (6 : ℝ) * 82944 ≤ g := by
    exact_mod_cast hlarge
  have hfour : (4 : ℝ) < Real.exp 2 := by
    calc
      (4 : ℝ) = 2 * 2 := by norm_num
      _ < Real.exp 1 * Real.exp 1 :=
        mul_lt_mul Real.exp_one_gt_two Real.exp_one_gt_two.le
          (by norm_num) (by positivity)
      _ = Real.exp 2 := by
        rw [← Real.exp_add]
        norm_num
  have hrExp : r ≤ Real.exp r := by
    exact le_trans (le_add_of_nonneg_right (by norm_num))
      (Real.add_one_le_exp r)
  have hcoeff :
      4 * r ≤ Real.exp (3 * r) := by
    calc
      4 * r ≤ Real.exp 2 * Real.exp r :=
        mul_le_mul hfour.le hrExp (by positivity) (by positivity)
      _ = Real.exp (2 + r) := by
        rw [← Real.exp_add]
      _ ≤ Real.exp (3 * r) := by
        apply Real.exp_le_exp.mpr
        linarith
  have hgauss :
      (g : ℝ) * r / 82944 ≤
        (D : ℝ) ^ 2 / (82944 * (x0 : ℝ)) := by
    dsimp only [r]
    calc
      (g : ℝ) * ((n : ℝ) / x0) / 82944 =
          ((g : ℝ) * n) / (82944 * x0) := by
        field_simp
      _ ≤ (D : ℝ) ^ 2 / (82944 * x0) :=
        div_le_div_of_nonneg_right hscaleR (by positivity)
  have hthree :
      3 * r ≤ (g : ℝ) * r / (2 * 82944) := by
    have hr0 : (0 : ℝ) ≤ r := by positivity
    nlinarith
  have htarget :
      (g : ℝ) / properStageHeadlineDenominator ≤
        (g : ℝ) * r / (2 * 82944) := by
    unfold properStageHeadlineDenominator
    have hg0 : (0 : ℝ) ≤ g := by positivity
    nlinarith
  calc
    (4 * (n : ℝ) / (x0 : ℝ)) *
          Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ)))) =
        (4 * r) *
          Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ)))) := by
      dsimp only [r]
      ring
    _ ≤ Real.exp (3 * r) *
          Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ)))) :=
      mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg _)
    _ ≤ Real.exp (3 * r) *
          Real.exp (-((g : ℝ) * r / 82944)) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.exp_le_exp.mpr (neg_le_neg hgauss)
      · positivity
    _ = Real.exp (3 * r - (g : ℝ) * r / 82944) := by
      rw [← Real.exp_add]
      congr 1
    _ ≤ Real.exp (-((g : ℝ) / properStageHeadlineDenominator)) := by
      apply Real.exp_le_exp.mpr
      linarith

/-! ## ENNReal normalization and the final stage bound -/

/-- Rewrite a finite `ENNReal` coefficient times an `ofReal` factor as one
`ofReal`. -/
theorem natCast_mul_ofReal_eq_of_nonneg
    (a : ℕ) (x : ℝ) :
    (a : ℝ≥0∞) * ENNReal.ofReal x =
      ENNReal.ofReal ((a : ℝ) * x) := by
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul]
  positivity

/-- Rewrite a finite natural ratio times an `ofReal` factor as one
`ofReal`. -/
theorem natCast_div_mul_ofReal_eq_of_nonneg
    (a b : ℕ) (hb : 0 < b) (x : ℝ) :
    (a : ℝ≥0∞) / (b : ℝ≥0∞) * ENNReal.ofReal x =
      ENNReal.ofReal (((a : ℝ) / (b : ℝ)) * x) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [← ENNReal.ofReal_natCast a, ← ENNReal.ofReal_natCast b,
    ← ENNReal.ofReal_div_of_pos hbR, ← ENNReal.ofReal_mul]
  positivity

/-- The exact state-dependent error of every proper substage has the paper's
single-exponential shape throughout the full printed species range. -/
theorem productiveProperStageStateError_le_headline
    (m n g Δ D x0 : ℕ) (X : Species m)
    (c0 : Config m n)
    (hn : 0 < n)
    (hgLarge : properStageHeadlineThreshold ≤ g)
    (hΔ4 : 4 ≤ Δ)
    (hm : m * g ≤ n)
    (hscale : g * n ≤ Δ ^ 2)
    (hΔD : Δ ≤ D) (hDx0 : D ≤ x0)
    (hx0 : count c0 X = x0)
    (hinit : HasPairwiseGap c0 X D) :
    productiveProperStageStateError X D x0 c0 ≤
      (3 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((g : ℝ) / properStageHeadlineDenominator))) := by
  have hg : 0 < g := by
    unfold properStageHeadlineThreshold at hgLarge
    omega
  have hD4 : 4 ≤ D := hΔ4.trans hΔD
  have hx0n : x0 ≤ n := by
    rw [← hx0]
    have htotal := count_add_zSum c0 X
    omega
  have hDn : D ≤ n := hDx0.trans hx0n
  obtain ⟨hgD, hmSq⟩ :=
    stage_gap_species_relations m n g Δ D hn hm hscale hΔD hDn
  let p : ℝ≥0∞ :=
    ENNReal.ofReal
      (Real.exp (-((g : ℝ) / properStageHeadlineDenominator)))
  let E : ℝ :=
    Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ))))
  let F : ℝ :=
    Real.exp
      (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ)) + (D : ℝ) / 160))
  have hx0pos : 0 < x0 := by omega
  have hx0R : (0 : ℝ) < x0 := by exact_mod_cast hx0pos
  have hscaleD : g * n ≤ D ^ 2 :=
    hscale.trans (Nat.pow_le_pow_left hΔD 2)
  have hclock : ENNReal.ofReal (Real.exp (-(x0 : ℝ) / 8)) ≤ p := by
    dsimp only [p]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    unfold properStageHeadlineDenominator
    have hgDR : (g : ℝ) ≤ D := by exact_mod_cast hgD
    have hDx0R : (D : ℝ) ≤ x0 := by exact_mod_cast hDx0
    nlinarith
  have hstate :=
    productiveProperStageStateError_le_pair_envelopes
      X D x0 hD4 hDx0 c0 hinit
  by_cases hwide : 4 * D ≤ x0
  · have hsum :=
      properPairStateEnvelope_sum_le
        c0 X D x0 hx0 hD4 hwide
    have hAReal :=
      four_ratio_mul_exp_le n g D x0 hx0pos hx0n hscaleD
        (by
          unfold properStageHeadlineThreshold at hgLarge
          omega)
    have hA :
        (2 : ℝ≥0∞) *
            ((((2 * n : ℕ) : ℝ≥0∞) / (x0 : ℝ≥0∞)) *
              ENNReal.ofReal E) ≤ p := by
      have hA' := ENNReal.ofReal_le_ofReal hAReal
      dsimp only [E, p]
      rw [natCast_div_mul_ofReal_eq_of_nonneg
        (2 * n) x0 hx0pos _]
      rw [← ENNReal.ofReal_ofNat,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      convert hA' using 1
      push_cast
      ring_nf
    have hmExp :
        ((2 * m : ℕ) : ℝ) ≤ Real.exp ((D : ℝ) / 320) := by
      exact two_species_le_exp_gap m g D 320 hg (by norm_num)
        hgD hmSq (by
          unfold properStageHeadlineThreshold at hgLarge
          omega)
    have hbaseRate :
        (g : ℝ) / 82944 ≤
          (D : ℝ) ^ 2 / (82944 * (x0 : ℝ)) := by
      have hscaleR :
          (g : ℝ) * (n : ℝ) ≤ (D : ℝ) ^ 2 := by
        exact_mod_cast hscaleD
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 82944)
        (by positivity : (0 : ℝ) < 82944 * x0)]
      have hx0nR : (x0 : ℝ) ≤ n := by exact_mod_cast hx0n
      nlinarith
    have hBReal :
        ((2 * m : ℕ) : ℝ) * F ≤
          Real.exp (-((g : ℝ) / properStageHeadlineDenominator)) := by
      calc
        ((2 * m : ℕ) : ℝ) * F ≤
            Real.exp ((D : ℝ) / 320) *
              Real.exp
                (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ)) +
                  (D : ℝ) / 160)) :=
          mul_le_mul_of_nonneg_right hmExp (Real.exp_nonneg _)
        _ = Real.exp
            (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ)) +
              (D : ℝ) / 320)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ Real.exp (-((g : ℝ) /
              properStageHeadlineDenominator)) := by
          apply Real.exp_le_exp.mpr
          have htargetRate :
              (g : ℝ) / properStageHeadlineDenominator ≤
                (D : ℝ) ^ 2 / (82944 * (x0 : ℝ)) := by
            calc
              (g : ℝ) / properStageHeadlineDenominator ≤
                  (g : ℝ) / 82944 := by
                apply div_le_div_of_nonneg_left
                · positivity
                · norm_num
                · norm_num [properStageHeadlineDenominator]
              _ ≤ (D : ℝ) ^ 2 / (82944 * (x0 : ℝ)) :=
                hbaseRate
          exact neg_le_neg <|
            htargetRate.trans (le_add_of_nonneg_right (by positivity))
    have hB :
        (2 : ℝ≥0∞) * ((m : ℝ≥0∞) * ENNReal.ofReal F) ≤ p := by
      have hB' := ENNReal.ofReal_le_ofReal hBReal
      rw [← mul_assoc,
        show (2 : ℝ≥0∞) * (m : ℝ≥0∞) =
          ((2 * m : ℕ) : ℝ≥0∞) by norm_num]
      rw [natCast_mul_ofReal_eq_of_nonneg
        (2 * m) F]
      exact hB'
    have hsum' :
        (∑ Y ∈ Finset.univ.erase X,
            properPairStateEnvelope D x0 (pairGapNat c0 X Y)) ≤
          ((((2 * n : ℕ) : ℝ≥0∞) / (x0 : ℝ≥0∞)) *
              ENNReal.ofReal E) +
            (m : ℝ≥0∞) * ENNReal.ofReal F := by
      simpa only [E, F] using hsum
    calc
      productiveProperStageStateError X D x0 c0 ≤
          2 * (∑ Y ∈ Finset.univ.erase X,
            properPairStateEnvelope D x0 (pairGapNat c0 X Y)) +
          ENNReal.ofReal (Real.exp (-(x0 : ℝ) / 8)) := hstate
      _ ≤ 2 *
          (((((2 * n : ℕ) : ℝ≥0∞) / (x0 : ℝ≥0∞)) *
              ENNReal.ofReal E) +
            (m : ℝ≥0∞) * ENNReal.ofReal F) +
          ENNReal.ofReal (Real.exp (-(x0 : ℝ) / 8)) :=
        add_le_add
          (by simpa [mul_comm] using mul_le_mul_left hsum' 2)
          le_rfl
      _ = (2 *
            ((((2 * n : ℕ) : ℝ≥0∞) / (x0 : ℝ≥0∞)) *
              ENNReal.ofReal E)) +
          (2 * ((m : ℝ≥0∞) * ENNReal.ofReal F)) +
          ENNReal.ofReal (Real.exp (-(x0 : ℝ) / 8)) := by ring
      _ ≤ p + p + p := add_le_add (add_le_add hA hB) hclock
      _ = (3 : ℝ≥0∞) * p := by ring
  · have hnarrow : x0 ≤ 4 * D := by omega
    have hsum :=
      properPairStateEnvelope_sum_le_species c0 X D x0 hx0pos
    have hmExp :
        ((2 * m : ℕ) : ℝ) ≤
          Real.exp ((D : ℝ) / properStageHeadlineDenominator) := by
      exact two_species_le_exp_gap
        m g D properStageHeadlineDenominator hg
        (by unfold properStageHeadlineDenominator; norm_num)
        hgD hmSq (by
          unfold properStageHeadlineThreshold at hgLarge
          unfold properStageHeadlineDenominator
          omega)
    have hrate :
        (2 : ℝ) * (D : ℝ) / properStageHeadlineDenominator ≤
          (D : ℝ) ^ 2 / (82944 * (x0 : ℝ)) := by
      have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
      have hnarrowR : (x0 : ℝ) ≤ 4 * D := by exact_mod_cast hnarrow
      rw [div_le_div_iff₀
        (by
          norm_num [properStageHeadlineDenominator] :
            (0 : ℝ) < properStageHeadlineDenominator)
        (by positivity : (0 : ℝ) < 82944 * x0)]
      norm_num [properStageHeadlineDenominator]
      nlinarith
    have hNReal :
        ((2 * m : ℕ) : ℝ) * E ≤
          Real.exp (-((g : ℝ) / properStageHeadlineDenominator)) := by
      calc
        ((2 * m : ℕ) : ℝ) * E ≤
            Real.exp ((D : ℝ) / properStageHeadlineDenominator) *
              Real.exp
                (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ)))) :=
          mul_le_mul_of_nonneg_right hmExp (Real.exp_nonneg _)
        _ = Real.exp
            ((D : ℝ) / properStageHeadlineDenominator -
              (D : ℝ) ^ 2 / (82944 * (x0 : ℝ))) := by
          rw [← Real.exp_add]
          congr 1
        _ ≤ Real.exp
            (-((D : ℝ) / properStageHeadlineDenominator)) := by
          apply Real.exp_le_exp.mpr
          have hrate' :
              (D : ℝ) / properStageHeadlineDenominator +
                  (D : ℝ) / properStageHeadlineDenominator ≤
                (D : ℝ) ^ 2 / (82944 * (x0 : ℝ)) := by
            calc
              (D : ℝ) / properStageHeadlineDenominator +
                    (D : ℝ) / properStageHeadlineDenominator =
                  (2 : ℝ) * D / properStageHeadlineDenominator := by
                ring
              _ ≤ (D : ℝ) ^ 2 / (82944 * (x0 : ℝ)) := hrate
          calc
            (D : ℝ) / properStageHeadlineDenominator -
                  (D : ℝ) ^ 2 / (82944 * (x0 : ℝ)) ≤
                (D : ℝ) / properStageHeadlineDenominator -
                  ((D : ℝ) / properStageHeadlineDenominator +
                    (D : ℝ) / properStageHeadlineDenominator) :=
              sub_le_sub_left hrate' _
            _ = -((D : ℝ) / properStageHeadlineDenominator) := by
              ring
        _ ≤ Real.exp
            (-((g : ℝ) / properStageHeadlineDenominator)) := by
          apply Real.exp_le_exp.mpr
          have hgDR : (g : ℝ) ≤ D := by exact_mod_cast hgD
          have hden : (0 : ℝ) ≤
              (properStageHeadlineDenominator : ℝ) := by positivity
          exact neg_le_neg
            (div_le_div_of_nonneg_right hgDR hden)
    have hN :
        (2 : ℝ≥0∞) * ((m : ℝ≥0∞) * ENNReal.ofReal E) ≤ p := by
      have hN' := ENNReal.ofReal_le_ofReal hNReal
      rw [← mul_assoc,
        show (2 : ℝ≥0∞) * (m : ℝ≥0∞) =
          ((2 * m : ℕ) : ℝ≥0∞) by norm_num]
      rw [natCast_mul_ofReal_eq_of_nonneg
        (2 * m) E]
      exact hN'
    have hsum' :
        (∑ Y ∈ Finset.univ.erase X,
            properPairStateEnvelope D x0 (pairGapNat c0 X Y)) ≤
          (m : ℝ≥0∞) * ENNReal.ofReal E := by
      simpa only [E] using hsum
    calc
      productiveProperStageStateError X D x0 c0 ≤
          2 * (∑ Y ∈ Finset.univ.erase X,
            properPairStateEnvelope D x0 (pairGapNat c0 X Y)) +
          ENNReal.ofReal (Real.exp (-(x0 : ℝ) / 8)) := hstate
      _ ≤ 2 * ((m : ℝ≥0∞) * ENNReal.ofReal E) +
          ENNReal.ofReal (Real.exp (-(x0 : ℝ) / 8)) :=
        add_le_add
          (by simpa [mul_comm] using mul_le_mul_left hsum' 2)
          le_rfl
      _ ≤ p + p := add_le_add hN hclock
      _ ≤ (3 : ℝ≥0∞) * p := by
        calc
          p + p ≤ p + p + p := le_add_right le_rfl
          _ = (3 : ℝ≥0∞) * p := by ring

end Tri.Multi

#print axioms Tri.Multi.productiveProperStageStateError_le_pair_envelopes
#print axioms Tri.Multi.properPairStateEnvelope_sum_le
#print axioms Tri.Multi.productiveProperStageStateError_le_headline
