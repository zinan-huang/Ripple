/-
  Ripple.LPP.ExampleGamma — Connecting the Euler γ PIVP to the Kurtz framework

  The gamma PIVP (8 variables, degree 3) from Ripple.Number.EulerGamma
  is encoded as a RateSpec whose drift matches the PIVP field. Each
  monomial term in the ODE becomes a reaction (jump direction + rate).

  Variables (indices 0–7): f, g, w, u, v, r, p, q
  ODE:
    f' = w                    (linear)
    g' = -p·q·v               (degree 3)
    w' = -w + u + v            (linear)
    u' = -u + r·v              (degree 2)
    v' = -v                    (linear)
    r' = -r²                   (degree 2)
    p' = p·v                   (degree 2)
    q' = v - q                 (linear)

  Reactions (one per monomial term, 11 total):
    R0:  f += 1       rate = x_w           (f' = +w)
    R1:  g -= 1       rate = x_p·x_q·x_v  (g' = -pqv)
    R2:  w -= 1       rate = x_w           (w' = -w)
    R3:  w += 1       rate = x_u           (w' = +u)
    R4:  w += 1       rate = x_v           (w' = +v)
    R5:  u -= 1       rate = x_u           (u' = -u)
    R6:  u += 1       rate = x_r·x_v       (u' = +rv)
    R7:  v -= 1       rate = x_v           (v' = -v)
    R8:  r -= 1       rate = x_r²          (r' = -r²)
    R9:  p += 1       rate = x_p·x_v       (p' = +pv)
    R10: q += 1       rate = x_v           (q' = +v)
    R11: q -= 1       rate = x_q           (q' = -q)

  Note: R3 and R4 have the same jump direction (w += 1) but different
  rates. They can be kept as separate reactions or merged. We keep them
  separate for clarity.

  Similarly R4 and R10 have different jump directions, even though both
  have rate x_v.
-/

import Ripple.Kurtz.Defs
import Ripple.CTMC.DensityDependentAbsorbing

namespace Ripple.LPP

open Ripple Ripple.Kurtz MeasureTheory Filter Topology

/-! ## The gamma PIVP field (standalone, avoids importing EulerGamma which has Mathlib drift) -/

/-- The vector field for the Euler gamma PIVP (8 variables).
  Matches gammaPIVP.field from Ripple.Number.EulerGamma. -/
noncomputable def gammaField (y : Fin 8 → ℝ) : Fin 8 → ℝ :=
  ![y 2,                          -- f' = w
    -(y 6 * y 7 * y 4),           -- g' = -pqv
    -(y 2) + y 3 + y 4,           -- w' = -w + u + v
    -(y 3) + y 5 * y 4,           -- u' = -u + rv
    -(y 4),                        -- v' = -v
    -(y 5 ^ 2),                    -- r' = -r²
    y 6 * y 4,                    -- p' = pv
    y 4 - y 7]                     -- q' = v - q

/-! ## Jump directions for the gamma PIVP -/

/-- Jump direction: species i gains 1. -/
private def jumpPlus (i : Fin 8) : Fin 8 → ℤ :=
  fun j => if j = i then 1 else 0

/-- Jump direction: species i loses 1. -/
private def jumpMinus (i : Fin 8) : Fin 8 → ℤ :=
  fun j => if j = i then -1 else 0

/-! ## Rate functions -/

/-- Rate for R0: f' = +w. Rate = x_w = x 2. -/
private noncomputable def gammaRate_R0 (x : Fin 8 → ℝ) : ℝ := x 2

/-- Rate for R1: g' = -pqv. Rate = x_p · x_q · x_v = x 6 · x 7 · x 4. -/
private noncomputable def gammaRate_R1 (x : Fin 8 → ℝ) : ℝ := x 6 * x 7 * x 4

/-- Rate for R2: w' = -w. Rate = x_w = x 2. -/
private noncomputable def gammaRate_R2 (x : Fin 8 → ℝ) : ℝ := x 2

/-- Rate for R3: w' = +u. Rate = x_u = x 3. -/
private noncomputable def gammaRate_R3 (x : Fin 8 → ℝ) : ℝ := x 3

/-- Rate for R4: w' = +v. Rate = x_v = x 4. -/
private noncomputable def gammaRate_R4 (x : Fin 8 → ℝ) : ℝ := x 4

/-- Rate for R5: u' = -u. Rate = x_u = x 3. -/
private noncomputable def gammaRate_R5 (x : Fin 8 → ℝ) : ℝ := x 3

/-- Rate for R6: u' = +rv. Rate = x_r · x_v = x 5 · x 4. -/
private noncomputable def gammaRate_R6 (x : Fin 8 → ℝ) : ℝ := x 5 * x 4

/-- Rate for R7: v' = -v. Rate = x_v = x 4. -/
private noncomputable def gammaRate_R7 (x : Fin 8 → ℝ) : ℝ := x 4

/-- Rate for R8: r' = -r². Rate = x_r² = (x 5)². -/
private noncomputable def gammaRate_R8 (x : Fin 8 → ℝ) : ℝ := x 5 ^ 2

/-- Rate for R9: p' = +pv. Rate = x_p · x_v = x 6 · x 4. -/
private noncomputable def gammaRate_R9 (x : Fin 8 → ℝ) : ℝ := x 6 * x 4

/-- Rate for R10: q' = +v. Rate = x_v = x 4. -/
private noncomputable def gammaRate_R10 (x : Fin 8 → ℝ) : ℝ := x 4

/-- Rate for R11: q' = -q. Rate = x_q = x 7. -/
private noncomputable def gammaRate_R11 (x : Fin 8 → ℝ) : ℝ := x 7

/-! ## The RateSpec -/

/-- Jump direction for the k-th gamma reaction. -/
private def gammaJump : Fin 11 → (Fin 8 → ℤ)
  | 0 => jumpPlus 0    -- f += 1
  | 1 => jumpMinus 1   -- g -= 1
  | 2 => jumpMinus 2   -- w -= 1
  | 3 => jumpPlus 2    -- w += 1
  | 4 => jumpMinus 3   -- u -= 1
  | 5 => jumpPlus 3    -- u += 1
  | 6 => jumpMinus 4   -- v -= 1
  | 7 => jumpMinus 5   -- r -= 1
  | 8 => jumpPlus 6    -- p += 1
  | 9 => jumpPlus 7    -- q += 1
  | 10 => jumpMinus 7  -- q -= 1

/-- Rate function for the k-th gamma reaction. -/
private noncomputable def gammaRate : Fin 11 → (Fin 8 → ℝ) → ℝ
  | 0, x => x 2                    -- f' = +w
  | 1, x => x 6 * x 7 * x 4       -- g' = -pqv
  | 2, x => x 2                    -- w' = -w
  | 3, x => x 3 + x 4             -- w' = +u + v
  | 4, x => x 3                    -- u' = -u
  | 5, x => x 5 * x 4             -- u' = +rv
  | 6, x => x 4                    -- v' = -v
  | 7, x => x 5 ^ 2               -- r' = -r²
  | 8, x => x 6 * x 4             -- p' = +pv
  | 9, x => x 4                    -- q' = +v
  | 10, x => x 7                   -- q' = -q

/-- The 11 reactions of the gamma PIVP encoded as a RateSpec. -/
noncomputable def gammaRateSpec : RateSpec 8 where
  jumps := Finset.image gammaJump Finset.univ
  rate := fun ℓ x =>
    ∑ k : Fin 11, if gammaJump k = ℓ then gammaRate k x else 0
  rate_nonneg := by
    intro ℓ _hℓ x hx
    apply Finset.sum_nonneg
    intro k _
    split_ifs with h
    · fin_cases k <;> simp only [gammaRate]
      · exact hx 2
      · exact mul_nonneg (mul_nonneg (hx 6) (hx 7)) (hx 4)
      · exact hx 2
      · exact add_nonneg (hx 3) (hx 4)
      · exact hx 3
      · exact mul_nonneg (hx 5) (hx 4)
      · exact hx 4
      · exact sq_nonneg _
      · exact mul_nonneg (hx 6) (hx 4)
      · exact hx 4
      · exact hx 7
    · exact le_refl _
  rate_support := by
    intro ℓ hℓ
    ext x
    simp only [Pi.zero_apply]
    apply Finset.sum_eq_zero
    intro k _
    have : gammaJump k ≠ ℓ := by
      intro h
      exact hℓ (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, h⟩)
    simp [this]
  rate_lipschitz := by
    intro ℓ _hℓ R hR
    refine ⟨11 * (3 * R ^ 2 + 2 * R + 2), by positivity, ?_⟩
    intro x y hx hy
    have hxi : ∀ i, |x i| ≤ R := fun i => (norm_le_pi_norm x i).trans hx
    have hyi : ∀ i, |y i| ≤ R := fun i => (norm_le_pi_norm y i).trans hy
    have hdiff : ∀ i, |x i - y i| ≤ ‖x - y‖ := fun i => by
      have : ‖(x - y) i‖ ≤ ‖x - y‖ := norm_le_pi_norm (x - y) i
      rwa [Pi.sub_apply, Real.norm_eq_abs] at this
    have hδ := norm_nonneg (x - y)
    simp only [Real.norm_eq_abs]
    rw [show (fun x => ∑ k : Fin 11,
        if gammaJump k = ℓ then gammaRate k x else 0) x -
      (fun x => ∑ k : Fin 11,
        if gammaJump k = ℓ then gammaRate k x else 0) y =
      ∑ k : Fin 11, ((if gammaJump k = ℓ then gammaRate k x else 0) -
        (if gammaJump k = ℓ then gammaRate k y else 0)) from by
      simp [Finset.sum_sub_distrib]]
    calc |∑ k : Fin 11, _|
        ≤ ∑ k : Fin 11, |((if gammaJump k = ℓ then gammaRate k x else 0) -
            (if gammaJump k = ℓ then gammaRate k y else 0))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin 11, ((3 * R ^ 2 + 2 * R + 2) * ‖x - y‖) := by
          apply Finset.sum_le_sum
          intro k _
          split_ifs with h
          · fin_cases k <;> simp only [gammaRate]
            -- k=0: |x 2 - y 2| (linear)
            · calc |x 2 - y 2| ≤ ‖x - y‖ := hdiff 2
                _ ≤ (3 * R ^ 2 + 2 * R + 2) * ‖x - y‖ := by nlinarith [sq_nonneg R]
            -- k=1: |x 6 * x 7 * x 4 - y 6 * y 7 * y 4| (trilinear)
            · have h1 : x 6 * x 7 * x 4 - y 6 * y 7 * y 4 =
                  x 6 * x 7 * (x 4 - y 4) + x 6 * (x 7 - y 7) * y 4 +
                  (x 6 - y 6) * y 7 * y 4 := by ring
              calc |x 6 * x 7 * x 4 - y 6 * y 7 * y 4|
                  = |x 6 * x 7 * (x 4 - y 4) + x 6 * (x 7 - y 7) * y 4 +
                      (x 6 - y 6) * y 7 * y 4| := by rw [h1]
                _ ≤ |x 6 * x 7 * (x 4 - y 4)| + |x 6 * (x 7 - y 7) * y 4| +
                      |(x 6 - y 6) * y 7 * y 4| := by
                    calc _ ≤ |x 6 * x 7 * (x 4 - y 4) + x 6 * (x 7 - y 7) * y 4| +
                              |(x 6 - y 6) * y 7 * y 4| := abs_add_le _ _
                       _ ≤ _ := by linarith [abs_add_le (x 6 * x 7 * (x 4 - y 4))
                                     (x 6 * (x 7 - y 7) * y 4)]
                _ ≤ R * R * ‖x - y‖ + R * ‖x - y‖ * R + ‖x - y‖ * R * R := by
                    simp only [abs_mul]
                    have hb1 : |x 6| * |x 7| ≤ R * R :=
                      mul_le_mul (hxi 6) (hxi 7) (abs_nonneg _) (by linarith)
                    have hb2 : |x 6| * |x 7| * |x 4 - y 4| ≤ R * R * ‖x - y‖ :=
                      mul_le_mul hb1 (hdiff 4) (abs_nonneg _) (by positivity)
                    have hb3 : |x 6| * |x 7 - y 7| ≤ R * ‖x - y‖ :=
                      mul_le_mul (hxi 6) (hdiff 7) (abs_nonneg _) (by linarith)
                    have hb4 : |x 6| * |x 7 - y 7| * |y 4| ≤ R * ‖x - y‖ * R :=
                      mul_le_mul hb3 (hyi 4) (abs_nonneg _) (by positivity)
                    have hb5 : |x 6 - y 6| * |y 7| ≤ ‖x - y‖ * R :=
                      mul_le_mul (hdiff 6) (hyi 7) (abs_nonneg _) hδ
                    have hb6 : |x 6 - y 6| * |y 7| * |y 4| ≤ ‖x - y‖ * R * R :=
                      mul_le_mul hb5 (hyi 4) (abs_nonneg _) (by positivity)
                    linarith
                _ = 3 * R ^ 2 * ‖x - y‖ := by ring
                _ ≤ (3 * R ^ 2 + 2 * R + 2) * ‖x - y‖ := by nlinarith [hR]
            -- k=2: |x 2 - y 2| (linear)
            · calc |x 2 - y 2| ≤ ‖x - y‖ := hdiff 2
                _ ≤ (3 * R ^ 2 + 2 * R + 2) * ‖x - y‖ := by nlinarith [sq_nonneg R]
            -- k=3: |(x 3 + x 4) - (y 3 + y 4)| (sum)
            · have h1 : x 3 + x 4 - (y 3 + y 4) = (x 3 - y 3) + (x 4 - y 4) := by ring
              calc |x 3 + x 4 - (y 3 + y 4)|
                  = |(x 3 - y 3) + (x 4 - y 4)| := by rw [h1]
                _ ≤ |x 3 - y 3| + |x 4 - y 4| := abs_add_le _ _
                _ ≤ ‖x - y‖ + ‖x - y‖ := add_le_add (hdiff 3) (hdiff 4)
                _ = 2 * ‖x - y‖ := by ring
                _ ≤ (3 * R ^ 2 + 2 * R + 2) * ‖x - y‖ := by nlinarith [sq_nonneg R, hR]
            -- k=4: |x 3 - y 3| (linear)
            · calc |x 3 - y 3| ≤ ‖x - y‖ := hdiff 3
                _ ≤ (3 * R ^ 2 + 2 * R + 2) * ‖x - y‖ := by nlinarith [sq_nonneg R]
            -- k=5: |x 5 * x 4 - y 5 * y 4| (bilinear)
            · have h1 : x 5 * x 4 - y 5 * y 4 =
                  x 5 * (x 4 - y 4) + (x 5 - y 5) * y 4 := by ring
              calc |x 5 * x 4 - y 5 * y 4|
                  = |x 5 * (x 4 - y 4) + (x 5 - y 5) * y 4| := by rw [h1]
                _ ≤ |x 5 * (x 4 - y 4)| + |(x 5 - y 5) * y 4| := abs_add_le _ _
                _ ≤ R * ‖x - y‖ + ‖x - y‖ * R := by
                    simp only [abs_mul]
                    nlinarith [hxi 5, hyi 4, hdiff 4, hdiff 5, abs_nonneg (x 5),
                      abs_nonneg (y 4), abs_nonneg (x 4 - y 4), abs_nonneg (x 5 - y 5)]
                _ = 2 * R * ‖x - y‖ := by ring
                _ ≤ (3 * R ^ 2 + 2 * R + 2) * ‖x - y‖ := by nlinarith [sq_nonneg R]
            -- k=6: |x 4 - y 4| (linear)
            · calc |x 4 - y 4| ≤ ‖x - y‖ := hdiff 4
                _ ≤ (3 * R ^ 2 + 2 * R + 2) * ‖x - y‖ := by nlinarith [sq_nonneg R]
            -- k=7: |x 5 ^ 2 - y 5 ^ 2| (quadratic)
            · have h1 : x 5 ^ 2 - y 5 ^ 2 = (x 5 + y 5) * (x 5 - y 5) := by ring
              calc |x 5 ^ 2 - y 5 ^ 2|
                  = |(x 5 + y 5) * (x 5 - y 5)| := by rw [h1]
                _ = |x 5 + y 5| * |x 5 - y 5| := abs_mul _ _
                _ ≤ (|x 5| + |y 5|) * ‖x - y‖ := by
                    nlinarith [abs_add_le (x 5) (y 5), hdiff 5, abs_nonneg (x 5 + y 5)]
                _ ≤ (R + R) * ‖x - y‖ := by nlinarith [hxi 5, hyi 5]
                _ = 2 * R * ‖x - y‖ := by ring
                _ ≤ (3 * R ^ 2 + 2 * R + 2) * ‖x - y‖ := by nlinarith [sq_nonneg R]
            -- k=8: |x 6 * x 4 - y 6 * y 4| (bilinear)
            · have h1 : x 6 * x 4 - y 6 * y 4 =
                  x 6 * (x 4 - y 4) + (x 6 - y 6) * y 4 := by ring
              calc |x 6 * x 4 - y 6 * y 4|
                  = |x 6 * (x 4 - y 4) + (x 6 - y 6) * y 4| := by rw [h1]
                _ ≤ |x 6 * (x 4 - y 4)| + |(x 6 - y 6) * y 4| := abs_add_le _ _
                _ ≤ R * ‖x - y‖ + ‖x - y‖ * R := by
                    simp only [abs_mul]
                    nlinarith [hxi 6, hyi 4, hdiff 4, hdiff 6, abs_nonneg (x 6),
                      abs_nonneg (y 4), abs_nonneg (x 4 - y 4), abs_nonneg (x 6 - y 6)]
                _ = 2 * R * ‖x - y‖ := by ring
                _ ≤ (3 * R ^ 2 + 2 * R + 2) * ‖x - y‖ := by nlinarith [sq_nonneg R]
            -- k=9: |x 4 - y 4| (linear)
            · calc |x 4 - y 4| ≤ ‖x - y‖ := hdiff 4
                _ ≤ (3 * R ^ 2 + 2 * R + 2) * ‖x - y‖ := by nlinarith [sq_nonneg R]
            -- k=10: |x 7 - y 7| (linear)
            · calc |x 7 - y 7| ≤ ‖x - y‖ := hdiff 7
                _ ≤ (3 * R ^ 2 + 2 * R + 2) * ‖x - y‖ := by nlinarith [sq_nonneg R]
          · simp; positivity
      _ = 11 * (3 * R ^ 2 + 2 * R + 2) * ‖x - y‖ := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_assoc]

/-! ## Drift equality -/

private theorem gammaJump_injective : Function.Injective gammaJump := by
  decide

private theorem gammaRate_sum_eq (k : Fin 11) (x : Fin 8 → ℝ) :
    (∑ j : Fin 11, if gammaJump j = gammaJump k then gammaRate j x else 0) =
      gammaRate k x := by
  conv_lhs => rw [Finset.sum_eq_single k
    (fun j _ hjk => by simp [show gammaJump j ≠ gammaJump k from
      fun h => hjk (gammaJump_injective h)])
    (fun hk => absurd (Finset.mem_univ k) hk)]
  simp

set_option maxHeartbeats 6400000 in
/-- The drift of gammaRateSpec equals the gamma PIVP field. -/
theorem gammaRateSpec_drift_eq_gammaField :
    gammaRateSpec.drift = gammaField := by
  ext x i
  simp only [RateSpec.drift, gammaRateSpec]
  rw [Finset.sum_image (fun a _ b _ h => gammaJump_injective h)]
  simp_rw [gammaRate_sum_eq]
  fin_cases i <;> (
    simp only [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_zero,
      gammaJump, gammaRate, jumpPlus, jumpMinus, gammaField]
    norm_num
    simp (config := { decide := true }) only [ite_true, ite_false, zero_add, add_zero]
    try ring)

/-! ## Mean-field solution -/

/-- The gamma PIVP solution as closed-form functions.
  Components: f, g, w, u, v, r, p, q.
  v(t) = e^{-t}, r(t) = 1/(1+t), p(t) = e^{1-e^{-t}}, q(t) = te^{-t},
  u(t) = e^{-t}·log(1+t), w(t) = e^{-t}·(1+t)·log(1+t),
  f(t) = ∫₀ᵗ w(s) ds, g(t) = -∫₀ᵗ p(s)·q(s)·e^{-s} ds. -/
noncomputable def gammaSol (t : ℝ) : Fin 8 → ℝ :=
  ![∫ s in (0:ℝ)..t, Real.exp (-s) * (1 + s) * Real.log (1 + s),  -- f
    -(∫ s in (0:ℝ)..t, Real.exp (1 - Real.exp (-s)) * (s * Real.exp (-s)) * Real.exp (-s)),  -- g
    Real.exp (-t) * (1 + t) * Real.log (1 + t),  -- w
    Real.exp (-t) * Real.log (1 + t),             -- u
    Real.exp (-t),                                 -- v
    1 / (1 + t),                                   -- r
    Real.exp (1 - Real.exp (-t)),                  -- p
    t * Real.exp (-t)]                             -- q

private theorem gammaG_continuous :
    Continuous (fun s : ℝ =>
      Real.exp (1 - Real.exp (-s)) * (s * Real.exp (-s)) * Real.exp (-s)) :=
  ((Real.continuous_exp.comp (continuous_const.sub (Real.continuous_exp.comp continuous_neg))).mul
    (continuous_id.mul (Real.continuous_exp.comp continuous_neg))).mul
    (Real.continuous_exp.comp continuous_neg)

set_option maxHeartbeats 1600000 in
/-- The gamma ODE solution satisfies the gammaField ODE.
  Proof requires FTC + chain rule for each component. -/
theorem gammaSol_is_solution (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt gammaSol (gammaField (gammaSol t)) t := by
  have h1t_pos : (0:ℝ) < 1 + t := by linarith
  have h1t_ne : (1:ℝ) + t ≠ 0 := ne_of_gt h1t_pos
  have h_exp_neg : HasDerivAt (fun x => Real.exp (-x)) (Real.exp (-t) * -1) t :=
    ((hasDerivAt_id t).neg).exp
  have h_1t : HasDerivAt (fun x : ℝ => 1 + x) (0 + 1) t :=
    (hasDerivAt_const t 1).add (hasDerivAt_id t)
  have h_log1t : HasDerivAt (fun x => Real.log (1 + x)) ((0 + 1) / (1 + t)) t :=
    h_1t.log h1t_ne
  rw [hasDerivAt_pi]
  intro i; fin_cases i
  · -- f' = w (FTC): d/dt ∫₀ᵗ W(s) ds = W(t)
    have hW_cont : ContinuousAt (fun s => Real.exp (-s) * (1 + s) * Real.log (1 + s)) t :=
      ((Real.continuous_exp.comp continuous_neg).continuousAt.mul
        ((continuous_const.add continuous_id).continuousAt)).mul
        ((continuous_const.add continuous_id).continuousAt.log h1t_ne)
    have hW_meas : StronglyMeasurableAtFilter
        (fun s => Real.exp (-s) * (1 + s) * Real.log (1 + s)) (𝓝 t) :=
      (Measurable.stronglyMeasurable (((Real.continuous_exp.comp continuous_neg).mul
        (continuous_const.add continuous_id)).measurable.mul
        ((continuous_const.add continuous_id).measurable.log))).stronglyMeasurableAtFilter
    have hW_int : IntervalIntegrable (fun s => Real.exp (-s) * (1 + s) * Real.log (1 + s))
        volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      intro s hs
      apply ContinuousAt.continuousWithinAt
      have hs1 : 0 ≤ s := by
        simp only [Set.mem_uIcc] at hs
        cases hs with | inl h => linarith [h.1] | inr h => linarith [h.2]
      exact ((Real.continuous_exp.comp continuous_neg).continuousAt.mul
        ((continuous_const.add continuous_id).continuousAt)).mul
        ((continuous_const.add continuous_id).continuousAt.log
          (ne_of_gt (show (0:ℝ) < 1 + s by linarith)))
    change HasDerivAt (fun u => ∫ s in (0:ℝ)..u,
        Real.exp (-s) * (1 + s) * Real.log (1 + s))
      (Real.exp (-t) * (1 + t) * Real.log (1 + t)) t
    exact intervalIntegral.integral_hasDerivAt_right hW_int hW_meas hW_cont
  · -- g' = -pqv (FTC + neg)
    change HasDerivAt (fun u => -(∫ s in (0:ℝ)..u,
        Real.exp (1 - Real.exp (-s)) * (s * Real.exp (-s)) * Real.exp (-s)))
      (-(Real.exp (1 - Real.exp (-t)) * (t * Real.exp (-t)) * Real.exp (-t))) t
    exact (intervalIntegral.integral_hasDerivAt_right
      (gammaG_continuous.intervalIntegrable 0 t)
      gammaG_continuous.stronglyMeasurable.stronglyMeasurableAtFilter
      gammaG_continuous.continuousAt).neg
  · -- w' = -w + u + v
    change HasDerivAt (fun u => Real.exp (-u) * (1 + u) * Real.log (1 + u))
      (-(Real.exp (-t) * (1 + t) * Real.log (1 + t)) + Real.exp (-t) * Real.log (1 + t) +
        Real.exp (-t)) t
    exact ((h_exp_neg.mul h_1t).mul h_log1t).congr_deriv (by
      field_simp [h1t_ne]; simp only [Pi.mul_apply]; ring)
  · -- u' = -u + rv
    change HasDerivAt (fun u => Real.exp (-u) * Real.log (1 + u))
      (-(Real.exp (-t) * Real.log (1 + t)) + 1 / (1 + t) * Real.exp (-t)) t
    exact (h_exp_neg.mul h_log1t).congr_deriv (by field_simp [h1t_ne]; ring)
  · -- v' = -v
    change HasDerivAt (fun u => Real.exp (-u)) (-Real.exp (-t)) t
    exact h_exp_neg.congr_deriv (by ring)
  · -- r' = -r²
    change HasDerivAt (fun u => 1 / (1 + u)) (-(1 / (1 + t)) ^ 2) t
    exact ((hasDerivAt_const t (1:ℝ)).div h_1t h1t_ne).congr_deriv (by field_simp [h1t_ne]; ring)
  · -- p' = pv
    change HasDerivAt (fun u => Real.exp (1 - Real.exp (-u)))
      (Real.exp (1 - Real.exp (-t)) * Real.exp (-t)) t
    exact (((hasDerivAt_const t (1:ℝ)).sub h_exp_neg).exp).congr_deriv (by
      dsimp only [Pi.sub_apply, Pi.one_apply, Function.comp]; ring)
  · -- q' = v - q
    change HasDerivAt (fun u => u * Real.exp (-u))
      (Real.exp (-t) - t * Real.exp (-t)) t
    exact ((hasDerivAt_id t).mul h_exp_neg).congr_deriv (by dsimp [id]; ring)

/-- The gamma mean-field solution package. -/
noncomputable def gammaMeanField : MeanFieldSolution 8 gammaRateSpec where
  x₀ := ![0, 0, 0, 0, 1, 1, 1, 0]
  sol := gammaSol
  sol_init := by
    ext i
    fin_cases i <;> simp [gammaSol, Real.exp_zero, Real.log_one,
      intervalIntegral.integral_same]
  sol_ode := by
    intro t ht
    rw [gammaRateSpec_drift_eq_gammaField]
    exact gammaSol_is_solution t ht

/-! ## The Kurtz convergence statement for gamma

The density-dependent CTMC with gammaRateSpec converges to the gamma ODE
in the mean-field limit. Combined with the PIVP → γ result from
EulerGamma.lean, this gives: the stochastic system computes γ. -/

/-- The stochastic density-dependent CTMC for the gamma system at population N. -/
noncomputable def gammaCTMC (N : ℕ) (hN : 0 < N) : CTMC.DensityDepCTMC 8 :=
  ⟨N, hN, gammaRateSpec⟩

/-- Superseded by `gammaCompiled_kurtz_convergence` in ExampleGammaCompiled.lean.

The 8-species non-conservative gamma system cannot use the CTMC framework
(which requires ConservativeJumps). The compiled 21-species version
(BD + x_uno) is conservative and has a complete proof: 0 sorry, 0 axiom. -/

end Ripple.LPP
