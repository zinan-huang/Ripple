-- Ripple/LPP/NAPExactClock.lean
/-
  Exact exponent for the marked-set compiler (Lemma 16 of the PP-to-NAP paper).

  The clock `u` of a `MarkedCompilation` solves `u' = q (u)` with `q s = ((1 - lam) Σ_J source s)²`.
  If `|q s - q*| ≤ B e^{-κ s}`, then `u t ≥ q* t - C`. The proof uses the monotone quantity
  `u t - q* t - c e^{-κ u t}` on the tail where `q ≥ q*/2`; no time change integral and no
  `θ < 1` loss are needed. This gives the readout rate `exp(-(κ ((1 - lam) ω)²) t)`.
-/

import Ripple.LPP.NAPLayerCopyPipeline

namespace Ripple
namespace NAPTransport
namespace LayerCopy

open Set Filter Topology Finset

/-- **Exact clock lower bound.** If `u' = q (u)`, `u 0 = 0`, `u` is monotone and unbounded, and
`q` converges exponentially to `qs`, then `u t ≥ qs * t - C`. -/
theorem clock_lower_exact {q u : ℝ → ℝ} {qs B κ : ℝ} (hκ : 0 < κ)
    (hq : ∀ s, 0 ≤ s → |q s - qs| ≤ B * Real.exp (-κ * s))
    (hu0 : u 0 = 0) (hu : ∀ t, 0 ≤ t → HasDerivAt u (q (u t)) t)
    (hmono : Monotone u) (htop : Tendsto u atTop atTop) :
    ∃ C, ∀ t, 0 ≤ t → qs * t - C ≤ u t := by
  have hunn : ∀ t, 0 ≤ t → 0 ≤ u t := fun t ht => by
    have := hmono ht
    rwa [hu0] at this
  by_cases hqs : qs ≤ 0
  · refine ⟨0, fun t ht => ?_⟩
    have : qs * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hqs ht
    linarith [hunn t ht]
  have hqs : 0 < qs := not_le.mp hqs
  have hB : 0 ≤ B := by
    have h0 := hq 0 le_rfl
    have : 0 ≤ B * Real.exp (-κ * 0) := le_trans (abs_nonneg _) h0
    simpa using this
  -- tail where `B e^{-κ s} ≤ qs / 2`
  have hdecay : Tendsto (fun s : ℝ => B * Real.exp (-κ * s)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => -κ * s) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by linarith)
    have := (Real.tendsto_exp_atBot.comp h1).const_mul B
    simpa using this
  obtain ⟨S, hS⟩ := eventually_atTop.mp (hdecay.eventually (ge_mem_nhds (half_pos hqs)))
  obtain ⟨t0, ht0S, ht0⟩ :=
    ((htop.eventually_ge_atTop (max S 0)).and (eventually_ge_atTop (0 : ℝ))).exists
  have htail : ∀ t, t0 ≤ t → B * Real.exp (-κ * u t) ≤ qs / 2 := fun t ht =>
    hS _ (le_trans (le_max_left _ _) (le_trans ht0S (hmono ht)))
  have htail0 : ∀ t, t0 ≤ t → 0 ≤ u t := fun t ht => hunn t (le_trans ht0 ht)
  have hqlow : ∀ t, t0 ≤ t → qs / 2 ≤ q (u t) ∧ -(B * Real.exp (-κ * u t)) ≤ q (u t) - qs := by
    intro t ht
    have h := hq (u t) (htail0 t ht)
    have h2 := htail t ht
    have h3 := abs_le.mp h
    constructor <;> linarith [h3.1, h3.2]
  set c : ℝ := 2 * B / (κ * qs) with hc
  have hc0 : 0 ≤ c := by positivity
  let W : ℝ → ℝ := fun t => u t - qs * t - c * Real.exp (-κ * u t)
  have hW : ∀ t, 0 ≤ t →
      HasDerivAt W (q (u t) - qs + c * (κ * (q (u t) * Real.exp (-κ * u t)))) t := by
    intro t ht
    have h1 := hu t ht
    have h2 : HasDerivAt (fun t : ℝ => qs * t) qs t := by
      simpa using (hasDerivAt_id t).const_mul qs
    have h3 : HasDerivAt (fun t : ℝ => Real.exp (-κ * u t))
        (Real.exp (-κ * u t) * (-κ * q (u t))) t := by
      have := (h1.const_mul (-κ)).exp
      simpa using this
    have h4 := (h1.sub h2).sub (h3.const_mul c)
    convert h4 using 1
    ring
  have hWnn : ∀ t, t0 ≤ t → 0 ≤ q (u t) - qs + c * (κ * (q (u t) * Real.exp (-κ * u t))) := by
    intro t ht
    obtain ⟨hl1, hl2⟩ := hqlow t ht
    have hE : 0 ≤ Real.exp (-κ * u t) := (Real.exp_pos _).le
    have hkey : c * (κ * (q (u t) * Real.exp (-κ * u t)))
        = (B * Real.exp (-κ * u t)) * (2 * q (u t) / qs) := by
      rw [hc]; field_simp
    have hratio : 1 ≤ 2 * q (u t) / qs := by
      rw [le_div_iff₀ hqs]; linarith
    have hBE : 0 ≤ B * Real.exp (-κ * u t) := mul_nonneg hB hE
    nlinarith
  have hmonoW : MonotoneOn W (Ici t0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici t0)
    · intro t ht
      exact (hW t (le_trans ht0 ht)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hW t (le_trans ht0 (le_of_lt ht))).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hW t (le_trans ht0 (le_of_lt ht))).deriv]
      exact hWnn t (le_of_lt ht)
  refine ⟨max (-(W t0)) (qs * t0), fun t ht => ?_⟩
  by_cases htt : t0 ≤ t
  · have hle : W t0 ≤ W t := hmonoW (mem_Ici.mpr le_rfl) (mem_Ici.mpr htt) htt
    have hE : 0 ≤ c * Real.exp (-κ * u t) := mul_nonneg hc0 (Real.exp_pos _).le
    have : W t = u t - qs * t - c * Real.exp (-κ * u t) := rfl
    have hm := le_max_left (-(W t0)) (qs * t0)
    linarith
  · have htt : t < t0 := not_le.mp htt
    have hm := le_max_right (-(W t0)) (qs * t0)
    have : qs * t ≤ qs * t0 := mul_le_mul_of_nonneg_left htt.le hqs.le
    linarith [hunn t ht]

/-- **Exact exponent of the marked-set compiler.** Under the exponential bound on the original
marked mass, the compiled marked readout converges at rate `κ ((1 - lam) ω)²`, with no `θ`.
Here `ω` is the limit of the slack mass `Σ_J source`: `ω = ν` when `J = M`, `ω = 1 - ν` when
`J = Mᶜ`; the limit and the exponential bound on the slack mass are derived from `hA`. -/
theorem MarkedCompilation.readout_rate_exact {n : ℕ} {g : QuadPP n} {M J : Finset (Fin n)}
    {b : Bool} {lam : ℚ} {hlam0 : 0 < lam} {x0 : Fin n → ℝ}
    (R : MarkedCompilation n g M J b lam hlam0 x0) {ν A κ ω : ℝ} (hκ : 0 < κ)
    (hωJ : (J = M ∧ ω = ν) ∨ (J = Mᶜ ∧ ω = 1 - ν))
    (hA : ∀ s, 0 ≤ s → |∑ j ∈ M, R.source s j - ν| ≤ A * Real.exp (-κ * s)) :
    ∃ C, ∀ t, 0 ≤ t →
      |∑ p ∈ copyMarkedSet n M b, copiedTrajectory n J lam R.source R.clock t p - ν|
        ≤ C * Real.exp (-(κ * ((1 - (lam : ℝ)) * ω) ^ 2) * t) := by
  classical
  -- exponential bound on the slack mass
  have hslack : ∀ s, 0 ≤ s → |∑ j ∈ J, R.source s j - ω| ≤ A * Real.exp (-κ * s) := by
    intro s hs
    rcases hωJ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hA s hs
    · have hsum := (R.source_simplex s hs).2
      have hcompl : ∑ j ∈ Mᶜ, R.source s j = 1 - ∑ j ∈ M, R.source s j := by
        have := Finset.sum_compl_add_sum M (R.source s)
        linarith
      rw [hcompl]
      have : 1 - ∑ j ∈ M, R.source s j - (1 - ν) = -(∑ j ∈ M, R.source s j - ν) := by ring
      rw [this, abs_neg]
      exact hA s hs
  have hA0 : 0 ≤ A := by
    have h0 := hslack 0 le_rfl
    have : 0 ≤ A * Real.exp (-κ * 0) := le_trans (abs_nonneg _) h0
    simpa using this
  set a : ℝ := 1 - (lam : ℝ) with ha
  set D : ℝ := |a| * A with hD
  have hD0 : 0 ≤ D := mul_nonneg (abs_nonneg _) hA0
  -- exponential bound on `q s = (a Σ_J source s)²`
  have hq : ∀ s, 0 ≤ s →
      |(a * ∑ j ∈ J, R.source s j) ^ 2 - (a * ω) ^ 2|
        ≤ (D * (D + 2 * |a * ω|)) * Real.exp (-κ * s) := by
    intro s hs
    have hE0 : 0 ≤ Real.exp (-κ * s) := (Real.exp_pos _).le
    have hE1 : Real.exp (-κ * s) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith
    have hd : |a * ∑ j ∈ J, R.source s j - a * ω| ≤ D * Real.exp (-κ * s) := by
      rw [← mul_sub, abs_mul, hD, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hslack s hs) (abs_nonneg _)
    set r := a * ∑ j ∈ J, R.source s j
    set rs := a * ω
    have hfac : r ^ 2 - rs ^ 2 = (r - rs) * ((r - rs) + 2 * rs) := by ring
    have hsum : |(r - rs) + 2 * rs| ≤ D + 2 * |rs| := by
      calc |(r - rs) + 2 * rs| ≤ |r - rs| + |2 * rs| := abs_add_le _ _
        _ ≤ D + 2 * |rs| := by
          rw [abs_mul, abs_two]
          have : |r - rs| ≤ D := le_trans hd (by nlinarith)
          linarith
    rw [hfac, abs_mul]
    calc |r - rs| * |(r - rs) + 2 * rs|
        ≤ (D * Real.exp (-κ * s)) * (D + 2 * |rs|) :=
          mul_le_mul hd hsum (abs_nonneg _) (mul_nonneg hD0 hE0)
      _ = (D * (D + 2 * |rs|)) * Real.exp (-κ * s) := by ring
  -- the exact clock bound
  obtain ⟨C0, hC0⟩ := clock_lower_exact (q := fun s => (a * ∑ j ∈ J, R.source s j) ^ 2)
    (u := R.clock) (qs := (a * ω) ^ 2) (B := D * (D + 2 * |a * ω|)) hκ hq R.clock_zero
    (fun t ht => (R.clock_nonneg_deriv t ht).2) R.clock_strictMono.monotone R.clock_tendsto
  refine ⟨A * Real.exp (κ * C0), fun t ht => ?_⟩
  rw [R.readout t ht]
  have hc0 : 0 ≤ R.clock t := (R.clock_nonneg_deriv t ht).1
  have h1 := hA (R.clock t) hc0
  have h2 : Real.exp (-κ * R.clock t) ≤ Real.exp (κ * C0) * Real.exp (-(κ * (a * ω) ^ 2) * t) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := hC0 t ht
    nlinarith
  calc _ ≤ A * Real.exp (-κ * R.clock t) := h1
    _ ≤ A * (Real.exp (κ * C0) * Real.exp (-(κ * (a * ω) ^ 2) * t)) :=
        mul_le_mul_of_nonneg_left h2 hA0
    _ = _ := by ring

/-- **Marked-set PP to marked-set NAP with the exact exponent.** For every simplex initial point
there is an admissible slack set `J` (`M` or `Mᶜ`) with positive initial mass and a compilation
whose marked readout converges at rate `κ ((1 - lam) ω)²` whenever the original marked mass
converges at rate `κ` to `ν`; here `ω` is the limit of the slack mass. -/
theorem pp_to_nap_layer_copy_exact (n : ℕ) (g : QuadPP n)
    (M : Finset (Fin n)) (lam : ℚ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (x0 : Fin n → ℝ) (hx0n : ∀ j, 0 ≤ x0 j) (hx0s : ∑ j, x0 j = 1) :
    ∃ J : Finset (Fin n), ∃ b : Bool, (J = M ∨ J = Mᶜ) ∧ 0 < ∑ j ∈ J, x0 j ∧
      ∃ R : MarkedCompilation n g M J b lam hlam0 x0,
        ∀ ν A κ ω : ℝ, 0 < κ → ((J = M ∧ ω = ν) ∨ (J = Mᶜ ∧ ω = 1 - ν)) →
          (∀ s, 0 ≤ s → |∑ j ∈ M, R.source s j - ν| ≤ A * Real.exp (-κ * s)) →
          ∃ C, ∀ t, 0 ≤ t →
            |∑ p ∈ copyMarkedSet n M b, copiedTrajectory n J lam R.source R.clock t p - ν|
              ≤ C * Real.exp (-(κ * ((1 - (lam : ℝ)) * ω) ^ 2) * t) := by
  obtain ⟨J, b, hJ, hpos, ⟨R⟩⟩ := pp_to_nap_layer_copy_of_init n g M lam hlam0 hlam1 x0 hx0n hx0s
  exact ⟨J, b, hJ, hpos, R, fun ν A κ ω hκ hω hA => R.readout_rate_exact hκ hω hA⟩

end LayerCopy
end NAPTransport
end Ripple
