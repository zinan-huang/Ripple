/-
  Ripple.Kurtz.StrongApprox.ChernoffMaximal — finite-grid block oscillation bounds (W5), (W7) from
  the exponential maximal inequality

  Mathematics: (W5): `P(sup_{s≤h}|Y(s)−s| > z) ≤ 2 exp(−z²/(2(h+z)))`.

  For independent centered increments `R i` whose moment generating functions are dominated by
  those of centered Poisson variables with means `lam i` (`Λ = Σ_{i<q} lam i`):
  * upper tail: `P(∃ k ≤ q, S_k > z) ≤ exp(−z²/(2(Λ+z)))` for `z > 0`, via `θ = log(1 + z/Λ)` and
    the Poisson rate bound `poisH_ge_right`;
  * lower tail: `P(∃ k ≤ q, S_k < −z) ≤ exp(−z²/(2Λ))` for `0 < z < Λ`, via `θ = −log(1 − z/Λ)`
    and `poisH_ge_left`.
  For Gaussian-type increments (`mgf (R i) θ ≤ exp (v i θ²/2)`, `V = Σ v i`):
  `P(∃ k ≤ q, S_k > z) ≤ exp(−z²/(2V))` via `θ = z/V` (the finite-grid form of (W7)).
  These are (W5)/(W7) on finite grids; the passage to a right-continuous (resp. continuous)
  process over a block is the consumer's task.
-/

import Mathlib
import Ripple.Kurtz.StrongApprox.ExponentialMaximal
import Ripple.Kurtz.StrongApprox.PoissonQuantileBound

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Chernoff form of the exponential maximal inequality: if `mgf (R i) θ ≤ exp (c i)` then
`P(∃ k ≤ q, S_k > z) ≤ exp (Σ_{i<q} c i − θ z)`. -/
theorem exp_maximal_le_of_mgf_le [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ}
    (hmeas : ∀ i, Measurable (R i)) (hindep : iIndepFun R P) (hint : ∀ i, Integrable (R i) P)
    (hmean : ∀ i, ∫ ω, R i ω ∂P = 0) {θ : ℝ} (hθ : 0 ≤ θ)
    (hexp : ∀ i, Integrable (fun ω => Real.exp (θ * R i ω)) P) {c : ℕ → ℝ}
    (hmgf : ∀ i, mgf (R i) P θ ≤ Real.exp (c i)) (z : ℝ) (q : ℕ) :
    (P {ω | ∃ k ≤ q, z < partialSum R k ω}).toReal ≤ Real.exp (∑ i ∈ range q, c i - θ * z) := by
  have h1 := exp_maximal hmeas hindep hint hmean hθ hexp z q
  rw [mgf_partialSum hmeas hindep] at h1
  have h2 : ∏ i ∈ range q, mgf (R i) P θ ≤ ∏ i ∈ range q, Real.exp (c i) :=
    Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => hmgf i)
  rw [← Real.exp_sum] at h2
  have hpos : 0 < Real.exp (θ * z) := Real.exp_pos _
  rw [Real.exp_sub, le_div_iff₀ hpos, mul_comm]
  exact h1.trans h2

/-- **(W5), upper tail, finite grid**: with `mgf (R i) θ ≤ exp (lam i (e^θ − 1 − θ))` at
`θ = log(1 + z/Λ)`, `P(∃ k ≤ q, S_k > z) ≤ exp(−z²/(2(Λ + z)))`. -/
theorem poisson_chernoff_maximal_upper [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ}
    (hmeas : ∀ i, Measurable (R i)) (hindep : iIndepFun R P) (hint : ∀ i, Integrable (R i) P)
    (hmean : ∀ i, ∫ ω, R i ω ∂P = 0) {lam : ℕ → ℝ} {q : ℕ} (hΛ : 0 < ∑ i ∈ range q, lam i)
    {z : ℝ} (hz : 0 < z)
    (hexp : ∀ i, Integrable
      (fun ω => Real.exp (Real.log (1 + z / ∑ i ∈ range q, lam i) * R i ω)) P)
    (hmgf : ∀ i, mgf (R i) P (Real.log (1 + z / ∑ i ∈ range q, lam i)) ≤
      Real.exp (lam i * (Real.exp (Real.log (1 + z / ∑ i ∈ range q, lam i)) - 1 -
        Real.log (1 + z / ∑ i ∈ range q, lam i)))) :
    (P {ω | ∃ k ≤ q, z < partialSum R k ω}).toReal ≤
      Real.exp (-(z ^ 2 / (2 * (∑ i ∈ range q, lam i + z)))) := by
  set Λ : ℝ := ∑ i ∈ range q, lam i with hΛ_def
  set t : ℝ := 1 + z / Λ with ht_def
  have hzΛ : 0 ≤ z / Λ := by positivity
  have ht1 : 1 ≤ t := by rw [ht_def]; linarith
  have htpos : 0 < t := by linarith
  have hθ : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hexpt : Real.exp (Real.log t) = t := Real.exp_log htpos
  have hΛt : Λ * t = Λ + z := by rw [ht_def]; field_simp; try ring
  have hΛt1 : Λ * (t - 1) = z := by rw [ht_def]; field_simp; try ring
  have h := exp_maximal_le_of_mgf_le hmeas hindep hint hmean hθ hexp
    (c := fun i => lam i * (Real.exp (Real.log t) - 1 - Real.log t)) hmgf z q
  refine h.trans (Real.exp_le_exp.mpr ?_)
  rw [← Finset.sum_mul, hexpt]
  have hpH := poisH_ge_right ht1
  unfold poisH at hpH
  have hkey : z ^ 2 / (2 * (Λ + z)) = Λ * ((t - 1) ^ 2 / (2 * t)) := by
    rw [ht_def]; field_simp; try ring
  have hlog : Λ * t * Real.log t = (Λ + z) * Real.log t := by rw [hΛt]
  have hmul := mul_le_mul_of_nonneg_left hpH hΛ.le
  rw [hkey]
  nlinarith [hmul, hlog, hΛt, hΛt1]

theorem partialSum_neg (R : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    partialSum (fun i ω => -R i ω) k ω = -partialSum R k ω := by
  unfold partialSum; rw [Finset.sum_neg_distrib]

/-- **(W5), lower tail, finite grid**: with `mgf (−R i) θ ≤ exp (lam i (e^{−θ} − 1 + θ))` at
`θ = −log(1 − z/Λ)`, `0 < z < Λ`: `P(∃ k ≤ q, S_k < −z) ≤ exp(−z²/(2Λ))`. -/
theorem poisson_chernoff_maximal_lower [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ}
    (hmeas : ∀ i, Measurable (R i)) (hindep : iIndepFun R P) (hint : ∀ i, Integrable (R i) P)
    (hmean : ∀ i, ∫ ω, R i ω ∂P = 0) {lam : ℕ → ℝ} {q : ℕ} {z : ℝ} (hz : 0 < z)
    (hzΛ : z < ∑ i ∈ range q, lam i)
    (hexp : ∀ i, Integrable
      (fun ω => Real.exp (-Real.log (1 - z / ∑ i ∈ range q, lam i) * -R i ω)) P)
    (hmgf : ∀ i, mgf (fun ω => -R i ω) P (-Real.log (1 - z / ∑ i ∈ range q, lam i)) ≤
      Real.exp (lam i * (Real.exp (-(-Real.log (1 - z / ∑ i ∈ range q, lam i))) - 1 +
        -Real.log (1 - z / ∑ i ∈ range q, lam i)))) :
    (P {ω | ∃ k ≤ q, partialSum R k ω < -z}).toReal ≤
      Real.exp (-(z ^ 2 / (2 * ∑ i ∈ range q, lam i))) := by
  set Λ : ℝ := ∑ i ∈ range q, lam i with hΛ_def
  have hΛ : 0 < Λ := hz.trans hzΛ
  set t : ℝ := 1 - z / Λ with ht_def
  have hzΛ' : 0 ≤ z / Λ := by positivity
  have ht1 : t ≤ 1 := by rw [ht_def]; linarith
  have htpos : 0 < t := by rw [ht_def, sub_pos, div_lt_one hΛ]; exact hzΛ
  have hθ : 0 ≤ -Real.log t := by linarith [Real.log_nonpos htpos.le ht1]
  have hexpt : Real.exp (-(-Real.log t)) = t := by rw [neg_neg, Real.exp_log htpos]
  have hΛt : Λ * t = Λ - z := by rw [ht_def]; field_simp; try ring
  have hmeas' : ∀ i, Measurable fun ω => -R i ω := fun i => (hmeas i).neg
  have hindep' : iIndepFun (fun i ω => -R i ω) P := by
    have := hindep.comp (fun _ x => -x) (fun _ => measurable_neg)
    exact this
  have hint' : ∀ i, Integrable (fun ω => -R i ω) P := fun i => (hint i).neg
  have hmean' : ∀ i, ∫ ω, -R i ω ∂P = 0 := fun i => by rw [integral_neg, hmean i, neg_zero]
  have h := exp_maximal_le_of_mgf_le hmeas' hindep' hint' hmean' hθ hexp
    (c := fun i => lam i * (Real.exp (-(-Real.log t)) - 1 + -Real.log t)) hmgf z q
  have hset : {ω | ∃ k ≤ q, z < partialSum (fun i ω => -R i ω) k ω} =
      {ω | ∃ k ≤ q, partialSum R k ω < -z} := by
    ext ω; simp only [mem_setOf_eq, partialSum_neg]
    constructor
    · rintro ⟨k, hk, h⟩; exact ⟨k, hk, by linarith⟩
    · rintro ⟨k, hk, h⟩; exact ⟨k, hk, by linarith⟩
  rw [hset] at h
  refine h.trans (Real.exp_le_exp.mpr ?_)
  rw [← Finset.sum_mul, hexpt]
  have hpH := poisH_ge_left htpos.le ht1
  unfold poisH at hpH
  have hkey : z ^ 2 / (2 * Λ) = Λ * ((1 - t) ^ 2 / 2) := by
    rw [ht_def]; field_simp; try ring
  have hlog : Λ * t * Real.log t = (Λ - z) * Real.log t := by rw [hΛt]
  have hmul := mul_le_mul_of_nonneg_left hpH hΛ.le
  rw [hkey]
  nlinarith [hmul, hlog, hΛt]

/-- **(W7), finite grid**: with `mgf (R i) θ ≤ exp (v i θ²/2)` at `θ = z/V`, `V = Σ_{i<q} v i > 0`:
`P(∃ k ≤ q, S_k > z) ≤ exp(−z²/(2V))`. -/
theorem gaussian_chernoff_maximal [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ}
    (hmeas : ∀ i, Measurable (R i)) (hindep : iIndepFun R P) (hint : ∀ i, Integrable (R i) P)
    (hmean : ∀ i, ∫ ω, R i ω ∂P = 0) {v : ℕ → ℝ} {q : ℕ} (hV : 0 < ∑ i ∈ range q, v i)
    {z : ℝ} (hz : 0 ≤ z)
    (hexp : ∀ i, Integrable (fun ω => Real.exp (z / (∑ i ∈ range q, v i) * R i ω)) P)
    (hmgf : ∀ i, mgf (R i) P (z / ∑ i ∈ range q, v i) ≤
      Real.exp (v i * (z / ∑ i ∈ range q, v i) ^ 2 / 2)) :
    (P {ω | ∃ k ≤ q, z < partialSum R k ω}).toReal ≤
      Real.exp (-(z ^ 2 / (2 * ∑ i ∈ range q, v i))) := by
  set V : ℝ := ∑ i ∈ range q, v i with hV_def
  have hθ : 0 ≤ z / V := by positivity
  have h := exp_maximal_le_of_mgf_le hmeas hindep hint hmean hθ hexp
    (c := fun i => v i * (z / V) ^ 2 / 2) hmgf z q
  refine h.trans (Real.exp_le_exp.mpr (le_of_eq ?_))
  have hsum : ∑ i ∈ range q, v i * (z / V) ^ 2 / 2 = V * (z / V) ^ 2 / 2 := by
    rw [← Finset.sum_div, ← Finset.sum_mul]
  rw [hsum]
  have hV' : V ≠ 0 := hV.ne'
  field_simp
  try ring

end Ripple.Kurtz.StrongApprox
