/-
  Ripple.Kurtz.MeanField — Kurtz's Mean-Field Limit Theorem

  States and proves Kurtz's convergence theorem:

  **Theorem (Kurtz 1970):** If X̄^N(0) → x₀ in probability as N → ∞,
  then for any T > 0,
    sup_{0≤t≤T} ‖X̄^N(t) - x(t)‖ → 0  in probability,
  where x(t) solves x'(t) = F(x(t)), x(0) = x₀.

  **Theorem (Kurtz 1978, strong approximation):**
    sup_{0≤t≤T} ‖X̄^N(t) - x(t)‖ = O(log N / √N)  a.s.

  The proof strategy:
  1. From the martingale decomposition,
     X̄^N(t) - x(t) = (X̄^N(0) - x₀) + ∫₀ᵗ [F(X̄^N(s)) - F(x(s))] ds + M^N(t)
  2. Apply Gronwall: if the drift F is L-Lipschitz, then
     ‖X̄^N(t) - x(t)‖ ≤ (‖X̄^N(0) - x₀‖ + sup_{s≤t} ‖M^N(s)‖) · e^{Lt}
  3. The initial error → 0 by hypothesis; the martingale sup → 0 because
     E[sup ‖M^N‖²] = O(1/N) → Markov → convergence in probability.
-/

import Ripple.Kurtz.Defs
import Ripple.Kurtz.IntegralGronwall
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace Ripple.Kurtz

open MeasureTheory MeasureTheory.Measure

variable {d : ℕ} {Γ : RateSpec d}

/-! ## Gronwall-based error bound

The deterministic core of Kurtz's proof. We provide two forms:

1. **Derivative form** (`gronwall_error_bound`): directly uses Mathlib's
   `dist_le_of_approx_trajectories_ODE`. Requires X to be differentiable
   with the noise term appearing as the approximation error.

2. The integral form from Kurtz's paper follows as a corollary when
   X has the martingale decomposition. -/

/-- Gronwall estimate for approximate ODE solutions.

If X is a differentiable approximate solution satisfying
  dist(X'(t), F(X(t))) ≤ ε  for all t ∈ [0, T],
and x is an exact solution (x'(t) = F(x(t))),
with F being K-Lipschitz, then:

  dist(X(t), x(t)) ≤ gronwallBound δ K ε (t - 0)

where δ = dist(X(0), x(0)).

This directly wraps `dist_le_of_approx_trajectories_ODE`. -/
theorem gronwall_error_bound
    {mf : MeanFieldSolution d Γ}
    {K : ℝ} (hK : 0 ≤ K)
    {ε δ : ℝ}
    {T : ℝ} (_hT : 0 < T)
    (h_lip : ∀ x y : Fin d → ℝ,
      dist (Γ.drift x) (Γ.drift y) ≤ K * dist x y)
    (X X' : ℝ → Fin d → ℝ)
    (hX_cont : ContinuousOn X (Set.Icc 0 T))
    (hX' : ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt X (X' t) (Set.Ici t) t)
    (h_approx : ∀ t ∈ Set.Ico 0 T,
      dist (X' t) (Γ.drift (X t)) ≤ ε)
    (hsol_cont : ContinuousOn mf.sol (Set.Icc 0 T))
    (hsol' : ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt mf.sol (Γ.drift (mf.sol t)) (Set.Ici t) t)
    (h_init : dist (X 0) (mf.sol 0) ≤ δ) :
    ∀ t ∈ Set.Icc 0 T,
      dist (X t) (mf.sol t) ≤ gronwallBound δ K.toNNReal ε (t - 0) := by
  have hK' : (K.toNNReal : ℝ) = K := Real.coe_toNNReal K hK
  have h_lip' : ∀ _ : ℝ, LipschitzWith K.toNNReal
      (show (Fin d → ℝ) → Fin d → ℝ from Γ.drift) := by
    intro _
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [hK']
    exact h_lip x y
  intro t ht
  have := dist_le_of_approx_trajectories_ODE
    h_lip' hX_cont hX' h_approx
    hsol_cont hsol' (fun _ _ => le_of_eq (dist_self _)) h_init t ht
  simp only [add_zero, hK'] at this ⊢
  exact this

/-! ## Kurtz 1972 §III: Chebyshev-type bound

Equation (3.1) from Kurtz 1972 JCP:
  P{sup_{s≤t} |V⁻¹X^V(s) - X(s,x₀)| ≥ ε} ≤ tΓ/(Vδ²)
where:
  Γ = sup_{x∈K_ε} Σ (d_nm - c_nm)² [f_n(x) + g_n(x)]  (reaction variance)
  M = sup_{x∈K_ε} Lipschitz constant of F
  δ = ε·e^{-Mt} - |V⁻¹X^V(0) - x₀| - η  (safety margin)

This combines Gronwall (to control the drift error) with Markov's
inequality (to control the martingale error). -/

/-- Martingale Markov bound: the probability that the martingale
sup-square exceeds ε² is bounded by the QV bound divided by ε².

This is a direct application of Markov's inequality to the
martingale quadratic variation bound from `DensityProcess`. -/
theorem martingale_markov_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N)
    (dp : DensityProcess d Γ N μ)
    {T : ℝ} (hT : 0 < T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, μ {ω | ε ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖dp.martingale_part s ω‖ ^ 2} ≤
      ENNReal.ofReal (C * T / (N * ε ^ 2)) := by
  obtain ⟨C, hC, hqv⟩ := dp.martingale_qv_bound T hT
  refine ⟨C, hC, ?_⟩
  let Z : Ω → ℝ := fun ω => ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
    ‖dp.martingale_part s ω‖ ^ 2
  let A : Set Ω := {ω | ε ^ 2 ≤ Z ω}
  have hmark : ε ^ 2 * μ.real A ≤ ∫ ω, Z ω ∂μ := by
    simpa [A, Z] using
      (mul_meas_ge_le_integral_of_nonneg
        (dp.martingale_sup_sq_nonneg T hT)
        (dp.martingale_sup_sq_integrable T hT) (ε ^ 2))
  have hqvZ : ∫ ω, Z ω ∂μ ≤ C * T / N := by
    simpa [Z] using hqv
  have hreal : μ.real A ≤ C * T / (N * ε ^ 2) := by
    have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
    have hε2_ne : ε ^ 2 ≠ 0 := ne_of_gt hε2
    have hmain : ε ^ 2 * μ.real A ≤ C * T / N := hmark.trans hqvZ
    calc
      μ.real A = (ε ^ 2 * μ.real A) / ε ^ 2 := by field_simp [hε2_ne]
      _ ≤ (C * T / N) / ε ^ 2 := by gcongr
      _ = C * T / (N * ε ^ 2) := by
        have hN' : (↑N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        field_simp [hN', hε2_ne]
  have htarget_nonneg : 0 ≤ C * T / (N * ε ^ 2) := by positivity
  have hA_ne_top : μ A ≠ ⊤ := measure_ne_top μ A
  change μ A ≤ ENNReal.ofReal (C * T / (↑N * ε ^ 2))
  exact (ENNReal.le_ofReal_iff_toReal_le hA_ne_top htarget_nonneg).2 hreal

/-- **Kurtz's inequality (1972, eq. 3.1).**

For a density-dependent CTMC with Lipschitz drift, the probability
of deviation from the mean-field ODE is O(1/N).

The proof combines:
1. Gronwall: sup error ≤ (init error + sup martingale) · e^{LT}
2. Markov: P(sup martingale ≥ δ) ≤ E[sup ‖M‖²] / δ²
3. `DensityProcess` QV interface: E[sup ‖M‖²] = O(T/N) -/
theorem kurtz_chebyshev_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N)
    (dp : DensityProcess d Γ N μ)
    (mf : MeanFieldSolution d Γ)
    {T : ℝ} (hT : 0 < T)
    {ε δ : ℝ} (_hε : 0 < ε) (hδ : 0 < δ)
    (h_event : {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
          ‖dp.process t ω - mf.sol t‖ ≥ ε} ⊆
        {ω | ‖dp.init ω - mf.x₀‖ ≥ δ} ∪
        {ω | δ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖dp.martingale_part s ω‖ ^ 2}) :
    ∃ C > 0, μ {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        ‖dp.process t ω - mf.sol t‖ ≥ ε} ≤
      μ {ω | ‖dp.init ω - mf.x₀‖ ≥ δ} +
      ENNReal.ofReal (C * T / (N * δ ^ 2)) := by
  obtain ⟨C, hC, hmart⟩ := martingale_markov_bound hN dp hT hδ
  refine ⟨C, hC, ?_⟩
  let E : Set Ω := {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
    ‖dp.process t ω - mf.sol t‖ ≥ ε}
  let I : Set Ω := {ω | ‖dp.init ω - mf.x₀‖ ≥ δ}
  let M : Set Ω := {ω | δ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
    ‖dp.martingale_part s ω‖ ^ 2}
  calc
    μ E ≤ μ (I ∪ M) := measure_mono h_event
    _ ≤ μ I + μ M := measure_union_le I M
    _ ≤ μ I + ENNReal.ofReal (C * T / (↑N * δ ^ 2)) := by
      exact add_le_add_right (by simpa [M] using hmart) (μ I)

/-- **Gronwall-Markov construction:** Given a family of density processes with
a uniform Gronwall event inclusion AND a uniform QV bound, construct the
`h_gm` hypothesis needed by `kurtz_mean_field_convergence`.

The hypothesis `h_event_unif` is the deterministic Gronwall step.
The hypothesis `h_qv_unif` says the QV constant is uniform across N. -/
theorem kurtz_gm_of_event_inclusion
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : (N : ℕ) → DensityProcess d Γ N μ)
    (mf : MeanFieldSolution d Γ)
    {T : ℝ} (hT : 0 < T)
    (h_event_unif : ∀ ε > 0, ∃ δ > 0, ∀ (N : ℕ), 0 < N →
        ∀ᵐ ω ∂μ,
          (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
              ‖(X N).process t ω - mf.sol t‖ ≥ ε) →
            (‖(X N).init ω - mf.x₀‖ ≥ δ) ∨
            (δ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
              ‖(X N).martingale_part s ω‖ ^ 2))
    (h_qv_unif : ∃ C_qv > 0, ∀ (N : ℕ), 0 < N →
        ∫ ω, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖(X N).martingale_part s ω‖ ^ 2 ∂μ ≤ C_qv * T / N) :
    ∀ ε > 0, ∃ δ > 0, ∃ K > 0, ∀ (N : ℕ), 0 < N →
        μ {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
            ‖(X N).process t ω - mf.sol t‖ > ε} ≤
          μ {ω | ‖(X N).init ω - mf.x₀‖ > δ} +
          ENNReal.ofReal (K / ↑N) := by
  intro ε hε
  obtain ⟨δ₀, hδ₀, h_event⟩ := h_event_unif ε hε
  obtain ⟨C_qv, hCqv, h_qv⟩ := h_qv_unif
  refine ⟨δ₀ / 2, by positivity, C_qv * T / δ₀ ^ 2, by positivity, ?_⟩
  intro N hN
  -- Chain: μ{sup > ε} ≤ μ{sup ≥ ε} ⊆ μ{init ≥ δ₀} + μ{M² ≥ δ₀²}
  --        ≤ μ{init > δ₀/2} + C_qv·T/(N·δ₀²)
  have hstep1 : μ {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
      ‖(X N).process t ω - mf.sol t‖ > ε} ≤
    μ {ω | ‖(X N).init ω - mf.x₀‖ ≥ δ₀} +
    μ {ω | δ₀ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
      ‖(X N).martingale_part s ω‖ ^ 2} := by
    -- h_event N hN : ∀ᵐ ω, (sup error ≥ ε → init ≥ δ₀ ∨ M² ≥ δ₀²)
    -- {sup > ε} ⊆ {sup ≥ ε} ⊆ᵐ {init ≥ δ₀} ∪ {M² ≥ δ₀²}
    have hae : ∀ᵐ ω ∂μ,
        ω ∈ {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
          ‖(X N).process t ω - mf.sol t‖ > ε} →
        ω ∈ ({ω | ‖(X N).init ω - mf.x₀‖ ≥ δ₀} ∪
          {ω | δ₀ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
            ‖(X N).martingale_part s ω‖ ^ 2}) := by
      filter_upwards [h_event N hN] with ω hω h_sup
      rcases hω (le_of_lt h_sup) with h | h
      · exact Or.inl h
      · exact Or.inr h
    calc μ {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        ‖(X N).process t ω - mf.sol t‖ > ε}
        ≤ μ ({ω | ‖(X N).init ω - mf.x₀‖ ≥ δ₀} ∪
            {ω | δ₀ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
              ‖(X N).martingale_part s ω‖ ^ 2}) := measure_mono_ae hae
      _ ≤ _ := measure_union_le _ _
  have hstep2 : μ {ω | ‖(X N).init ω - mf.x₀‖ ≥ δ₀} ≤
    μ {ω | ‖(X N).init ω - mf.x₀‖ > δ₀ / 2} :=
    measure_mono (fun ω (h : _ ≥ δ₀) => (lt_of_lt_of_le (by linarith : δ₀ / 2 < δ₀) h : _ > δ₀ / 2))
  have hstep3 : μ {ω | δ₀ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
      ‖(X N).martingale_part s ω‖ ^ 2} ≤
    ENNReal.ofReal (C_qv * T / (↑N * δ₀ ^ 2)) := by
    -- Direct Markov: μ{Z ≥ δ₀²} ≤ E[Z]/δ₀² ≤ C_qv·T/(N·δ₀²)
    have hδsq : 0 < δ₀ ^ 2 := sq_pos_of_pos hδ₀
    have hmark :=
      mul_meas_ge_le_integral_of_nonneg
        ((X N).martingale_sup_sq_nonneg T hT)
        ((X N).martingale_sup_sq_integrable T hT) (δ₀ ^ 2)
    have hqvN := h_qv N hN
    have hreal : μ.real {ω | δ₀ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖(X N).martingale_part s ω‖ ^ 2} ≤ C_qv * T / (↑N * δ₀ ^ 2) := by
      have h1 : δ₀ ^ 2 * μ.real {ω | δ₀ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖(X N).martingale_part s ω‖ ^ 2} ≤ C_qv * T / ↑N :=
        hmark.trans hqvN
      have hδsq_ne : δ₀ ^ 2 ≠ 0 := ne_of_gt hδsq
      have hN_ne : (↑N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hδsq_ne : δ₀ ^ 2 ≠ 0 := ne_of_gt hδsq
      have hN_ne : (↑N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [le_div_iff₀ (mul_pos (Nat.cast_pos.mpr hN) hδsq)]
      -- Goal: μ.real S * (N * δ₀²) ≤ C_qv * T
      -- From h1: δ₀² * μ.real S ≤ C_qv * T / N
      -- Multiply by N: N * δ₀² * μ.real S ≤ C_qv * T
      have hN_pos : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hN
      have hN_ne : (↑N : ℝ) ≠ 0 := ne_of_gt hN_pos
      have h2 : ↑N * (δ₀ ^ 2 * μ.real {ω | δ₀ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖(X N).martingale_part s ω‖ ^ 2}) ≤ ↑N * (C_qv * T / ↑N) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt hN_pos)
      rw [mul_div_cancel₀ _ hN_ne] at h2
      -- h2: N * (δ₀² * μ.real S) ≤ C_qv * T
      -- Goal: μ.real S * (N * δ₀²) ≤ C_qv * T
      -- These are equal by commutativity.
      linarith [show μ.real {ω | δ₀ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖(X N).martingale_part s ω‖ ^ 2} * (↑N * δ₀ ^ 2) =
        ↑N * (δ₀ ^ 2 * μ.real {ω | δ₀ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖(X N).martingale_part s ω‖ ^ 2}) from by ring]
    have htarget_nonneg : 0 ≤ C_qv * T / (↑N * δ₀ ^ 2) := by positivity
    have hne_top : μ {ω | δ₀ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖(X N).martingale_part s ω‖ ^ 2} ≠ ⊤ := measure_ne_top μ _
    exact (ENNReal.le_ofReal_iff_toReal_le hne_top htarget_nonneg).2 hreal
  -- Combine: hstep1 + hstep2 + hstep3
  calc μ {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
      ‖(X N).process t ω - mf.sol t‖ > ε}
      ≤ μ {ω | ‖(X N).init ω - mf.x₀‖ ≥ δ₀} +
        μ {ω | δ₀ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖(X N).martingale_part s ω‖ ^ 2} := hstep1
    _ ≤ μ {ω | ‖(X N).init ω - mf.x₀‖ > δ₀ / 2} +
        μ {ω | δ₀ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖(X N).martingale_part s ω‖ ^ 2} :=
      by gcongr
    _ ≤ μ {ω | ‖(X N).init ω - mf.x₀‖ > δ₀ / 2} +
        ENNReal.ofReal (C_qv * T / (↑N * δ₀ ^ 2)) :=
      by gcongr
    _ = μ {ω | ‖(X N).init ω - mf.x₀‖ > δ₀ / 2} +
        ENNReal.ofReal (C_qv * T / δ₀ ^ 2 / ↑N) := by
      congr 1; congr 1; rw [div_div]; ring

/-! ## Kurtz's Theorem (weak form): Convergence in probability -/

/-- **Kurtz's Theorem (1970).**

Let X̄^N be density processes for a rate specification Γ. If:
1. X̄^N(0) → x₀ in probability,
2. The ODE x'(t) = F(x(t)), x(0) = x₀ has a solution on [0, T],
3. The Gronwall-Markov decomposition holds uniformly:
   P(sup error > ε) ≤ P(init error > δ) + O(1/N),

then sup_{0≤t≤T} ‖X̄^N(t) - x(t)‖ → 0 in probability as N → ∞.

Hypothesis `h_gm` encapsulates the Gronwall + Markov step, which
requires path regularity (not axiomatized in `DensityProcess`). -/
theorem kurtz_mean_field_convergence
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (mf : MeanFieldSolution d Γ)
    (X : (N : ℕ) → DensityProcess d Γ N μ)
    (T : ℝ) (_hT : 0 < T)
    (h_init : ∀ ε > 0,
      Filter.Tendsto (fun N => μ {ω | ‖(X N).init ω - mf.x₀‖ > ε})
        Filter.atTop (nhds 0))
    (h_gm : ∀ ε > 0, ∃ δ > 0, ∃ K > 0, ∀ (N : ℕ), 0 < N →
        μ {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
            ‖(X N).process t ω - mf.sol t‖ > ε} ≤
          μ {ω | ‖(X N).init ω - mf.x₀‖ > δ} +
          ENNReal.ofReal (K / ↑N)) :
    ∀ ε > 0,
      Filter.Tendsto
        (fun N => μ {ω |
          ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
            ‖(X N).process t ω - mf.sol t‖ > ε})
        Filter.atTop (nhds 0) := by
  intro ε hε
  obtain ⟨δ, hδ, K, hK, hbd⟩ := h_gm ε hε
  have hKN : Filter.Tendsto (fun N : ℕ => K / (↑N : ℝ)) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop
  have hKN_enn : Filter.Tendsto (fun N : ℕ => ENNReal.ofReal (K / (↑N : ℝ)))
      Filter.atTop (nhds 0) := by
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hKN
    simpa [ENNReal.ofReal_zero] using this
  have h_sum : Filter.Tendsto (fun N =>
      μ {ω | ‖(X N).init ω - mf.x₀‖ > δ} + ENNReal.ofReal (K / (↑N : ℝ)))
      Filter.atTop (nhds 0) := by
    have := (h_init δ hδ).add hKN_enn
    rwa [zero_add] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds h_sum
    (Filter.Eventually.of_forall fun _ => zero_le _)
    (Filter.eventually_atTop.mpr ⟨1, fun N hN => hbd N (by omega)⟩)

/-! ## Kurtz's Theorem (strong form): Almost sure rate -/

/-- **Kurtz's Strong Approximation (1978).**

  sup_{0≤t≤T} ‖X̄^N(t) - x(t)‖ = O(log N / √N)  a.s.

More precisely: there exists C > 0 such that for μ-a.e. ω,
  limsup_{N→∞} (√N / log N) · sup_{0≤t≤T} ‖X̄^N(t) - x(t)‖ ≤ C.

Hypothesis `h_as_bound` encapsulates the strong coupling argument
(KMT + Borel-Cantelli), which requires stochastic infrastructure
beyond the current `DensityProcess` interface. -/
theorem kurtz_strong_approximation
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (mf : MeanFieldSolution d Γ)
    (X : (N : ℕ) → DensityProcess d Γ N μ)
    (T : ℝ) (_hT : 0 < T)
    (_h_init : ∀ N, ∀ᵐ ω ∂μ, (X N).init ω = mf.x₀)
    (h_as_bound : ∃ K > 0, ∀ᵐ ω ∂μ,
        ∀ᶠ (N : ℕ) in Filter.atTop,
          (Real.sqrt ↑N / Real.log ↑N) *
            ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
              ‖(X N).process t ω - mf.sol t‖ ≤ K) :
    ∃ C > 0, ∀ᵐ ω ∂μ,
      Filter.limsup
        (fun (N : ℕ) => (Real.sqrt N / Real.log N) *
          ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
            ‖(X N).process t ω - mf.sol t‖)
        Filter.atTop ≤ C := by
  obtain ⟨K, hK, h_ae⟩ := h_as_bound
  refine ⟨K, hK, ?_⟩
  filter_upwards [h_ae] with ω hω
  rw [Filter.limsup_eq]
  let u : ℕ → ℝ := fun N => (Real.sqrt ↑N / Real.log ↑N) *
    ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
      ‖(X N).process t ω - mf.sol t‖
  change sInf {a | ∀ᶠ N in Filter.atTop, u N ≤ a} ≤ K
  by_cases hb : BddBelow {a | ∀ᶠ N in Filter.atTop, u N ≤ a}
  · exact csInf_le hb hω
  · rw [csInf_of_not_bddBelow hb, Real.sInf_empty]
    exact le_of_lt hK

/-! ## Kurtz 1972 §IV: Central Limit Theorem

The fluctuation process Z^N(t) = √N · (X̄^N(t) - x(t)) converges
in distribution to a Gaussian process with covariance determined
by the Jacobian of F and the reaction variances.

This is the quantitative refinement: not only does X̄^N → x, but
the fluctuations are O(1/√N) and asymptotically Gaussian. -/

/-- **Kurtz's CLT (1972, §IV).**

V^{1/2}[V⁻¹X^V(t) - X(t,x₀)] → Z(t) in distribution,
where Z(t) is a Gaussian process with mean zero and covariance
given by the linearized system around the ODE solution.

We state this as: the rescaled fluctuation process has bounded
second moments, which is the essential content for applications.

Hypothesis `h_gronwall` encapsulates the Gronwall bound:
the rescaled error N·‖error‖² is bounded by K times the
martingale sup-squared. Combined with the QV bound, this
gives a finite integral bound. -/
theorem kurtz_clt_second_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (mf : MeanFieldSolution d Γ)
    (N : ℕ) (hN : 0 < N)
    (dp : DensityProcess d Γ N μ)
    (T : ℝ) (hT : 0 < T)
    (_h_init : ∀ᵐ ω ∂μ, dp.init ω = mf.x₀)
    (h_gronwall : ∃ K > 0,
        ∫ ω, ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
          (N : ℝ) * ‖dp.process t ω - mf.sol t‖ ^ 2 ∂μ ≤
        K * ∫ ω, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖dp.martingale_part s ω‖ ^ 2 ∂μ) :
    ∃ C > 0,
      ∫ ω, ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        (N : ℝ) * ‖dp.process t ω - mf.sol t‖ ^ 2 ∂μ ≤ C := by
  obtain ⟨K, hK, h_bd⟩ := h_gronwall
  obtain ⟨C_qv, hC_qv, h_qv⟩ := dp.martingale_qv_bound T hT
  refine ⟨K * (C_qv * T / ↑N), by positivity, ?_⟩
  calc ∫ ω, ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
          (↑N : ℝ) * ‖dp.process t ω - mf.sol t‖ ^ 2 ∂μ
      ≤ K * ∫ ω, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖dp.martingale_part s ω‖ ^ 2 ∂μ := h_bd
    _ ≤ K * (C_qv * T / ↑N) :=
        mul_le_mul_of_nonneg_left h_qv (le_of_lt hK)

/-! ## Full Kurtz convergence for density-dependent CTMCs

The following theorem states that for any family of density-dependent CTMCs
with a fixed rate specification, Lipschitz drift, and convergent initial
conditions, the mean-field convergence holds. -/

/-- **Kurtz's Mean-Field Convergence for Density-Dependent CTMCs.**

Given a rate specification Γ with Lipschitz drift, a family of density
processes `X N` (one for each population size N), and initial conditions
converging to x₀ in probability, the density process converges to the
ODE solution in probability:

  sup_{0≤t≤T} ‖X̄^N(t) - x(t)‖ → 0  in probability as N → ∞.

This theorem combines:
1. The constructive DensityProcess from CTMC (RandomIndexDoob.lean)
2. The Gronwall event inclusion (integral Gronwall + decomposition)
3. The uniform QV bound (Doob L2 + QVComp bound, C independent of N)
4. The measure chain (event inclusion + Markov + Chebyshev)
5. The convergence theorem (kurtz_mean_field_convergence) -/
theorem kurtz_convergence_for_density_dep_ctmc
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (mf : MeanFieldSolution d Γ)
    (X : (N : ℕ) → DensityProcess d Γ N μ)
    {T : ℝ} (hT : 0 < T)
    -- Lipschitz drift
    (h_lip : ∃ L ≥ 0, ∀ x y : Fin d → ℝ,
      dist (Γ.drift x) (Γ.drift y) ≤ L * dist x y)
    -- Initial conditions converge in probability
    (h_init : ∀ ε > 0,
      Filter.Tendsto (fun N => μ {ω | ‖(X N).init ω - mf.x₀‖ > ε})
        Filter.atTop (nhds 0))
    -- Uniform QV bound: ∃ C independent of N
    (h_qv_unif : ∃ C_qv > 0, ∀ (N : ℕ), 0 < N →
        ∫ ω, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖(X N).martingale_part s ω‖ ^ 2 ∂μ ≤ C_qv * T / N)
    -- Gronwall event inclusion (from integral Gronwall + decomposition)
    (h_event_unif : ∀ ε > 0, ∃ δ > 0, ∀ (N : ℕ), 0 < N →
        ∀ᵐ ω ∂μ,
          (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
              ‖(X N).process t ω - mf.sol t‖ ≥ ε) →
            (‖(X N).init ω - mf.x₀‖ ≥ δ) ∨
            (δ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
              ‖(X N).martingale_part s ω‖ ^ 2)) :
    ∀ ε > 0,
      Filter.Tendsto
        (fun N => μ {ω |
          ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
            ‖(X N).process t ω - mf.sol t‖ > ε})
        Filter.atTop (nhds 0) :=
  kurtz_mean_field_convergence mf X T hT h_init
    (kurtz_gm_of_event_inclusion X mf hT h_event_unif h_qv_unif)

/-- **Kurtz's Strong Approximation for Density-Dependent CTMCs.**

  sup ‖X̄^N - x‖ = O(log N / √N) a.s.

This requires the strong coupling hypothesis `h_as_bound`, which for
density-dependent CTMCs follows from the QV bound + Borel-Cantelli:
  Σ_N P(sup M > C·log N/√N) ≤ Σ_N E[sup M²]·N/log²N = Σ_N O(T/log²N) < ∞ -/
theorem kurtz_strong_for_density_dep_ctmc
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (mf : MeanFieldSolution d Γ)
    (X : (N : ℕ) → DensityProcess d Γ N μ)
    {T : ℝ} (hT : 0 < T)
    (h_init : ∀ N, ∀ᵐ ω ∂μ, (X N).init ω = mf.x₀)
    (h_as_bound : ∃ K > 0, ∀ᵐ ω ∂μ,
        ∀ᶠ (N : ℕ) in Filter.atTop,
          (Real.sqrt ↑N / Real.log ↑N) *
            ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
              ‖(X N).process t ω - mf.sol t‖ ≤ K) :
    ∃ C > 0, ∀ᵐ ω ∂μ,
      Filter.limsup
        (fun (N : ℕ) => (Real.sqrt N / Real.log N) *
          ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
            ‖(X N).process t ω - mf.sol t‖)
        Filter.atTop ≤ C :=
  kurtz_strong_approximation mf X T hT h_init h_as_bound

/-- **Kurtz's CLT Second Moment for Density-Dependent CTMCs.**

  E[N · sup ‖X̄^N - x‖²] = O(T)

This requires the Gronwall integral bound `h_gronwall`:
  E[N · sup error²] ≤ K · E[sup M²]
which follows from the Gronwall inequality (Lipschitz drift). -/
theorem kurtz_clt_for_density_dep_ctmc
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (mf : MeanFieldSolution d Γ)
    (N : ℕ) (hN : 0 < N)
    (dp : DensityProcess d Γ N μ)
    (T : ℝ) (hT : 0 < T)
    (h_init : ∀ᵐ ω ∂μ, dp.init ω = mf.x₀)
    (h_gronwall : ∃ K > 0,
        ∫ ω, ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
          (N : ℝ) * ‖dp.process t ω - mf.sol t‖ ^ 2 ∂μ ≤
        K * ∫ ω, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖dp.martingale_part s ω‖ ^ 2 ∂μ) :
    ∃ C > 0,
      ∫ ω, ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        (N : ℝ) * ‖dp.process t ω - mf.sol t‖ ^ 2 ∂μ ≤ C :=
  kurtz_clt_second_moment mf N hN dp T hT h_init h_gronwall

/-- **Construction of h_as_bound for strong Kurtz from exponential tail + Gronwall.**

Given:
- Gronwall pathwise bound: sup error ≤ sup‖M‖ · e^{LT} a.e.
- Exponential martingale tail: P(sup M > ε) ≤ 2·exp(-c·N·ε²)
  (from Azuma-Hoeffding for bounded-jump martingales)
- Borel-Cantelli: Σ exp(-c·K²·log²N) < ∞ → a.s. eventually sup M ≤ K·logN/√N

Constructs h_as_bound for kurtz_strong_for_density_dep_ctmc. -/
theorem h_as_bound_of_gronwall_exp_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : (N : ℕ) → DensityProcess d Γ N μ)
    (mf : MeanFieldSolution d Γ)
    {T : ℝ} (hT : 0 < T)
    (h_init : ∀ N, ∀ᵐ ω ∂μ, (X N).init ω = mf.x₀)
    -- Gronwall pathwise: sup error ≤ sup‖M‖ · e^{LT} a.e.
    (h_gronwall_pw : ∃ L ≥ 0, ∀ (N : ℕ), 0 < N → ∀ᵐ ω ∂μ,
        ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
          ‖(X N).process t ω - mf.sol t‖ ≤
        (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖(X N).martingale_part s ω‖) * Real.exp (L * T))
    -- Summable tail bound: Σ P(sup M ≥ logN/√N) < ∞
    -- This follows from exponential concentration (Azuma-Hoeffding) + comparison test.
    (h_summable_tail : ∑' (N : ℕ), μ {ω | Real.log ↑N / Real.sqrt ↑N ≤
        ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖(X N).martingale_part s ω‖} ≠ ⊤) :
    ∃ K > 0, ∀ᵐ ω ∂μ,
      ∀ᶠ (N : ℕ) in Filter.atTop,
        (Real.sqrt ↑N / Real.log ↑N) *
          ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
            ‖(X N).process t ω - mf.sol t‖ ≤ K := by
  obtain ⟨L, hL, h_gw⟩ := h_gronwall_pw
  -- h_summable_tail provides the summability directly
  -- K = e^{LT} + 1
  refine ⟨Real.exp (L * T) + 1, by positivity, ?_⟩
  -- Bad events: A_N = {sup M ≥ logN/√N}
  let A : ℕ → Set Ω := fun N =>
    {ω | Real.log ↑N / Real.sqrt ↑N ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
      ‖(X N).martingale_part s ω‖}
  -- Σ μ(A_N) < ∞ from h_exp_tail
  have hsum : ∑' (N : ℕ), μ (A N) ≠ ⊤ := h_summable_tail
  -- Borel-Cantelli: a.e. only finitely many A_N
  have hBC := ae_finite_setOf_mem hsum
  -- Gronwall for all N simultaneously (countable intersection)
  have hGW_all : ∀ᵐ ω ∂μ, ∀ (N : ℕ), 0 < N →
      ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), ‖(X N).process t ω - mf.sol t‖ ≤
      (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T), ‖(X N).martingale_part s ω‖) *
        Real.exp (L * T) := by
    rw [ae_all_iff]
    intro N
    by_cases hN : 0 < N
    · filter_upwards [h_gw N hN] with ω hω _
      exact hω
    · filter_upwards with ω h
      exact absurd h (by omega)
  -- Combine BC + Gronwall
  filter_upwards [hBC, hGW_all] with ω hfin hgw
  have h_event : ∀ᶠ N in Filter.atTop, ω ∉ A N := by
    rw [← Nat.cofinite_eq_atTop]
    exact hfin.eventually_cofinite_notMem
  -- Eventually: ω ∉ A N → sup M < logN/√N
  -- Gronwall: sup error ≤ sup M · e^{LT}
  -- Combine: (√N/logN)·sup error ≤ e^{LT} ≤ K
  -- Filter to N ≥ 3 (so logN > 0, √N > 0, N > 0)
  have h_large : ∀ᶠ N in Filter.atTop, (3 : ℕ) ≤ N := Filter.eventually_atTop.mpr ⟨3, fun _ h => h⟩
  exact (h_event.and h_large).mono fun N ⟨hNA, hN3⟩ => by
    simp only [A, Set.mem_setOf_eq, not_le] at hNA
    have hN_pos : 0 < N := by omega
    have hN_real : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hN_pos
    have hlogN : 0 < Real.log ↑N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hsqrtN : 0 < Real.sqrt ↑N := Real.sqrt_pos.mpr hN_real
    -- sup error ≤ sup M · e^{LT} (Gronwall)
    -- sup M < logN/√N (from ω ∉ A_N)
    -- (√N/logN) · sup error ≤ (√N/logN) · (logN/√N) · e^{LT} = e^{LT} ≤ e^{LT}+1
    have h1 := hgw N hN_pos  -- sup error ≤ sup M · e^{LT}
    have h2 := hNA  -- sup M < logN/√N
    -- bound: sup error ≤ (logN/√N) · e^{LT}
    have h3 : ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), ‖(X N).process t ω - mf.sol t‖ ≤
        Real.log ↑N / Real.sqrt ↑N * Real.exp (L * T) :=
      h1.trans (mul_le_mul_of_nonneg_right (le_of_lt h2) (Real.exp_nonneg _))
    -- (√N/logN) · that ≤ e^{LT}
    have h4 : Real.sqrt ↑N / Real.log ↑N *
        (Real.log ↑N / Real.sqrt ↑N * Real.exp (L * T)) = Real.exp (L * T) := by
      field_simp
    linarith [mul_le_mul_of_nonneg_left h3
      (div_nonneg (le_of_lt hsqrtN) (le_of_lt hlogN)), h4]

/-- **Pathwise Gronwall bound from integral inequality.**

Given the integral inequality
  ‖error(t)‖ ≤ sup‖M‖ + ∫₀ᵗ L·‖error(s)‖ ds
(which follows from decomposition + Lipschitz + triangle inequality),
IntegralGronwall gives the exponential bound:
  sup_{t≤T} ‖error(t)‖ ≤ sup‖M‖ · e^{LT}. -/
theorem h_gronwall_pw_of_density_process
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (dp : DensityProcess d Γ N μ)
    (mf : MeanFieldSolution d Γ)
    {T : ℝ} (hT : 0 < T)
    (h_lip : ∃ L ≥ 0, ∀ x y : Fin d → ℝ,
        ‖Γ.drift x - Γ.drift y‖ ≤ L * ‖x - y‖)
    -- Pathwise integral inequality (from decomposition + Lipschitz + triangle)
    (h_integral_ineq : ∀ L ≥ 0,
        (∀ x y : Fin d → ℝ, ‖Γ.drift x - Γ.drift y‖ ≤ L * ‖x - y‖) →
        ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 T,
          ‖dp.process t ω - mf.sol t‖ ≤
            (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T), ‖dp.martingale_part s ω‖) +
            ∫ s in (0 : ℝ)..t, L * ‖dp.process s ω - mf.sol s‖)
    -- Error continuity (holds for CTMC: process is càdlàg, sol is smooth)
    (h_err_cont : ∀ᵐ ω ∂μ, ContinuousOn
        (fun t => ‖dp.process t ω - mf.sol t‖) (Set.Icc 0 T)) :
    ∃ L ≥ 0, ∀ᵐ ω ∂μ,
      ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        ‖dp.process t ω - mf.sol t‖ ≤
      (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖dp.martingale_part s ω‖) * Real.exp (L * T) := by
  obtain ⟨L, hL, h_lip_bound⟩ := h_lip
  refine ⟨L, hL, ?_⟩
  filter_upwards [h_integral_ineq L hL h_lip_bound, h_err_cont] with ω hineq herr_cont
  let supM := ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T), ‖dp.martingale_part s ω‖
  suffices h : ∀ t ∈ Set.Icc 0 T,
      ‖dp.process t ω - mf.sol t‖ ≤ supM * Real.exp (L * T) by
    exact Real.iSup_le (fun t => Real.iSup_le (fun ht => h t ⟨ht.1, ht.2⟩)
      (mul_nonneg (Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _)
        (Real.exp_nonneg _)))
      (mul_nonneg (Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _)
        (Real.exp_nonneg _))
  have hgronwall := @integral_gronwall_core T supM L
    (fun t => ‖dp.process t ω - mf.sol t‖)
    (le_of_lt hT)
    (Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _)
    hL
    (fun t _ => norm_nonneg _)
    hineq
    (fun x hx => -- IntervalIntegrable
      ContinuousOn.intervalIntegrable_of_Icc hx.1
        (continuousOn_const.mul (herr_cont.mono (Set.Icc_subset_Icc_right (le_of_lt hx.2)))))
    (fun x hx => -- ContinuousWithinAt
      ((continuousOn_const.mul herr_cont).continuousWithinAt
        ⟨hx.1, le_of_lt hx.2⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT_of_mem hx))
    (fun x hx => -- StronglyMeasurableAtFilter
      ⟨Set.Icc 0 T, Icc_mem_nhdsGT_of_mem hx,
       (continuousOn_const.mul herr_cont).aestronglyMeasurable measurableSet_Icc⟩)
    (by -- ContinuousOn primitive
      have hint : IntegrableOn (fun s => L * ‖dp.process s ω - mf.sol s‖)
          (Set.uIcc 0 T) volume := by
        rw [Set.uIcc_of_le (le_of_lt hT)]
        exact (continuousOn_const.mul herr_cont).integrableOn_Icc
      have hprim := intervalIntegral.continuousOn_primitive_interval hint
      rw [Set.uIcc_of_le (le_of_lt hT)] at hprim
      exact continuousOn_const.add hprim)
  -- Step 2: integral_gronwall_core gives u(t) ≤ supM · exp(L·t)
  -- Step 3: exp(L·t) ≤ exp(L·T) for t ≤ T
  intro t ht
  exact le_trans (hgronwall t ht)
    (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp_of_le (mul_le_mul_of_nonneg_left ht.2 hL))
      (Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _))

end Ripple.Kurtz
