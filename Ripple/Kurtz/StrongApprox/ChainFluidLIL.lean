/-
  Ripple.Kurtz.StrongApprox.ChainFluidLIL — the LIL-scale chain-to-fluid rate
  from the Poisson representation and the envelope, by pathwise
  Gronwall.

  The chain is stated through the **random time-change representation** (Kurtz 1978; EK Ch. 11,
  (1.2)): a path `X : ℝ → (Fin d → ℝ)` is a time-change solution at scale `N` for the driver paths
  `Y l : ℝ → ℕ` if, for `t ∈ [0, T]`,
    `X t = X 0 + Σ_l ((Y l (N ∫_0^t β l (X s) ds) : ℝ) / N) • v l`,
  with rate functions `0 ≤ β l ≤ b l` (bounded, measurable) and jump vectors `v l`. The fluid path
  solves `x t = x₀ + ∫_0^t F (x s) ds`, `F y = Σ_l β l y • v l`, `F` globally `L`-Lipschitz.

  Relation to Ripple's canonical-law chain (`DensityDepCTMC.canonicalRecordMeasure`,
  `Ripple/Kurtz/Defs.lean`): that a time-change solution driven by independent unit Poisson
  processes has the canonical law is Kurtz's representation theorem; it is a **separate
  obligation, not proved here**. Everything below is a pathwise statement about every time-change
  solution, plus an almost-sure statement over the driver family space `familyMeasure ι P`.

  Results: `timeChange_sub_fluid` (the remainder identity (1.21)), `timeChange_gronwall`
  (pathwise: `‖X t − x t‖ ≤ e^{Lt} (‖X 0 − x₀‖ + N⁻¹ Σ_l ‖v l‖ e l)` whenever
  `|Y l u − u| ≤ e l` on `[0, N b_l T]`), and `ae_chain_fluid_rate` (almost surely, for all large
  `N`, every time-change solution satisfies the bound with
  `e l = 8 √(N b_l T log log (N b_l T)) + 1`).
-/

import Mathlib
import Ripple.Kurtz.StrongApprox.PoissonLIL
import Ripple.Kurtz.IntegralGronwall

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset Filter Topology

section Deterministic

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- The drift `F y = Σ_l β l y • v l`. -/
def tcDrift (β : ι → (Fin d → ℝ) → ℝ) (v : ι → Fin d → ℝ) (y : Fin d → ℝ) : Fin d → ℝ :=
  ∑ l, β l y • v l

/-- The internal clock `τ l t = ∫_0^t β l (X s) ds`. -/
noncomputable def clock (β : ι → (Fin d → ℝ) → ℝ) (X : ℝ → Fin d → ℝ) (l : ι) (t : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..t, β l (X s)

/-- The time-change remainder `Σ_l ((Y l (N τ_l t) − N τ_l t) / N) • v l`. -/
noncomputable def tcRemainder (β : ι → (Fin d → ℝ) → ℝ) (v : ι → Fin d → ℝ) (Y : ι → ℝ → ℕ)
    (N : ℕ) (X : ℝ → Fin d → ℝ) (t : ℝ) : Fin d → ℝ :=
  ∑ l, (((Y l (N * clock β X l t) : ℝ) - N * clock β X l t) / N) • v l

variable {β : ι → (Fin d → ℝ) → ℝ} {v : ι → Fin d → ℝ} {b : ι → ℝ} {X : ℝ → Fin d → ℝ}

theorem intervalIntegrable_rate (hβ0 : ∀ l y, 0 ≤ β l y) (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l)) (hXm : Measurable X) (l : ι) (a c : ℝ) :
    IntervalIntegrable (fun s => β l (X s)) volume a c := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := b l) (by simp) ?_ ?_
  · exact ((hβm l).comp hXm).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hβ0 l (X s))]
    exact hβb l (X s)

theorem intervalIntegrable_rate_smul (hβ0 : ∀ l y, 0 ≤ β l y) (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l)) (hXm : Measurable X) (l : ι) (a c : ℝ) :
    IntervalIntegrable (fun s => β l (X s) • v l) volume a c := by
  have h := intervalIntegrable_rate hβ0 hβb hβm hXm l a c
  exact ⟨h.1.smul_const (v l), h.2.smul_const (v l)⟩

theorem clock_nonneg (hβ0 : ∀ l y, 0 ≤ β l y) (l : ι) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ clock β X l t :=
  intervalIntegral.integral_nonneg ht fun s _ => hβ0 l (X s)

theorem clock_le (hβ0 : ∀ l y, 0 ≤ β l y) (hβb : ∀ l y, β l y ≤ b l) (hβm : ∀ l, Measurable (β l))
    (hXm : Measurable X) (l : ι) {t : ℝ} (ht : 0 ≤ t) : clock β X l t ≤ b l * t := by
  unfold clock
  have h := intervalIntegral.integral_mono_on ht (intervalIntegrable_rate hβ0 hβb hβm hXm l 0 t)
    intervalIntegrable_const (fun s _ => hβb l (X s))
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
  linarith

theorem clock_mono (hβ0 : ∀ l y, 0 ≤ β l y) (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l)) (hXm : Measurable X) (l : ι) : Monotone (clock β X l) := by
  intro s t hst
  unfold clock
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_rate hβ0 hβb hβm hXm l 0 s) (intervalIntegrable_rate hβ0 hβb hβm hXm l s t)]
  have : 0 ≤ ∫ u in s..t, β l (X u) := intervalIntegral.integral_nonneg hst fun u _ => hβ0 l (X u)
  linarith

theorem continuous_clock (hβ0 : ∀ l y, 0 ≤ β l y) (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l)) (hXm : Measurable X) (l : ι) : Continuous (clock β X l) := by
  unfold clock
  exact intervalIntegral.continuous_primitive
    (fun a c => intervalIntegrable_rate hβ0 hβb hβm hXm l a c) 0

/-- **The remainder identity (1.21)**: a time-change solution satisfies the fluid equation up to
`tcRemainder`. -/
theorem timeChange_sub_fluid (hβ0 : ∀ l y, 0 ≤ β l y) (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l)) (hXm : Measurable X) {Y : ι → ℝ → ℕ} {N : ℕ} (hN : 0 < N)
    {t : ℝ} (hX : X t = X 0 + ∑ l, ((Y l (N * clock β X l t) : ℝ) / N) • v l) :
    X t = X 0 + (∫ s in (0:ℝ)..t, tcDrift β v (X s)) + tcRemainder β v Y N X t := by
  have hNr : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hint : ∫ s in (0:ℝ)..t, tcDrift β v (X s) = ∑ l, clock β X l t • v l := by
    unfold tcDrift clock
    rw [intervalIntegral.integral_finsetSum (fun l _ =>
      intervalIntegrable_rate_smul (v := v) hβ0 hβb hβm hXm l 0 t)]
    exact Finset.sum_congr rfl fun l _ => intervalIntegral.integral_smul_const _ _
  rw [hint, hX, add_assoc]
  congr 1
  unfold tcRemainder
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← add_smul]
  congr 1
  field_simp
  ring

theorem norm_tcRemainder_le (hβ0 : ∀ l y, 0 ≤ β l y) (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l)) (hXm : Measurable X) {Y : ι → ℝ → ℕ} {N : ℕ} (hN : 0 < N)
    {T : ℝ} {e : ι → ℝ}
    (hD : ∀ l, ∀ u ∈ Icc (0:ℝ) (N * (b l * T)), |(Y l u : ℝ) - u| ≤ e l) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) T) :
    ‖tcRemainder β v Y N X t‖ ≤ (N:ℝ)⁻¹ * ∑ l, ‖v l‖ * e l := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  unfold tcRemainder
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hNr]
  have hu : (N:ℝ) * clock β X l t ∈ Icc (0:ℝ) (N * (b l * T)) := by
    constructor
    · exact mul_nonneg hNr.le (clock_nonneg hβ0 l ht.1)
    · refine mul_le_mul_of_nonneg_left ?_ hNr.le
      have h1 := clock_le hβ0 hβb hβm hXm l ht.1
      have hb : 0 ≤ b l := (hβ0 l (X 0)).trans (hβb l (X 0))
      nlinarith [ht.2]
  have h := hD l _ hu
  have hv := norm_nonneg (v l)
  calc |(Y l (N * clock β X l t) : ℝ) - N * clock β X l t| / N * ‖v l‖
      ≤ e l / N * ‖v l‖ := by gcongr
    _ = (N:ℝ)⁻¹ * (‖v l‖ * e l) := by ring

/-- A time-change solution is eventually constant to the right of every time. -/
theorem timeChange_eventually_right (hβ0 : ∀ l y, 0 ≤ β l y) (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l)) (hXm : Measurable X) {Y : ι → ℝ → ℕ}
    (hYrc : ∀ l u, ∀ᶠ u' in 𝓝[≥] u, Y l u' = Y l u) {N : ℕ} {T : ℝ}
    (hX : ∀ t ∈ Icc (0:ℝ) T, X t = X 0 + ∑ l, ((Y l (N * clock β X l t) : ℝ) / N) • v l)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) T) :
    ∀ᶠ s in 𝓝[≥] t, s ∈ Icc (0:ℝ) T → X s = X t := by
  have hall : ∀ l, ∀ᶠ s in 𝓝[≥] t, Y l (N * clock β X l s) = Y l (N * clock β X l t) := by
    intro l
    have hmap : Tendsto (fun s => (N:ℝ) * clock β X l s) (𝓝[≥] t) (𝓝[≥] (N * clock β X l t)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (((continuous_clock hβ0 hβb hβm hXm l).const_smul (N:ℝ)).tendsto t |>.mono_left
          nhdsWithin_le_nhds)
        (Filter.mem_of_superset self_mem_nhdsWithin fun s (hs : t ≤ s) =>
          (mul_le_mul_of_nonneg_left (clock_mono hβ0 hβb hβm hXm l hs) (Nat.cast_nonneg N) :
            (N:ℝ) * clock β X l t ≤ N * clock β X l s))
    exact hmap.eventually (hYrc l (N * clock β X l t))
  filter_upwards [Filter.eventually_all.mpr hall] with s hs hsT
  rw [hX s hsT, hX t ht]
  congr 1
  exact Finset.sum_congr rfl fun l _ => by rw [hs l]

/-- **Pathwise Gronwall (1.21)**: for every time-change solution on `[0, T]`,
`‖X t − x t‖ ≤ e^{L t} (‖X 0 − x₀‖ + N⁻¹ Σ_l ‖v l‖ e l)` whenever the drivers satisfy
`|Y l u − u| ≤ e l` on `[0, N b_l T]`. -/
theorem timeChange_gronwall (hβ0 : ∀ l y, 0 ≤ β l y) (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l)) {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ y z, ‖tcDrift β v y - tcDrift β v z‖ ≤ L * ‖y - z‖) {T : ℝ} (hT : 0 ≤ T)
    {x : ℝ → Fin d → ℝ} {x₀ : Fin d → ℝ} (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Icc (0:ℝ) T, x t = x₀ + ∫ s in (0:ℝ)..t, tcDrift β v (x s))
    (hXm : Measurable X) {Y : ι → ℝ → ℕ} (hYmono : ∀ l, Monotone (Y l))
    (hYrc : ∀ l u, ∀ᶠ u' in 𝓝[≥] u, Y l u' = Y l u) {N : ℕ} (hN : 0 < N)
    (hX : ∀ t ∈ Icc (0:ℝ) T, X t = X 0 + ∑ l, ((Y l (N * clock β X l t) : ℝ) / N) • v l)
    {e : ι → ℝ} (hD : ∀ l, ∀ u ∈ Icc (0:ℝ) (N * (b l * T)), |(Y l u : ℝ) - u| ≤ e l)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) T) :
    ‖X t - x t‖ ≤ (‖X 0 - x₀‖ + (N:ℝ)⁻¹ * ∑ l, ‖v l‖ * e l) * Real.exp (L * t) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hb : ∀ l, 0 ≤ b l := fun l => (hβ0 l (X 0)).trans (hβb l (X 0))
  have he : ∀ l, 0 ≤ e l := fun l =>
    (abs_nonneg _).trans (hD l 0 ⟨le_rfl, mul_nonneg hNr.le (mul_nonneg (hb l) hT)⟩)
  have hρ : 0 ≤ (N:ℝ)⁻¹ * ∑ l, ‖v l‖ * e l :=
    mul_nonneg (inv_nonneg.mpr hNr.le)
      (Finset.sum_nonneg fun l _ => mul_nonneg (norm_nonneg _) (he l))
  -- (i) the error is bounded and a.e.-strongly measurable on `[0, T]`
  obtain ⟨Bx, hBx⟩ := isCompact_Icc.exists_bound_of_continuousOn hxc
  have hXb : ∀ s ∈ Icc (0:ℝ) T,
      ‖X s‖ ≤ ‖X 0‖ + ∑ l, ((Y l (N * (b l * T)) : ℝ) / N) * ‖v l‖ := by
    intro s hs
    rw [hX s hs]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ((norm_sum_le _ _).trans
      (Finset.sum_le_sum fun l _ => ?_)))
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ hNr.le) (norm_nonneg _)
    have h1 : (N:ℝ) * clock β X l s ≤ N * (b l * T) := by
      refine mul_le_mul_of_nonneg_left ?_ hNr.le
      have := clock_le hβ0 hβb hβm hXm l hs.1
      nlinarith [hs.2, hb l]
    exact_mod_cast hYmono l h1
  have hub : ∀ s ∈ Icc (0:ℝ) T, ‖X s - x s‖ ≤
      ‖X 0‖ + ∑ l, ((Y l (N * (b l * T)) : ℝ) / N) * ‖v l‖ + Bx := by
    intro s hs
    have := norm_sub_le (X s) (x s)
    have := hXb s hs
    have := hBx s hs
    linarith
  have hxm : AEStronglyMeasurable x (volume.restrict (Icc (0:ℝ) T)) :=
    hxc.aestronglyMeasurable measurableSet_Icc
  have hum : AEStronglyMeasurable (fun s => ‖X s - x s‖) (volume.restrict (Icc (0:ℝ) T)) :=
    (hXm.aestronglyMeasurable.sub hxm).norm
  have huint : IntegrableOn (fun s => ‖X s - x s‖) (Icc (0:ℝ) T) :=
    Integrable.mono' (integrable_const (‖X 0‖ + ∑ l, ((Y l (N * (b l * T)) : ℝ) / N) * ‖v l‖ + Bx))
      hum
      (ae_restrict_of_forall_mem measurableSet_Icc fun s hs => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact hub s hs)
  have hLu_int : IntegrableOn (fun s => L * ‖X s - x s‖) (Icc (0:ℝ) T) := huint.const_mul L
  -- (ii) right-continuity of the error on `[0, T)`
  have hurc : ∀ s ∈ Ico (0:ℝ) T, ContinuousWithinAt (fun s => L * ‖X s - x s‖) (Ioi s) s := by
    intro s hs
    have hsI : s ∈ Icc (0:ℝ) T := ⟨hs.1, hs.2.le⟩
    have hXev := timeChange_eventually_right hβ0 hβb hβm hXm hYrc hX hsI
    have hXev' : ∀ᶠ s' in 𝓝[>] s, X s' = X s := by
      have h1 : ∀ᶠ s' in 𝓝[>] s, s' ∈ Icc (0:ℝ) T := Icc_mem_nhdsGT_of_mem hs
      have h2 : ∀ᶠ s' in 𝓝[>] s, s' ∈ Icc (0:ℝ) T → X s' = X s :=
        hXev.filter_mono (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
      filter_upwards [h1, h2] with s' h1 h2
      exact h2 h1
    have hxt : Tendsto x (𝓝[>] s) (𝓝 (x s)) :=
      (hxc.continuousWithinAt hsI).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT_of_mem hs)
    have hXt : Tendsto X (𝓝[>] s) (𝓝 (X s)) :=
      tendsto_const_nhds.congr' (hXev'.mono fun s' h => h.symm)
    exact tendsto_const_nhds.mul (hXt.sub hxt).norm
  -- (iii) the integral inequality
  have hFX_int : ∀ t', IntervalIntegrable (fun s => tcDrift β v (X s)) volume 0 t' := by
    intro t'
    have hfun : (fun s => tcDrift β v (X s)) = ∑ l, fun s => β l (X s) • v l := by
      funext s
      simp [tcDrift, Finset.sum_apply]
    rw [hfun]
    exact IntervalIntegrable.sum _ fun l _ =>
      intervalIntegrable_rate_smul (v := v) hβ0 hβb hβm hXm l 0 t'
  have hFcont : Continuous (tcDrift β v) :=
    (LipschitzWith.of_dist_le_mul (K := ⟨L, hL⟩) fun y z => by
      rw [dist_eq_norm, dist_eq_norm]
      exact hF y z).continuous
  have hFx_int : ∀ t' ∈ Icc (0:ℝ) T,
      IntervalIntegrable (fun s => tcDrift β v (x s)) volume 0 t' := fun t' ht' =>
    ContinuousOn.intervalIntegrable_of_Icc ht'.1
      ((hFcont.comp_continuousOn hxc).mono (Icc_subset_Icc_right ht'.2))
  have hineq : ∀ t' ∈ Icc (0:ℝ) T, ‖X t' - x t'‖ ≤
      (‖X 0 - x₀‖ + (N:ℝ)⁻¹ * ∑ l, ‖v l‖ * e l) + ∫ s in (0:ℝ)..t', L * ‖X s - x s‖ := by
    intro t' ht'
    have h1 := timeChange_sub_fluid hβ0 hβb hβm hXm hN (hX t' ht')
    have h2 := hx t' ht'
    have hsub : X t' - x t' = (X 0 - x₀) +
        (∫ s in (0:ℝ)..t', (tcDrift β v (X s) - tcDrift β v (x s))) +
          tcRemainder β v Y N X t' := by
      rw [intervalIntegral.integral_sub (hFX_int t') (hFx_int t' ht'), h1, h2]
      abel
    have hR := norm_tcRemainder_le (v := v) hβ0 hβb hβm hXm hN hD ht'
    have hFint : IntervalIntegrable (fun s => ‖tcDrift β v (X s) - tcDrift β v (x s)‖)
        volume 0 t' := ((hFX_int t').sub (hFx_int t' ht')).norm
    have hLu : IntervalIntegrable (fun s => L * ‖X s - x s‖) volume 0 t' :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le ht'.1).mpr
        (hLu_int.mono_set (Icc_subset_Icc_right ht'.2))
    have hnorm : ‖∫ s in (0:ℝ)..t', (tcDrift β v (X s) - tcDrift β v (x s))‖ ≤
        ∫ s in (0:ℝ)..t', L * ‖X s - x s‖ := by
      refine (intervalIntegral.norm_integral_le_integral_norm ht'.1).trans ?_
      exact intervalIntegral.integral_mono_on ht'.1 hFint hLu fun s _ => hF _ _
    calc ‖X t' - x t'‖
        = ‖(X 0 - x₀) + (∫ s in (0:ℝ)..t', (tcDrift β v (X s) - tcDrift β v (x s))) +
            tcRemainder β v Y N X t'‖ := by rw [hsub]
      _ ≤ ‖X 0 - x₀‖ + ‖∫ s in (0:ℝ)..t', (tcDrift β v (X s) - tcDrift β v (x s))‖ +
            ‖tcRemainder β v Y N X t'‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (‖X 0 - x₀‖ + (N:ℝ)⁻¹ * ∑ l, ‖v l‖ * e l) + ∫ s in (0:ℝ)..t', L * ‖X s - x s‖ := by
          linarith
  -- (iv) Gronwall
  exact Ripple.Kurtz.integral_gronwall (T := T) (α := ‖X 0 - x₀‖ + (N:ℝ)⁻¹ * ∑ l, ‖v l‖ * e l)
    (β := L) (u := fun s => ‖X s - x s‖) hT (by positivity) hL (fun s _ => norm_nonneg _) hineq
    (fun s hs => (intervalIntegrable_iff_integrableOn_Icc_of_le hs.1).mpr
      (hLu_int.mono_set (Icc_subset_Icc_right hs.2.le)))
    hurc
    (fun s hs => ⟨Icc 0 T, Icc_mem_nhdsGT_of_mem hs, hLu_int.aestronglyMeasurable⟩)
    (by
      have hint : IntegrableOn (fun s => L * ‖X s - x s‖) (uIcc 0 T) volume := by
        rw [uIcc_of_le hT]
        exact hLu_int
      have hprim := intervalIntegral.continuousOn_primitive_interval hint
      rw [uIcc_of_le hT] at hprim
      exact continuousOn_const.add hprim)
    t ht

end Deterministic

/-! ### The almost-sure rate over the driver family -/

section Stochastic

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {N : ℕ → Ω → ℕ} {d : ℕ} {ι : Type*} [Fintype ι]

/-- The envelope value `8 √(U log log U) + 1` at horizon `U`. -/
noncomputable def envelope (U : ℝ) : ℝ := 8 * Real.sqrt (U * Real.log (Real.log U)) + 1

/-- Almost surely, the drivers of the family are eventually inside the envelope on every
horizon `n (b l T)` simultaneously for all `l`. -/
theorem ae_family_envelope (hNm : ∀ i, Measurable (N i)) (hN : iIndepFun N P)
    (hNl : ∀ i k, P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1)) (b : ι → ℝ)
    (hb : ∀ l, 0 ≤ b l) (T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ ω ∂(familyMeasure ι P), ∀ᶠ n : ℕ in atTop, ∀ l, ∀ u ∈ Icc (0:ℝ) (n * (b l * T)),
      |(poisFamily ι N l u ω : ℝ) - u| ≤ envelope (n * (b l * T)) := by
  have hall : ∀ l, ∀ᵐ ω ∂(familyMeasure ι P), ∀ᶠ U : ℝ in atTop, ∀ u ∈ Icc (0:ℝ) U,
      |(poisFamily ι N l u ω : ℝ) - u| ≤ envelope U := fun l =>
    ae_familyMeasure_of_ae ι l (ae_poisPath_envelope hNm hN hNl)
  filter_upwards [ae_all_iff.mpr hall] with ω hω
  rw [Filter.eventually_all]
  intro l
  by_cases hbl : 0 < b l * T
  · obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp (hω l)
    have hev : ∀ᶠ n : ℕ in atTop, U₀ ≤ (n:ℝ) * (b l * T) :=
      (tendsto_natCast_atTop_atTop.atTop_mul_const hbl).eventually_ge_atTop U₀
    filter_upwards [hev] with n hn
    exact hU₀ _ hn
  · have hzero : b l * T = 0 := le_antisymm (not_lt.mp hbl) (mul_nonneg (hb l) hT)
    refine Filter.Eventually.of_forall fun n u hu => ?_
    rw [hzero, mul_zero] at hu ⊢
    have hu0 : u = 0 := le_antisymm hu.2 hu.1
    rw [hu0]
    simp only [poisFamily, poisPath_zero]
    unfold envelope
    simp

/-- **LIL-scale chain-to-fluid rate** (with the explicit envelope):
almost surely on the driver family space, for all large `n`, every measurable time-change
solution `X` at scale `n` driven by the family satisfies, for `t ∈ [0, T]`,
`‖X t − x t‖ ≤ e^{L t} (‖X 0 − x₀‖ + n⁻¹ Σ_l ‖v l‖ (8 √(n b_l T log log (n b_l T)) + 1))`.
With `X 0 = x₀` this is `sup_{t ≤ T} ‖X_n − x‖ = O(√(log log n / n))` with the explicit
constant `8 e^{LT} Σ_l ‖v l‖ √(b_l T)` in front of `√(log log n / n)` (asymptotically). -/
theorem ae_chain_fluid_rate (hNm : ∀ i, Measurable (N i)) (hN : iIndepFun N P)
    (hNl : ∀ i k, P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1))
    {β : ι → (Fin d → ℝ) → ℝ} {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y) (hβb : ∀ l y, β l y ≤ b l) (hβm : ∀ l, Measurable (β l))
    {L : ℝ} (hL : 0 ≤ L) (hF : ∀ y z, ‖tcDrift β v y - tcDrift β v z‖ ≤ L * ‖y - z‖)
    {T : ℝ} (hT : 0 ≤ T) {x : ℝ → Fin d → ℝ} {x₀ : Fin d → ℝ} (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Icc (0:ℝ) T, x t = x₀ + ∫ s in (0:ℝ)..t, tcDrift β v (x s)) :
    ∀ᵐ ω ∂(familyMeasure ι P), ∀ᶠ n : ℕ in atTop, ∀ X : ℝ → Fin d → ℝ, Measurable X →
      (∀ t ∈ Icc (0:ℝ) T, X t = X 0 +
        ∑ l, ((poisFamily ι N l (n * clock β X l t) ω : ℝ) / n) • v l) →
      ∀ t ∈ Icc (0:ℝ) T, ‖X t - x t‖ ≤
        (‖X 0 - x₀‖ + (n:ℝ)⁻¹ * ∑ l, ‖v l‖ * envelope (n * (b l * T))) * Real.exp (L * t) := by
  have hb : ∀ l, 0 ≤ b l := fun l => (hβ0 l x₀).trans (hβb l x₀)
  filter_upwards [ae_family_envelope hNm hN hNl b hb T hT] with ω hω
  filter_upwards [hω, Filter.eventually_gt_atTop 0] with n hn hn0 X hXm hX t ht
  exact timeChange_gronwall hβ0 hβb hβm hL hF hT hxc hx hXm
    (Y := fun l u => poisFamily ι N l u ω) (fun l => fun s t hst => poisPath_mono N hst (ω l))
    (fun l u => poisPath_eventually_right N u (ω l)) hn0 hX (e := fun l => envelope (n * (b l * T)))
    (fun l u hu => hn l u hu) ht

end Stochastic

end Ripple.Kurtz.StrongApprox
