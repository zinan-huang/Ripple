/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.CTMC.ExpMartingale
import Ripple.Kurtz.ExponentialTailPath
import Ripple.Kurtz.FiniteHorizon

/-!
# Kurtz's law of large numbers with an exponential tail

Assembly of FIX-KURTZ2-FINAL §3 for canonical density-dependent CTMCs
(`CTMC.DensityDepCTMC.mk N hN Γ`):

* `Kurtz.frozen_martingale_exp_tail` (Theorem 3.1): there are `Λ > 0` and `J ≥ 1` depending only
  on the rate specification such that for every horizon `T > 0`, population `N`, simplex initial
  state and `0 < δ ≤ 2TΛJ`,
  `P(sup_{t ≤ T} ‖M_N(t)‖ ≥ δ) ≤ 2 d e · exp(−N δ² / (4 T Λ J²))`,
  where `M_N` is the frozen martingale part of the density process.  The event is stated in the
  squared form used by the Gronwall inclusion (`δ² ≤ ⨆ ‖M_N(s)‖²`) and in the plain form
  (`frozen_martingale_exp_tail_sup`).
* `Kurtz.kurtz_finite_horizon_exp_tail` (Theorem 3.3): there are `K ≥ 1`, `c > 0`, `ε₀ > 0`
  depending only on `Γ` and `T` such that for every `N`, every simplex `x₀` and every
  `0 < ε ≤ ε₀` with `‖x₀/N − x(0)‖ < ε/K`,
  `P(sup_{t ≤ T} ‖X̄_N(t) − x(t)‖ > ε) ≤ 2 d e · exp(−c N ε²)`.
* `Kurtz.kurtz_finite_horizon_log_rate` (Corollary 3.4): the `√(log N / N)` high-probability scale.

The proof of Theorem 3.1 combines the pathwise bound
`DensityDepCTMC.GoodRecords.frozen_martingale_coord_le_pathExpSum_max` (equations (3.3)–(3.4)),
the identification of the pathwise exponential sum with the record-index martingale exponent
(`DensityDepCTMC.pathExpSum_eq_realExpSum`), Ville's maximal inequality
`QMatrix.ville_realExpSum` (Lemma 2.3), a union bound over the `d` coordinates and two signs, and
a limit `δ' ↑ δ`.
-/

namespace Ripple

open MeasureTheory Set Filter Topology
open Ripple.CTMC

namespace CTMC.DensityDepCTMC

variable {d : ℕ} (M : DensityDepCTMC d)

/-- With nonnegative holding times the pathwise exponential sum `A_n(T)` is the record-index
exponent `log Z_n(T)` of the exponential martingale module. -/
theorem pathExpSum_eq_realExpSum (φ : (Fin d → Fin (M.N + 1)) → ℝ) (T : ℝ) (n : ℕ)
    (ω : M.canonicalRecordΩ) (hnn : ∀ k, 0 ≤ (ω (k + 1)).1) :
    M.pathExpSum φ T n ω = M.toQMatrix.realExpSum φ T n ω := by
  rw [M.pathExpSum_eq_clamped φ T n ω hnn]
  unfold QMatrix.realExpSum QMatrix.realStepExponent QMatrix.recTime QMatrix.expCompRateReal
    expCompReal
  rfl

end CTMC.DensityDepCTMC

namespace Kurtz

variable {d : ℕ}

/-- The sign `σ(b) = ±1` used in the union bound over the two tails of a coordinate. -/
noncomputable def tailSign (b : Bool) : ℝ := if b then 1 else -1

theorem abs_tailSign (b : Bool) : |tailSign b| = 1 := by
  cases b <;> simp [tailSign]

theorem tailSign_sq (b : Bool) : tailSign b ^ 2 = 1 := by
  cases b <;> simp [tailSign]

/-- **Exponential tail of the frozen martingale part at a fixed level `δ' < δ`** (the body of
the proof of FIX-KURTZ2-FINAL Theorem 3.1).  For a density-dependent chain `M` with exit rates
`λ(x) ≤ N Λ` and coordinate jump bound `J ≥ 1`, with `θ₀ = δ / (2TΛJ²)` and `θ₀ J ≤ 1`: every
event on which the martingale sup over `[0, T]` exceeds `δ'` has probability at most
`2 d e · exp(−N (θ₀ δ' − T Λ θ₀² J²))`. -/
theorem frozen_martingale_exp_tail_of_lt (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (hcons : M.ConservativeJumps) (hBC : M.BoundaryCompatibleOnSimplex) (hinit : M.InSimplex x₀)
    {T : ℝ} (hT : 0 < T) {Λ J : ℝ} (hΛpos : 0 < Λ) (hΛ : ∀ x, M.exitRateAt x ≤ M.N * Λ)
    (hJ1 : 1 ≤ J)
    (hJ : ∀ x y, 0 < M.offDiagRate x y → ∀ i : Fin d, |(y i : ℝ) - (x i : ℝ)| ≤ J)
    {δ δ' : ℝ} (hδ' : 0 < δ') (hlt : δ' < δ) (hθJ : δ / (2 * T * Λ * J ^ 2) * J ≤ 1)
    (E : Set M.canonicalRecordΩ)
    (hE : ∀ ω ∈ E, ∃ s ∈ Icc (0 : ℝ) T,
      δ' < ‖M.frozenMartingalePart M.canonicalPathMap s ω‖) :
    M.canonicalRecordMeasure x₀ E ≤
      ENNReal.ofReal (2 * d * Real.exp 1 * Real.exp (-(M.N * (δ / (2 * T * Λ * J ^ 2) * δ' -
        T * Λ * (δ / (2 * T * Λ * J ^ 2)) ^ 2 * J ^ 2)))) := by
  set θ₀ : ℝ := δ / (2 * T * Λ * J ^ 2) with hθ₀
  have hJ0 : 0 ≤ J := zero_le_one.trans hJ1
  have hδ : 0 < δ := hδ'.trans hlt
  have hθ₀pos : 0 < θ₀ := by positivity
  have hNpos : (0 : ℝ) < M.N := by exact_mod_cast M.hN
  -- the level of Ville's inequality
  set la : ℝ := θ₀ * M.N * δ' - T * M.N * Λ * θ₀ ^ 2 * J ^ 2 - θ₀ * J with hla
  set a : ℝ := Real.exp la with ha
  have hapos : 0 < a := Real.exp_pos _
  -- the `2d` record-index events
  set Esub : Fin d × Bool → Set M.canonicalRecordΩ := fun p =>
    {ω | ∃ n, a ≤ Real.exp (M.toQMatrix.realExpSum
      (fun x => tailSign p.2 * θ₀ * (x p.1 : ℝ)) T n ω)} with hEsub
  -- pathwise: on the good event, `E` is covered by the record-index events
  have hcover : ∀ᵐ ω ∂M.canonicalRecordMeasure x₀, ω ∈ E → ω ∈ ⋃ p, Esub p := by
    filter_upwards [M.goodRecords_ae x₀ hcons hinit hT] with ω hg hωE
    obtain ⟨s, hs, hsδ⟩ := hE ω hωE
    -- a coordinate and a sign with `σ M_i(s) > δ'`
    obtain ⟨i, hi⟩ : ∃ i : Fin d, δ' < |M.frozenMartingalePart M.canonicalPathMap s ω i| := by
      by_contra h
      push Not at h
      have : ‖M.frozenMartingalePart M.canonicalPathMap s ω‖ ≤ δ' :=
        (pi_norm_le_iff_of_nonneg hδ'.le).mpr fun i => by
          rw [Real.norm_eq_abs]; exact h i
      exact absurd hsδ (not_lt.mpr this)
    obtain ⟨b, hb⟩ : ∃ b : Bool,
        δ' < tailSign b * M.frozenMartingalePart M.canonicalPathMap s ω i := by
      rcases lt_abs.mp hi with h | h
      · exact ⟨true, by simpa [tailSign] using h⟩
      · exact ⟨false, by simpa [tailSign] using h⟩
    set θ : ℝ := tailSign b * θ₀ with hθ
    have hθabs : |θ| = θ₀ := by rw [hθ, abs_mul, abs_tailSign, one_mul, abs_of_pos hθ₀pos]
    have hθsq : θ ^ 2 = θ₀ ^ 2 := by rw [hθ, mul_pow, tailSign_sq, one_mul]
    have hθJ' : |θ| * J ≤ 1 := by rw [hθabs]; exact hθJ
    obtain ⟨n, hn⟩ := hg.frozen_martingale_coord_le_pathExpSum_max hBC hJ0 hJ hΛ i hθJ' hs
    rw [hθabs, hθsq] at hn
    have hlin : θ * M.N * M.frozenMartingalePart M.canonicalPathMap s ω i =
        θ₀ * M.N * (tailSign b * M.frozenMartingalePart M.canonicalPathMap s ω i) := by
      rw [hθ]; ring
    rw [hlin] at hn
    have hgt : la + θ₀ * J <
        max (M.pathExpSum (fun x => θ * (x i : ℝ)) T n ω)
          (M.pathExpSum (fun x => θ * (x i : ℝ)) T (n + 1) ω + θ₀ * J) := by
      have h1 : θ₀ * M.N * δ' < θ₀ * M.N * (tailSign b *
          M.frozenMartingalePart M.canonicalPathMap s ω i) :=
        mul_lt_mul_of_pos_left hb (by positivity)
      rw [hla]
      linarith
    have hθJ0 : 0 ≤ θ₀ * J := by positivity
    obtain ⟨m, hm⟩ : ∃ m, la < M.pathExpSum (fun x => θ * (x i : ℝ)) T m ω := by
      rcases lt_max_iff.mp hgt with h | h
      · exact ⟨n, by linarith⟩
      · exact ⟨n + 1, by linarith⟩
    refine Set.mem_iUnion.mpr ⟨(i, b), m, ?_⟩
    rw [← M.pathExpSum_eq_realExpSum _ T m ω hg.hold_nonneg]
    exact (Real.exp_lt_exp.mpr hm).le
  -- Ville's inequality for each of the `2d` events
  have hville : ∀ p : Fin d × Bool, M.canonicalRecordMeasure x₀ (Esub p) ≤ ENNReal.ofReal (1 / a) :=
    fun p => M.toQMatrix.ville_realExpSum _ T x₀ hapos
  -- the value of `1/a`
  have h1a : 1 / a = Real.exp (θ₀ * J) *
      Real.exp (-(M.N * (θ₀ * δ' - T * Λ * θ₀ ^ 2 * J ^ 2))) := by
    rw [ha, one_div, ← Real.exp_neg, ← Real.exp_add, hla]
    congr 1
    ring
  have hX : 0 < Real.exp (-(M.N * (θ₀ * δ' - T * Λ * θ₀ ^ 2 * J ^ 2))) := Real.exp_pos _
  have hexp1 : Real.exp (θ₀ * J) ≤ Real.exp 1 := Real.exp_le_exp.mpr hθJ
  calc M.canonicalRecordMeasure x₀ E
      ≤ M.canonicalRecordMeasure x₀ (⋃ p, Esub p) := measure_mono_ae hcover
    _ ≤ ∑ p : Fin d × Bool, M.canonicalRecordMeasure x₀ (Esub p) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _p : Fin d × Bool, ENNReal.ofReal (1 / a) := Finset.sum_le_sum fun p _ => hville p
    _ = ENNReal.ofReal (((d * 2 : ℕ) : ℝ) * (1 / a)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_bool, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (2 * d * Real.exp 1 *
          Real.exp (-(M.N * (θ₀ * δ' - T * Λ * θ₀ ^ 2 * J ^ 2)))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [h1a]
        push_cast
        have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        nlinarith [mul_le_mul_of_nonneg_right hexp1 hX.le, mul_nonneg hd
          (sub_nonneg.mpr (mul_le_mul_of_nonneg_right hexp1 hX.le))]

/-- The algebra of the constants: `θ₀ δ − T Λ θ₀² J² = δ² / (4 T Λ J²)` for
`θ₀ = δ / (2 T Λ J²)`. -/
theorem tail_exponent_eq {T Λ J δ : ℝ} (hT : 0 < T) (hΛ : 0 < Λ) (hJ : 0 < J) :
    δ / (2 * T * Λ * J ^ 2) * δ - T * Λ * (δ / (2 * T * Λ * J ^ 2)) ^ 2 * J ^ 2 =
      δ ^ 2 / (4 * T * Λ * J ^ 2) := by
  field_simp
  ring

/-- Passage to the limit `δ' ↑ δ` in the tail bound. -/
theorem measure_le_of_forall_lt {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (E : Set Ω)
    {δ : ℝ} (hδ : 0 < δ) (g : ℝ → ℝ) (hg : Continuous g)
    (h : ∀ δ', 0 < δ' → δ' < δ → μ E ≤ ENNReal.ofReal (g δ')) :
    μ E ≤ ENNReal.ofReal (g δ) := by
  have htend : Tendsto (fun δ' => ENNReal.ofReal (g δ')) (𝓝[<] δ) (𝓝 (ENNReal.ofReal (g δ))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp
      (tendsto_nhdsWithin_of_tendsto_nhds (hg.tendsto δ))
  have hev : ∀ᶠ δ' in 𝓝[<] δ, μ E ≤ ENNReal.ofReal (g δ') := by
    filter_upwards [Ioo_mem_nhdsLT hδ] with δ' hδ'
    exact h δ' hδ'.1 hδ'.2
  exact ge_of_tendsto htend hev

/-- The shared body of the two forms of Theorem 3.1: the limit `δ' ↑ δ` of
`frozen_martingale_exp_tail_of_lt`. -/
theorem frozen_martingale_exp_tail_of_forall (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (hcons : M.ConservativeJumps) (hBC : M.BoundaryCompatibleOnSimplex) (hinit : M.InSimplex x₀)
    {T : ℝ} (hT : 0 < T) {Λ J : ℝ} (hΛpos : 0 < Λ) (hΛ : ∀ x, M.exitRateAt x ≤ M.N * Λ)
    (hJ1 : 1 ≤ J)
    (hJ : ∀ x y, 0 < M.offDiagRate x y → ∀ i : Fin d, |(y i : ℝ) - (x i : ℝ)| ≤ J)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 2 * T * Λ * J)
    (E : Set M.canonicalRecordΩ)
    (hE : ∀ ω ∈ E, ∀ δ', 0 < δ' → δ' < δ → ∃ s ∈ Icc (0 : ℝ) T,
      δ' < ‖M.frozenMartingalePart M.canonicalPathMap s ω‖) :
    M.canonicalRecordMeasure x₀ E ≤
      ENNReal.ofReal (2 * d * Real.exp 1 * Real.exp (-(M.N * δ ^ 2 / (4 * T * Λ * J ^ 2)))) := by
  have hJpos : 0 < J := zero_lt_one.trans_le hJ1
  set θ₀ : ℝ := δ / (2 * T * Λ * J ^ 2) with hθ₀
  have hθJ : θ₀ * J ≤ 1 := by
    rw [hθ₀, div_mul_eq_mul_div, div_le_one (by positivity)]
    calc δ * J ≤ 2 * T * Λ * J * J := mul_le_mul_of_nonneg_right hδle hJpos.le
      _ = 2 * T * Λ * J ^ 2 := by ring
  set g : ℝ → ℝ := fun δ' =>
    2 * d * Real.exp 1 * Real.exp (-(M.N * (θ₀ * δ' - T * Λ * θ₀ ^ 2 * J ^ 2))) with hg
  have hgcont : Continuous g :=
    continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul ((continuous_const.mul continuous_id).sub continuous_const)).neg)
  have hgδ : g δ = 2 * d * Real.exp 1 * Real.exp (-(M.N * δ ^ 2 / (4 * T * Λ * J ^ 2))) := by
    have hte := tail_exponent_eq (δ := δ) hT hΛpos hJpos
    rw [← hθ₀] at hte
    simp only [hg]
    rw [hte, mul_div_assoc]
  rw [← hgδ]
  refine measure_le_of_forall_lt _ E hδ g hgcont fun δ' hδ' hlt => ?_
  exact frozen_martingale_exp_tail_of_lt M x₀ hcons hBC hinit hT hΛpos hΛ hJ1 hJ hδ' hlt hθJ E
    fun ω hω => hE ω hω δ' hδ' hlt

/-- **Exponential tail of the frozen martingale part (FIX-KURTZ2-FINAL Theorem 3.1), squared
form.** For the canonical family `DensityDepCTMC.mk N hN Γ` there are `Λ > 0` and `J ≥ 1`,
depending only on `Γ`, such that for every `T > 0`, `N`, simplex `x₀` and `0 < δ ≤ 2TΛJ`,
`P(δ² ≤ sup_{s ≤ T} ‖M_N(s)‖²) ≤ 2 d e · exp(−N δ² / (4 T Λ J²))`. -/
theorem frozen_martingale_exp_tail (Γ : RateSpec d)
    (hConservative : ∀ (N : ℕ) (hN : 0 < N), (CTMC.DensityDepCTMC.mk N hN Γ).ConservativeJumps)
    (hBoundary : ∀ (N : ℕ) (hN : 0 < N),
      (CTMC.DensityDepCTMC.mk N hN Γ).BoundaryCompatibleOnSimplex) :
    ∃ Λ > (0 : ℝ), ∃ J ≥ (1 : ℝ), ∀ {T : ℝ}, 0 < T →
      ∀ (N : ℕ) (hN : 0 < N) (x₀ : Fin d → Fin (N + 1)),
        (CTMC.DensityDepCTMC.mk N hN Γ).InSimplex x₀ →
        ∀ {δ : ℝ}, 0 < δ → δ ≤ 2 * T * Λ * J →
        (CTMC.DensityDepCTMC.mk N hN Γ).canonicalRecordMeasure x₀
          {ω | δ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
            ‖(CTMC.DensityDepCTMC.mk N hN Γ).frozenMartingalePart
              (CTMC.DensityDepCTMC.mk N hN Γ).canonicalPathMap s ω‖ ^ 2} ≤
          ENNReal.ofReal (2 * d * Real.exp 1 *
            Real.exp (-(N * δ ^ 2 / (4 * T * Λ * J ^ 2)))) := by
  obtain ⟨Λ, hΛpos, hΛ⟩ := Γ.exists_exitRate_bound_uniform
  obtain ⟨J, hJ1, hJ⟩ := Γ.exists_coord_jump_bound
  refine ⟨Λ, hΛpos, J, hJ1, ?_⟩
  intro T hT N hN x₀ hinit δ hδ hδle
  refine frozen_martingale_exp_tail_of_forall (CTMC.DensityDepCTMC.mk N hN Γ) x₀
    (hConservative N hN) (hBoundary N hN) hinit hT hΛpos (hΛ N hN) hJ1
    (fun x y hxy i => hJ N hN x y i hxy) hδ hδle _ ?_
  intro ω hω δ' hδ' hlt
  by_contra h
  push Not at h
  have hsup : (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
      ‖(CTMC.DensityDepCTMC.mk N hN Γ).frozenMartingalePart
        (CTMC.DensityDepCTMC.mk N hN Γ).canonicalPathMap s ω‖ ^ 2) ≤ δ' ^ 2 := by
    refine Real.iSup_le (fun s => Real.iSup_le (fun hs => ?_) (sq_nonneg _)) (sq_nonneg _)
    exact pow_le_pow_left₀ (norm_nonneg _) (h s hs) 2
  have hωE : δ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
      ‖(CTMC.DensityDepCTMC.mk N hN Γ).frozenMartingalePart
        (CTMC.DensityDepCTMC.mk N hN Γ).canonicalPathMap s ω‖ ^ 2 := hω
  nlinarith

/-- **Exponential tail of the frozen martingale part (FIX-KURTZ2-FINAL Theorem 3.1).**
`P(δ ≤ sup_{s ≤ T} ‖M_N(s)‖) ≤ 2 d e · exp(−N δ² / (4 T Λ J²))` for `0 < δ ≤ 2TΛJ`, with `Λ > 0`
and `J ≥ 1` depending only on `Γ`. -/
theorem frozen_martingale_exp_tail_sup (Γ : RateSpec d)
    (hConservative : ∀ (N : ℕ) (hN : 0 < N), (CTMC.DensityDepCTMC.mk N hN Γ).ConservativeJumps)
    (hBoundary : ∀ (N : ℕ) (hN : 0 < N),
      (CTMC.DensityDepCTMC.mk N hN Γ).BoundaryCompatibleOnSimplex) :
    ∃ Λ > (0 : ℝ), ∃ J ≥ (1 : ℝ), ∀ {T : ℝ}, 0 < T →
      ∀ (N : ℕ) (hN : 0 < N) (x₀ : Fin d → Fin (N + 1)),
        (CTMC.DensityDepCTMC.mk N hN Γ).InSimplex x₀ →
        ∀ {δ : ℝ}, 0 < δ → δ ≤ 2 * T * Λ * J →
        (CTMC.DensityDepCTMC.mk N hN Γ).canonicalRecordMeasure x₀
          {ω | δ ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
            ‖(CTMC.DensityDepCTMC.mk N hN Γ).frozenMartingalePart
              (CTMC.DensityDepCTMC.mk N hN Γ).canonicalPathMap s ω‖} ≤
          ENNReal.ofReal (2 * d * Real.exp 1 *
            Real.exp (-(N * δ ^ 2 / (4 * T * Λ * J ^ 2)))) := by
  obtain ⟨Λ, hΛpos, hΛ⟩ := Γ.exists_exitRate_bound_uniform
  obtain ⟨J, hJ1, hJ⟩ := Γ.exists_coord_jump_bound
  refine ⟨Λ, hΛpos, J, hJ1, ?_⟩
  intro T hT N hN x₀ hinit δ hδ hδle
  refine frozen_martingale_exp_tail_of_forall (CTMC.DensityDepCTMC.mk N hN Γ) x₀
    (hConservative N hN) (hBoundary N hN) hinit hT hΛpos (hΛ N hN) hJ1
    (fun x y hxy i => hJ N hN x y i hxy) hδ hδle _ ?_
  intro ω hω δ' hδ' hlt
  by_contra h
  push Not at h
  have hsup : (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
      ‖(CTMC.DensityDepCTMC.mk N hN Γ).frozenMartingalePart
        (CTMC.DensityDepCTMC.mk N hN Γ).canonicalPathMap s ω‖) ≤ δ' :=
    Real.iSup_le (fun s => Real.iSup_le (fun hs => h s hs) hδ'.le) hδ'.le
  have hωE : δ ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
      ‖(CTMC.DensityDepCTMC.mk N hN Γ).frozenMartingalePart
        (CTMC.DensityDepCTMC.mk N hN Γ).canonicalPathMap s ω‖ := hω
  linarith

/-- The supremum of the error on `[0, T]` only sees the solution on `[0, T]`. -/
theorem sup_err_extendLeft' {Γ : RateSpec d} (mf : MeanFieldSolution d Γ) (T : ℝ)
    (X : ℝ → Fin d → ℝ) :
    (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), ‖X t - mf.extendLeft.sol t‖) =
      ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), ‖X t - mf.sol t‖ := by
  refine iSup_congr fun t => iSup_congr fun ht => ?_
  rw [mf.extendLeft_sol_of_nonneg ht.1]

/-- **Kurtz's law of large numbers with an exponential tail (FIX-KURTZ2-FINAL Theorem 3.3).**
For the canonical family `DensityDepCTMC.mk N hN Γ` and a mean-field solution `x` with
`‖x(t)‖ ≤ 1`, there are `K ≥ 1`, `c > 0` and `ε₀ > 0`, depending only on `Γ` and `T`, such that
for every population `N`, every simplex initial state `x₀` and every `0 < ε ≤ ε₀` with
`‖x₀/N − x(0)‖ < ε/K`,
`P(sup_{0 ≤ t ≤ T} ‖X̄_N(t) − x(t)‖ > ε) ≤ 2 d e · exp(−c N ε²)`
under the canonical path law.  (`K = 2 e^{LT}`, `ε₀ = 2TΛJK`, `c = 1/(4TΛJ²K²)` with `L` the
Lipschitz constant of the drift on the unit ball and `Λ, J` from Theorem 3.1.) -/
theorem kurtz_finite_horizon_exp_tail [NeZero d]
    (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (hConservative : ∀ (N : ℕ) (hN : 0 < N), (CTMC.DensityDepCTMC.mk N hN Γ).ConservativeJumps)
    (hBoundary : ∀ (N : ℕ) (hN : 0 < N),
      (CTMC.DensityDepCTMC.mk N hN Γ).BoundaryCompatibleOnSimplex)
    (hSolBound : ∀ t : ℝ, 0 ≤ t → ‖mf.sol t‖ ≤ 1)
    {T : ℝ} (hT : 0 < T) :
    ∃ K ≥ (1 : ℝ), ∃ c > (0 : ℝ), ∃ ε₀ > (0 : ℝ),
      ∀ (N : ℕ) (hN : 0 < N) (x₀ : Fin d → Fin (N + 1)),
        (CTMC.DensityDepCTMC.mk N hN Γ).InSimplex x₀ →
        ∀ {ε : ℝ}, 0 < ε → ε ≤ ε₀ →
        ‖(fun i => (↑(x₀ i) : ℝ) / ↑N) - mf.x₀‖ < ε / K →
        (CTMC.DensityDepCTMC.mk N hN Γ).canonicalRecordMeasure x₀
          {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
            ‖(CTMC.DensityDepCTMC.mk N hN Γ).frozenDensityProcess
                (CTMC.DensityDepCTMC.mk N hN Γ).canonicalPathMap t ω - mf.sol t‖ > ε} ≤
          ENNReal.ofReal (2 * d * Real.exp 1 * Real.exp (-(c * N * ε ^ 2))) := by
  obtain ⟨Λ, hΛpos, J, hJ1, htail⟩ := frozen_martingale_exp_tail Γ hConservative hBoundary
  have hJpos : 0 < J := zero_lt_one.trans_le hJ1
  have hDrift : ∀ (N : ℕ) (hN : 0 < N),
      (CTMC.DensityDepCTMC.mk N hN Γ).DriftZeroAtAbsorbingOnSimplex :=
    fun N hN => driftZeroAtAbsorbingOnSimplex_of_boundaryCompatible _ (hBoundary N hN)
  obtain ⟨K, hK1, hincl⟩ :=
    frozen_event_inclusion_generic_linear Γ mf.extendLeft hDrift hConservative
      (fun t ht => by rw [mf.extendLeft_sol_of_nonneg ht]; exact hSolBound t ht)
      mf.extendLeft_measurable
      (fun i t _ => mf.extendLeft_drift_intervalIntegrable i t) hT
  have hKpos : 0 < K := zero_lt_one.trans_le hK1
  refine ⟨K, hK1, 1 / (4 * T * Λ * J ^ 2 * K ^ 2), by positivity, 2 * T * Λ * J * K,
    by positivity, ?_⟩
  intro N hN x₀ hinit ε hε hε₀ hclose
  let E : Set (CTMC.DensityDepCTMC.mk N hN Γ).canonicalRecordΩ :=
    {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
      ‖(CTMC.DensityDepCTMC.mk N hN Γ).frozenDensityProcess
        (CTMC.DensityDepCTMC.mk N hN Γ).canonicalPathMap t ω - mf.sol t‖ > ε}
  let A : Set (CTMC.DensityDepCTMC.mk N hN Γ).canonicalRecordΩ :=
    {ω | (ε / K) ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
      ‖(CTMC.DensityDepCTMC.mk N hN Γ).frozenMartingalePart
        (CTMC.DensityDepCTMC.mk N hN Γ).canonicalPathMap s ω‖ ^ 2}
  change (CTMC.DensityDepCTMC.mk N hN Γ).canonicalRecordMeasure x₀ E ≤ _
  have hδpos : 0 < ε / K := div_pos hε hKpos
  have hδle : ε / K ≤ 2 * T * Λ * J := by
    rw [div_le_iff₀ hKpos]
    linarith
  have h_event := hincl hε N hN x₀ hinit
  simp only [CTMC.DensityDepCTMC.toFrozenDensityProcess] at h_event
  have hinit_ae :=
    (CTMC.DensityDepCTMC.mk N hN Γ).canonical_frozenInitialCondition_eq_scaledState_ae x₀
  have hEA : ∀ᵐ ω ∂(CTMC.DensityDepCTMC.mk N hN Γ).canonicalRecordMeasure x₀,
      ω ∈ E → ω ∈ A := by
    filter_upwards [h_event, hinit_ae] with ω hω hinit' hE
    have hsup : (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        ‖(CTMC.DensityDepCTMC.mk N hN Γ).frozenDensityProcess
          (CTMC.DensityDepCTMC.mk N hN Γ).canonicalPathMap t ω - mf.extendLeft.sol t‖) ≥ ε := by
      rw [sup_err_extendLeft' mf T (fun t => (CTMC.DensityDepCTMC.mk N hN Γ).frozenDensityProcess
        (CTMC.DensityDepCTMC.mk N hN Γ).canonicalPathMap t ω)]
      exact le_of_lt hE
    rcases hω hsup with hbad | hA
    · exfalso
      rw [hinit', mf.extendLeft_x₀] at hbad
      exact absurd hclose (not_lt.mpr hbad)
    · exact hA
  calc (CTMC.DensityDepCTMC.mk N hN Γ).canonicalRecordMeasure x₀ E
      ≤ (CTMC.DensityDepCTMC.mk N hN Γ).canonicalRecordMeasure x₀ A := measure_mono_ae hEA
    _ ≤ ENNReal.ofReal (2 * d * Real.exp 1 *
          Real.exp (-(N * (ε / K) ^ 2 / (4 * T * Λ * J ^ 2)))) :=
        htail hT N hN x₀ hinit hδpos hδle
    _ = ENNReal.ofReal (2 * d * Real.exp 1 *
          Real.exp (-(1 / (4 * T * Λ * J ^ 2 * K ^ 2) * N * ε ^ 2))) := by
        congr 3
        field_simp

/-- **The `√(log N / N)` high-probability scale (FIX-KURTZ2-FINAL Corollary 3.4).** For every
`p > 0` there is `C > 0` (namely `C = √(p/c)`) such that for all sufficiently large `N`, if
`‖x₀/N − x(0)‖ < (C/K) √(log N / N)` then
`P(sup_{t ≤ T} ‖X̄_N(t) − x(t)‖ > C √(log N / N)) ≤ 2 d e · N^{−p}`. -/
theorem kurtz_finite_horizon_log_rate [NeZero d]
    (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (hConservative : ∀ (N : ℕ) (hN : 0 < N), (CTMC.DensityDepCTMC.mk N hN Γ).ConservativeJumps)
    (hBoundary : ∀ (N : ℕ) (hN : 0 < N),
      (CTMC.DensityDepCTMC.mk N hN Γ).BoundaryCompatibleOnSimplex)
    (hSolBound : ∀ t : ℝ, 0 ≤ t → ‖mf.sol t‖ ≤ 1)
    {T : ℝ} (hT : 0 < T) :
    ∃ K ≥ (1 : ℝ), ∀ p > (0 : ℝ), ∃ C > (0 : ℝ), ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (hN : 0 < N)
      (x₀ : Fin d → Fin (N + 1)), (CTMC.DensityDepCTMC.mk N hN Γ).InSimplex x₀ →
        ‖(fun i => (↑(x₀ i) : ℝ) / ↑N) - mf.x₀‖ < C * Real.sqrt (Real.log N / N) / K →
        (CTMC.DensityDepCTMC.mk N hN Γ).canonicalRecordMeasure x₀
          {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
            ‖(CTMC.DensityDepCTMC.mk N hN Γ).frozenDensityProcess
                (CTMC.DensityDepCTMC.mk N hN Γ).canonicalPathMap t ω - mf.sol t‖ >
              C * Real.sqrt (Real.log N / N)} ≤
          ENNReal.ofReal (2 * d * Real.exp 1 * (N : ℝ) ^ (-p)) := by
  obtain ⟨K, hK1, c, hc, ε₀, hε₀, hmain⟩ :=
    kurtz_finite_horizon_exp_tail Γ mf hConservative hBoundary hSolBound hT
  refine ⟨K, hK1, fun p hp => ⟨Real.sqrt (p / c), Real.sqrt_pos.mpr (div_pos hp hc), ?_⟩⟩
  set C := Real.sqrt (p / c) with hC
  have hCpos : 0 < C := Real.sqrt_pos.mpr (div_pos hp hc)
  have hCsq : C ^ 2 = p / c := Real.sq_sqrt (div_pos hp hc).le
  -- `C √(log N / N) → 0`, so it is eventually at most `ε₀`
  have hlim : Tendsto (fun N : ℕ => C * Real.sqrt (Real.log N / N)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun N : ℕ => Real.log N / N) atTop (𝓝 0) := by
      have := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop
      simpa [Function.comp_def] using this
    have h1 := (Real.continuous_sqrt.tendsto 0).comp h0
    rw [Real.sqrt_zero] at h1
    simpa using h1.const_mul C
  obtain ⟨N₀, hN₀⟩ := (eventually_atTop.mp
    ((hlim.eventually (Iio_mem_nhds hε₀)).and (eventually_ge_atTop 2)))
  refine ⟨N₀, fun N hN hNpos x₀ hinit hclose => ?_⟩
  obtain ⟨hεN, hN2⟩ := hN₀ N hN
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hlogpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hNr : (0 : ℝ) < N := by linarith
  have hεpos : 0 < C * Real.sqrt (Real.log N / N) :=
    mul_pos hCpos (Real.sqrt_pos.mpr (div_pos hlogpos hNr))
  refine (hmain N hNpos x₀ hinit hεpos (Set.mem_Iio.mp hεN).le hclose).trans_eq ?_
  have hexp : Real.exp (-(c * N * (C * Real.sqrt (Real.log N / N)) ^ 2)) = (N : ℝ) ^ (-p) := by
    rw [mul_pow, Real.sq_sqrt (div_pos hlogpos hNr).le, hCsq, Real.rpow_def_of_pos hNr]
    congr 1
    field_simp
  rw [hexp]

end Kurtz

end Ripple
