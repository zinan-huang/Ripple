/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.LPP.SynPPKurtz
import Ripple.CTMC.FrozenGeneratorSkeletonBound

/-!
# Kurtz's law of large numbers on a finite horizon

Kurtz, "Solutions of ordinary differential equations as limits of pure jump Markov
processes", J. Appl. Prob. 7 (1970), Theorem 3.1; Ethier–Kurtz, *Markov Processes*, Ch. 11,
Theorem 2.1: for a density-dependent family of CTMCs with locally Lipschitz drift `F`, if the
initial densities converge to `x₀` and the solution `x(t)` of `ẋ = F(x)`, `x(0) = x₀` stays in
the domain on `[0, T]`, then `sup_{t ≤ T} ‖X̄^N(t) − x(t)‖ → 0` in probability.

`kurtz_finite_horizon` proves this for the canonical density-dependent CTMC
`DensityDepCTMC.mk N hN Γ` of a finite rate specification `Γ` on the lattice cube, with random
initial states whose densities converge in probability to `x₀` (the paper's initial condition);
`kurtz_finite_horizon_of_close` is the uniform statement over deterministic initial states
within a small distance `γ` of `x₀`.  The hypotheses are model conditions of the lattice chain
(conservative jumps; jumps leaving the lattice have rate zero at simplex states) and the domain
condition `‖x(t)‖ ≤ 1` for `t ≥ 0`.  Measurability of the solution and integrability of
`F ∘ x` are not assumed: they hold for the tangent-line extension `MeanFieldSolution.extendLeft`,
which agrees with `x` on `[0, ∞)`.  The Doob L² maximal inequality, carried as `FrozenDoobL2` by
`kurtz_finite_horizon_generic`, is proved here from the model conditions
(`frozenDoobL2_of_boundaryCompatible`), and the quadratic-variation rate bound is
`RateSpec.exists_instantQVRate_bound_uniform`.
-/

namespace Ripple
namespace Kurtz

open MeasureTheory

variable {d : ℕ}

/-- On the simplex, boundary compatibility makes the drift vanish at every absorbing lattice
state (an absorbing state has zero exit rate, hence zero generator drift, and the generator drift
equals the rate-specification drift on the simplex). -/
theorem driftZeroAtAbsorbingOnSimplex_of_boundaryCompatible (M : CTMC.DensityDepCTMC d)
    (hBC : M.BoundaryCompatibleOnSimplex) : M.DriftZeroAtAbsorbingOnSimplex := by
  intro x hx hexit
  change M.rateSpec.drift (M.scaledState x) = 0
  rw [← M.generatorDrift_eq_rateSpec_drift_of_boundaryCompatibleOnSimplex hBC hx]
  funext i
  exact M.generatorDrift_eq_zero_of_exitRateAt_zero
    (by simpa [CTMC.DensityDepCTMC.exitRateAt] using hexit) i

/-- **Doob's L² maximal inequality for the frozen canonical martingale**, for every rate
specification whose lattice chains are conservative and boundary compatible on the simplex. -/
theorem frozenDoobL2_of_boundaryCompatible [NeZero d] (Γ : RateSpec d)
    (hcons : ∀ (N : ℕ) (hN : 0 < N), (CTMC.DensityDepCTMC.mk N hN Γ).ConservativeJumps)
    (hBC : ∀ (N : ℕ) (hN : 0 < N),
      (CTMC.DensityDepCTMC.mk N hN Γ).BoundaryCompatibleOnSimplex) :
    FrozenDoobL2 Γ (CTMC.DensityDepCTMC.frozenMartingalePartDoobL2Constant d) := by
  intro N hN x₀ hinit T hT
  let M : CTMC.DensityDepCTMC d := CTMC.DensityDepCTMC.mk N hN Γ
  have heq :=
    M.canonical_frozenMartingalePart_eq_frozenGeneratorMartingalePart_ae
      x₀ (hcons N hN) hinit (hBC N hN)
  have hgenerator := Ripple.CTMC.frozenGeneratorMP_skeleton_bound_ae M x₀ hinit hT
  have hbridge : ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      ∃ n, (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2) ≤
      (4 / 3 : ℝ) * M.frozenClockSkeletonSupSq T n records +
        4 * M.frozenTruncatedJumpSqSum T n records := by
    filter_upwards [heq, hgenerator] with records heq_records hgenerator_records
    obtain ⟨n, hn⟩ := hgenerator_records
    refine ⟨n, ?_⟩
    simpa only [heq_records] using hn
  exact M.frozenMartingalePart_DoobL2_of_skeleton_bound_ae
    x₀ hinit hT hbridge
    (fun n => M.frozenClockTruncatedQVIntegralSum_le_frozenQV_setIntegral
      x₀ hinit T hT n)

/-! ### Regularity of mean-field solutions

`MeanFieldSolution.sol` is constrained only for `t ≥ 0`.  The tangent-line extension below
agrees with it on `[0, ∞)` and is continuous on `ℝ`, so measurability of the solution and
integrability of `F ∘ x` need not be assumed. -/

namespace MeanFieldSolution

variable {Γ : RateSpec d}

/-- The extension of a mean-field solution to negative times by its tangent line at `0`:
`x(t)` for `t ≥ 0`, `x₀ + t F(x₀)` for `t < 0`. -/
noncomputable def extendLeft (mf : MeanFieldSolution d Γ) : MeanFieldSolution d Γ where
  x₀ := mf.x₀
  sol := fun t => if 0 ≤ t then mf.sol t else mf.x₀ + t • Γ.drift mf.x₀
  sol_init := by simp [mf.sol_init]
  sol_ode := by
    intro t ht
    rcases ht.lt_or_eq with htpos | rfl
    · have heq : (fun s : ℝ => if 0 ≤ s then mf.sol s else mf.x₀ + s • Γ.drift mf.x₀)
          =ᶠ[nhds t] mf.sol := by
        filter_upwards [lt_mem_nhds htpos] with s hs
        simp [hs.le]
      rw [if_pos htpos.le]
      exact (mf.sol_ode t htpos.le).congr_of_eventuallyEq heq
    · rw [if_pos le_rfl, mf.sol_init]
      have hR : HasDerivWithinAt
          (fun s : ℝ => if 0 ≤ s then mf.sol s else mf.x₀ + s • Γ.drift mf.x₀)
          (Γ.drift mf.x₀) (Set.Ici 0) 0 := by
        have h := (mf.sol_ode 0 le_rfl).hasDerivWithinAt (s := Set.Ici 0)
        rw [mf.sol_init] at h
        exact h.congr (fun y hy => if_pos hy) (if_pos le_rfl)
      have hL : HasDerivWithinAt
          (fun s : ℝ => if 0 ≤ s then mf.sol s else mf.x₀ + s • Γ.drift mf.x₀)
          (Γ.drift mf.x₀) (Set.Iic 0) 0 := by
        have h : HasDerivAt (fun s : ℝ => mf.x₀ + s • Γ.drift mf.x₀) (Γ.drift mf.x₀) 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Γ.drift mf.x₀)).const_add mf.x₀
        refine h.hasDerivWithinAt.congr (fun y hy => ?_) ?_
        · rcases (Set.mem_Iic.mp hy).lt_or_eq with hlt | rfl
          · simp [not_le.mpr hlt]
          · simp [mf.sol_init]
        · simp [mf.sol_init]
      have h := hR.union hL
      rwa [Set.Ici_union_Iic, hasDerivWithinAt_univ] at h

theorem extendLeft_sol_of_nonneg (mf : MeanFieldSolution d Γ) {t : ℝ} (ht : 0 ≤ t) :
    mf.extendLeft.sol t = mf.sol t := by
  simp [extendLeft, ht]

theorem extendLeft_x₀ (mf : MeanFieldSolution d Γ) : mf.extendLeft.x₀ = mf.x₀ := rfl

theorem extendLeft_continuous (mf : MeanFieldSolution d Γ) : Continuous mf.extendLeft.sol := by
  rw [continuous_iff_continuousAt]
  intro t
  rcases le_or_gt 0 t with ht | ht
  · exact (mf.extendLeft.sol_ode t ht).continuousAt
  · have heq : (fun s : ℝ => mf.x₀ + s • Γ.drift mf.x₀) =ᶠ[nhds t] mf.extendLeft.sol := by
      filter_upwards [gt_mem_nhds ht] with s hs
      simp [extendLeft, not_le.mpr hs]
    exact (continuous_const.add (continuous_id.smul continuous_const)).continuousAt.congr heq

theorem extendLeft_measurable (mf : MeanFieldSolution d Γ) : Measurable mf.extendLeft.sol :=
  mf.extendLeft_continuous.measurable

theorem extendLeft_drift_intervalIntegrable (mf : MeanFieldSolution d Γ) (i : Fin d) (t : ℝ) :
    IntervalIntegrable (fun s : ℝ => (Γ.drift (mf.extendLeft.sol s)) i)
      MeasureTheory.volume (0 : ℝ) t :=
  ((continuous_apply i).comp (Γ.drift_continuous.comp mf.extendLeft_continuous)).intervalIntegrable
    0 t

end MeanFieldSolution

/-- The supremum of the error on `[0, T]` only sees the solution on `[0, T]`. -/
private theorem sup_err_extendLeft {Γ : RateSpec d} (mf : MeanFieldSolution d Γ) (T : ℝ)
    (X : ℝ → Fin d → ℝ) :
    (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), ‖X t - mf.extendLeft.sol t‖) =
      ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), ‖X t - mf.sol t‖ := by
  refine iSup_congr fun t => iSup_congr fun ht => ?_
  rw [mf.extendLeft_sol_of_nonneg ht.1]

/-- **Kurtz's law of large numbers on `[0, T]`, uniform over nearby initial states.** For every
`ε, η > 0` there are `γ > 0` and `N₀` such that for every `N ≥ N₀` and every simplex initial
state `x₀` with `‖x₀/N − x(0)‖ ≤ γ`, `P(sup_{0 ≤ t ≤ T} ‖X̄^N(t) − x(t)‖ > ε) ≤ η` under the
canonical path measure. -/
theorem kurtz_finite_horizon_of_close [NeZero d]
    (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (hConservative : ∀ (N : ℕ) (hN : 0 < N),
      (CTMC.DensityDepCTMC.mk N hN Γ).ConservativeJumps)
    (hBoundary : ∀ (N : ℕ) (hN : 0 < N),
      (CTMC.DensityDepCTMC.mk N hN Γ).BoundaryCompatibleOnSimplex)
    (hSolBound : ∀ t : ℝ, 0 ≤ t → ‖mf.sol t‖ ≤ 1)
    {T : ℝ} (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∃ γ > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (hN : 0 < N) (x₀ : Fin d → Fin (N + 1)),
      (CTMC.DensityDepCTMC.mk N hN Γ).InSimplex x₀ →
      ‖(fun i => (↑(x₀ i) : ℝ) / ↑N) - mf.x₀‖ ≤ γ →
      (CTMC.DensityDepCTMC.mk N hN Γ).canonicalRecordMeasure x₀
        {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
          ‖(CTMC.DensityDepCTMC.mk N hN Γ).frozenDensityProcess
              (CTMC.DensityDepCTMC.mk N hN Γ).canonicalPathMap t ω - mf.sol t‖ > ε} ≤
        ENNReal.ofReal η := by
  have hDrift : ∀ (N : ℕ) (hN : 0 < N),
      (CTMC.DensityDepCTMC.mk N hN Γ).DriftZeroAtAbsorbingOnSimplex :=
    fun N hN => driftZeroAtAbsorbingOnSimplex_of_boundaryCompatible _ (hBoundary N hN)
  obtain ⟨C_qv, _hC_qv_pos, hqv⟩ :=
    frozen_martingale_qv_bound_uniform_of_doob Γ
      (CTMC.DensityDepCTMC.frozenMartingalePartDoobL2Constant_pos d)
      (frozenDoobL2_of_boundaryCompatible Γ hConservative hBoundary)
      (Γ.exists_instantQVRate_bound_uniform) hT
  obtain ⟨δ, hδ_pos, h_event⟩ :=
    frozen_event_inclusion_generic Γ mf.extendLeft hDrift hConservative
      (fun t ht => by rw [mf.extendLeft_sol_of_nonneg ht]; exact hSolBound t ht)
      mf.extendLeft_measurable
      (fun i t _ => mf.extendLeft_drift_intervalIntegrable i t) hT hε
  refine ⟨δ / 2, half_pos hδ_pos, Nat.ceil (C_qv * T / (η * δ ^ 2)) + 1, ?_⟩
  intro N hN_ge hN x₀ hinit hclose
  set M_ctmc : CTMC.DensityDepCTMC d := CTMC.DensityDepCTMC.mk N hN Γ
  set dp := M_ctmc.toFrozenDensityProcess x₀ (hDrift N hN) (hConservative N hN) hinit
  set μ := M_ctmc.canonicalRecordMeasure x₀
  let E : Set M_ctmc.canonicalRecordΩ :=
    {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), ‖dp.process t ω - mf.sol t‖ > ε}
  let I : Set M_ctmc.canonicalRecordΩ := {ω | ‖dp.init ω - mf.x₀‖ ≥ δ}
  let A : Set M_ctmc.canonicalRecordΩ :=
    {ω | δ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T), ‖dp.martingale_part s ω‖ ^ 2}
  change μ E ≤ ENNReal.ofReal η
  have hN_pos_real : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hδ_sq_pos : 0 < δ ^ 2 := sq_pos_of_pos hδ_pos
  have hN_markov_real : C_qv * T / (η * δ ^ 2) < (N : ℝ) := by
    calc
      C_qv * T / (η * δ ^ 2)
          ≤ (Nat.ceil (C_qv * T / (η * δ ^ 2)) : ℝ) := Nat.le_ceil _
      _ < (Nat.ceil (C_qv * T / (η * δ ^ 2)) + 1 : ℕ) := by
        exact_mod_cast Nat.lt_succ_self (Nat.ceil (C_qv * T / (η * δ ^ (2 : ℕ))))
      _ ≤ (N : ℝ) := by exact_mod_cast hN_ge
  have h_markov_real_target : C_qv * T / ((N : ℝ) * δ ^ 2) ≤ η := by
    have hden_pos : 0 < η * δ ^ 2 := mul_pos hη hδ_sq_pos
    have hmul : C_qv * T < (N : ℝ) * (η * δ ^ 2) := by
      rwa [div_lt_iff₀ hden_pos] at hN_markov_real
    have hden2_pos : 0 < (N : ℝ) * δ ^ 2 := mul_pos hN_pos_real hδ_sq_pos
    rw [div_le_iff₀ hden2_pos]
    nlinarith
  have h_event_ae : ∀ᵐ ω ∂μ,
      (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), ‖dp.process t ω - mf.sol t‖ ≥ ε) →
        (‖dp.init ω - mf.x₀‖ ≥ δ) ∨
        (δ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T), ‖dp.martingale_part s ω‖ ^ 2) := by
    have h := h_event N hN x₀ hinit
    simp only at h
    filter_upwards [h] with ω hω hsup
    rw [← sup_err_extendLeft mf T (fun t => dp.process t ω)] at hsup
    exact hω hsup
  have hstep1 : μ E ≤ μ I + μ A := by
    have hae : ∀ᵐ ω ∂μ, ω ∈ E → ω ∈ I ∪ A := by
      filter_upwards [h_event_ae] with ω hω hE
      rcases hω (le_of_lt hE) with hinit_bad | hmart_bad
      · exact Or.inl hinit_bad
      · exact Or.inr hmart_bad
    calc
      μ E ≤ μ (I ∪ A) := _root_.MeasureTheory.measure_mono_ae hae
      _ ≤ μ I + μ A := _root_.MeasureTheory.measure_union_le I A
  have hinit_eq_ae : ∀ᵐ ω ∂μ, dp.init ω = (fun i => (↑(x₀ i) : ℝ) / ↑N) := by
    have h := M_ctmc.canonical_frozenInitialCondition_eq_scaledState_ae x₀
    simpa [μ, M_ctmc, dp, CTMC.DensityDepCTMC.toFrozenDensityProcess] using h
  have hI_zero : μ I = 0 := by
    rw [_root_.MeasureTheory.measure_eq_zero_iff_ae_notMem]
    filter_upwards [hinit_eq_ae] with ω hω hωI
    have hle : ‖dp.init ω - mf.x₀‖ ≤ δ / 2 := by rw [hω]; exact hclose
    exact (not_le_of_gt (lt_of_le_of_lt hle (half_lt_self hδ_pos))) hωI
  have hA_le : μ A ≤ ENNReal.ofReal η := by
    have hmark :=
      _root_.MeasureTheory.mul_meas_ge_le_integral_of_nonneg
        (by simpa [μ, dp, A] using dp.martingale_sup_sq_nonneg T hT)
        (by simpa [μ, dp, A] using dp.martingale_sup_sq_integrable T hT)
        (δ ^ 2)
    have hqvN : ∫ ω, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖dp.martingale_part s ω‖ ^ 2 ∂μ ≤ C_qv * T / ↑N := by
      have hraw := hqv N hN x₀ hinit
      simpa [μ, M_ctmc, dp, CTMC.DensityDepCTMC.toFrozenDensityProcess] using hraw
    have hreal : μ.real A ≤ η := by
      have h1 : δ ^ 2 * μ.real A ≤ C_qv * T / ↑N := by
        simpa [A] using hmark.trans hqvN
      have hA_to_qv : μ.real A ≤ C_qv * T / ((N : ℝ) * δ ^ 2) := by
        rw [le_div_iff₀ (mul_pos hN_pos_real hδ_sq_pos)]
        have h2 : (N : ℝ) * (δ ^ 2 * μ.real A) ≤ (N : ℝ) * (C_qv * T / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 hN_pos_real.le
        rw [mul_div_cancel₀ _ (ne_of_gt hN_pos_real)] at h2
        linarith [show μ.real A * ((N : ℝ) * δ ^ 2) = (N : ℝ) * (δ ^ 2 * μ.real A) by ring]
      exact hA_to_qv.trans h_markov_real_target
    have hA_ne_top : μ A ≠ ⊤ := _root_.MeasureTheory.measure_ne_top μ A
    exact (ENNReal.le_ofReal_iff_toReal_le hA_ne_top hη.le).2 hreal
  calc
    μ E ≤ μ I + μ A := hstep1
    _ = μ A := by rw [hI_zero, zero_add]
    _ ≤ ENNReal.ofReal η := hA_le

/-- The path law of the canonical chain `DensityDepCTMC.mk N hN Γ` whose initial state is drawn
from the distribution `ν` on lattice states: `Σ_x ν(x) P_x`. -/
noncomputable def randomInitRecordMeasure (N : ℕ) (hN : 0 < N) (Γ : RateSpec d)
    (ν : PMF (Fin d → Fin (N + 1))) :
    Measure (CTMC.DensityDepCTMC.mk N hN Γ).canonicalRecordΩ :=
  ∑ x, ν x • (CTMC.DensityDepCTMC.mk N hN Γ).canonicalRecordMeasure x

/-- **Kurtz's law of large numbers on `[0, T]`** (Kurtz 1970, Thm 3.1; Ethier–Kurtz 11.2.1),
for canonical density-dependent CTMCs with random initial states.  If the initial state of
the population-`N` chain has law `ν N`, supported on the simplex, and the initial densities
`X^N(0)/N` converge in probability to `x(0)`, then `sup_{0 ≤ t ≤ T} ‖X̄^N(t) − x(t)‖ → 0` in
probability. -/
theorem kurtz_finite_horizon [NeZero d]
    (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (hConservative : ∀ (N : ℕ) (hN : 0 < N),
      (CTMC.DensityDepCTMC.mk N hN Γ).ConservativeJumps)
    (hBoundary : ∀ (N : ℕ) (hN : 0 < N),
      (CTMC.DensityDepCTMC.mk N hN Γ).BoundaryCompatibleOnSimplex)
    (hSolBound : ∀ t : ℝ, 0 ≤ t → ‖mf.sol t‖ ≤ 1)
    {T : ℝ} (hT : 0 < T)
    (ν : (N : ℕ) → PMF (Fin d → Fin (N + 1)))
    (hν_simplex : ∀ (N : ℕ) (hN : 0 < N) (x : Fin d → Fin (N + 1)),
      ν N x ≠ 0 → (CTMC.DensityDepCTMC.mk N hN Γ).InSimplex x)
    (hν : ∀ γ > 0, Filter.Tendsto
      (fun N => (ν N).toOuterMeasure
        {x | γ < ‖(fun i => (↑(x i) : ℝ) / ↑N) - mf.x₀‖})
      Filter.atTop (nhds 0))
    (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun N => if hN : 0 < N then
        randomInitRecordMeasure N hN Γ (ν N)
          {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
            ‖(CTMC.DensityDepCTMC.mk N hN Γ).frozenDensityProcess
                (CTMC.DensityDepCTMC.mk N hN Γ).canonicalPathMap t ω - mf.sol t‖ > ε}
        else 0)
      Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  by_cases htop : e = ⊤
  · exact Filter.Eventually.of_forall fun _ => htop ▸ le_top
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  have he2_top : e / 2 ≠ ⊤ := ENNReal.div_ne_top htop (by norm_num)
  set η := (e / 2).toReal with hη_def
  have hη : 0 < η := ENNReal.toReal_pos he2.ne' he2_top
  have hofη : ENNReal.ofReal η = e / 2 := ENNReal.ofReal_toReal he2_top
  obtain ⟨γ, hγ, N₀, hclose⟩ :=
    kurtz_finite_horizon_of_close Γ mf hConservative hBoundary hSolBound hT ε hε η hη
  have hfar := (ENNReal.tendsto_nhds_zero.1 (hν γ hγ)) (e / 2) he2
  filter_upwards [Filter.eventually_ge_atTop N₀, hfar] with N hN₀ hfarN
  split_ifs with hN
  swap
  · exact zero_le
  set E := {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
      ‖(CTMC.DensityDepCTMC.mk N hN Γ).frozenDensityProcess
          (CTMC.DensityDepCTMC.mk N hN Γ).canonicalPathMap t ω - mf.sol t‖ > ε}
  set F : Set (Fin d → Fin (N + 1)) :=
    {x | γ < ‖(fun i => (↑(x i) : ℝ) / ↑N) - mf.x₀‖}
  have hpoint : ∀ x : Fin d → Fin (N + 1),
      ν N x * (CTMC.DensityDepCTMC.mk N hN Γ).canonicalRecordMeasure x E ≤
        ν N x * (e / 2) + F.indicator (ν N) x := by
    intro x
    by_cases hx0 : ν N x = 0
    · simp [hx0]
    by_cases hxF : x ∈ F
    · rw [Set.indicator_of_mem hxF]
      calc ν N x * (CTMC.DensityDepCTMC.mk N hN Γ).canonicalRecordMeasure x E
          ≤ ν N x * 1 := by gcongr; exact prob_le_one
        _ = ν N x := mul_one _
        _ ≤ ν N x * (e / 2) + ν N x := le_add_self
    · rw [Set.indicator_of_notMem hxF, add_zero]
      have hle : ‖(fun i => (↑(x i) : ℝ) / ↑N) - mf.x₀‖ ≤ γ := not_lt.mp hxF
      have h := hclose N hN₀ hN x (hν_simplex N hN x hx0) hle
      rw [hofη] at h
      gcongr
  calc randomInitRecordMeasure N hN Γ (ν N) E
      = ∑ x, ν N x * (CTMC.DensityDepCTMC.mk N hN Γ).canonicalRecordMeasure x E := by
        simp [randomInitRecordMeasure, Finset.sum_apply]
    _ ≤ ∑ x, (ν N x * (e / 2) + F.indicator (ν N) x) := Finset.sum_le_sum fun x _ => hpoint x
    _ = (∑ x, ν N x) * (e / 2) + (ν N).toOuterMeasure F := by
        rw [Finset.sum_add_distrib, Finset.sum_mul, PMF.toOuterMeasure_apply, tsum_fintype]
    _ ≤ 1 * (e / 2) + e / 2 := by
        have h1 : ∑ x, ν N x = 1 := by simpa [tsum_fintype] using (ν N).tsum_coe
        rw [h1]
        exact add_le_add le_rfl hfarN
    _ = e := by rw [one_mul, ENNReal.add_halves]

end Kurtz
end Ripple
