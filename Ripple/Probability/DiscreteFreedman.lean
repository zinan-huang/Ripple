/-
  Ripple.Probability.DiscreteFreedman — Discrete-Time Freedman Inequality

  The core probabilistic theorem: for a discrete martingale with bounded
  increments and predictable quadratic variation control,
    P(∃ n ≤ N, X_n ≥ u and W_N ≤ v) ≤ exp(-u²/(2(v + cu/3)))

  Proof: exponential supermartingale Z_n = exp(λX_n - ψW_n) via
  Bernstein one-step + optional stopping.
-/

import Ripple.Probability.BennettLemma
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

namespace Ripple.Probability

open MeasureTheory Set Real
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory

noncomputable def prob {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : Set Ω) : ℝ :=
  (μ E).toReal

variable {Ω : Type*} {m0 : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0}

/-! ## Discrete Freedman hypothesis -/

/-- The hypothesis bundle for discrete Freedman's inequality.
    All the data needed: martingale + bounded increments + predictable QV domination. -/
structure DiscreteFreedmanHypothesis
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0)
    (X W : ℕ → Ω → ℝ) (c : ℝ) where
  martingale : Martingale X ℱ μ
  init_zero : X 0 =ᵐ[μ] 0
  increment_bound : ∀ n, ∀ᵐ ω ∂μ, |X (n + 1) ω - X n ω| ≤ c
  c_nonneg : 0 ≤ c
  W_adapted : StronglyAdapted ℱ W
  W_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ W n ω
  W_mono : ∀ n, ∀ᵐ ω ∂μ, W n ω ≤ W (n + 1) ω
  dW_predictable : ∀ n, StronglyMeasurable[ℱ n] (fun ω => W (n + 1) ω - W n ω)
  condvar_le_dW : ∀ n,
    μ[fun ω => (X (n + 1) ω - X n ω) ^ 2 | ℱ n] ≤ᵐ[μ] fun ω => W (n + 1) ω - W n ω

/-! ## Exponential process -/

noncomputable def freedmanExpProcess (X W : ℕ → Ω → ℝ) (t c : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  exp (t * X n ω - bernstein_psi t c * W n ω)

lemma bernstein_psi_nonneg {t c : ℝ} (ht : 0 ≤ t) (htc : t * c < 3) :
    0 ≤ bernstein_psi t c := by
  unfold bernstein_psi
  rw [if_pos ⟨htc, ht⟩]
  have hden : 0 < 2 * (1 - t * c / 3) := by nlinarith
  exact div_nonneg (sq_nonneg t) hden.le

lemma freedman_X_upper_ae
    {X W : ℕ → Ω → ℝ} {c : ℝ}
    (hyp : DiscreteFreedmanHypothesis μ ℱ X W c) :
    ∀ n, ∀ᵐ ω ∂μ, X n ω ≤ (n : ℝ) * c := by
  intro n
  induction n with
  | zero =>
      filter_upwards [hyp.init_zero] with ω h0
      simp [h0]
  | succ n ih =>
      filter_upwards [ih, hyp.increment_bound n] with ω hX hinc
      have hdiff : X (n + 1) ω - X n ω ≤ c := (le_abs_self _).trans hinc
      have hstep : X (n + 1) ω ≤ X n ω + c := by linarith
      have hbound : X (n + 1) ω ≤ (n : ℝ) * c + c := by linarith
      simpa [Nat.cast_succ, add_mul] using hbound

lemma freedmanExpProcess_stronglyAdapted
    {X W : ℕ → Ω → ℝ} {c t : ℝ}
    (hyp : DiscreteFreedmanHypothesis μ ℱ X W c) :
    StronglyAdapted ℱ (freedmanExpProcess X W t c) := by
  intro n
  unfold freedmanExpProcess
  have hX : StronglyMeasurable[ℱ n] (X n) := hyp.martingale.stronglyMeasurable n
  have hW : StronglyMeasurable[ℱ n] (W n) := hyp.W_adapted n
  fun_prop

lemma freedmanExpProcess_integrable
    {X W : ℕ → Ω → ℝ} {c t : ℝ}
    (hyp : DiscreteFreedmanHypothesis μ ℱ X W c)
    (ht : 0 ≤ t) (htc : t * c < 3) :
    ∀ n, Integrable (freedmanExpProcess X W t c n) μ := by
  intro n
  have hadp : StronglyAdapted ℱ (freedmanExpProcess X W t c) :=
    freedmanExpProcess_stronglyAdapted (μ := μ) (ℱ := ℱ) (t := t) hyp
  have hsm : StronglyMeasurable (freedmanExpProcess X W t c n) :=
    (hadp n).mono (ℱ.le n)
  refine Integrable.of_bound hsm.aestronglyMeasurable (exp (t * ((n : ℝ) * c))) ?_
  filter_upwards [freedman_X_upper_ae (μ := μ) (ℱ := ℱ) hyp n, hyp.W_nonneg n] with ω hX hW
  unfold freedmanExpProcess
  rw [Real.norm_eq_abs, abs_of_nonneg (exp_nonneg _)]
  rw [exp_le_exp]
  have hpsi : 0 ≤ bernstein_psi t c := bernstein_psi_nonneg ht htc
  have htX : t * X n ω ≤ t * ((n : ℝ) * c) :=
    mul_le_mul_of_nonneg_left hX ht
  have hWterm : -(bernstein_psi t c * W n ω) ≤ 0 := by
    have hmul : 0 ≤ bernstein_psi t c * W n ω := mul_nonneg hpsi hW
    linarith
  linarith

lemma freedman_increment_integrable
    {X W : ℕ → Ω → ℝ} {c : ℝ}
    (hyp : DiscreteFreedmanHypothesis μ ℱ X W c) (n : ℕ) :
    Integrable (fun ω => X (n + 1) ω - X n ω) μ :=
  (hyp.martingale.integrable (n + 1)).sub (hyp.martingale.integrable n)

lemma freedman_increment_sq_integrable
    {X W : ℕ → Ω → ℝ} {c : ℝ}
    (hyp : DiscreteFreedmanHypothesis μ ℱ X W c) (n : ℕ) :
    Integrable (fun ω => (X (n + 1) ω - X n ω) ^ 2) μ := by
  have hsm : StronglyMeasurable (fun ω => (X (n + 1) ω - X n ω) ^ 2) := by
    have hX1 : StronglyMeasurable (X (n + 1)) :=
      (hyp.martingale.stronglyMeasurable (n + 1)).mono (ℱ.le (n + 1))
    have hX0 : StronglyMeasurable (X n) :=
      (hyp.martingale.stronglyMeasurable n).mono (ℱ.le n)
    fun_prop
  refine Integrable.of_bound hsm.aestronglyMeasurable (c ^ 2) ?_
  filter_upwards [hyp.increment_bound n] with ω hd
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hd' : |X (n + 1) ω - X n ω| ≤ |c| := by
    simpa [abs_of_nonneg hyp.c_nonneg] using hd
  exact sq_le_sq.mpr hd'

lemma freedman_exp_increment_integrable
    {X W : ℕ → Ω → ℝ} {c t : ℝ}
    (hyp : DiscreteFreedmanHypothesis μ ℱ X W c)
    (ht : 0 ≤ t) (n : ℕ) :
    Integrable (fun ω => exp (t * (X (n + 1) ω - X n ω))) μ := by
  have hsm : StronglyMeasurable (fun ω => exp (t * (X (n + 1) ω - X n ω))) := by
    have hX1 : StronglyMeasurable (X (n + 1)) :=
      (hyp.martingale.stronglyMeasurable (n + 1)).mono (ℱ.le (n + 1))
    have hX0 : StronglyMeasurable (X n) :=
      (hyp.martingale.stronglyMeasurable n).mono (ℱ.le n)
    fun_prop
  refine Integrable.of_bound hsm.aestronglyMeasurable (exp (t * c)) ?_
  filter_upwards [hyp.increment_bound n] with ω hd
  rw [Real.norm_eq_abs, abs_of_nonneg (exp_nonneg _), exp_le_exp]
  have hdle : X (n + 1) ω - X n ω ≤ c := (le_abs_self _).trans hd
  exact mul_le_mul_of_nonneg_left hdle ht

lemma freedman_condExp_increment_eq_zero
    {X W : ℕ → Ω → ℝ} {c : ℝ}
    (hyp : DiscreteFreedmanHypothesis μ ℱ X W c) (n : ℕ) :
    μ[fun ω => X (n + 1) ω - X n ω | ℱ n] =ᵐ[μ] 0 := by
  change μ[X (n + 1) - X n | ℱ n] =ᵐ[μ] (0 : Ω → ℝ)
  have hsub := condExp_sub
    (hyp.martingale.integrable (n + 1)) (hyp.martingale.integrable n) (ℱ n)
  have hnext := hyp.martingale.condExp_ae_eq (Nat.le_succ n)
  have hcur := hyp.martingale.condExp_ae_eq (le_refl n)
  filter_upwards [hsub, hnext, hcur] with ω hsubω hnextω hcurω
  have hnextω' : μ[X (n + 1) | ℱ n] ω = X n ω := by
    change μ[X n.succ | ℱ n] ω = X n ω
    exact hnextω
  calc
    μ[X (n + 1) - X n | ℱ n] ω
        = (μ[X (n + 1) | ℱ n] - μ[X n | ℱ n]) ω := hsubω
    _ = μ[X (n + 1) | ℱ n] ω - μ[X n | ℱ n] ω := rfl
    _ = X n ω - X n ω := by rw [hnextω', hcurω]
    _ = (0 : Ω → ℝ) ω := by simp

lemma freedman_condExp_exp_increment_le
    {X W : ℕ → Ω → ℝ} {c t : ℝ}
    (hyp : DiscreteFreedmanHypothesis μ ℱ X W c)
    (ht : 0 ≤ t) (htc : t * c < 3) (n : ℕ) :
    μ[fun ω => exp (t * (X (n + 1) ω - X n ω)) | ℱ n]
      ≤ᵐ[μ] fun ω => 1 + bernstein_psi t c * (W (n + 1) ω - W n ω) := by
  let d : Ω → ℝ := fun ω => X (n + 1) ω - X n ω
  let q : Ω → ℝ := fun ω => d ω ^ 2
  let ψ : ℝ := bernstein_psi t c
  have hd_int : Integrable d μ := freedman_increment_integrable (μ := μ) (ℱ := ℱ) hyp n
  have hq_int : Integrable q μ := by
    simpa [q, d] using freedman_increment_sq_integrable (μ := μ) (ℱ := ℱ) hyp n
  have hexp_int : Integrable (fun ω => exp (t * d ω)) μ := by
    simpa [d] using freedman_exp_increment_integrable (μ := μ) (ℱ := ℱ) hyp ht n
  have hpoly_int : Integrable (fun ω => 1 + (t * d ω + ψ * q ω)) μ :=
    (integrable_const (1 : ℝ)).add ((hd_int.const_mul t).add (hq_int.const_mul ψ))
  have hbern :
      (fun ω => exp (t * d ω)) ≤ᵐ[μ]
        fun ω => 1 + (t * d ω + ψ * q ω) := by
    filter_upwards [hyp.increment_bound n] with ω hd
    have h := bernstein_one_step (d := d ω) (c := c) (t := t) hd hyp.c_nonneg ht htc
    simp [q, ψ]
    linarith
  have hmono :
      μ[fun ω => exp (t * d ω) | ℱ n]
        ≤ᵐ[μ] μ[fun ω => 1 + (t * d ω + ψ * q ω) | ℱ n] :=
    condExp_mono hexp_int hpoly_int hbern
  have hd0 : μ[d | ℱ n] =ᵐ[μ] 0 := by
    simpa [d] using freedman_condExp_increment_eq_zero (μ := μ) (ℱ := ℱ) hyp n
  have hψ_nonneg : 0 ≤ ψ := by
    simpa [ψ] using bernstein_psi_nonneg ht htc
  have hpoly_ce :
      μ[fun ω => 1 + (t * d ω + ψ * q ω) | ℱ n]
        ≤ᵐ[μ] fun ω => 1 + ψ * (W (n + 1) ω - W n ω) := by
    change
      μ[(fun _ : Ω => (1 : ℝ)) + ((fun ω => t * d ω) + fun ω => ψ * q ω) | ℱ n]
        ≤ᵐ[μ] fun ω => 1 + ψ * (W (n + 1) ω - W n ω)
    have hconst : μ[fun _ : Ω => (1 : ℝ) | ℱ n] = fun _ : Ω => (1 : ℝ) :=
      condExp_const (ℱ.le n) (1 : ℝ)
    have hsum := condExp_add ((integrable_const (1 : ℝ)) : Integrable (fun _ : Ω => (1 : ℝ)) μ)
      ((hd_int.const_mul t).add (hq_int.const_mul ψ)) (ℱ n)
    have hsum2 := condExp_add (hd_int.const_mul t) (hq_int.const_mul ψ) (ℱ n)
    have ht_d : μ[fun ω => t * d ω | ℱ n] =ᵐ[μ] fun ω => t * μ[d | ℱ n] ω := by
      simpa [Pi.smul_apply] using condExp_smul (μ := μ) t d (ℱ n)
    have hψ_q : μ[fun ω => ψ * q ω | ℱ n] =ᵐ[μ] fun ω => ψ * μ[q | ℱ n] ω := by
      simpa [Pi.smul_apply] using condExp_smul (μ := μ) ψ q (ℱ n)
    have hq_le :
        μ[q | ℱ n] ≤ᵐ[μ] fun ω => W (n + 1) ω - W n ω := by
      simpa [q, d] using hyp.condvar_le_dW n
    filter_upwards [hsum, hsum2, ht_d, hψ_q, hd0, hq_le] with
      ω hsumω hsum2ω ht_dω hψ_qω hd0ω hq_leω
    have hmul : ψ * μ[q | ℱ n] ω ≤ ψ * (W (n + 1) ω - W n ω) :=
      mul_le_mul_of_nonneg_left hq_leω hψ_nonneg
    calc
      μ[(fun _ : Ω => (1 : ℝ)) + ((fun ω => t * d ω) + fun ω => ψ * q ω) | ℱ n] ω
          = (μ[fun _ : Ω => (1 : ℝ) | ℱ n] +
              μ[(fun ω => t * d ω) + fun ω => ψ * q ω | ℱ n]) ω := hsumω
      _ = μ[fun _ : Ω => (1 : ℝ) | ℱ n] ω +
            μ[(fun ω => t * d ω) + fun ω => ψ * q ω | ℱ n] ω := rfl
      _ = μ[fun _ : Ω => (1 : ℝ) | ℱ n] ω +
            (μ[fun ω => t * d ω | ℱ n] ω + μ[fun ω => ψ * q ω | ℱ n] ω) := by
              rw [hsum2ω]
              simp only [Pi.add_apply]
      _ = 1 + (t * μ[d | ℱ n] ω + ψ * μ[q | ℱ n] ω) := by
              rw [hconst, ht_dω, hψ_qω]
      _ = 1 + ψ * μ[q | ℱ n] ω := by
              rw [hd0ω]
              simp
      _ ≤ 1 + ψ * (W (n + 1) ω - W n ω) := by linarith
  simpa [d, ψ] using hmono.trans hpoly_ce

/-! ## Core: exponential supermartingale -/

theorem freedmanExpProcess_supermartingale
    {X W : ℕ → Ω → ℝ} {c : ℝ}
    (hyp : DiscreteFreedmanHypothesis μ ℱ X W c)
    {t : ℝ} (ht : 0 ≤ t) (htc : t * c < 3) :
    Supermartingale (freedmanExpProcess X W t c) ℱ μ := by
  refine supermartingale_nat
    (freedmanExpProcess_stronglyAdapted (μ := μ) (ℱ := ℱ) (t := t) hyp)
    (freedmanExpProcess_integrable (μ := μ) (ℱ := ℱ) hyp ht htc) ?_
  intro n
  let ψ : ℝ := bernstein_psi t c
  let d : Ω → ℝ := fun ω => X (n + 1) ω - X n ω
  let ΔW : Ω → ℝ := fun ω => W (n + 1) ω - W n ω
  let A : Ω → ℝ := fun ω => freedmanExpProcess X W t c n ω * exp (-(ψ * ΔW ω))
  have hA_sm : StronglyMeasurable[ℱ n] A := by
    have hZ : StronglyMeasurable[ℱ n] (freedmanExpProcess X W t c n) :=
      freedmanExpProcess_stronglyAdapted (μ := μ) (ℱ := ℱ) (t := t) hyp n
    have hΔW : StronglyMeasurable[ℱ n] ΔW := by
      simpa [ΔW] using hyp.dW_predictable n
    dsimp [A, ψ]
    fun_prop
  have hexp_int : Integrable (fun ω => exp (t * d ω)) μ := by
    simpa [d] using freedman_exp_increment_integrable (μ := μ) (ℱ := ℱ) hyp ht n
  have hZ_eq :
      freedmanExpProcess X W t c (n + 1) =ᵐ[μ]
        fun ω => A ω * exp (t * d ω) := by
    refine ae_of_all μ ?_
    intro ω
    dsimp [A, d, ΔW, ψ, freedmanExpProcess]
    rw [← exp_add, ← exp_add]
    congr 1
    ring
  have hAexp_int : Integrable (fun ω => A ω * exp (t * d ω)) μ :=
    (freedmanExpProcess_integrable (μ := μ) (ℱ := ℱ) hyp ht htc (n + 1)).congr hZ_eq
  have hpull :
      μ[fun ω => A ω * exp (t * d ω) | ℱ n]
        =ᵐ[μ] fun ω => A ω * μ[fun ω => exp (t * d ω) | ℱ n] ω :=
    condExp_mul_of_stronglyMeasurable_left hA_sm hAexp_int hexp_int
  have hce :
      μ[freedmanExpProcess X W t c (n + 1) | ℱ n]
        =ᵐ[μ] fun ω => A ω * μ[fun ω => exp (t * d ω) | ℱ n] ω :=
    (condExp_congr_ae hZ_eq).trans hpull
  have hmgf :
      μ[fun ω => exp (t * d ω) | ℱ n]
        ≤ᵐ[μ] fun ω => 1 + ψ * ΔW ω := by
    simpa [d, ΔW, ψ] using
      freedman_condExp_exp_increment_le (μ := μ) (ℱ := ℱ) hyp ht htc n
  have hψ_nonneg : 0 ≤ ψ := by
    simpa [ψ] using bernstein_psi_nonneg ht htc
  filter_upwards [hce, hmgf, hyp.W_mono n] with ω hceω hmgfω hWmonoω
  rw [hceω]
  have hΔW_nonneg : 0 ≤ ΔW ω := by
    dsimp [ΔW]
    linarith
  have hψΔW_nonneg : 0 ≤ ψ * ΔW ω := mul_nonneg hψ_nonneg hΔW_nonneg
  have hA_nonneg : 0 ≤ A ω := by
    dsimp [A, freedmanExpProcess]
    positivity
  have hmul_mgf :
      A ω * μ[fun ω => exp (t * d ω) | ℱ n] ω
        ≤ A ω * (1 + ψ * ΔW ω) :=
    mul_le_mul_of_nonneg_left hmgfω hA_nonneg
  have hscalar : exp (-(ψ * ΔW ω)) * (1 + ψ * ΔW ω) ≤ 1 :=
    exp_neg_mul_one_add_le_one hψΔW_nonneg
  calc
    A ω * μ[fun ω => exp (t * d ω) | ℱ n] ω
        ≤ A ω * (1 + ψ * ΔW ω) := hmul_mgf
    _ = freedmanExpProcess X W t c n ω *
          (exp (-(ψ * ΔW ω)) * (1 + ψ * ΔW ω)) := by
            dsimp [A]
            ring
    _ ≤ freedmanExpProcess X W t c n ω * 1 := by
            exact mul_le_mul_of_nonneg_left hscalar (exp_nonneg _)
    _ = freedmanExpProcess X W t c n ω := by simp

lemma freedman_W_mono_le_ae
    {X W : ℕ → Ω → ℝ} {c : ℝ}
    (hyp : DiscreteFreedmanHypothesis μ ℱ X W c) :
    ∀ N, ∀ᵐ ω ∂μ, ∀ n, n ≤ N → W n ω ≤ W N ω := by
  intro N
  induction N with
  | zero =>
      exact ae_of_all μ fun ω n hn => by
        have hn0 : n = 0 := by omega
        simp [hn0]
  | succ N ih =>
      filter_upwards [ih, hyp.W_mono N] with ω hih hstep n hn
      by_cases hnN : n ≤ N
      · exact (hih n hnN).trans hstep
      · have hn_eq : n = N + 1 := by omega
        simp [hn_eq]

lemma Supermartingale.integral_stoppedValue_le_initial
    {Z : ℕ → Ω → ℝ} (hZ : Supermartingale Z ℱ μ)
    {τ : Ω → ℕ∞} (hτ : IsStoppingTime ℱ τ)
    {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N)
    (hzero_le : (fun _ : Ω => (0 : ℕ∞)) ≤ τ) :
    ∫ ω, stoppedValue Z τ ω ∂μ ≤ ∫ ω, Z 0 ω ∂μ := by
  have hopt := hZ.neg.expected_stoppedValue_mono
    (isStoppingTime_const ℱ 0) hτ hzero_le hbdd
  have hconst :
      stoppedValue (-Z) (fun _ : Ω => ((0 : ℕ) : ℕ∞)) = (-Z) 0 :=
    stoppedValue_const (-Z) 0
  have hstop_neg :
      stoppedValue (-Z) τ = fun ω => -stoppedValue Z τ ω := by
    ext ω
    simp [stoppedValue]
  have hopt' :
      ∫ ω, (-Z) 0 ω ∂μ ≤ ∫ ω, -stoppedValue Z τ ω ∂μ := by
    convert hopt using 1
  simp only [Pi.neg_apply] at hopt'
  rw [integral_neg, integral_neg] at hopt'
  linarith

lemma discrete_freedman_exp_tail
    {X W : ℕ → Ω → ℝ} {c : ℝ}
    (hyp : DiscreteFreedmanHypothesis μ ℱ X W c)
    {u v t : ℝ} (_hu : 0 < u) (_hv : 0 ≤ v)
    (ht : 0 ≤ t) (htc : t * c < 3)
    {N : ℕ} :
    prob μ {ω | (∃ n, n ≤ N ∧ u ≤ X n ω) ∧ W N ω ≤ v}
      ≤ exp (bernstein_psi t c * v - t * u) := by
  let ψ : ℝ := bernstein_psi t c
  let Z : ℕ → Ω → ℝ := freedmanExpProcess X W t c
  let E : Set Ω := {ω | (∃ n, n ≤ N ∧ u ≤ X n ω) ∧ W N ω ≤ v}
  let a : ℝ := exp (t * u - ψ * v)
  let τ : Ω → ℕ∞ := fun ω => ((hittingBtwn Z (Ici a) (0 : ℕ) N ω : ℕ) : ℕ∞)
  have hψ_nonneg : 0 ≤ ψ := by
    simpa [ψ] using bernstein_psi_nonneg ht htc
  have hZsuper : Supermartingale Z ℱ μ := by
    simpa [Z] using freedmanExpProcess_supermartingale (μ := μ) (ℱ := ℱ) hyp ht htc
  have hX_meas : ∀ n, Measurable (X n) := by
    intro n
    exact ((hyp.martingale.stronglyMeasurable n).mono (ℱ.le n)).measurable
  have hW_meas : Measurable (W N) :=
    ((hyp.W_adapted N).mono (ℱ.le N)).measurable
  have hhit_meas : MeasurableSet {ω | ∃ n, n ≤ N ∧ u ≤ X n ω} := by
    rw [show {ω : Ω | ∃ n, n ≤ N ∧ u ≤ X n ω} =
        (⋃ n : ℕ, {ω : Ω | n ≤ N ∧ u ≤ X n ω}) by
      ext ω
      simp]
    refine MeasurableSet.iUnion fun n => ?_
    by_cases hn : n ≤ N
    · simpa [hn] using measurableSet_le measurable_const (hX_meas n)
    · have hempty : {ω : Ω | n ≤ N ∧ u ≤ X n ω} = ∅ := by
        ext ω
        simp [hn]
      rw [hempty]
      exact MeasurableSet.empty
  have hE_meas : MeasurableSet E := by
    dsimp [E]
    exact hhit_meas.inter (measurableSet_le hW_meas measurable_const)
  have hτ : IsStoppingTime ℱ τ := by
    dsimp [τ]
    exact hZsuper.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hbdd : ∀ ω, τ ω ≤ N := by
    intro ω
    dsimp [τ]
    exact_mod_cast hittingBtwn_le (u := Z) (s := Ici a) (n := 0) (m := N) ω
  have hzero_le : (fun _ : Ω => (0 : ℕ∞)) ≤ τ := by
    intro ω
    dsimp [τ]
    exact_mod_cast le_hittingBtwn (u := Z) (s := Ici a) (n := 0) (m := N) (Nat.zero_le N) ω
  have hZτ_int : Integrable (stoppedValue Z τ) μ :=
    integrable_stoppedValue ℕ hτ hZsuper.integrable hbdd
  have hZτ_nonneg : 0 ≤ᵐ[μ] stoppedValue Z τ := by
    refine ae_of_all μ ?_
    intro ω
    dsimp [Z, freedmanExpProcess, stoppedValue]
    exact exp_nonneg _
  have hstop_le :
      ∫ ω, stoppedValue Z τ ω ∂μ ≤ ∫ ω, Z 0 ω ∂μ :=
    Supermartingale.integral_stoppedValue_le_initial hZsuper hτ hbdd hzero_le
  have hZ0_le_one : (∫ ω, Z 0 ω ∂μ) ≤ 1 := by
    have hpoint : Z 0 ≤ᵐ[μ] fun _ : Ω => (1 : ℝ) := by
      filter_upwards [hyp.init_zero, hyp.W_nonneg 0] with ω hX0 hW0
      dsimp [Z, freedmanExpProcess, ψ]
      rw [hX0]
      simp only [Pi.zero_apply, mul_zero]
      rw [← exp_zero, exp_le_exp]
      have hmul : 0 ≤ bernstein_psi t c * W 0 ω := mul_nonneg hψ_nonneg hW0
      linarith
    have hint1 : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const (1 : ℝ)
    have h := integral_mono_ae (hZsuper.integrable 0) hint1 hpoint
    rw [integral_const, probReal_univ] at h
    simpa using h
  have ha_pos : 0 < a := by
    dsimp [a]
    exact exp_pos _
  have hlower_ae :
      ∀ᵐ ω ∂μ, ω ∈ E → a ≤ stoppedValue Z τ ω := by
    filter_upwards [freedman_W_mono_le_ae (μ := μ) (ℱ := ℱ) hyp N] with ω hWle hωE
    rcases hωE with ⟨⟨n, hnN, hXn⟩, hWN⟩
    have hWnv : W n ω ≤ v := (hWle n hnN).trans hWN
    have hZn : a ≤ Z n ω := by
      dsimp [a, Z, freedmanExpProcess, ψ]
      rw [exp_le_exp]
      have htu : t * u ≤ t * X n ω := mul_le_mul_of_nonneg_left hXn ht
      have hψW : bernstein_psi t c * W n ω ≤ bernstein_psi t c * v :=
        mul_le_mul_of_nonneg_left hWnv hψ_nonneg
      linarith
    have hhit : ∃ j ∈ Icc 0 N, Z j ω ∈ Ici a :=
      ⟨n, ⟨Nat.zero_le n, hnN⟩, hZn⟩
    simpa [τ] using stoppedValue_hittingBtwn_mem (u := Z) (s := Ici a) hhit
  have hconst_int : IntegrableOn (fun _ : Ω => a) E μ :=
    (integrable_const a).integrableOn
  have hstop_int_on : IntegrableOn (stoppedValue Z τ) E μ :=
    hZτ_int.integrableOn
  have hconst_le :
      a * μ.real E ≤ ∫ ω in E, stoppedValue Z τ ω ∂μ := by
    have hmono := setIntegral_mono_on_ae hconst_int hstop_int_on hE_meas hlower_ae
    rw [setIntegral_const] at hmono
    simpa [smul_eq_mul, mul_comm] using hmono
  have hset_le :
      ∫ ω in E, stoppedValue Z τ ω ∂μ ≤ ∫ ω, stoppedValue Z τ ω ∂μ :=
    setIntegral_le_integral hZτ_int hZτ_nonneg
  have hmul_prob : a * μ.real E ≤ 1 :=
    hconst_le.trans (hset_le.trans (hstop_le.trans hZ0_le_one))
  have hprob_inv : μ.real E ≤ a⁻¹ := by
    rw [show a⁻¹ = a⁻¹ * (1 : ℝ) by ring]
    exact (le_inv_mul_iff₀ ha_pos).2 hmul_prob
  have hainv : a⁻¹ = exp (ψ * v - t * u) := by
    dsimp [a]
    rw [← exp_neg]
    congr 1
    ring
  simpa [prob, E, ψ, hainv] using hprob_inv

/-! ## Discrete Freedman theorem -/

theorem discrete_freedman
    {X W : ℕ → Ω → ℝ} {c : ℝ}
    (hyp : DiscreteFreedmanHypothesis μ ℱ X W c)
    {u v : ℝ} (hu : 0 < u) (hv : 0 ≤ v)
    {N : ℕ} :
    prob μ {ω | (∃ n, n ≤ N ∧ u ≤ X n ω) ∧ W N ω ≤ v}
      ≤ exp (-(u ^ 2) / (2 * (v + c * u / 3))) := by
  by_cases hv_pos : 0 < v
  · let t : ℝ := u / (v + c * u / 3)
    have hden_pos : 0 < v + c * u / 3 := by
      have hcu : 0 ≤ c * u / 3 := div_nonneg (mul_nonneg hyp.c_nonneg hu.le) (by norm_num)
      linarith
    have ht : 0 ≤ t := by
      dsimp [t]
      exact div_nonneg hu.le hden_pos.le
    have htc : t * c < 3 := by
      dsimp [t]
      rw [div_mul_eq_mul_div]
      rw [div_lt_iff₀ hden_pos]
      nlinarith
    have htail :=
      discrete_freedman_exp_tail (μ := μ) (ℱ := ℱ) hyp hu hv ht htc (N := N)
    have hopt :
        bernstein_psi t c * v - t * u =
          -(u ^ 2) / (2 * (v + c * u / 3)) := by
      simpa [t] using bernstein_optimal (u := u) (v := v) (c := c) hu hv_pos hyp.c_nonneg
    exact htail.trans_eq (by rw [hopt])
  · have hv_eq : v = 0 := by
      exact le_antisymm (le_of_not_gt hv_pos) hv
    by_cases hc_pos : 0 < c
    · let t : ℝ := 3 / (2 * c)
      have ht : 0 ≤ t := by
        dsimp [t]
        exact div_nonneg (by norm_num) (mul_nonneg (by norm_num) hc_pos.le)
      have htc : t * c < 3 := by
        dsimp [t]
        field_simp [hc_pos.ne']
        norm_num
      have htail :=
        discrete_freedman_exp_tail (μ := μ) (ℱ := ℱ) hyp hu hv ht htc (N := N)
      have hopt :
          bernstein_psi t c * v - t * u =
            -(u ^ 2) / (2 * (v + c * u / 3)) := by
        rw [hv_eq]
        dsimp [t]
        simp only [mul_zero, zero_sub, zero_add]
        field_simp [hc_pos.ne', hu.ne']
      exact htail.trans_eq (by rw [hopt])
    · have hc_eq : c = 0 := by
        exact le_antisymm (le_of_not_gt hc_pos) hyp.c_nonneg
      have hprob_le_one :
          prob μ {ω | (∃ n, n ≤ N ∧ u ≤ X n ω) ∧ W N ω ≤ v} ≤ 1 := by
        unfold prob
        exact measureReal_le_one
      simpa [hv_eq, hc_eq] using hprob_le_one

end Ripple.Probability
