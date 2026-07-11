/-
  Ripple.Kurtz.Defs — Density-Dependent Markov Chains and Kurtz's Theorem

  Formalizes the setting of Kurtz (1970, 1978):
    - Density-dependent continuous-time Markov chains on ℤ_≥0^d
    - Transition rates q^N(x, x+ℓ) = N · β_ℓ(x/N)
    - Drift function F(x) = Σ_ℓ ℓ · β_ℓ(x)
    - Mean-field convergence: X̄^N(t) → x(t) where x'(t) = F(x(t))

  The CTMC infrastructure lives in `Ripple.CTMC`. This file keeps the
  analytic interface used by the Kurtz proof: a random density process with
  martingale decomposition and quadratic-variation estimates.

  References:
  - T. G. Kurtz, "Solutions of ODEs as limits of pure jump Markov
    processes," J. Appl. Prob. 7(1):49–58, 1970.
  - T. G. Kurtz, "Strong approximation theorems for density dependent
    Markov chains," Stoch. Proc. Appl. 6(3):223–240, 1978.
  - Anderson-Kurtz, "Stochastic Analysis of Biochemical Systems,"
    Springer, 2015.
-/

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Probability.Martingale.Basic
import Ripple.Core.PIVP

namespace Ripple.Kurtz

open MeasureTheory MeasureTheory.Measure Topology

/-- Sup-norm squared is bounded by the sum of coordinate squares on finite
real vector spaces.  This is the deterministic reduction used to combine
coordinatewise martingale estimates into the vector-valued bound. -/
theorem vector_norm_sq_le_sum_sq {d : ℕ} (v : Fin d → ℝ) :
    ‖v‖ ^ 2 ≤ ∑ i, (v i) ^ 2 := by
  let S : ℝ := ∑ i, (v i) ^ 2
  have hS_nonneg : 0 ≤ S := by
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hnorm_le_sqrt : ‖v‖ ≤ Real.sqrt S := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg S)]
    intro i
    rw [Real.norm_eq_abs]
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  have hnorm_nonneg : 0 ≤ ‖v‖ := norm_nonneg _
  have hsqrt_nonneg : 0 ≤ Real.sqrt S := Real.sqrt_nonneg S
  have hsquare : ‖v‖ ^ 2 ≤ (Real.sqrt S) ^ 2 := by
    nlinarith
  simpa [S, Real.sq_sqrt hS_nonneg] using hsquare

/-- A finite-horizon supremum of vector norm-squares is bounded by the sum of
coordinatewise finite-horizon suprema. -/
theorem vector_timeSup_norm_sq_le_sum_coord_timeSup_sq {d : ℕ}
    (f : ℝ → Fin d → ℝ) {T : ℝ} (_hT : 0 ≤ T)
    (hbound : ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ T → ‖f t‖ ≤ C) :
    (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), ‖f t‖ ^ 2) ≤
      ∑ i, ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), (f t i) ^ 2 := by
  obtain ⟨C₀, hC₀⟩ := hbound
  let C : ℝ := max C₀ 0
  have hC_nonneg : 0 ≤ C := le_max_right C₀ 0
  have hC : ∀ t : ℝ, 0 ≤ t → t ≤ T → ‖f t‖ ≤ C := by
    intro t ht0 htT
    exact (hC₀ t ht0 htT).trans (le_max_left C₀ 0)
  have hcoord_inner_bdd (i : Fin d) (t : ℝ) :
      BddAbove (Set.range fun _ : 0 ≤ t ∧ t ≤ T => (f t i) ^ 2) := by
    refine ⟨C ^ 2, ?_⟩
    rintro y ⟨ht, rfl⟩
    have hcoord_norm : ‖f t i‖ ≤ C :=
      (norm_le_pi_norm (f t) i).trans (hC t ht.1 ht.2)
    rw [Real.norm_eq_abs] at hcoord_norm
    rw [← sq_abs]
    exact sq_le_sq' (by nlinarith [hC_nonneg, abs_nonneg (f t i)]) hcoord_norm
  have hcoord_outer_bdd (i : Fin d) :
      BddAbove (Set.range fun t : ℝ =>
        ⨆ (_ : 0 ≤ t ∧ t ≤ T), (f t i) ^ 2) := by
    refine ⟨C ^ 2, ?_⟩
    rintro y ⟨t, rfl⟩
    exact Real.iSup_le (fun ht => by
      have hcoord_norm : ‖f t i‖ ≤ C :=
        (norm_le_pi_norm (f t) i).trans (hC t ht.1 ht.2)
      rw [Real.norm_eq_abs] at hcoord_norm
      rw [← sq_abs]
      exact sq_le_sq' (by nlinarith [hC_nonneg, abs_nonneg (f t i)]) hcoord_norm)
      (sq_nonneg C)
  have hcoord_le (i : Fin d) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ T) :
      (f t i) ^ 2 ≤ ⨆ (u : ℝ) (_ : 0 ≤ u ∧ u ≤ T), (f u i) ^ 2 := by
    exact le_trans (le_ciSup (hcoord_inner_bdd i t) ht)
      (le_ciSup (hcoord_outer_bdd i) t)
  refine Real.iSup_le ?_ (by
    exact Finset.sum_nonneg fun i _ =>
      Real.iSup_nonneg fun t => Real.iSup_nonneg fun _ => sq_nonneg (f t i))
  intro t
  refine Real.iSup_le ?_ (by
    exact Finset.sum_nonneg fun i _ =>
      Real.iSup_nonneg fun u => Real.iSup_nonneg fun _ => sq_nonneg (f u i))
  intro ht
  calc
    ‖f t‖ ^ 2 ≤ ∑ i, (f t i) ^ 2 := vector_norm_sq_le_sum_sq (f t)
    _ ≤ ∑ i, ⨆ (u : ℝ) (_ : 0 ≤ u ∧ u ≤ T), (f u i) ^ 2 := by
      exact Finset.sum_le_sum fun i _ => hcoord_le i t ht

/-! ## Density-dependent rate functions

The jump directions ℓ ∈ ℤ^d are finitely many, each with a Lipschitz
rate function β_ℓ : ℝ_≥0^d → ℝ_≥0. -/

/-- A density-dependent rate specification: finitely many jump directions,
each with a Lipschitz rate function. -/
structure RateSpec (d : ℕ) where
  /-- The finite set of jump directions. -/
  jumps : Finset (Fin d → ℤ)
  /-- Rate function for each jump direction. -/
  rate : (Fin d → ℤ) → (Fin d → ℝ) → ℝ
  /-- Rates are non-negative on the non-negative orthant. -/
  rate_nonneg : ∀ ℓ ∈ jumps, ∀ x : Fin d → ℝ,
    (∀ i, 0 ≤ x i) → 0 ≤ rate ℓ x
  /-- Only listed jumps have nonzero rates. -/
  rate_support : ∀ ℓ, ℓ ∉ jumps → rate ℓ = 0
  /-- Rates are Lipschitz on bounded sets. -/
  rate_lipschitz : ∀ ℓ ∈ jumps, ∀ R > 0, ∃ L > 0,
    ∀ x y : Fin d → ℝ, ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖rate ℓ x - rate ℓ y‖ ≤ L * ‖x - y‖

namespace RateSpec

variable {d : ℕ} (Γ : RateSpec d)

/-- The drift function F(x) = Σ_ℓ ℓ · β_ℓ(x).
This is the vector field of the limiting ODE x'(t) = F(x(t)). -/
noncomputable def drift (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => ∑ ℓ ∈ Γ.jumps, (ℓ i : ℝ) * Γ.rate ℓ x

/-- The drift is Lipschitz on bounded sets.
This is the key regularity needed for Picard-Lindelöf. -/
theorem drift_lipschitz_on_ball (R : ℝ) (hR : 0 < R) :
    ∃ L > 0, ∀ x y : Fin d → ℝ, ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖Γ.drift x - Γ.drift y‖ ≤ L * ‖x - y‖ := by
  have h_each : ∀ p ∈ Γ.jumps.attach, ∃ Lℓ > 0,
      ∀ x y : Fin d → ℝ, ‖x‖ ≤ R → ‖y‖ ≤ R →
        |Γ.rate p.1 x - Γ.rate p.1 y| ≤ Lℓ * ‖x - y‖ := by
    intro ⟨ℓ, hℓ⟩ _
    obtain ⟨Lℓ, hpos, hbd⟩ := Γ.rate_lipschitz ℓ hℓ R hR
    exact ⟨Lℓ, hpos, fun x y hx hy => by
      have := hbd x y hx hy; rwa [Real.norm_eq_abs] at this⟩
  choose Lip hLip_pos hLip_bd using h_each
  set S := ∑ p ∈ Γ.jumps.attach,
    ‖(fun i => (p.1 i : ℝ))‖ * Lip p (Finset.mem_attach _ _)
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun p _ =>
    mul_nonneg (norm_nonneg _) (le_of_lt (hLip_pos p (Finset.mem_attach _ _)))
  refine ⟨S + 1, by linarith, ?_⟩
  intro x y hx hy
  apply (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ (S + 1) * ‖x - y‖)).mpr
  intro i
  change |Γ.drift x i - Γ.drift y i| ≤ (S + 1) * ‖x - y‖
  simp only [drift]
  rw [show (∑ ℓ ∈ Γ.jumps, (ℓ i : ℝ) * Γ.rate ℓ x) -
      (∑ ℓ ∈ Γ.jumps, (ℓ i : ℝ) * Γ.rate ℓ y) =
      ∑ ℓ ∈ Γ.jumps, (ℓ i : ℝ) * (Γ.rate ℓ x - Γ.rate ℓ y) from by
    simp [Finset.sum_sub_distrib, mul_sub]]
  rw [← Finset.sum_attach]
  have step1 : |∑ p ∈ Γ.jumps.attach,
      (p.1 i : ℝ) * (Γ.rate p.1 x - Γ.rate p.1 y)| ≤ S * ‖x - y‖ := by
    calc |∑ p ∈ Γ.jumps.attach, (p.1 i : ℝ) * (Γ.rate p.1 x - Γ.rate p.1 y)|
        ≤ ∑ p ∈ Γ.jumps.attach, |(p.1 i : ℝ)| * |Γ.rate p.1 x - Γ.rate p.1 y| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          gcongr with p _; exact le_of_eq (abs_mul _ _)
      _ ≤ ∑ p ∈ Γ.jumps.attach,
            ‖(fun j => (p.1 j : ℝ))‖ * (Lip p (Finset.mem_attach _ _) * ‖x - y‖) := by
          apply Finset.sum_le_sum; intro p _
          apply mul_le_mul
          · exact norm_le_pi_norm (fun j => (p.1 j : ℝ)) i
          · exact hLip_bd p (Finset.mem_attach _ _) x y hx hy
          · exact abs_nonneg _
          · exact norm_nonneg _
      _ = S * ‖x - y‖ := by
          rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro p _; ring
  linarith [norm_nonneg (x - y)]

/-- A finite deterministic bound on jump vector norms.  This deliberately uses
the sum of norms rather than a maximum, because it is easy to use with
`Finset.single_le_sum` and is sufficient for the CTMC QV estimates. -/
noncomputable def jumpNormBound : ℝ :=
  ∑ ℓ ∈ Γ.jumps, ‖(fun i => (ℓ i : ℝ))‖

theorem jumpNormBound_nonneg : 0 ≤ Γ.jumpNormBound :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem jump_norm_le_bound {ℓ : Fin d → ℤ} (hℓ : ℓ ∈ Γ.jumps) :
    ‖(fun i => (ℓ i : ℝ))‖ ≤ Γ.jumpNormBound := by
  exact Finset.single_le_sum
    (f := fun ℓ : Fin d → ℤ => ‖(fun i : Fin d => (ℓ i : ℝ))‖)
    (fun _ _ => norm_nonneg _) hℓ

/-- Uniform rate bound on a bounded ball for all listed jumps. -/
theorem exists_rate_bound_on_ball (R : ℝ) (hR : 0 < R) :
    ∃ B > 0, ∀ ℓ ∈ Γ.jumps, ∀ x : Fin d → ℝ, ‖x‖ ≤ R →
      |Γ.rate ℓ x| ≤ B := by
  have h_each : ∀ ℓ ∈ Γ.jumps, ∃ Bp > 0,
      ∀ x : Fin d → ℝ, ‖x‖ ≤ R → |Γ.rate ℓ x| ≤ Bp := by
    intro ℓ hℓ
    obtain ⟨L, hLpos, hLip⟩ := Γ.rate_lipschitz ℓ hℓ R hR
    refine ⟨|Γ.rate ℓ 0| + L * R + 1, by positivity, ?_⟩
    intro x hx
    have h0 : ‖(0 : Fin d → ℝ)‖ ≤ R := by
      rw [norm_zero]
      exact le_of_lt hR
    have hdist := hLip x 0 hx h0
    rw [Real.norm_eq_abs] at hdist
    calc
      |Γ.rate ℓ x| = |(Γ.rate ℓ x - Γ.rate ℓ 0) + Γ.rate ℓ 0| := by ring_nf
      _ ≤ |Γ.rate ℓ x - Γ.rate ℓ 0| + |Γ.rate ℓ 0| := abs_add_le _ _
      _ ≤ L * ‖x - 0‖ + |Γ.rate ℓ 0| := by gcongr
      _ ≤ L * R + |Γ.rate ℓ 0| := by
        gcongr
        simpa using hx
      _ ≤ |Γ.rate ℓ 0| + L * R + 1 := by linarith
  let Bp : (Fin d → ℤ) → ℝ :=
    fun ℓ => if hℓ : ℓ ∈ Γ.jumps then Classical.choose (h_each ℓ hℓ) else 0
  have hBp_pos : ∀ ℓ (hℓ : ℓ ∈ Γ.jumps), 0 < Bp ℓ := by
    intro ℓ hℓ
    dsimp [Bp]
    rw [dif_pos hℓ]
    exact (Classical.choose_spec (h_each ℓ hℓ)).1
  have hBp_bound : ∀ ℓ (hℓ : ℓ ∈ Γ.jumps), ∀ x : Fin d → ℝ, ‖x‖ ≤ R →
      |Γ.rate ℓ x| ≤ Bp ℓ := by
    intro ℓ hℓ x hx
    dsimp [Bp]
    rw [dif_pos hℓ]
    exact (Classical.choose_spec (h_each ℓ hℓ)).2 x hx
  refine ⟨(∑ ℓ ∈ Γ.jumps, Bp ℓ) + 1, ?_, ?_⟩
  · have hsum_nonneg : 0 ≤ ∑ ℓ ∈ Γ.jumps, Bp ℓ :=
      Finset.sum_nonneg fun ℓ hℓ => le_of_lt (hBp_pos ℓ hℓ)
    linarith
  · intro ℓ hℓ x hx
    have hp_le :
        Bp ℓ ≤ ∑ ℓ ∈ Γ.jumps, Bp ℓ :=
      Finset.single_le_sum
        (f := fun ℓ : Fin d → ℤ => Bp ℓ)
        (fun q hq => le_of_lt (hBp_pos q hq)) hℓ
    have hx_bound := hBp_bound ℓ hℓ x hx
    calc
      |Γ.rate ℓ x| ≤ Bp ℓ := hx_bound
      _ ≤ ∑ ℓ ∈ Γ.jumps, Bp ℓ := hp_le
      _ ≤ (∑ ℓ ∈ Γ.jumps, Bp ℓ) + 1 := by linarith

/-- If all listed rates are bounded by `B` at `x`, then the drift is bounded
by `jumpNormBound * B`. -/
theorem drift_norm_le_of_rate_bound (x : Fin d → ℝ) {B : ℝ}
    (hB_nonneg : 0 ≤ B)
    (hB : ∀ ℓ ∈ Γ.jumps, |Γ.rate ℓ x| ≤ B) :
    ‖Γ.drift x‖ ≤ Γ.jumpNormBound * B := by
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg Γ.jumpNormBound_nonneg hB_nonneg)]
  intro i
  change |Γ.drift x i| ≤ Γ.jumpNormBound * B
  simp only [drift]
  calc
    |∑ ℓ ∈ Γ.jumps, (ℓ i : ℝ) * Γ.rate ℓ x|
        ≤ ∑ ℓ ∈ Γ.jumps, |(ℓ i : ℝ)| * |Γ.rate ℓ x| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          gcongr with ℓ hℓ
          exact le_of_eq (abs_mul _ _)
    _ ≤ ∑ ℓ ∈ Γ.jumps, ‖(fun j : Fin d => (ℓ j : ℝ))‖ * B := by
          apply Finset.sum_le_sum
          intro ℓ hℓ
          apply mul_le_mul
          · exact norm_le_pi_norm (fun j : Fin d => (ℓ j : ℝ)) i
          · exact hB ℓ hℓ
          · exact abs_nonneg _
          · exact norm_nonneg _
    _ = Γ.jumpNormBound * B := by
          simp [jumpNormBound, Finset.sum_mul]

/-- Uniform drift bound on a bounded ball. -/
theorem exists_drift_bound_on_ball (R : ℝ) (hR : 0 < R) :
    ∃ C > 0, ∀ x : Fin d → ℝ, ‖x‖ ≤ R → ‖Γ.drift x‖ ≤ C := by
  obtain ⟨B, hBpos, hB⟩ := Γ.exists_rate_bound_on_ball R hR
  have hprod_nonneg : 0 ≤ Γ.jumpNormBound * B :=
    mul_nonneg Γ.jumpNormBound_nonneg (le_of_lt hBpos)
  refine ⟨Γ.jumpNormBound * B + 1, by linarith, ?_⟩
  intro x hx
  calc
    ‖Γ.drift x‖ ≤ Γ.jumpNormBound * B :=
      Γ.drift_norm_le_of_rate_bound x (le_of_lt hBpos) (fun ℓ hℓ => hB ℓ hℓ x hx)
    _ ≤ Γ.jumpNormBound * B + 1 := by linarith

end RateSpec

/-! ## The stochastic model

We package the density process X̄^N(t) = X^N(t)/N as a random variable
satisfying the martingale decomposition:

  X̄^N(t) = X̄^N(0) + ∫₀ᵗ F(X̄^N(s)) ds + M^N(t)

where M^N is a martingale with predictable quadratic variation
⟨M^N⟩_t = O(1/N).

`Ripple.CTMC.DensityDependent` supplies this interface from a realized
finite-state CTMC path map plus the QV estimates. -/

/-- A density process for population size N with rate specification Γ.
This packages the stochastic process X̄^N along with its martingale
decomposition and the bound on the martingale part. -/
structure DensityProcess (d : ℕ) (Γ : RateSpec d) (N : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] where
  /-- The density process X̄^N(t, ω) ∈ ℝ^d. -/
  process : ℝ → Ω → Fin d → ℝ
  /-- Density paths stay in the unit cube, hence have sup-norm at most one. -/
  process_norm_le_one : ∀ t ω, ‖process t ω‖ ≤ 1
  /-- Initial condition. -/
  init : Ω → Fin d → ℝ
  /-- The martingale error term M^N(t, ω). -/
  martingale_part : ℝ → Ω → Fin d → ℝ
  /-- Martingale decomposition:
    X̄^N(t) = X̄^N(0) + ∫₀ᵗ F(X̄^N(s)) ds + M^N(t). -/
  decomposition : ∀ t ≥ 0, ∀ᵐ ω ∂μ,
    process t ω = init ω + (fun i =>
      ∫ s in Set.Icc 0 t, (Γ.drift (process s ω)) i) +
      martingale_part t ω
  /-- M^N(0) = 0. -/
  martingale_init : ∀ᵐ ω ∂μ, martingale_part 0 ω = 0
  /-- The martingale sup-square random variable is non-negative.

    This is mathematically immediate, but it is kept as an explicit analytic
    regularity field because the supremum is over a real time interval. -/
  martingale_sup_sq_nonneg : ∀ T > 0,
    0 ≤ᵐ[μ] fun ω => ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
      ‖martingale_part s ω‖ ^ 2
  /-- Integrability needed for Markov's inequality. -/
  martingale_sup_sq_integrable : ∀ T > 0,
    Integrable (fun ω => ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
      ‖martingale_part s ω‖ ^ 2) μ
  /-- Quadratic variation bound: E[sup_{s≤t} ‖M^N(s)‖²] ≤ C·t/N
    for some constant C depending on the rate bound on [0,T].

    This is the key estimate: the martingale fluctuations are O(1/√N). -/
  martingale_qv_bound : ∀ T > 0, ∃ C > 0,
    ∫ ω, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
      ‖martingale_part s ω‖ ^ 2 ∂μ ≤ C * T / N

/-! ## The limiting ODE

The mean-field limit is the solution to x'(t) = F(x(t)), x(0) = x₀.
We use Ripple's existing PIVP infrastructure when the ODE is polynomial
(which it is for population protocols). -/

/-- The ODE solution x(t) with x'(t) = Γ.drift(x(t)), x(0) = x₀.
Existence and uniqueness follow from the Lipschitz condition on F. -/
structure MeanFieldSolution (d : ℕ) (Γ : RateSpec d) where
  /-- Initial condition. -/
  x₀ : Fin d → ℝ
  /-- The solution trajectory. -/
  sol : ℝ → Fin d → ℝ
  /-- Initial condition is satisfied. -/
  sol_init : sol 0 = x₀
  /-- The ODE is satisfied. -/
  sol_ode : ∀ t ≥ 0, HasDerivAt sol (Γ.drift (sol t)) t

/-- A family of density processes for all population sizes, with the
uniform estimates needed by Kurtz's finite-horizon theorem.

The uniform quadratic-variation constant and Gronwall event inclusion are
family-level data: they cannot be recovered from the per-`N` existential
fields of arbitrary `DensityProcess` values. CTMC/PLPP constructions should
build this package from the common `RateSpec` estimates and the deterministic
Gronwall argument. -/
structure DensityProcessFamily (d : ℕ) (Γ : RateSpec d)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] where
  /-- The population-`N` density process. -/
  densityProcess : (N : ℕ) → DensityProcess d Γ N μ
  /-- Uniform martingale quadratic-variation bound across all population sizes. -/
  martingale_qv_bound_uniform : ∀ T > 0, ∃ C_qv > 0, ∀ (N : ℕ), 0 < N →
    ∫ ω, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
      ‖(densityProcess N).martingale_part s ω‖ ^ 2 ∂μ ≤ C_qv * T / N
  /-- Uniform deterministic Gronwall event inclusion across all population sizes. -/
  gronwall_event_inclusion_uniform :
    ∀ (mf : MeanFieldSolution d Γ), ∀ T > 0, ∀ ε > 0, ∃ δ > 0,
      ∀ (N : ℕ), 0 < N → ∀ᵐ ω ∂μ,
        (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
            ‖(densityProcess N).process t ω - mf.sol t‖ ≥ ε) →
          (‖(densityProcess N).init ω - mf.x₀‖ ≥ δ) ∨
          (δ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
            ‖(densityProcess N).martingale_part s ω‖ ^ 2)

end Ripple.Kurtz
