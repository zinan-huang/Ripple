import Mathlib

/-!
# Linear ODEs with continuous coefficients: global existence and uniqueness

For a continuous family of linear maps `B : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)`, the linear
ODE `ψ' = B s ψ` has, for every initial time `t` and value `a`, a unique solution defined on
all of `ℝ`.  This is used for the adjoint equation of the linearized mean-field ODE.

Existence is by Picard iteration `ψ₀ = a`, `ψ_{k+1}(s) = a + ∫_t^s B r (ψ_k r) dr`.  On
`|s - t| ≤ R`, with `β` a bound for `‖B‖` there, the increments satisfy
`‖ψ_{k+1} s - ψ_k s‖ ≤ ‖a‖ (β |s - t|)^(k+1) / (k+1)!`, so the iterates converge pointwise.
The limit is locally Lipschitz (hence continuous), satisfies the integral equation by dominated
convergence, and is differentiable by the fundamental theorem of calculus.
Uniqueness is Mathlib's Gronwall-based `ODE_solution_unique_of_mem_Icc`.
-/

open MeasureTheory Filter Topology Set intervalIntegral
open scoped Interval

namespace Ripple.Kurtz

section LinearODE

variable {d : ℕ}

local notation "E" => (Fin d → ℝ)

/-- Picard iterates of the linear ODE `ψ' = B s ψ`, `ψ t = a`. -/
noncomputable def linPicard (B : ℝ → E →L[ℝ] E) (t : ℝ) (a : E) : ℕ → ℝ → E
  | 0 => fun _ => a
  | k + 1 => fun s => a + ∫ r in t..s, B r (linPicard B t a k r)

lemma linPicard_zero (B : ℝ → E →L[ℝ] E) (t : ℝ) (a : E) (s : ℝ) :
    linPicard B t a 0 s = a := rfl

lemma linPicard_succ (B : ℝ → E →L[ℝ] E) (t : ℝ) (a : E) (k : ℕ) (s : ℝ) :
    linPicard B t a (k + 1) s = a + ∫ r in t..s, B r (linPicard B t a k r) := rfl

lemma continuous_linPicard (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (t : ℝ) (a : E) :
    ∀ k, Continuous (linPicard B t a k)
  | 0 => continuous_const
  | k + 1 => by
    have hg : Continuous fun r => B r (linPicard B t a k r) :=
      hB.clm_apply (continuous_linPicard B hB t a k)
    exact continuous_const.add
      (intervalIntegral.continuous_primitive (fun _ _ => hg.intervalIntegrable _ _) t)

lemma abs_sub_le_of_mem_uIoc {t s r : ℝ} (hr : r ∈ Ι t s) : |r - t| ≤ |s - t| :=
  Set.abs_sub_left_of_mem_uIcc (Set.uIoc_subset_uIcc hr)

lemma abs_integral_abs_sub_pow (t s : ℝ) (n : ℕ) :
    |∫ r in t..s, |r - t| ^ n| = |s - t| ^ (n + 1) / (n + 1) := by
  rcases le_total t s with hts | hst
  · have h1 : (∫ r in t..s, |r - t| ^ n) = ∫ r in t..s, (r - t) ^ n := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [Set.uIcc_of_le hts] at hr
      rw [abs_of_nonneg (by linarith [hr.1])]
    rw [h1, intervalIntegral.integral_comp_sub_right (fun x => x ^ n) t, integral_pow]
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ s - t)]
    simp only [sub_self]
    rw [zero_pow (Nat.succ_ne_zero n), sub_zero]
    exact abs_of_nonneg (by positivity)
  · have h1 : (∫ r in s..t, |r - t| ^ n) = ∫ r in s..t, (t - r) ^ n := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [Set.uIcc_of_le hst] at hr
      rw [abs_of_nonpos (by linarith [hr.2]), neg_sub]
    rw [intervalIntegral.integral_symm, h1,
      intervalIntegral.integral_comp_sub_left (fun x => x ^ n) t, integral_pow]
    rw [abs_of_nonpos (by linarith : s - t ≤ 0)]
    simp only [sub_self]
    rw [zero_pow (Nat.succ_ne_zero n), sub_zero, abs_neg, neg_sub]
    exact abs_of_nonneg (by have : 0 ≤ t - s := by linarith
                            positivity)

/-- Factorial bound on the Picard increments on `|s - t| ≤ R`. -/
lemma linPicard_diff_bound (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (t : ℝ) (a : E)
    {R β : ℝ} (hβ0 : 0 ≤ β) (hβ : ∀ r, |r - t| ≤ R → ‖B r‖ ≤ β) :
    ∀ k s, |s - t| ≤ R →
      ‖linPicard B t a (k + 1) s - linPicard B t a k s‖ ≤
        ‖a‖ * (β * |s - t|) ^ (k + 1) / ((k + 1).factorial : ℝ)
  | 0, s, hs => by
    simp only [linPicard_succ, linPicard_zero, add_sub_cancel_left, zero_add, pow_one,
      Nat.factorial_one, Nat.cast_one, div_one]
    calc ‖∫ r in t..s, B r a‖ ≤ (β * ‖a‖) * |s - t| := by
          refine intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => ?_
          calc ‖B r a‖ ≤ ‖B r‖ * ‖a‖ := (B r).le_opNorm a
            _ ≤ β * ‖a‖ := mul_le_mul_of_nonneg_right
                (hβ r ((abs_sub_le_of_mem_uIoc hr).trans hs)) (norm_nonneg _)
      _ = ‖a‖ * (β * |s - t|) := by ring
  | k + 1, s, hs => by
    have hc := continuous_linPicard B hB t a
    have hdiff : linPicard B t a (k + 2) s - linPicard B t a (k + 1) s =
        ∫ r in t..s, B r (linPicard B t a (k + 1) r - linPicard B t a k r) := by
      rw [linPicard_succ, linPicard_succ B t a k, add_sub_add_left_eq_sub,
        ← intervalIntegral.integral_sub ((hB.clm_apply (hc _)).intervalIntegrable _ _)
          ((hB.clm_apply (hc _)).intervalIntegrable _ _)]
      simp only [map_sub]
    rw [hdiff]
    set c : ℝ := ‖a‖ * β ^ (k + 2) / ((k + 1).factorial : ℝ) with hc_def
    have hc0 : 0 ≤ c := by positivity
    have hnorm : ‖∫ r in t..s, B r (linPicard B t a (k + 1) r - linPicard B t a k r)‖ ≤
        |∫ r in t..s, c * |r - t| ^ (k + 1)| := by
      refine intervalIntegral.norm_integral_le_abs_of_norm_le ?_ ?_
      · refine (ae_restrict_iff' measurableSet_uIoc).2 (Filter.Eventually.of_forall fun r hr => ?_)
        have hrt : |r - t| ≤ R := (abs_sub_le_of_mem_uIoc hr).trans hs
        have hIH := linPicard_diff_bound B hB t a hβ0 hβ k r hrt
        calc ‖B r (linPicard B t a (k + 1) r - linPicard B t a k r)‖
            ≤ ‖B r‖ * ‖linPicard B t a (k + 1) r - linPicard B t a k r‖ := (B r).le_opNorm _
          _ ≤ β * (‖a‖ * (β * |r - t|) ^ (k + 1) / ((k + 1).factorial : ℝ)) :=
              mul_le_mul (hβ r hrt) hIH (norm_nonneg _) hβ0
          _ = c * |r - t| ^ (k + 1) := by rw [hc_def]; ring
      · exact (continuous_const.mul ((continuous_id.sub continuous_const).abs.pow _)
          ).intervalIntegrable _ _
    refine hnorm.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg hc0,
      abs_integral_abs_sub_pow, hc_def, Nat.factorial_succ (k + 1)]
    push_cast
    field_simp
    ring

/-- `1 + ∑_{j<n} x^(j+1)/(j+1)! ≤ ∑' j, x^j/j!` for `x ≥ 0`. -/
lemma one_add_sum_range_pow_succ_div_le_tsum {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    1 + ∑ j ∈ Finset.range n, x ^ (j + 1) / ((j + 1).factorial : ℝ) ≤
      ∑' j, x ^ j / (j.factorial : ℝ) := by
  have hs := Real.summable_pow_div_factorial x
  calc 1 + ∑ j ∈ Finset.range n, x ^ (j + 1) / ((j + 1).factorial : ℝ)
      = ∑ j ∈ Finset.range (n + 1), x ^ j / (j.factorial : ℝ) := by
        rw [Finset.sum_range_succ']
        simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
        ring
    _ ≤ ∑' j, x ^ j / (j.factorial : ℝ) :=
        hs.sum_le_tsum _ (fun j _ => by positivity)

/-- Uniform bound on the Picard iterates on `|s - t| ≤ R`. -/
lemma linPicard_norm_le (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (t : ℝ) (a : E)
    {R β : ℝ} (hβ0 : 0 ≤ β) (hβ : ∀ r, |r - t| ≤ R → ‖B r‖ ≤ β) (k : ℕ) (s : ℝ)
    (hs : |s - t| ≤ R) :
    ‖linPicard B t a k s‖ ≤ ‖a‖ * ∑' j, (β * R) ^ j / (j.factorial : ℝ) := by
  have hR : 0 ≤ R := (abs_nonneg _).trans hs
  have htel : linPicard B t a k s = a +
      ∑ j ∈ Finset.range k, (linPicard B t a (j + 1) s - linPicard B t a j s) := by
    rw [Finset.sum_range_sub (fun j => linPicard B t a j s)]
    simp [linPicard_zero]
  rw [htel]
  calc ‖a + ∑ j ∈ Finset.range k, (linPicard B t a (j + 1) s - linPicard B t a j s)‖
      ≤ ‖a‖ + ∑ j ∈ Finset.range k, ‖linPicard B t a (j + 1) s - linPicard B t a j s‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ ‖a‖ + ∑ j ∈ Finset.range k, ‖a‖ * ((β * R) ^ (j + 1) / ((j + 1).factorial : ℝ)) := by
        gcongr with j hj
        refine (linPicard_diff_bound B hB t a hβ0 hβ j s hs).trans ?_
        rw [mul_div_assoc]
        gcongr
    _ = ‖a‖ * (1 + ∑ j ∈ Finset.range k, (β * R) ^ (j + 1) / ((j + 1).factorial : ℝ)) := by
        rw [mul_add, mul_one, Finset.mul_sum]
    _ ≤ ‖a‖ * ∑' j, (β * R) ^ j / (j.factorial : ℝ) :=
        mul_le_mul_of_nonneg_left
          (one_add_sum_range_pow_succ_div_le_tsum (mul_nonneg hβ0 hR) k) (norm_nonneg _)

lemma abs_sub_le_iff_mem_Icc {r t R : ℝ} : |r - t| ≤ R ↔ r ∈ Icc (t - R) (t + R) := by
  rw [abs_sub_le_iff, mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- `‖B‖` is bounded on every compact time window. -/
lemma exists_opNorm_bound (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (t R : ℝ) :
    ∃ β : ℝ, 0 ≤ β ∧ ∀ r, |r - t| ≤ R → ‖B r‖ ≤ β := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := t - R) (b := t + R)).exists_bound_of_continuousOn hB.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun r hr =>
    (hC r (abs_sub_le_iff_mem_Icc.1 hr)).trans (le_max_left _ _)⟩

lemma summable_linPicard_diff (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (t : ℝ) (a : E)
    (s : ℝ) : Summable fun j => linPicard B t a (j + 1) s - linPicard B t a j s := by
  obtain ⟨β, hβ0, hβ⟩ := exists_opNorm_bound B hB t |s - t|
  have hs := (summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial (β * |s - t|))
  refine Summable.of_norm_bounded (g := fun j => ‖a‖ * ((β * |s - t|) ^ (j + 1) /
    ((j + 1).factorial : ℝ))) (hs.mul_left ‖a‖) fun j => ?_
  exact (linPicard_diff_bound B hB t a hβ0 hβ j s le_rfl).trans
    (le_of_eq (mul_div_assoc _ _ _))

/-- The global solution: the sum of the Picard series. -/
noncomputable def linSol (B : ℝ → E →L[ℝ] E) (t : ℝ) (a : E) (s : ℝ) : E :=
  a + ∑' j, (linPicard B t a (j + 1) s - linPicard B t a j s)

lemma tendsto_linPicard (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (t : ℝ) (a : E) (s : ℝ) :
    Tendsto (fun k => linPicard B t a k s) atTop (𝓝 (linSol B t a s)) := by
  have h := (summable_linPicard_diff B hB t a s).hasSum.tendsto_sum_nat
  have hfun : (fun k => linPicard B t a k s) = fun k => a +
      ∑ j ∈ Finset.range k, (linPicard B t a (j + 1) s - linPicard B t a j s) := by
    funext k
    rw [Finset.sum_range_sub (fun j => linPicard B t a j s)]
    simp [linPicard_zero]
  rw [hfun]
  exact tendsto_const_nhds.add h

lemma linSol_norm_le (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (t : ℝ) (a : E)
    {R β : ℝ} (hβ0 : 0 ≤ β) (hβ : ∀ r, |r - t| ≤ R → ‖B r‖ ≤ β) (s : ℝ)
    (hs : |s - t| ≤ R) :
    ‖linSol B t a s‖ ≤ ‖a‖ * ∑' j, (β * R) ^ j / (j.factorial : ℝ) :=
  le_of_tendsto' (tendsto_linPicard B hB t a s).norm
    (fun k => linPicard_norm_le B hB t a hβ0 hβ k s hs)

lemma linSol_lipschitz (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (t : ℝ) (a : E)
    {R β : ℝ} (hβ0 : 0 ≤ β) (hβ : ∀ r, |r - t| ≤ R → ‖B r‖ ≤ β) {s s' : ℝ}
    (hs : |s - t| ≤ R) (hs' : |s' - t| ≤ R) :
    ‖linSol B t a s - linSol B t a s'‖ ≤
      β * (‖a‖ * ∑' j, (β * R) ^ j / (j.factorial : ℝ)) * |s - s'| := by
  set S : ℝ := ‖a‖ * ∑' j, (β * R) ^ j / (j.factorial : ℝ)
  have hc := continuous_linPicard B hB t a
  have hk : ∀ k, ‖linPicard B t a (k + 1) s - linPicard B t a (k + 1) s'‖ ≤
      β * S * |s - s'| := by
    intro k
    rw [linPicard_succ, linPicard_succ, add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left ((hB.clm_apply (hc k)).intervalIntegrable _ _)
        ((hB.clm_apply (hc k)).intervalIntegrable _ _)]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => ?_
    have hrt : |r - t| ≤ R := by
      rw [abs_sub_le_iff_mem_Icc]
      exact Set.uIcc_subset_Icc (abs_sub_le_iff_mem_Icc.1 hs') (abs_sub_le_iff_mem_Icc.1 hs)
        (Set.uIoc_subset_uIcc hr)
    calc ‖B r (linPicard B t a k r)‖ ≤ ‖B r‖ * ‖linPicard B t a k r‖ := (B r).le_opNorm _
      _ ≤ β * S := mul_le_mul (hβ r hrt) (linPicard_norm_le B hB t a hβ0 hβ k r hrt)
          (norm_nonneg _) hβ0
  have hlim : Tendsto (fun k => linPicard B t a (k + 1) s - linPicard B t a (k + 1) s')
      atTop (𝓝 (linSol B t a s - linSol B t a s')) :=
    ((tendsto_linPicard B hB t a s).comp (tendsto_add_atTop_nat 1)).sub
      ((tendsto_linPicard B hB t a s').comp (tendsto_add_atTop_nat 1))
  exact le_of_tendsto' hlim.norm hk

lemma continuous_linSol (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (t : ℝ) (a : E) :
    Continuous (linSol B t a) := by
  refine continuous_iff_continuousAt.2 fun s₀ => ?_
  set R : ℝ := |s₀ - t| + 1
  obtain ⟨β, hβ0, hβ⟩ := exists_opNorm_bound B hB t R
  set S : ℝ := ‖a‖ * ∑' j, (β * R) ^ j / (j.factorial : ℝ)
  have hS : 0 ≤ S := le_trans (norm_nonneg _) (linSol_norm_le B hB t a hβ0 hβ t
    (by simp only [sub_self, abs_zero, R]; positivity))
  have hL : LipschitzOnWith (Real.toNNReal (β * S)) (linSol B t a) (Icc (t - R) (t + R)) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [dist_eq_norm, Real.dist_eq, Real.coe_toNNReal _ (mul_nonneg hβ0 hS)]
    exact linSol_lipschitz B hB t a hβ0 hβ (abs_sub_le_iff_mem_Icc.2 hx)
      (abs_sub_le_iff_mem_Icc.2 hy)
  have h1 : |s₀ - t| < R := by simp only [R]; linarith
  rw [abs_sub_lt_iff] at h1
  exact hL.continuousOn.continuousAt (Icc_mem_nhds (by linarith) (by linarith))

/-- The Picard limit satisfies the integral equation. -/
lemma linSol_eq_integral (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (t : ℝ) (a : E) (s : ℝ) :
    linSol B t a s = a + ∫ r in t..s, B r (linSol B t a r) := by
  obtain ⟨β, hβ0, hβ⟩ := exists_opNorm_bound B hB t |s - t|
  set S : ℝ := ‖a‖ * ∑' j, (β * |s - t|) ^ j / (j.factorial : ℝ)
  have hc := continuous_linPicard B hB t a
  have h1 : Tendsto (fun k => linPicard B t a (k + 1) s) atTop (𝓝 (linSol B t a s)) :=
    (tendsto_linPicard B hB t a s).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun k => linPicard B t a (k + 1) s) atTop
      (𝓝 (a + ∫ r in t..s, B r (linSol B t a r))) := by
    show Tendsto (fun k => a + ∫ r in t..s, B r (linPicard B t a k r)) atTop _
    refine tendsto_const_nhds.add ?_
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => β * S) (Eventually.of_forall fun k => (hB.clm_apply (hc k)).aestronglyMeasurable)
      (Eventually.of_forall fun k => Eventually.of_forall fun r hr => ?_)
      intervalIntegral.intervalIntegrable_const
      (Eventually.of_forall fun r _ =>
        ((B r).continuous.tendsto _).comp (tendsto_linPicard B hB t a r))
    have hrt : |r - t| ≤ |s - t| := abs_sub_le_of_mem_uIoc hr
    calc ‖B r (linPicard B t a k r)‖ ≤ ‖B r‖ * ‖linPicard B t a k r‖ := (B r).le_opNorm _
      _ ≤ β * S := mul_le_mul (hβ r hrt) (linPicard_norm_le B hB t a hβ0 hβ k r hrt)
          (norm_nonneg _) hβ0
  exact tendsto_nhds_unique h1 h2

theorem linSol_self (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (t : ℝ) (a : E) :
    linSol B t a t = a := by
  rw [linSol_eq_integral B hB t a t, intervalIntegral.integral_same, add_zero]

theorem hasDerivAt_linSol (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (t : ℝ) (a : E) (s : ℝ) :
    HasDerivAt (linSol B t a) (B s (linSol B t a s)) s := by
  have hg : Continuous fun r => B r (linSol B t a r) :=
    hB.clm_apply (continuous_linSol B hB t a)
  exact ((hg.integral_hasStrictDerivAt t s).hasDerivAt.const_add a).congr_of_eventuallyEq
    (Eventually.of_forall fun s' => linSol_eq_integral B hB t a s')

/-- Global existence for a linear ODE with continuous coefficients: for every initial time `t`
and initial value `a` there is `ψ : ℝ → ℝⁿ` with `ψ t = a` and `ψ' s = B s (ψ s)` for all
`s ∈ ℝ`.  The solution is the sum of the Picard series. -/
theorem exists_linear_ode_sol {d : ℕ} (B : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (hB : Continuous B) (t : ℝ) (a : Fin d → ℝ) :
    ∃ ψ : ℝ → Fin d → ℝ, ψ t = a ∧ ∀ s, HasDerivAt ψ (B s (ψ s)) s :=
  ⟨linSol B t a, linSol_self B hB t a, hasDerivAt_linSol B hB t a⟩

/-- Uniqueness for a linear ODE with continuous coefficients: two global solutions of
`ψ' = B s ψ` that agree at one time agree everywhere.  On each compact window `B s` is
Lipschitz with a uniform constant, and Mathlib's Gronwall uniqueness theorem applies. -/
theorem linear_ode_sol_unique {d : ℕ} (B : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (hB : Continuous B) {t : ℝ} {ψ φ : ℝ → Fin d → ℝ}
    (hψ : ∀ s, HasDerivAt ψ (B s (ψ s)) s) (hφ : ∀ s, HasDerivAt φ (B s (φ s)) s)
    (h : ψ t = φ t) : ψ = φ := by
  funext x
  set R : ℝ := |x - t| + 1
  obtain ⟨β, hβ0, hβ⟩ := exists_opNorm_bound B hB t R
  have hRpos : 0 < R := by simp only [R]; positivity
  have hxR : |x - t| < R := by simp only [R]; linarith
  rw [abs_sub_lt_iff] at hxR
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun s => (hψ s).continuousAt
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun s => (hφ s).continuousAt
  have hlip : ∀ r ∈ Ioo (t - R) (t + R),
      LipschitzOnWith ⟨β, hβ0⟩ (fun x => B r x) (univ : Set (Fin d → ℝ)) := by
    intro r hr
    have hrt : |r - t| ≤ R := abs_sub_le_iff_mem_Icc.2 (Ioo_subset_Icc_self hr)
    refine ((B r).lipschitz.weaken ?_).lipschitzOnWith
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact hβ r hrt
  exact ODE_solution_unique_of_mem_Icc (v := fun r x => B r x) (s := fun _ => univ)
    hlip (by constructor <;> linarith) hψc.continuousOn (fun r _ => hψ r)
    (fun _ _ => mem_univ _) hφc.continuousOn (fun r _ => hφ r) (fun _ _ => mem_univ _) h
    ⟨by linarith, by linarith⟩

end LinearODE

/-! ### Coordinate form: the adjoint equation and the forward fundamental solution

FIX-KURTZ2-FINAL, Lemma 4.1 (backward adjoint, forward fundamental matrix, and transpose bridge).
For a continuous matrix field `A : ℝ → Matrix (Fin d) (Fin d) ℝ`, the backward adjoint equation
`ψ' = −Aᵀ ψ` and the forward equation `z' = A z` are instances of the linear ODE above, and the
pairing `ψ ⬝ᵥ z` is constant in time, so `(z τ)_i = ψ_{τ,i}(s) ⬝ᵥ z(s)` when `ψ_{τ,i}(τ) = e_i`. -/

section Adjoint

open Matrix

variable {d : ℕ}

/-- The matrix `A` as a continuous linear map `v ↦ A *ᵥ v` on `Fin d → ℝ`. -/
noncomputable def matCLM (A : Matrix (Fin d) (Fin d) ℝ) : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' A)

@[simp]
theorem matCLM_apply (A : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) : matCLM A v = A *ᵥ v := by
  simp [matCLM, Matrix.toLin'_apply]

/-- `A ↦ matCLM A` is linear, hence continuous (finite dimensions). -/
noncomputable def matCLMLin :
    Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] ((Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) :=
  (LinearMap.toContinuousLinearMap :
      ((Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) ≃ₗ[ℝ] ((Fin d → ℝ) →L[ℝ] (Fin d → ℝ))).toLinearMap.comp
    (Matrix.toLin' : Matrix (Fin d) (Fin d) ℝ ≃ₗ[ℝ] ((Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))).toLinearMap

theorem continuous_matCLM : Continuous fun A : Matrix (Fin d) (Fin d) ℝ => matCLM A :=
  (matCLMLin (d := d)).continuous_of_finiteDimensional.congr fun _ => rfl

/-- The backward adjoint solution `ψ` with `ψ τ = a` and `ψ' s = −(A s)ᵀ *ᵥ ψ s`
(FINAL Lemma 4.1 (i)), as the Picard series of the linear ODE. -/
noncomputable def adjointSol (A : ℝ → Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) (a : Fin d → ℝ) :
    ℝ → Fin d → ℝ :=
  linSol (fun s => -(matCLM (A s)ᵀ)) τ a

/-- The forward fundamental solution `z` with `z s₀ = ℓ` and `z' r = A r *ᵥ z r`
(FINAL Lemma 4.1 (ii)); `ℓ ↦ z r` is the fundamental matrix `Φ(r, s₀)`. -/
noncomputable def fundamentalSol (A : ℝ → Matrix (Fin d) (Fin d) ℝ) (s₀ : ℝ) (ℓ : Fin d → ℝ) :
    ℝ → Fin d → ℝ :=
  linSol (fun r => matCLM (A r)) s₀ ℓ

theorem continuous_neg_matCLM_transpose {A : ℝ → Matrix (Fin d) (Fin d) ℝ} (hA : Continuous A) :
    Continuous fun s => -(matCLM (A s)ᵀ) :=
  (continuous_matCLM.comp hA.matrix_transpose).neg

theorem continuous_matCLM_comp {A : ℝ → Matrix (Fin d) (Fin d) ℝ} (hA : Continuous A) :
    Continuous fun s => matCLM (A s) :=
  continuous_matCLM.comp hA

theorem adjointSol_self {A : ℝ → Matrix (Fin d) (Fin d) ℝ} (hA : Continuous A) (τ : ℝ)
    (a : Fin d → ℝ) : adjointSol A τ a τ = a :=
  linSol_self _ (continuous_neg_matCLM_transpose hA) τ a

theorem hasDerivAt_adjointSol {A : ℝ → Matrix (Fin d) (Fin d) ℝ} (hA : Continuous A) (τ : ℝ)
    (a : Fin d → ℝ) (s : ℝ) :
    HasDerivAt (adjointSol A τ a) (-((A s)ᵀ *ᵥ adjointSol A τ a s)) s := by
  have h := hasDerivAt_linSol _ (continuous_neg_matCLM_transpose hA) τ a s
  refine h.congr_deriv ?_
  simp [adjointSol]

theorem fundamentalSol_self {A : ℝ → Matrix (Fin d) (Fin d) ℝ} (hA : Continuous A) (s₀ : ℝ)
    (ℓ : Fin d → ℝ) : fundamentalSol A s₀ ℓ s₀ = ℓ :=
  linSol_self _ (continuous_matCLM_comp hA) s₀ ℓ

theorem hasDerivAt_fundamentalSol {A : ℝ → Matrix (Fin d) (Fin d) ℝ} (hA : Continuous A)
    (s₀ : ℝ) (ℓ : Fin d → ℝ) (r : ℝ) :
    HasDerivAt (fundamentalSol A s₀ ℓ) (A r *ᵥ fundamentalSol A s₀ ℓ r) r := by
  have h := hasDerivAt_linSol _ (continuous_matCLM_comp hA) s₀ ℓ r
  refine h.congr_deriv ?_
  simp [fundamentalSol]

/-- Existence form of the backward adjoint equation. -/
theorem exists_adjoint_sol (A : ℝ → Matrix (Fin d) (Fin d) ℝ) (hA : Continuous A) (τ : ℝ)
    (a : Fin d → ℝ) :
    ∃ ψ : ℝ → Fin d → ℝ, ψ τ = a ∧ ∀ s, HasDerivAt ψ (-((A s)ᵀ *ᵥ ψ s)) s :=
  ⟨adjointSol A τ a, adjointSol_self hA τ a, hasDerivAt_adjointSol hA τ a⟩

/-- Existence form of the forward equation. -/
theorem exists_fundamental_sol (A : ℝ → Matrix (Fin d) (Fin d) ℝ) (hA : Continuous A) (s₀ : ℝ)
    (ℓ : Fin d → ℝ) :
    ∃ z : ℝ → Fin d → ℝ, z s₀ = ℓ ∧ ∀ r, HasDerivAt z (A r *ᵥ z r) r :=
  ⟨fundamentalSol A s₀ ℓ, fundamentalSol_self hA s₀ ℓ, hasDerivAt_fundamentalSol hA s₀ ℓ⟩

/-- Uniqueness for the backward adjoint equation. -/
theorem adjoint_sol_unique {A : ℝ → Matrix (Fin d) (Fin d) ℝ} (hA : Continuous A) {τ : ℝ}
    {ψ φ : ℝ → Fin d → ℝ} (hψ : ∀ s, HasDerivAt ψ (-((A s)ᵀ *ᵥ ψ s)) s)
    (hφ : ∀ s, HasDerivAt φ (-((A s)ᵀ *ᵥ φ s)) s) (h : ψ τ = φ τ) : ψ = φ :=
  linear_ode_sol_unique (fun s => -(matCLM (A s)ᵀ)) (continuous_neg_matCLM_transpose hA)
    (t := τ) (fun s => (hψ s).congr_deriv (by simp)) (fun s => (hφ s).congr_deriv (by simp)) h

/-- Uniqueness for the forward equation. -/
theorem fundamental_sol_unique {A : ℝ → Matrix (Fin d) (Fin d) ℝ} (hA : Continuous A) {s₀ : ℝ}
    {z w : ℝ → Fin d → ℝ} (hz : ∀ r, HasDerivAt z (A r *ᵥ z r) r)
    (hw : ∀ r, HasDerivAt w (A r *ᵥ w r) r) (h : z s₀ = w s₀) : z = w :=
  linear_ode_sol_unique (fun r => matCLM (A r)) (continuous_matCLM_comp hA)
    (t := s₀) (fun r => (hz r).congr_deriv (by simp)) (fun r => (hw r).congr_deriv (by simp)) h

/-- The pairing of a backward adjoint solution with a forward solution has zero derivative. -/
theorem hasDerivAt_dotProduct_adjoint_fundamental (A : ℝ → Matrix (Fin d) (Fin d) ℝ)
    {ψ z : ℝ → Fin d → ℝ} (hψ : ∀ s, HasDerivAt ψ (-((A s)ᵀ *ᵥ ψ s)) s)
    (hz : ∀ r, HasDerivAt z (A r *ᵥ z r) r) (r : ℝ) :
    HasDerivAt (fun r => ψ r ⬝ᵥ z r) 0 r := by
  have hψi := hasDerivAt_pi.1 (hψ r)
  have hzi := hasDerivAt_pi.1 (hz r)
  have h : HasDerivAt (fun r => ∑ i, ψ r i * z r i)
      (∑ i, ((-((A r)ᵀ *ᵥ ψ r)) i * z r i + ψ r i * (A r *ᵥ z r) i)) r :=
    HasDerivAt.fun_sum fun i _ => (hψi i).mul (hzi i)
  have hzero : (∑ i, ((-((A r)ᵀ *ᵥ ψ r)) i * z r i + ψ r i * (A r *ᵥ z r) i)) = 0 := by
    rw [Finset.sum_add_distrib]
    change (-((A r)ᵀ *ᵥ ψ r)) ⬝ᵥ z r + ψ r ⬝ᵥ (A r *ᵥ z r) = 0
    rw [neg_dotProduct, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, neg_add_cancel]
  rw [hzero] at h
  exact h

/-- **Transpose bridge (FINAL Lemma 4.1 (iii)).** For a backward adjoint solution `ψ`
(`ψ' = −Aᵀ ψ`) and a forward solution `z` (`z' = A z`), the pairing `ψ ⬝ᵥ z` is constant:
`ψ τ ⬝ᵥ z τ = ψ s ⬝ᵥ z s` for all `s, τ`. -/
theorem adjoint_bridge (A : ℝ → Matrix (Fin d) (Fin d) ℝ) {ψ z : ℝ → Fin d → ℝ}
    (hψ : ∀ s, HasDerivAt ψ (-((A s)ᵀ *ᵥ ψ s)) s) (hz : ∀ r, HasDerivAt z (A r *ᵥ z r) r)
    (s τ : ℝ) : ψ τ ⬝ᵥ z τ = ψ s ⬝ᵥ z s := by
  have hd := hasDerivAt_dotProduct_adjoint_fundamental A hψ hz
  exact is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt) (fun r => (hd r).deriv) τ s

/-- Coordinate reading of the bridge: if `ψ τ = e_i` then `(z τ) i = ψ s ⬝ᵥ z s`; with
`z s = ℓ` this is `(Φ(τ, s) ℓ)_i = ψ_{τ,i}(s) ⬝ᵥ ℓ`. -/
theorem adjoint_bridge_coord (A : ℝ → Matrix (Fin d) (Fin d) ℝ) {ψ z : ℝ → Fin d → ℝ}
    (hψ : ∀ s, HasDerivAt ψ (-((A s)ᵀ *ᵥ ψ s)) s) (hz : ∀ r, HasDerivAt z (A r *ᵥ z r) r)
    {τ : ℝ} {i : Fin d} (hτ : ψ τ = Pi.single i 1) (s : ℝ) : z τ i = ψ s ⬝ᵥ z s := by
  rw [← adjoint_bridge A hψ hz s τ, hτ]
  simp [dotProduct, Pi.single_apply]

/-- The fundamental solution through `ℓ` at time `s`, read at time `τ` in coordinate `i`, is the
pairing of `ℓ` with the adjoint solution `ψ_{τ,i}` (`ψ_{τ,i}(τ) = e_i`). -/
theorem fundamentalSol_apply_eq_adjointSol_dotProduct {A : ℝ → Matrix (Fin d) (Fin d) ℝ}
    (hA : Continuous A) (s τ : ℝ) (ℓ : Fin d → ℝ) (i : Fin d) :
    fundamentalSol A s ℓ τ i = adjointSol A τ (Pi.single i 1) s ⬝ᵥ ℓ := by
  rw [adjoint_bridge_coord A (hasDerivAt_adjointSol hA τ _) (hasDerivAt_fundamentalSol hA s ℓ)
    (adjointSol_self hA τ _) s, fundamentalSol_self hA s ℓ]

end Adjoint

end Ripple.Kurtz
