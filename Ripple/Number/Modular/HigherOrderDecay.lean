/-
  Higher-order exponential decay for modular forms whose `q`-expansion
  vanishes to higher order at `∞`.

  Mathlib's `ModularFormClass.exp_decay_atImInfty` only states the
  first-order decay (rate `2π/h`) for `q`-expansion-zero forms.  The
  Sturm bound at level `Γ(1)` for weights `k ≥ 12` needs higher-order
  decay: if the first `n` `q`-coefficients vanish, then the form decays
  at rate `2π·n/h`.

  The key step (provided here) is the iterated-derivative version of
  vanishing: vanishing of the first `n` `q`-coefficients is equivalent
  to vanishing of the first `n` iterated derivatives of `cuspFunction`
  at `0`.  The full decay-rate bound then follows from Mathlib's
  Taylor-series expansion (`AnalyticAt.exists_eventuallyEq_sum_add_pow_mul`)
  combined with the analytic structure of `cuspFunction`; this is the
  remaining piece for a future commit.
-/
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Analysis.Analytic.Order

namespace Ripple
namespace Number
namespace Modular

open UpperHalfPlane

/-- If the first `n` `q`-expansion coefficients of a function `f : ℍ → ℂ`
vanish, then the first `n` iterated derivatives of `cuspFunction h f`
at `0` vanish.  This is the analytic-side translation of the formal
identity `qExpansion_coeff`. -/
lemma iteratedDeriv_cuspFunction_zero_of_qExpansion_coeff_zero
    {h : ℝ} (f : ℍ → ℂ)
    {n : ℕ}
    (hcoeff : ∀ m < n,
      (UpperHalfPlane.qExpansion h f).coeff m = 0) :
    ∀ m < n, iteratedDeriv m (UpperHalfPlane.cuspFunction h f) 0 = 0 := by
  intro m hm
  have hcoeffm : (UpperHalfPlane.qExpansion h f).coeff m = 0 := hcoeff m hm
  rw [UpperHalfPlane.qExpansion_coeff f m] at hcoeffm
  have hfact : ((m.factorial : ℂ))⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact_mod_cast Nat.factorial_ne_zero m
  exact (mul_eq_zero.mp hcoeffm).resolve_left hfact

/-- Taylor factorisation of `cuspFunction h f` near `0` when the first
`n` `q`-coefficients vanish: there exists an analytic `F` such that
eventually near `0`, `cuspFunction h f q = q^n · F q`. -/
lemma cuspFunction_eq_pow_mul_analytic
    {F : Type*} [FunLike F ℍ ℂ] (f : F) {k : ℤ} {h : ℝ}
    {Γ : Subgroup (GL (Fin 2) ℝ)} [ModularFormClass F Γ k]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    {n : ℕ}
    (hcoeff : ∀ m < n,
      (UpperHalfPlane.qExpansion h f).coeff m = 0) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧
      ∀ᶠ q in nhds (0 : ℂ),
        UpperHalfPlane.cuspFunction h f q = q ^ n • G q := by
  have hanalytic : AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction h (f : ℍ → ℂ)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero (f := f) hh hΓ
  obtain ⟨G, hG, hEq⟩ := hanalytic.exists_eventuallyEq_sum_add_pow_mul n
  -- The Taylor sum collapses because each `iteratedDeriv i = 0` for `i < n`.
  have hderiv := iteratedDeriv_cuspFunction_zero_of_qExpansion_coeff_zero
    (f := (f : ℍ → ℂ)) (h := h) (n := n) hcoeff
  refine ⟨G, hG, ?_⟩
  filter_upwards [hEq] with q hq
  -- The sum vanishes term-by-term, leaving `q^n • G q`.
  have hsum :
      (∑ i ∈ Finset.range n, (q ^ i / (i.factorial : ℂ)) •
        iteratedDeriv i
          (UpperHalfPlane.cuspFunction h (f : ℍ → ℂ)) 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hderiv i (Finset.mem_range.mp hi)]
    simp
  rw [hq, hsum, zero_add]

/-- Big-O bound on `cuspFunction h f` near `0`: when the first `n`
`q`-coefficients vanish, `cuspFunction h f q = O(|q|^n)` near `0`. -/
lemma cuspFunction_isBigO_pow_of_qExpansion_coeff_zero
    {F : Type*} [FunLike F ℍ ℂ] (f : F) {k : ℤ} {h : ℝ}
    {Γ : Subgroup (GL (Fin 2) ℝ)} [ModularFormClass F Γ k]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    {n : ℕ}
    (hcoeff : ∀ m < n,
      (UpperHalfPlane.qExpansion h f).coeff m = 0) :
    UpperHalfPlane.cuspFunction h (f : ℍ → ℂ) =O[nhds (0 : ℂ)]
      fun q : ℂ => q ^ n := by
  obtain ⟨G, hG, hEq⟩ :=
    cuspFunction_eq_pow_mul_analytic f hh hΓ hcoeff
  -- `G` is continuous at 0, hence `‖G q‖ ≤ ‖G 0‖ + 1` eventually.
  have hC : ContinuousAt G 0 := hG.continuousAt
  have hEv : ∀ᶠ q in nhds (0 : ℂ), ‖G q‖ ≤ ‖G 0‖ + 1 := by
    have htend : Filter.Tendsto G (nhds 0) (nhds (G 0)) := hC
    have := Metric.tendsto_nhds.mp htend 1 zero_lt_one
    filter_upwards [this] with q hq
    have hdist : ‖G q - G 0‖ < 1 := by simpa [dist_eq_norm] using hq
    have htri : ‖G q‖ ≤ ‖G 0‖ + ‖G q - G 0‖ := by
      have := norm_add_le (G 0) (G q - G 0); simpa using this
    linarith [le_of_lt hdist]
  -- Direct bound: cuspFunction h f q = q^n · G q ⇒ ‖cuspFunction‖ ≤ ‖q^n‖ · (‖G 0‖ + 1).
  refine Asymptotics.IsBigO.of_bound (‖G 0‖ + 1) ?_
  filter_upwards [hEq, hEv] with q hq hev
  rw [hq, smul_eq_mul, norm_mul]
  have : ‖q ^ n‖ * ‖G q‖ ≤ ‖q ^ n‖ * (‖G 0‖ + 1) := by
    apply mul_le_mul_of_nonneg_left hev (norm_nonneg _)
  calc ‖q ^ n‖ * ‖G q‖
      ≤ ‖q ^ n‖ * (‖G 0‖ + 1) := this
    _ = (‖G 0‖ + 1) * ‖q ^ n‖ := by ring
    _ = (‖G 0‖ + 1) * ‖(q ^ n : ℂ)‖ := rfl

/-- Higher-order exponential decay at `∞` for modular forms whose first
`n` `q`-coefficients vanish.

Composition of `cuspFunction_isBigO_pow_of_qExpansion_coeff_zero` (Big-O
near `q = 0`) with `qParam_tendsto_atImInfty` (which sends `atImInfty`
to `nhds 0` via `q τ = exp(2πiτ/h) → 0`).  The resulting decay rate
`2π·n/h` matches the highest non-vanishing q-coefficient. -/
theorem exp_decay_atImInfty_of_qExpansion_coeff_zero
    {F : Type*} [FunLike F ℍ ℂ] (f : F) {k : ℤ} {h : ℝ}
    {Γ : Subgroup (GL (Fin 2) ℝ)} [ModularFormClass F Γ k]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    {n : ℕ}
    (hcoeff : ∀ m < n,
      (UpperHalfPlane.qExpansion h f).coeff m = 0) :
    (f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-2 * Real.pi * n * τ.im / h) := by
  have hcusp : UpperHalfPlane.cuspFunction h (f : ℍ → ℂ) =O[nhds (0 : ℂ)]
      fun q : ℂ => q ^ n :=
    cuspFunction_isBigO_pow_of_qExpansion_coeff_zero f hh hΓ hcoeff
  -- Compose with `q τ → 0`.
  have htend : Filter.Tendsto (fun τ : ℍ => (Function.Periodic.qParam h (τ : ℂ)))
      UpperHalfPlane.atImInfty (nhds 0) :=
    UpperHalfPlane.qParam_tendsto_atImInfty hh
  have hcomp : (fun τ : ℍ =>
      UpperHalfPlane.cuspFunction h (f : ℍ → ℂ)
        (Function.Periodic.qParam h (τ : ℂ))) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => (Function.Periodic.qParam h (τ : ℂ)) ^ n :=
    hcusp.comp_tendsto htend
  -- LHS equals `f τ` via `eq_cuspFunction`.
  have hLHSeq : (fun τ : ℍ =>
      UpperHalfPlane.cuspFunction h (f : ℍ → ℂ)
        (Function.Periodic.qParam h (τ : ℂ))) = (fun τ : ℍ => (f : ℍ → ℂ) τ) := by
    funext τ
    simpa using
      (SlashInvariantFormClass.eq_cuspFunction (f := f) τ hΓ hh.ne')
  -- RHS bound: `‖(q τ)^n‖ = exp(-2π·n·τ.im/h)`.
  have hRHSnorm : ∀ τ : ℍ, ‖(Function.Periodic.qParam h (τ : ℂ)) ^ n‖
      = Real.exp (-2 * Real.pi * n * τ.im / h) := by
    intro τ
    rw [norm_pow, Function.Periodic.norm_qParam,
      ← Real.exp_nat_mul]
    congr 1
    have hcoe : ((τ : ℂ).im) = τ.im := UpperHalfPlane.coe_im τ
    rw [hcoe]
    field_simp
  rw [hLHSeq] at hcomp
  refine hcomp.trans ?_
  refine Asymptotics.IsBigO.of_bound 1 ?_
  refine Filter.Eventually.of_forall (fun τ => ?_)
  rw [hRHSnorm τ, Real.norm_of_nonneg (Real.exp_pos _).le]
  simp

end Modular
end Number
end Ripple
