/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockDepletionTail` — the per-clock depletion LOWER tail (Janson), PROVEN

This file discharges the *concentration* behind `hdec` in
`ClockCounterSurvival.survival_union_bound`: the probability that a single clock,
starting at counter `R`, has DEPLETED (reached counter `0`, i.e. accumulated `R`
decrements) within `H` steps is exponentially small whenever `H` is below the
mean depletion window `R / q` (where `q` is the per-step decrement probability).

## The mathematical fact (Doty et al. §4, Janson 2018)

A clock needs `R` decrements to deplete.  Its `R`-th-decrement waiting time is a
sum `S_R = ∑_{i<R} X_i` of `R` i.i.d. *geometric* decrement-gap variables, each a
shifted-`Geometric(q)` waiting time with mean `q⁻¹`, so `μ := E[S_R] = R / q`.
"Depleted within `H` steps" is exactly the LOWER-tail event `{S_R ≤ H}`.  Writing
`λ := H q / R = H / μ`, the hypothesis `H q < R` is `λ < 1`, and Janson's lower
tail (the `λ ≤ 1` half of Doty Theorem 4.3) gives

  `P[S_R ≤ H] = P[S_R ≤ λ μ] ≤ exp(−q · μ · (λ − 1 − log λ)) = exp(−R (λ − 1 − log λ))`.

Since `λ − 1 − log λ ≥ (1/8)(1 − λ)²` for `0 ≤ 1 − λ < 1`
(`janson_log_rate_lower_quadratic`), the rate is *strictly positive* and
quantitatively `≥ (R/8)(1 − H q / R)²`.

## What is PROVEN here (NOT carried)

* `iid_shifted_geometric_lower_tail` — the abstract Janson lower-tail
  concentration for a sum of `R` i.i.d. shifted-`Geometric(q)` variables on an
  arbitrary probability space, with the *positive* exponential rate.  This is the
  CONCENTRATION itself, proven from the `JansonGeometric` engine — it is **not**
  a hypothesis.
* `depletion_tail_rate_pos` — the rate `R (λ − 1 − log λ)` is `≥ (R/8)(1 − Hq/R)²`,
  hence strictly positive when `H q < R` and `0 < R`.
* `clock_depletion_tail_bridge` — a thin bridge: GIVEN the kernel→geometric
  coupling `P[Depleted by H under kernel] ≤ P[S_R ≤ H]` (the protocol-side
  comparison, the only carried input), it delivers exactly the `p_tail` bound
  that `survival_union_bound`'s `hdec` requires.  The concentration inside is the
  PROVEN `iid_shifted_geometric_lower_tail`, not an assumption.

The coupling `P[Depleted by H] ≤ P[S_R ≤ H]` (kernel ↦ geometric stochastic
domination) is genuinely a *separate* protocol fact and is the only thing carried;
the EXPONENTIAL TAIL is discharged here from Janson.  This is exactly the split the
task statement permits: the concentration is proven, the coupling is thin/carried.

Reuses: `ExactMajority.janson_geom_lower_tail_of_shifted_geometric_iInf_parameter`,
`ExactMajority.shifted_geometric_integrable_exp_sum_of_identDistrib`,
`ExactMajority.janson_log_rate_lower_quadratic` (all from `JansonGeometric.lean`).

NEW file; no existing file edited; no `sorry`/`admit`/`axiom`/`native_decide`.
Reference: Doty et al. (arXiv:2106.10201v2) §3.4, §4 (Theorem 4.3, Janson [39]).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.JansonGeometric

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Real

namespace ClockDepletionTail

/-! ## Part B — the positive Janson rate.

`R (λ − 1 − log λ) ≥ (R/8)(1 − λ)²` for `λ = H q / R ∈ [0, 1)`, so the depletion
rate is strictly positive when `H q < R` and `0 < R`. -/

/-- **Depletion rate positivity (quantitative).**  With `λ := H q / R`, if
`0 < R`, `0 < H q` and `H q < R` (so `0 < λ < 1`), the Janson rate satisfies
`R (λ − 1 − log λ) ≥ (R / 8) (1 − λ)² > 0`. -/
theorem depletion_tail_rate_pos {q : ℝ} {R H : ℕ}
    (hHq_pos : 0 < (H : ℝ) * q) (hR : 0 < R) (hRH : (H : ℝ) * q < R) :
    let lam : ℝ := (H : ℝ) * q / R
    0 < (R : ℝ) * (lam - 1 - Real.log lam) ∧
      (R : ℝ) / 8 * (1 - lam) ^ 2 ≤ (R : ℝ) * (lam - 1 - Real.log lam) := by
  intro lam
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hlam_pos : 0 < lam := div_pos hHq_pos hRpos
  have hlam_lt_one : lam < 1 := by
    rw [div_lt_one hRpos]; exact hRH
  set ε : ℝ := 1 - lam with hε
  have hε_nonneg : 0 ≤ ε := by rw [hε]; linarith
  have hε_lt_one : ε < 1 := by rw [hε]; linarith
  -- `(1 - ε) - 1 - log (1 - ε) ≥ (1/8) ε²`, and `1 - ε = lam`.
  have hquad := janson_log_rate_lower_quadratic hε_nonneg hε_lt_one
  have hlam_eq : (1 : ℝ) - ε = lam := by rw [hε]; ring
  rw [hlam_eq] at hquad
  -- so `lam - 1 - log lam ≥ (1/8) ε²`
  have hrate : (1 / 8 : ℝ) * ε ^ 2 ≤ lam - 1 - Real.log lam := by linarith [hquad]
  refine ⟨?_, ?_⟩
  · -- positivity
    have hε_pos : 0 < ε := by rw [hε]; linarith [hlam_lt_one]
    have hquad_pos : 0 < (1 / 8 : ℝ) * ε ^ 2 := by positivity
    have : 0 < lam - 1 - Real.log lam := lt_of_lt_of_le hquad_pos hrate
    positivity
  · -- the quantitative bound
    have : (R : ℝ) / 8 * (1 - lam) ^ 2 = (R : ℝ) * ((1 / 8 : ℝ) * ε ^ 2) := by
      rw [hε]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hrate hRpos.le

/-! ## Part C — the abstract Janson lower-tail concentration (PROVEN).

For `R` i.i.d. shifted-`Geometric(q)` variables `X_i` on an arbitrary probability
space, the depletion event `{∑_{i<R} X_i ≤ H}` has probability at most
`exp(−R (λ − 1 − log λ))` with `λ = H q / R`.  This is the concentration ITSELF;
it is discharged from `JansonGeometric`, not assumed. -/

/-- **Abstract i.i.d. shifted-geometric lower-tail (the concentration).**

Let `X 0, …, X (R−1)` be i.i.d. shifted-`Geometric(q)` waiting times on a
probability space `(Ω, P)` (each identically distributed to `n ↦ n+1` under
`geometricMeasure' q`), and `X i = 0` for `i ≥ R`.  If `0 < q ≤ 1`, `0 < R`, and
`H q < R`, then with `λ := H q / R` the depletion probability is bounded:

  `P.real {ω | ∑_{i<R} X i ω ≤ H} ≤ exp(−R · (λ − 1 − log λ))`.

The right side is `< 1` (the rate is positive by `depletion_tail_rate_pos`).  This
is Janson's geometric lower tail (Doty Thm 4.3, `λ ≤ 1` half), specialised to the
i.i.d. depletion-gap family. -/
theorem iid_shifted_geometric_lower_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ) (hq_pos : 0 < q) (hq_le_one : q ≤ 1)
    (R H : ℕ) (hR : 0 < R) (hRH : (H : ℝ) * q < R)
    (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X P)
    (h_meas : ∀ i, AEMeasurable (X i) P)
    (h_geom_ge_one : ∀ i, ∀ᵐ ω ∂P, 1 ≤ X i ω)
    (_h_support : ∀ i ≥ R, ∀ᵐ ω ∂P, X i ω = 0)
    (_h_geom_dist : ∀ i, ∫ ω, X i ω ∂P = q⁻¹)
    (hident : ∀ i (_hi : i ∈ Finset.range R),
      IdentDistrib (X i) (fun n : ℕ => (n : ℝ) + 1) P
        (geometricMeasure' hq_pos hq_le_one)) :
    P.real {ω | (∑ i ∈ Finset.range R, X i ω) ≤ (H : ℝ)} ≤
      Real.exp (-(R : ℝ) * ((H : ℝ) * q / R - 1 - Real.log ((H : ℝ) * q / R))) := by
  classical
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  -- ### Degenerate case `H = 0`: depletion in 0 steps is a.e. impossible.
  -- Each `X i ≥ 1` a.e. for `i < R` and `R ≥ 1`, so `∑_{i<R} X i ≥ 1 > 0 = H` a.e.;
  -- hence the event is null and the bound is trivial.
  rcases Nat.eq_zero_or_pos H with hH0 | hHpos
  · subst hH0
    -- a.e. `∑_{i<R} X i ≥ 1 > 0`, so the depletion set `{∑ ≤ 0}` is null.
    have hmem : (0 : ℕ) ∈ Finset.range R := Finset.mem_range.mpr hR
    have hae_sum_ge : ∀ᵐ ω ∂P, (1 : ℝ) ≤ ∑ i ∈ Finset.range R, X i ω := by
      -- from `∀ i, ∀ᵐ ω, 1 ≤ X i ω`: every term is ≥ 1 a.e.
      have hall : ∀ᵐ ω ∂P, ∀ i, (1 : ℝ) ≤ X i ω := ae_all_iff.mpr h_geom_ge_one
      filter_upwards [hall] with ω hω
      calc (1 : ℝ) = ∑ _i ∈ ({0} : Finset ℕ), (1 : ℝ) := by simp
        _ ≤ ∑ i ∈ Finset.range R, (1 : ℝ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro j hj; rw [Finset.mem_singleton] at hj; subst hj; exact hmem
            · intro _ _ _; norm_num
        _ ≤ ∑ i ∈ Finset.range R, X i ω := Finset.sum_le_sum (fun i _ => hω i)
    have hnull : P {ω | (∑ i ∈ Finset.range R, X i ω) ≤ ((0 : ℕ) : ℝ)} = 0 := by
      rw [← nonpos_iff_eq_zero]
      calc P {ω | (∑ i ∈ Finset.range R, X i ω) ≤ ((0 : ℕ) : ℝ)}
          ≤ P {ω | ¬ (1 : ℝ) ≤ ∑ i ∈ Finset.range R, X i ω} := by
            apply measure_mono
            intro ω hω
            simp only [Set.mem_setOf_eq, Nat.cast_zero] at hω
            simp only [Set.mem_setOf_eq, not_le]
            linarith
        _ = 0 := hae_sum_ge
    rw [Measure.real, hnull, ENNReal.toReal_zero]
    exact (Real.exp_pos _).le
  -- ### Main case `0 < H`, so `0 < λ`.
  --
  -- We assemble the Chernoff bound DIRECTLY (Markov on `exp(-s·S)` + product MGF +
  -- the analytic Janson pointwise log-MGF inequality) with the GENUINE minimum
  -- `p_min = q`.  We do NOT route through the `_of_shifted_geometric_*_iInf/janson`
  -- wrappers: their `p_min := ⨅ i ∈ Finset.range R, p i` convention takes an `iInf`
  -- over all `i : ℕ`, whose non-member branches contribute `sInf ∅ = 0`, forcing
  -- `p_min = 0` and a vacuous `exp 0 = 1` bound.  The non-vacuous content lives in
  -- `janson_geom_log_chernoff_of_pointwise_bound` (free `p_min`) and
  -- `shifted_geometric_mgf_closedForm_log_le_lower_janson_point`, which we use here.
  set p : ℕ → ℝ := fun _ => q with hp_def
  set μ_X : ℝ := ∑ i ∈ Finset.range R, (p i)⁻¹ with hμ_def
  have hμ_eq : μ_X = (R : ℝ) / q := by
    rw [hμ_def]
    simp only [hp_def]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  set lam : ℝ := (H : ℝ) * q / R with hlam_def
  have hHpos' : (0 : ℝ) < H := by exact_mod_cast hHpos
  have hlam_pos : 0 < lam := by
    rw [hlam_def]; exact div_pos (mul_pos hHpos' hq_pos) hRpos
  have hlam_lt_one : lam < 1 := by rw [hlam_def, div_lt_one hRpos]; exact hRH
  have hlam_mu : lam * μ_X = (H : ℝ) := by rw [hlam_def, hμ_eq]; field_simp
  -- Janson optimized negative parameter `t = -s`, `s = (1/λ − 1) q ≥ 0`.
  set s : ℝ := (lam⁻¹ - 1) * q with hs_def
  have hs_nonneg : 0 ≤ s := by
    rw [hs_def]
    apply mul_nonneg _ hq_pos.le
    have hone_le_inv : 1 ≤ lam⁻¹ := (one_le_inv₀ hlam_pos).2 hlam_lt_one.le
    linarith
  have ht_neg : (-s) ≤ 0 := by linarith
  have hconv : ∀ i ∈ Finset.range R, (1 - p i) * Real.exp (-s) < 1 := by
    intro i _
    simp only [hp_def]
    have h1 : (1 - q) * Real.exp (-s) ≤ (1 - q) * 1 := by
      apply mul_le_mul_of_nonneg_left _ (by linarith [hq_le_one] : (0:ℝ) ≤ 1 - q)
      exact (Real.exp_le_one_iff).mpr ht_neg
    have : (1 - q) * Real.exp (-s) ≤ 1 - q := by simpa using h1
    linarith [hq_pos]
  -- Integrability of `exp(-s · ∑ X_i)`.
  have h_int : Integrable (fun ω => Real.exp ((-s) * ∑ i ∈ Finset.range R, X i ω)) P :=
    shifted_geometric_integrable_exp_sum_of_identDistrib
      (P := P) (k := R) (X := X) (p := p) (t := -s) h_indep h_meas
      (fun i _ => by simpa [hp_def] using hq_pos)
      (fun i _ => by simpa [hp_def] using hq_le_one)
      hconv
      (by intro i hi; simpa [hp_def] using hident i hi)
  -- Define the depletion sum `S`.
  set S : Ω → ℝ := fun ω => ∑ i ∈ Finset.range R, X i ω with hS_def
  -- Step 1: Markov on `exp(-s·S)`.
  have h_markov : P.real {ω | S ω ≤ (H : ℝ)} ≤ Real.exp (-(-s) * (H : ℝ)) * mgf S P (-s) :=
    measure_le_le_exp_mul_mgf (H : ℝ) ht_neg h_int
  -- Step 2: `mgf S P (-s) = ∏ exp(-s)·q·(1-(1-q)exp(-s))⁻¹`.
  have h_sum_mgf : mgf S P (-s) = ∏ i ∈ Finset.range R, mgf (X i) P (-s) := by
    have hfun : S =ᵐ[P] (∑ i ∈ Finset.range R, X i) :=
      Filter.Eventually.of_forall (by intro ω; simp [hS_def, Finset.sum_apply])
    rw [hS_def, mgf_congr hfun]
    exact h_indep.mgf_sum₀ h_meas (Finset.range R)
  have h_prod_closed :
      (∏ i ∈ Finset.range R, mgf (X i) P (-s)) =
        ∏ i ∈ Finset.range R,
          Real.exp (-s) * p i * (1 - (1 - p i) * Real.exp (-s))⁻¹ :=
    shifted_geometric_product_mgf_of_identDistrib_of_nonpos
      (P := P) (k := R) (X := X) (p := p) (t := -s)
      (fun i _ => by simpa [hp_def] using hq_pos)
      (fun i _ => by simpa [hp_def] using hq_le_one) ht_neg
      (by intro i hi; simpa [hp_def] using hident i hi)
  -- Step 3: the pointwise analytic Janson log-MGF bound with GENUINE `p_min = q`.
  have hpoint : ∀ i ∈ Finset.range R,
      (-s) + Real.log (p i) - Real.log (1 - (1 - p i) * Real.exp (-s)) ≤
        (-s) * lam * (p i)⁻¹ - q * (p i)⁻¹ * (lam - 1 - Real.log lam) := by
    intro i _
    simp only [hp_def]
    exact shifted_geometric_mgf_closedForm_log_le_lower_janson_point
      (p := q) (p_min := q) (lam := lam) (s := s)
      (hp_pos := hq_pos) (hpmin_nonneg := hq_pos.le) (hpmin_le := le_rfl)
      (hlam_pos := hlam_pos) (hlam_le_one := hlam_lt_one.le) (hs := hs_def)
  -- Step 3b: aggregate the pointwise bounds (free `p_min = q`).
  have hlog_chernoff :
      -(-s) * (lam * μ_X) +
        ∑ i ∈ Finset.range R,
          ((-s) + Real.log (p i) - Real.log (1 - (1 - p i) * Real.exp (-s))) ≤
      -q * μ_X * (lam - 1 - Real.log lam) :=
    janson_geom_log_chernoff_of_pointwise_bound R p (-s) μ_X q lam hμ_def hpoint
  -- Step 4: turn the log bound into the product-MGF exponential bound.
  have h_exp_prod :
      Real.exp (-(-s) * (H : ℝ)) *
          (∏ i ∈ Finset.range R,
            Real.exp (-s) * p i * (1 - (1 - p i) * Real.exp (-s))⁻¹) ≤
        Real.exp (-q * μ_X * (lam - 1 - Real.log lam)) :=
    shifted_geometric_product_mgf_closedForm_mul_le_exp_of_log_bound
      R p (-s) (H : ℝ) (-q * μ_X * (lam - 1 - Real.log lam))
      (fun i _ => by simpa [hp_def] using hq_pos) hconv
      (by rw [← hlam_mu]; exact hlog_chernoff)
  -- Assemble: Markov ⟶ rewrite MGF ⟶ exponential bound ⟶ rate `-R·(…)`.
  have hrate : -q * μ_X * (lam - 1 - Real.log lam) =
      -(R : ℝ) * (lam - 1 - Real.log lam) := by rw [hμ_eq]; field_simp
  calc P.real {ω | (∑ i ∈ Finset.range R, X i ω) ≤ (H : ℝ)}
      = P.real {ω | S ω ≤ (H : ℝ)} := by rw [hS_def]
    _ ≤ Real.exp (-(-s) * (H : ℝ)) * mgf S P (-s) := h_markov
    _ = Real.exp (-(-s) * (H : ℝ)) *
          (∏ i ∈ Finset.range R,
            Real.exp (-s) * p i * (1 - (1 - p i) * Real.exp (-s))⁻¹) := by
          rw [h_sum_mgf, h_prod_closed]
    _ ≤ Real.exp (-q * μ_X * (lam - 1 - Real.log lam)) := h_exp_prod
    _ = Real.exp (-(R : ℝ) * (lam - 1 - Real.log lam)) := by rw [hrate]

/-! ## Part D — the bridge that supplies `hdec`.

`survival_union_bound`'s `hdec` wants, for one clock identity, a bound

  `(K^H) c₀ {c | Depleted j c} ≤ p_tail`     (in `ℝ≥0∞`).

Here `K^H` is the protocol transition kernel iterate and `{Depleted j}` is the
monotone "clock `j` reached counter `0` by step `H`" event.  The ONLY protocol-side
input is the *coupling* (stochastic domination)

  `(K^H) c₀ {Depleted j} ≤ ENNReal.ofReal (P.real {ω | S_R ω ≤ H})`,

i.e. "depleted-by-`H` under the kernel" has probability at most "the `R`-th
decrement-gap sum is `≤ H`" under the i.i.d. geometric model.  This is the genuine
kernel↦geometric comparison and is the only thing carried.  The EXPONENTIAL TAIL
itself is the PROVEN `iid_shifted_geometric_lower_tail`; it is not assumed. -/

/-- **Depletion-tail bridge (delivers `hdec`).**  Given the kernel↦geometric
coupling `hcouple` for one clock, the kernel mass of "depleted within `H` steps"
is at most the exponentially-small Janson lower-tail bound.  This is exactly the
`p_tail` shape required by `ClockCounterSurvival.survival_union_bound`'s `hdec`.

The tail bound is the proven concentration; only the stochastic-domination
`hcouple` is a protocol-side input. -/
theorem clock_depletion_tail_bridge
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ) (hq_pos : 0 < q) (hq_le_one : q ≤ 1)
    (R H : ℕ) (hR : 0 < R) (hRH : (H : ℝ) * q < R)
    (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X P)
    (h_meas : ∀ i, AEMeasurable (X i) P)
    (h_geom_ge_one : ∀ i, ∀ᵐ ω ∂P, 1 ≤ X i ω)
    (h_support : ∀ i ≥ R, ∀ᵐ ω ∂P, X i ω = 0)
    (h_geom_dist : ∀ i, ∫ ω, X i ω ∂P = q⁻¹)
    (hident : ∀ i (_hi : i ∈ Finset.range R),
      IdentDistrib (X i) (fun n : ℕ => (n : ℝ) + 1) P
        (geometricMeasure' hq_pos hq_le_one))
    (depletionMass : ℝ≥0∞)
    (hcouple :
      depletionMass ≤
        ENNReal.ofReal (P.real {ω | (∑ i ∈ Finset.range R, X i ω) ≤ (H : ℝ)})) :
    depletionMass ≤
      ENNReal.ofReal
        (Real.exp (-(R : ℝ) * ((H : ℝ) * q / R - 1 - Real.log ((H : ℝ) * q / R)))) :=
  hcouple.trans
    (ENNReal.ofReal_le_ofReal
      (iid_shifted_geometric_lower_tail P q hq_pos hq_le_one R H hR hRH X
        h_indep h_meas h_geom_ge_one h_support h_geom_dist hident))

end ClockDepletionTail

end ExactMajority
