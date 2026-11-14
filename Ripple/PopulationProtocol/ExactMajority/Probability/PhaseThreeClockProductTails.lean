import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockThinning

/-!
# Prefix products with conditional mean at most one (N12, step 4 scalar tool)

The step-4 estimates of PHASE3 (P13 half passages, P14's local cap spread and its
single stopping-time MGF composition (62)) all have the following shape: a product of
adapted nonnegative factors `X t`, each with conditional mean at most one given the past,
is a supermartingale, so on an initial event `E` its mean stays below `μ E`; Markov's
inequality then bounds the event on which the product is large. The factors are, for
example, `2^{[tagged participation]} (1 + 2/C)^{-[Clock pair]}` on the local cap window
and `e^{-q} 2^{[tagged participation]}` afterwards; the exponential compensation by the
observed Clock-pair count replaces the thinning of (60).

* `prefixProduct X N`: the product of `X 0, …, X (N - 1)`;
* `prefix_product_bound`: `∫ 1_E ∏_{t<N} X t ≤ μ E` for `E` in the time-zero σ-algebra;
* `prefix_product_tail`: Markov, `μ (E ∩ A) ≤ μ E / r` when the product is at least `r`
  on `E ∩ A`, with its `ENNReal` form `prefix_product_tail_ennreal`;
* `windowFactor A Y Z`: `Y` on the window `A` and `Z` off it, with the conditional-mean
  bound `windowFactor_condExp_le_one` from the bounds of `Y` on `A` and of `Z` off `A`.

Nothing here conditions on a future good event: the initial event `E` is the only
retained information and every bound is pathwise or conditional on the past.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockProductTails

open PhaseThreeScalar PhaseThreeClockPrefixTails

variable {Ω : Type*} {m : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m}

/-! ## The running product -/

/-- The product of the factors indexed by `0, …, N - 1`. -/
def prefixProduct (X : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ∏ t ∈ Finset.range N, X t ω

theorem prefixProduct_zero (X : ℕ → Ω → ℝ) (ω : Ω) : prefixProduct X 0 ω = 1 := by
  simp [prefixProduct]

theorem prefixProduct_succ (X : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) :
    prefixProduct X (N + 1) ω = prefixProduct X N ω * X N ω := by
  simp [prefixProduct, Finset.prod_range_succ]

theorem prefixProduct_nonneg {X : ℕ → Ω → ℝ} (hX : ∀ t ω, 0 ≤ X t ω) (N : ℕ) (ω : Ω) :
    0 ≤ prefixProduct X N ω :=
  Finset.prod_nonneg fun t _ => hX t ω

theorem prefixProduct_le {X : ℕ → Ω → ℝ} {b : ℝ} (hX : ∀ t ω, 0 ≤ X t ω)
    (hb : ∀ t ω, X t ω ≤ b) (N : ℕ) (ω : Ω) :
    prefixProduct X N ω ≤ b ^ N := by
  unfold prefixProduct
  calc ∏ t ∈ Finset.range N, X t ω ≤ ∏ _t ∈ Finset.range N, b :=
        Finset.prod_le_prod (fun t _ => hX t ω) (fun t _ => hb t ω)
    _ = b ^ N := by simp

theorem prefixProduct_stronglyMeasurable {X : ℕ → Ω → ℝ}
    (hX : ∀ t, StronglyMeasurable[ℱ (t + 1)] (X t)) (N : ℕ) :
    StronglyMeasurable[ℱ N] (prefixProduct X N) := by
  induction N with
  | zero =>
      have h : prefixProduct X 0 = fun _ => (1 : ℝ) := by
        funext ω
        exact prefixProduct_zero X ω
      rw [h]
      exact stronglyMeasurable_const
  | succ N ih =>
      have h : prefixProduct X (N + 1) = fun ω => prefixProduct X N ω * X N ω := by
        funext ω
        exact prefixProduct_succ X N ω
      rw [h]
      exact (ih.mono (ℱ.mono (Nat.le_succ N))).mul (hX N)

theorem prefixProduct_integrable {X : ℕ → Ω → ℝ} {b : ℝ}
    (hX : ∀ t, StronglyMeasurable[ℱ (t + 1)] (X t))
    (hnonneg : ∀ t ω, 0 ≤ X t ω) (hb : ∀ t ω, X t ω ≤ b) (N : ℕ) :
    Integrable (prefixProduct X N) μ := by
  refine Integrable.of_bound
    ((prefixProduct_stronglyMeasurable hX N).mono (ℱ.le N)).aestronglyMeasurable (b ^ N) ?_
  refine ae_of_all _ fun ω => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (prefixProduct_nonneg hnonneg N ω)]
  exact prefixProduct_le hnonneg hb N ω

theorem factor_integrable {X : ℕ → Ω → ℝ} {b : ℝ}
    (hX : ∀ t, StronglyMeasurable[ℱ (t + 1)] (X t))
    (hnonneg : ∀ t ω, 0 ≤ X t ω) (hb : ∀ t ω, X t ω ≤ b) (t : ℕ) :
    Integrable (X t) μ := by
  refine Integrable.of_bound ((hX t).mono (ℱ.le (t + 1))).aestronglyMeasurable b ?_
  refine ae_of_all _ fun ω => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg t ω)]
  exact hb t ω

/-! ## The supermartingale bound on a prefix event -/

/-- Factors with conditional mean at most one: the mean of the product on an initial
event never exceeds the probability of the event. -/
theorem prefix_product_bound {X : ℕ → Ω → ℝ} {b : ℝ}
    (hX : ∀ t, StronglyMeasurable[ℱ (t + 1)] (X t))
    (hnonneg : ∀ t ω, 0 ≤ X t ω) (hb : ∀ t ω, X t ω ≤ b)
    (hcond : ∀ t, μ[X t | ℱ t] ≤ᵐ[μ] fun _ => 1)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E) (N : ℕ) :
    (∫ ω, E.indicator (prefixProduct X N) ω ∂μ) ≤ μ.real E := by
  classical
  let Z : ℕ → Ω → ℝ := fun k => E.indicator (prefixProduct X k)
  have hEm : MeasurableSet E := (ℱ.le 0) _ hE
  have hPsm (k : ℕ) : StronglyMeasurable[ℱ k] (prefixProduct X k) :=
    prefixProduct_stronglyMeasurable hX k
  have hZint (k : ℕ) : Integrable (Z k) μ :=
    (prefixProduct_integrable hX hnonneg hb k).indicator hEm
  have hZsm (k : ℕ) : StronglyMeasurable[ℱ k] (Z k) :=
    (hPsm k).indicator ((ℱ.mono (Nat.zero_le k)) _ hE)
  have hZpos (k : ℕ) (ω : Ω) : 0 ≤ Z k ω := by
    by_cases h : ω ∈ E <;> simp [Z, h, prefixProduct_nonneg hnonneg]
  change (∫ ω, Z N ω ∂μ) ≤ _
  induction N with
  | zero =>
      simpa [Z, prefixProduct_zero] using (integral_indicator_one (μ := μ) hEm).le
  | succ N ih =>
      have hXint : Integrable (X N) μ := factor_integrable hX hnonneg hb N
      have hstep : Z (N + 1) = Z N * X N := by
        funext ω
        by_cases h : ω ∈ E <;> simp [Z, h, prefixProduct_succ]
      have hstepae : Z (N + 1) =ᵐ[μ] Z N * X N :=
        Filter.Eventually.of_forall (congrFun hstep)
      have hprodint : Integrable (Z N * X N) μ := (hZint (N + 1)).congr hstepae
      have hce : μ[Z (N + 1) | ℱ N] =ᵐ[μ] Z N * μ[X N | ℱ N] :=
        (condExp_congr_ae hstepae).trans
          (condExp_mul_of_stronglyMeasurable_left (hZsm N) hprodint hXint)
      have hbound : μ[Z (N + 1) | ℱ N] ≤ᵐ[μ] Z N := by
        filter_upwards [hce, hcond N] with ω hceω hcω
        rw [hceω]
        change Z N ω * μ[X N | ℱ N] ω ≤ Z N ω
        calc Z N ω * μ[X N | ℱ N] ω ≤ Z N ω * 1 :=
              mul_le_mul_of_nonneg_left hcω (hZpos N ω)
          _ = Z N ω := mul_one _
      calc
        (∫ ω, Z (N + 1) ω ∂μ) = ∫ ω, μ[Z (N + 1) | ℱ N] ω ∂μ :=
          (integral_condExp (ℱ.le N)).symm
        _ ≤ ∫ ω, Z N ω ∂μ := integral_mono_ae integrable_condExp (hZint N) hbound
        _ ≤ μ.real E := ih

/-- Markov's inequality for the product on a prefix event: if the product is at least
`r > 0` on `E ∩ A`, then `μ (E ∩ A) ≤ μ E / r`. -/
theorem prefix_product_tail {X : ℕ → Ω → ℝ} {b : ℝ}
    (hX : ∀ t, StronglyMeasurable[ℱ (t + 1)] (X t))
    (hnonneg : ∀ t ω, 0 ≤ X t ω) (hb : ∀ t ω, X t ω ≤ b)
    (hcond : ∀ t, μ[X t | ℱ t] ≤ᵐ[μ] fun _ => 1)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E) (N : ℕ) (A : Set Ω) {r : ℝ} (hr : 0 < r)
    (hA : ∀ ω ∈ E ∩ A, r ≤ prefixProduct X N ω) :
    μ.real (E ∩ A) ≤ μ.real E / r := by
  classical
  let Z : Ω → ℝ := E.indicator (prefixProduct X N)
  have hEm : MeasurableSet E := (ℱ.le 0) _ hE
  have hZint : Integrable Z μ := (prefixProduct_integrable hX hnonneg hb N).indicator hEm
  have hZpos : ∀ ω, 0 ≤ Z ω := by
    intro ω
    by_cases h : ω ∈ E <;> simp [Z, h, prefixProduct_nonneg hnonneg]
  have hsub : E ∩ A ⊆ {ω | r ≤ Z ω} := by
    intro ω hω
    change r ≤ Z ω
    rw [show Z ω = prefixProduct X N ω by simp [Z, hω.1]]
    exact hA ω hω
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hZpos) hZint r
  calc
    μ.real (E ∩ A) ≤ μ.real {ω | r ≤ Z ω} := measureReal_mono hsub
    _ ≤ (∫ ω, Z ω ∂μ) / r := by
      rw [le_div_iff₀ hr]
      simpa only [mul_comm] using hmarkov
    _ ≤ μ.real E / r :=
      div_le_div_of_nonneg_right (prefix_product_bound hX hnonneg hb hcond E hE N) hr.le

/-- The `ENNReal` form of `prefix_product_tail`. -/
theorem prefix_product_tail_ennreal {X : ℕ → Ω → ℝ} {b : ℝ}
    (hX : ∀ t, StronglyMeasurable[ℱ (t + 1)] (X t))
    (hnonneg : ∀ t ω, 0 ≤ X t ω) (hb : ∀ t ω, X t ω ≤ b)
    (hcond : ∀ t, μ[X t | ℱ t] ≤ᵐ[μ] fun _ => 1)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E) (N : ℕ) (A : Set Ω) {r : ℝ} (hr : 0 < r)
    (hA : ∀ ω ∈ E ∩ A, r ≤ prefixProduct X N ω) :
    μ (E ∩ A) ≤ ENNReal.ofReal (1 / r) * μ E := by
  apply PhaseThreeClockThinning.measure_le_of_real_weighted_bound μ _ _ _
    (by positivity)
  rw [one_div, inv_mul_eq_div]
  exact prefix_product_tail hX hnonneg hb hcond E hE N A hr hA

/-! ## Window factors -/

/-- `Y` on the window `A`, `Z` off it. -/
def windowFactor (A : Set Ω) (Y Z : Ω → ℝ) : Ω → ℝ :=
  A.indicator Y + Aᶜ.indicator Z

theorem windowFactor_of_mem {A : Set Ω} {Y Z : Ω → ℝ} {ω : Ω} (h : ω ∈ A) :
    windowFactor A Y Z ω = Y ω := by
  simp [windowFactor, h]

theorem windowFactor_of_not_mem {A : Set Ω} {Y Z : Ω → ℝ} {ω : Ω} (h : ω ∉ A) :
    windowFactor A Y Z ω = Z ω := by
  simp [windowFactor, h]

theorem windowFactor_nonneg {A : Set Ω} {Y Z : Ω → ℝ} (hY : ∀ ω, 0 ≤ Y ω)
    (hZ : ∀ ω, 0 ≤ Z ω) (ω : Ω) : 0 ≤ windowFactor A Y Z ω := by
  by_cases h : ω ∈ A
  · rw [windowFactor_of_mem h]; exact hY ω
  · rw [windowFactor_of_not_mem h]; exact hZ ω

theorem windowFactor_le {A : Set Ω} {Y Z : Ω → ℝ} {b : ℝ} (hY : ∀ ω, Y ω ≤ b)
    (hZ : ∀ ω, Z ω ≤ b) (ω : Ω) : windowFactor A Y Z ω ≤ b := by
  by_cases h : ω ∈ A
  · rw [windowFactor_of_mem h]; exact hY ω
  · rw [windowFactor_of_not_mem h]; exact hZ ω

theorem windowFactor_stronglyMeasurable {m' : MeasurableSpace Ω} {A : Set Ω} {Y Z : Ω → ℝ}
    (hA : MeasurableSet[m'] A) (hY : StronglyMeasurable[m'] Y)
    (hZ : StronglyMeasurable[m'] Z) :
    StronglyMeasurable[m'] (windowFactor A Y Z) :=
  (hY.indicator hA).add (hZ.indicator hA.compl)

/-- The conditional mean of a window factor is at most one when `Y` has conditional mean
at most one on the window and `Z` off it; the window must be known at the conditioning
time. -/
theorem windowFactor_condExp_le_one {A : Set Ω} {Y Z : Ω → ℝ} {t : ℕ}
    (hA : MeasurableSet[ℱ t] A) (hY : Integrable Y μ) (hZ : Integrable Z μ)
    (hcondY : ∀ᵐ ω ∂μ, ω ∈ A → μ[Y | ℱ t] ω ≤ 1)
    (hcondZ : ∀ᵐ ω ∂μ, ω ∉ A → μ[Z | ℱ t] ω ≤ 1) :
    μ[windowFactor A Y Z | ℱ t] ≤ᵐ[μ] fun _ => 1 := by
  have hYi : Integrable (A.indicator Y) μ := hY.indicator ((ℱ.le t) _ hA)
  have hZi : Integrable (Aᶜ.indicator Z) μ := hZ.indicator ((ℱ.le t) _ hA.compl)
  filter_upwards [condExp_add hYi hZi (ℱ t), condExp_indicator hY hA,
    condExp_indicator hZ hA.compl, hcondY, hcondZ] with ω ha hl hr hcY hcZ
  change μ[A.indicator Y + Aᶜ.indicator Z | ℱ t] ω ≤ 1
  simp only [Pi.add_apply] at ha
  rw [ha, hl, hr]
  by_cases h : ω ∈ A
  · have h' : ω ∉ Aᶜ := fun hc => hc h
    rw [Set.indicator_of_mem h, Set.indicator_of_notMem h', add_zero]
    exact hcY h
  · have h' : ω ∈ Aᶜ := h
    rw [Set.indicator_of_notMem h, Set.indicator_of_mem h', zero_add]
    exact hcZ h

/-- The constant factor one has conditional mean one. -/
theorem condExp_one_le (t : ℕ) :
    ∀ᵐ ω ∂μ, μ[(fun _ : Ω => (1 : ℝ)) | ℱ t] ω ≤ 1 := by
  rw [condExp_const (ℱ.le t) (1 : ℝ)]
  exact ae_of_all _ fun _ => le_rfl

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockProductTails

end
