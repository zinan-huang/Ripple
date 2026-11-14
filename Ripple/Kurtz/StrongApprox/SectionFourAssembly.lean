-- Ripple/Kurtz/StrongApprox/SectionFourAssembly.lean
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.Moments.Basic

/-!
# Section 4 assembly: rational suprema, tails to exponential moments, final assembly

The parts of the Section 4 argument (Kurtz 1978, Theorem 4.4) that need no stochastic integral.

* `pathSupIcc` is the countable rational supremum of a path norm on `[0, T]`; it is measurable
  and, for paths continuous on `[0, T]`, dominates the norm at every time of `[0, T]`.
* `integrable_exp_mul_of_exp_tail` and `integrable_exp_mul_of_gauss_tail` turn an exponential or
  sub-Gaussian tail bound into an exponential moment, with explicit constants
  `expTailMomentConst` and `gaussTailMomentConst` (layer cake).
* `sectionFour_final_assembly` combines uniform exponential moments of `betaT` and `R` with the
  two pathwise bounds into the bound `‖√N (Xchain - X) - V‖ ≤ γ_N log N / √N` and a uniform
  exponential moment of `γ_N = betaT N + R N / log 2` (Cauchy-Schwarz, no independence).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Ripple.Kurtz.StrongApprox.SectionFourAssembly

/-! ## Rational suprema on `[0, T]` -/

/-- Rational times in `[0, T]`. -/
abbrev RatIcc (T : ℝ) := {q : ℚ // 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T}

/-- The supremum of `‖Y q ω‖` over rational times in `[0, T]`, as a real number. -/
def pathSupIcc {Ω : Type*} {d : ℕ} (T : ℝ) (Y : ℝ → Ω → (Fin d → ℝ)) (ω : Ω) : ℝ :=
  (⨆ q : RatIcc T, ENNReal.ofReal ‖Y (q : ℝ) ω‖).toReal

theorem pathSupIcc_nonneg {Ω : Type*} {d : ℕ} (T : ℝ) (Y : ℝ → Ω → (Fin d → ℝ)) (ω : Ω) :
    0 ≤ pathSupIcc T Y ω :=
  ENNReal.toReal_nonneg

theorem measurable_pathSupIcc {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (T : ℝ)
    (Y : ℝ → Ω → (Fin d → ℝ)) (hY : ∀ q : RatIcc T, Measurable (Y (q : ℝ))) :
    Measurable (pathSupIcc T Y) := by
  unfold pathSupIcc
  refine Measurable.ennreal_toReal (Measurable.iSup fun q => ?_)
  exact (hY q).norm.ennreal_ofReal

/-- Rational times of `[0, T]` come arbitrarily close to every time of `[0, T]`. -/
theorem exists_ratIcc_near {T : ℝ} (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) {ε : ℝ}
    (hε : 0 < ε) : ∃ q : RatIcc T, |(q : ℝ) - t| < ε := by
  obtain ⟨ht0, htT⟩ := ht
  rcases lt_or_eq_of_le htT with hlt | heq
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t < min T (t + ε) from
      lt_min hlt (by linarith))
    have hq3 : (q : ℝ) < T := lt_of_lt_of_le hq2 (min_le_left _ _)
    have hq4 : (q : ℝ) < t + ε := lt_of_lt_of_le hq2 (min_le_right _ _)
    refine ⟨⟨q, by linarith, hq3.le⟩, ?_⟩
    rw [abs_lt]
    constructor <;> linarith
  · subst heq
    rcases eq_or_lt_of_le ht0 with h0 | hpos
    · refine ⟨⟨0, by simp, by simpa using hT⟩, ?_⟩
      simp [← h0, hε]
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max 0 (t - ε) < t from
        max_lt hpos (by linarith))
      have hq3 : 0 < (q : ℝ) := lt_of_le_of_lt (le_max_left _ _) hq1
      have hq4 : t - ε < (q : ℝ) := lt_of_le_of_lt (le_max_right _ _) hq1
      refine ⟨⟨q, hq3.le, hq2.le⟩, ?_⟩
      rw [abs_lt]
      constructor <;> linarith

/-- For a path continuous on `[0, T]`, the rational supremum is finite and dominates the norm at
every time of `[0, T]`. -/
theorem norm_le_pathSupIcc {Ω : Type*} {d : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (Y : ℝ → Ω → (Fin d → ℝ)) (ω : Ω) (hcont : ContinuousOn (fun t => Y t ω) (Icc 0 T))
    {t : ℝ} (ht : t ∈ Icc 0 T) : ‖Y t ω‖ ≤ pathSupIcc T Y ω := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hcont
  have hbd : (⨆ q : RatIcc T, ENNReal.ofReal ‖Y (q : ℝ) ω‖) ≤ ENNReal.ofReal M :=
    iSup_le fun q => ENNReal.ofReal_le_ofReal (hM _ ⟨q.2.1, q.2.2⟩)
  have hne : (⨆ q : RatIcc T, ENNReal.ofReal ‖Y (q : ℝ) ω‖) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbd
  have hrat : ∀ q : RatIcc T, ‖Y (q : ℝ) ω‖ ≤ pathSupIcc T Y ω := fun q =>
    (ENNReal.ofReal_le_iff_le_toReal hne).mp
      (le_iSup (fun q : RatIcc T => ENNReal.ofReal ‖Y (q : ℝ) ω‖) q)
  by_contra hlt
  rw [not_le] at hlt
  have hc : ContinuousWithinAt (fun s => ‖Y s ω‖) (Icc 0 T) t :=
    (hcont t ht).norm
  have hev : ∀ᶠ s in 𝓝[Icc 0 T] t, pathSupIcc T Y ω < ‖Y s ω‖ :=
    hc.eventually (lt_mem_nhds hlt)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  obtain ⟨q, hq⟩ := exists_ratIcc_near hT ht hδ
  have hq' : (q : ℝ) ∈ Metric.ball t δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    exact hq
  have := hball hq' ⟨q.2.1, q.2.2⟩
  exact absurd (hrat q) (not_le.mpr this)

/-! ## Layer cake -/

section LayerCake

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem lintegral_exp_le_layer {R : Ω → ℝ} (hR : Measurable R) (hR0 : ∀ ω, 0 ≤ R ω)
    {η : ℝ} (hη : 0 < η) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (η * R ω)) ∂P ≤
      1 + ∫⁻ t in Ioi (0 : ℝ), P {ω | t < R ω} * ENNReal.ofReal (η * Real.exp (η * t)) := by
  have hint : ∀ x : ℝ, ∫ t in (0 : ℝ)..x, η * Real.exp (η * t) = Real.exp (η * x) - 1 := by
    intro x
    simp
  have h1 : ∀ ω, ENNReal.ofReal (Real.exp (η * R ω)) =
      ENNReal.ofReal (∫ t in (0 : ℝ)..R ω, η * Real.exp (η * t)) + 1 := by
    intro ω
    rw [hint]
    have hge : 1 ≤ Real.exp (η * R ω) := Real.one_le_exp (mul_nonneg hη.le (hR0 ω))
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (sub_nonneg.2 hge) zero_le_one]
    congr 1
    ring
  simp_rw [h1]
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one, add_comm]
  refine add_le_add_right (le_of_eq ?_) 1
  refine lintegral_comp_eq_lintegral_meas_lt_mul P (Eventually.of_forall hR0) hR.aemeasurable
    (fun t _ => ?_) ?_
  · exact (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).intervalIntegrable _ _
  · exact ae_of_all _ fun t => by positivity

omit [IsProbabilityMeasure P] in
theorem integrable_and_integral_le_of_lintegral_le {R : Ω → ℝ} (hR : Measurable R) {η K : ℝ}
    (hK : 0 ≤ K)
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp (η * R ω)) ∂P ≤ ENNReal.ofReal K) :
    Integrable (fun ω => Real.exp (η * R ω)) P ∧ ∫ ω, Real.exp (η * R ω) ∂P ≤ K := by
  have hm : Measurable fun ω => Real.exp (η * R ω) :=
    Real.measurable_exp.comp (measurable_const.mul hR)
  have hnn : 0 ≤ᵐ[P] fun ω => Real.exp (η * R ω) := ae_of_all _ fun ω => (Real.exp_pos _).le
  refine ⟨⟨hm.aestronglyMeasurable, ?_⟩, ?_⟩
  · exact (hasFiniteIntegral_iff_ofReal hnn).2 (lt_of_le_of_lt h ENNReal.ofReal_lt_top)
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hm.aestronglyMeasurable]
    calc (∫⁻ ω, ENNReal.ofReal (Real.exp (η * R ω)) ∂P).toReal
        ≤ (ENNReal.ofReal K).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      _ = K := ENNReal.toReal_ofReal hK

/-- Explicit constant of the exponential-tail moment bound. -/
def expTailMomentConst (a c η : ℝ) : ℝ := 1 + a * η / (c - η)

/-- Explicit constant of the sub-Gaussian-tail moment bound. -/
def gaussTailMomentConst (a b η : ℝ) : ℝ :=
  1 + a * η * Real.exp (η ^ 2 / (2 * b)) * Real.sqrt (2 * Real.pi / b)

/-- An exponential tail `P(r < R) ≤ a e^{-c r}` gives `E e^{η R} ≤ 1 + a η / (c - η)` for
`0 < η < c`. -/
theorem integrable_exp_mul_of_exp_tail {R : Ω → ℝ} (hR : Measurable R) (hR0 : ∀ ω, 0 ≤ R ω)
    {a c : ℝ} (ha : 0 ≤ a)
    (htail : ∀ r : ℝ, 0 ≤ r → P {ω | r < R ω} ≤ ENNReal.ofReal (a * Real.exp (-c * r)))
    {η : ℝ} (hη : 0 < η) (hηc : η < c) :
    Integrable (fun ω => Real.exp (η * R ω)) P ∧
      ∫ ω, Real.exp (η * R ω) ∂P ≤ expTailMomentConst a c η := by
  have hcη : 0 < c - η := sub_pos.2 hηc
  have hK : 0 ≤ expTailMomentConst a c η := by
    unfold expTailMomentConst; positivity
  refine integrable_and_integral_le_of_lintegral_le hR hK ?_
  refine (lintegral_exp_le_layer hR hR0 hη).trans ?_
  have hpt : ∀ t ∈ Ioi (0 : ℝ), P {ω | t < R ω} * ENNReal.ofReal (η * Real.exp (η * t)) ≤
      ENNReal.ofReal (a * η * Real.exp (-(c - η) * t)) := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    calc P {ω | t < R ω} * ENNReal.ofReal (η * Real.exp (η * t))
        ≤ ENNReal.ofReal (a * Real.exp (-c * t)) * ENNReal.ofReal (η * Real.exp (η * t)) := by
          gcongr; exact htail t ht0
      _ = ENNReal.ofReal (a * η * Real.exp (-(c - η) * t)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have : Real.exp (-(c - η) * t) = Real.exp (-c * t) * Real.exp (η * t) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [this]; ring
  have hint : IntegrableOn (fun t : ℝ => a * η * Real.exp (-(c - η) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (a := -(c - η)) (by linarith) 0).const_mul _
  have hcalc : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (a * η * Real.exp (-(c - η) * t)) =
      ENNReal.ofReal (a * η / (c - η)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun t => by positivity)]
    congr 1
    rw [integral_const_mul, integral_exp_mul_Ioi (a := -(c - η)) (by linarith) 0]
    field_simp
    simp
  calc (1 : ℝ≥0∞) + ∫⁻ t in Ioi (0 : ℝ), P {ω | t < R ω} * ENNReal.ofReal (η * Real.exp (η * t))
      ≤ 1 + ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (a * η * Real.exp (-(c - η) * t)) := by
        exact add_le_add_right (setLIntegral_mono' measurableSet_Ioi hpt) 1
    _ = ENNReal.ofReal (expTailMomentConst a c η) := by
        rw [hcalc, expTailMomentConst, ENNReal.ofReal_add zero_le_one (by positivity),
          ENNReal.ofReal_one]

/-- A sub-Gaussian tail `P(r < R) ≤ a e^{-b r²}` gives an exponential moment of every order. -/
theorem integrable_exp_mul_of_gauss_tail {R : Ω → ℝ} (hR : Measurable R) (hR0 : ∀ ω, 0 ≤ R ω)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (htail : ∀ r : ℝ, 0 ≤ r → P {ω | r < R ω} ≤ ENNReal.ofReal (a * Real.exp (-b * r ^ 2)))
    {η : ℝ} (hη : 0 < η) :
    Integrable (fun ω => Real.exp (η * R ω)) P ∧
      ∫ ω, Real.exp (η * R ω) ∂P ≤ gaussTailMomentConst a b η := by
  have hK : 0 ≤ gaussTailMomentConst a b η := by
    unfold gaussTailMomentConst; positivity
  refine integrable_and_integral_le_of_lintegral_le hR hK ?_
  refine (lintegral_exp_le_layer hR hR0 hη).trans ?_
  set K : ℝ := a * η * Real.exp (η ^ 2 / (2 * b)) with hKdef
  have hKnn : 0 ≤ K := by positivity
  have hpt : ∀ t ∈ Ioi (0 : ℝ), P {ω | t < R ω} * ENNReal.ofReal (η * Real.exp (η * t)) ≤
      ENNReal.ofReal (K * Real.exp (-(b / 2) * t ^ 2)) := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    calc P {ω | t < R ω} * ENNReal.ofReal (η * Real.exp (η * t))
        ≤ ENNReal.ofReal (a * Real.exp (-b * t ^ 2)) * ENNReal.ofReal (η * Real.exp (η * t)) := by
          gcongr; exact htail t ht0
      _ = ENNReal.ofReal (a * η * Real.exp (η * t - b * t ^ 2)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have : Real.exp (η * t - b * t ^ 2) = Real.exp (-b * t ^ 2) * Real.exp (η * t) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [this]; ring
      _ ≤ ENNReal.ofReal (K * Real.exp (-(b / 2) * t ^ 2)) := by
          apply ENNReal.ofReal_le_ofReal
          have hexp : Real.exp (η * t - b * t ^ 2) ≤
              Real.exp (η ^ 2 / (2 * b)) * Real.exp (-(b / 2) * t ^ 2) := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.2
            have : 0 ≤ (η - b * t) ^ 2 / (2 * b) := by positivity
            have h2 : (η - b * t) ^ 2 / (2 * b) =
                η ^ 2 / (2 * b) - η * t + b / 2 * t ^ 2 := by field_simp; ring
            nlinarith
          calc a * η * Real.exp (η * t - b * t ^ 2)
              ≤ a * η * (Real.exp (η ^ 2 / (2 * b)) * Real.exp (-(b / 2) * t ^ 2)) := by
                gcongr
            _ = K * Real.exp (-(b / 2) * t ^ 2) := by rw [hKdef]; ring
  have hint : Integrable (fun t : ℝ => K * Real.exp (-(b / 2) * t ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < b / 2)).const_mul K
  have hcalc : ∫⁻ t, ENNReal.ofReal (K * Real.exp (-(b / 2) * t ^ 2)) =
      ENNReal.ofReal (K * Real.sqrt (2 * Real.pi / b)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun t => by positivity),
      integral_const_mul, integral_gaussian]
    congr 3
    field_simp
  calc (1 : ℝ≥0∞) + ∫⁻ t in Ioi (0 : ℝ), P {ω | t < R ω} * ENNReal.ofReal (η * Real.exp (η * t))
      ≤ 1 + ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (K * Real.exp (-(b / 2) * t ^ 2)) := by
        exact add_le_add_right (setLIntegral_mono' measurableSet_Ioi hpt) 1
    _ ≤ 1 + ∫⁻ t, ENNReal.ofReal (K * Real.exp (-(b / 2) * t ^ 2)) :=
        add_le_add_right (setLIntegral_le_lintegral _ _) 1
    _ = ENNReal.ofReal (gaussTailMomentConst a b η) := by
        rw [hcalc, gaussTailMomentConst, ENNReal.ofReal_add zero_le_one (by positivity),
          ENNReal.ofReal_one]

end LayerCake

/-! ## Final assembly -/

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- A family `f N`, `N ≥ 2`, of nonnegative measurable functions with a uniform exponential
moment of order `η` bounded by `C`. -/
structure UniformExpMoment (f : ℕ → Ω → ℝ) (η C : ℝ) (P : Measure Ω) : Prop where
  eta_pos : 0 < η
  measurable : ∀ N, 2 ≤ N → Measurable (f N)
  nonneg : ∀ N, 2 ≤ N → ∀ ω, 0 ≤ f N ω
  integrable : ∀ N, 2 ≤ N → Integrable (fun ω => Real.exp (η * f N ω)) P
  integral_le : ∀ N, 2 ≤ N → ∫ ω, Real.exp (η * f N ω) ∂P ≤ C

/-- `γ_N = betaT N + R N / log 2`. -/
def sectionFourGamma (betaT R : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  betaT N ω + R N ω / Real.log 2

/-- A smaller exponent keeps the exponential moment for a nonnegative function. -/
theorem integrable_exp_le_of_le {P : Measure Ω} {f : Ω → ℝ} (hf : Measurable f)
    (hf0 : ∀ ω, 0 ≤ f ω) {η C e : ℝ} (he : e ≤ η)
    (hint : Integrable (fun ω => Real.exp (η * f ω)) P)
    (hC : ∫ ω, Real.exp (η * f ω) ∂P ≤ C) :
    Integrable (fun ω => Real.exp (e * f ω)) P ∧ ∫ ω, Real.exp (e * f ω) ∂P ≤ C := by
  have hm : Measurable fun ω => Real.exp (e * f ω) :=
    Real.measurable_exp.comp (measurable_const.mul hf)
  have hle : ∀ ω, Real.exp (e * f ω) ≤ Real.exp (η * f ω) := fun ω =>
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right he (hf0 ω))
  have hi : Integrable (fun ω => Real.exp (e * f ω)) P :=
    hint.mono' hm.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact hle ω)
  exact ⟨hi, (integral_mono hi hint hle).trans hC⟩

/-- Cauchy-Schwarz in the form `∫ a b ≤ √(A B)` for functions `a, b ≥ 0` with
`∫ a² ≤ A` and `∫ b² ≤ B`, `A, B > 0`. -/
theorem integral_mul_le_sqrt {P : Measure Ω} {a b : Ω → ℝ} (ha : Measurable a)
    (hb : Measurable b) (ha0 : ∀ ω, 0 ≤ a ω) (hb0 : ∀ ω, 0 ≤ b ω)
    (ha2 : Integrable (fun ω => a ω ^ 2) P) (hb2 : Integrable (fun ω => b ω ^ 2) P)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hAi : ∫ ω, a ω ^ 2 ∂P ≤ A) (hBi : ∫ ω, b ω ^ 2 ∂P ≤ B) :
    Integrable (fun ω => a ω * b ω) P ∧ ∫ ω, a ω * b ω ∂P ≤ Real.sqrt (A * B) := by
  set u := Real.sqrt A with hu
  set v := Real.sqrt B with hv
  have hupos : 0 < u := Real.sqrt_pos.2 hA
  have hvpos : 0 < v := Real.sqrt_pos.2 hB
  have hu2 : u ^ 2 = A := Real.sq_sqrt hA.le
  have hv2 : v ^ 2 = B := Real.sq_sqrt hB.le
  set s := v / u with hs
  have hspos : 0 < s := div_pos hvpos hupos
  have hpt : ∀ ω, a ω * b ω ≤ (s * a ω ^ 2 + b ω ^ 2 / s) / 2 := by
    intro ω
    have h : s * a ω ^ 2 + b ω ^ 2 / s - 2 * (a ω * b ω) = (s * a ω - b ω) ^ 2 / s := by
      field_simp; ring
    have h0 : 0 ≤ (s * a ω - b ω) ^ 2 / s := by positivity
    linarith
  have hdom : Integrable (fun ω => (s * a ω ^ 2 + b ω ^ 2 / s) / 2) P :=
    ((ha2.const_mul s).add (hb2.div_const s)).div_const 2
  have hab : Measurable fun ω => a ω * b ω := ha.mul hb
  have hi : Integrable (fun ω => a ω * b ω) P :=
    hdom.mono' hab.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (mul_nonneg (ha0 ω) (hb0 ω))]; exact hpt ω)
  refine ⟨hi, ?_⟩
  have h1 : ∫ ω, a ω * b ω ∂P ≤ ∫ ω, (s * a ω ^ 2 + b ω ^ 2 / s) / 2 ∂P :=
    integral_mono hi hdom hpt
  have h2 : ∫ ω, (s * a ω ^ 2 + b ω ^ 2 / s) / 2 ∂P =
      (s * ∫ ω, a ω ^ 2 ∂P + (∫ ω, b ω ^ 2 ∂P) / s) / 2 := by
    rw [integral_div, integral_add (ha2.const_mul s) (hb2.div_const s), integral_const_mul,
      integral_div]
  have h3 : (s * ∫ ω, a ω ^ 2 ∂P + (∫ ω, b ω ^ 2 ∂P) / s) / 2 ≤ (s * A + B / s) / 2 := by
    have := mul_le_mul_of_nonneg_left hAi hspos.le
    have := div_le_div_of_nonneg_right hBi hspos.le
    linarith
  have h4 : (s * A + B / s) / 2 = Real.sqrt (A * B) := by
    rw [Real.sqrt_mul hA.le, ← hu, ← hv, hs, ← hu2, ← hv2]
    field_simp
    ring
  linarith

theorem sectionFour_final_assembly {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ}
    {X : ℝ → Fin d → ℝ} {V : ℝ → Ω → Fin d → ℝ} {Z Xchain : ℕ → ℝ → Ω → Fin d → ℝ}
    {betaT R : ℕ → Ω → ℝ} {lambdaBeta CBeta etaR CR : ℝ}
    (hBeta : UniformExpMoment betaT lambdaBeta CBeta P)
    (hR : UniformExpMoment R etaR CR P)
    (hB7 : ∀ᵐ ω ∂P, ∀ N : ℕ, 2 ≤ N → ∀ t ∈ Icc (0 : ℝ) T,
      ‖Xchain N t ω - Z N t ω‖ ≤ betaT N ω * Real.log (N : ℝ) / (N : ℝ))
    (hDiff : ∀ᵐ ω ∂P, ∀ N : ℕ, 2 ≤ N → ∀ t ∈ Icc (0 : ℝ) T,
      ‖Real.sqrt N • (Z N t ω - X t) - V t ω‖ ≤ R N ω / Real.sqrt N) :
    let etaGamma := min lambdaBeta (etaR * Real.log 2) / 2
    0 < etaGamma ∧
    (∀ N : ℕ, 2 ≤ N →
      Integrable (fun ω => Real.exp (etaGamma * sectionFourGamma betaT R N ω)) P ∧
      ∫ ω, Real.exp (etaGamma * sectionFourGamma betaT R N ω) ∂P ≤
        Real.sqrt (CBeta * CR)) ∧
    (∀ᵐ ω ∂P, ∀ N : ℕ, 2 ≤ N → ∀ t ∈ Icc (0 : ℝ) T,
      ‖Real.sqrt N • (Xchain N t ω - X t) - V t ω‖ ≤
        sectionFourGamma betaT R N ω * Real.log (N : ℝ) / Real.sqrt N) := by
  intro etaGamma
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmin : 0 < min lambdaBeta (etaR * Real.log 2) :=
    lt_min hBeta.eta_pos (mul_pos hR.eta_pos hlog2)
  have heta : 0 < etaGamma := by positivity
  refine ⟨heta, ?_, ?_⟩
  · intro N hN
    have h2e1 : 2 * etaGamma ≤ lambdaBeta := by
      have := min_le_left lambdaBeta (etaR * Real.log 2)
      simp only [etaGamma]; linarith
    have h2e2 : 2 * etaGamma / Real.log 2 ≤ etaR := by
      have := min_le_right lambdaBeta (etaR * Real.log 2)
      rw [div_le_iff₀ hlog2]
      simp only [etaGamma]; linarith
    have hβm := hBeta.measurable N hN
    have hRm := hR.measurable N hN
    -- the two factors
    set a : Ω → ℝ := fun ω => Real.exp (etaGamma * betaT N ω) with ha
    set b : Ω → ℝ := fun ω => Real.exp (etaGamma / Real.log 2 * R N ω) with hb
    have hsq : ∀ (x e : ℝ), Real.exp (e * x) ^ 2 = Real.exp (2 * e * x) := by
      intro x e; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have ha2 : (fun ω => a ω ^ 2) = fun ω => Real.exp ((2 * etaGamma) * betaT N ω) := by
      funext ω; exact hsq _ _
    have hb2 : (fun ω => b ω ^ 2) =
        fun ω => Real.exp ((2 * etaGamma / Real.log 2) * R N ω) := by
      funext ω
      rw [hsq]; congr 1; ring
    obtain ⟨hAint, hAle⟩ := integrable_exp_le_of_le hβm (hBeta.nonneg N hN)
      h2e1 (hBeta.integrable N hN) (hBeta.integral_le N hN)
    obtain ⟨hBint, hBle⟩ := integrable_exp_le_of_le hRm (hR.nonneg N hN)
      h2e2 (hR.integrable N hN)
      (hR.integral_le N hN)
    have hA1 : 1 ≤ CBeta := by
      have h1 : (1 : ℝ) ≤ ∫ ω, Real.exp ((2 * etaGamma) * betaT N ω) ∂P := by
        have := integral_mono (integrable_const (1 : ℝ)) hAint (fun ω =>
          Real.one_le_exp (mul_nonneg (by positivity) (hBeta.nonneg N hN ω)))
        simpa using this
      exact h1.trans hAle
    have hB1 : 1 ≤ CR := by
      have h1 : (1 : ℝ) ≤ ∫ ω, Real.exp ((2 * etaGamma / Real.log 2) * R N ω) ∂P := by
        have := integral_mono (integrable_const (1 : ℝ)) hBint (fun ω =>
          Real.one_le_exp (mul_nonneg (by positivity) (hR.nonneg N hN ω)))
        simpa using this
      exact h1.trans hBle
    have hcs := integral_mul_le_sqrt (P := P) (a := a) (b := b)
      (Real.measurable_exp.comp (measurable_const.mul hβm))
      (Real.measurable_exp.comp (measurable_const.mul hRm))
      (fun ω => (Real.exp_pos _).le) (fun ω => (Real.exp_pos _).le)
      (by rw [ha2]; exact hAint) (by rw [hb2]; exact hBint)
      (by linarith : 0 < CBeta) (by linarith : 0 < CR)
      (by rw [ha2]; exact hAle) (by rw [hb2]; exact hBle)
    have hprod : (fun ω => Real.exp (etaGamma * sectionFourGamma betaT R N ω)) =
        fun ω => a ω * b ω := by
      funext ω
      simp only [sectionFourGamma, ha, hb]
      rw [← Real.exp_add]; congr 1; ring
    rw [hprod]
    exact hcs
  · filter_upwards [hB7, hDiff] with ω h1 h2 N hN t ht
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < N := by linarith
    set sN := Real.sqrt N with hsN
    have hspos : 0 < sN := Real.sqrt_pos.2 hNpos
    have hsq : sN * sN = N := Real.mul_self_sqrt hNpos.le
    have hL : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN2
    have hRnn := hR.nonneg N hN ω
    have hdecomp : sN • (Xchain N t ω - X t) - V t ω =
        sN • (Xchain N t ω - Z N t ω) + (sN • (Z N t ω - X t) - V t ω) := by
      rw [smul_sub, smul_sub, smul_sub]; abel
    have hfirst : ‖sN • (Xchain N t ω - Z N t ω)‖ ≤ betaT N ω * Real.log N / sN := by
      rw [norm_smul, Real.norm_of_nonneg hspos.le]
      calc sN * ‖Xchain N t ω - Z N t ω‖ ≤ sN * (betaT N ω * Real.log N / N) :=
            mul_le_mul_of_nonneg_left (h1 N hN t ht) hspos.le
        _ = betaT N ω * Real.log N / sN := by
            rw [← hsq]; field_simp
    have hsecond : R N ω / sN ≤ R N ω / Real.log 2 * Real.log N / sN := by
      apply div_le_div_of_nonneg_right _ hspos.le
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      exact mul_le_mul_of_nonneg_left hL hRnn
    calc ‖sN • (Xchain N t ω - X t) - V t ω‖
        = ‖sN • (Xchain N t ω - Z N t ω) + (sN • (Z N t ω - X t) - V t ω)‖ := by rw [hdecomp]
      _ ≤ ‖sN • (Xchain N t ω - Z N t ω)‖ + ‖sN • (Z N t ω - X t) - V t ω‖ := norm_add_le _ _
      _ ≤ betaT N ω * Real.log N / sN + R N ω / Real.log 2 * Real.log N / sN :=
          add_le_add hfirst ((h2 N hN t ht).trans hsecond)
      _ = sectionFourGamma betaT R N ω * Real.log N / sN := by
          simp only [sectionFourGamma]; ring

end Assembly

end Ripple.Kurtz.StrongApprox.SectionFourAssembly
