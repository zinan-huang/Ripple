-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockPrefixMaximal.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockThinning
import Mathlib.Probability.Martingale.OptionalStopping

/-!
# Prefix-weighted maximal inequality for a nonnegative supermartingale

A finite-horizon hitting time is stopped before taking its expectation.
The infinite-horizon event is then an increasing union of finite-horizon
events. The coefficient is the initial potential bound times the original
prefix probability, with no elapsed-time or excursion factor.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockPrefixMaximal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m₀}

theorem prefix_supermartingale {Z : ℕ → Ω → ℝ}
    (hZ : Supermartingale Z ℱ μ)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E) :
    Supermartingale (fun t => E.indicator (Z t)) ℱ μ := by
  classical
  have hEm : MeasurableSet E := (ℱ.le 0) _ hE
  refine supermartingale_nat (fun t => ?_) (fun t => (hZ.integrable t).indicator hEm)
    (fun t => ?_)
  · exact (hZ.stronglyMeasurable t).indicator
      ((ℱ.mono (show 0 ≤ t from zero_le)) _ hE)
  · have hEt : MeasurableSet[ℱ t] E :=
      (ℱ.mono (show 0 ≤ t from zero_le)) _ hE
    filter_upwards [condExp_indicator (hZ.integrable (t + 1)) hEt,
      hZ.condExp_ae_le (Nat.le_succ t)] with ω hce hle
    change μ[E.indicator (Z (t + 1)) | ℱ t] ω ≤ E.indicator (Z t) ω
    rw [hce]
    by_cases hω : ω ∈ E
    · simpa only [Set.indicator_of_mem hω] using hle
    · simp only [Set.indicator_of_notMem hω, le_refl]

theorem prefix_maximal_finite_real {Z : ℕ → Ω → ℝ}
    (hZ : Supermartingale Z ℱ μ) (hnonneg : ∀ t ω, 0 ≤ Z t ω)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E)
    (ε : ℝ) (hε : 0 ≤ ε) (hzero : ∀ ω ∈ E, Z 0 ω ≤ ε)
    (N : ℕ) :
    μ.real (E ∩ {ω | ∃ t ≤ N, (1 : ℝ) ≤ Z t ω}) ≤ ε * μ.real E := by
  classical
  let P : ℕ → Ω → ℝ := fun t => E.indicator (Z t)
  have hP : Supermartingale P ℱ μ := prefix_supermartingale hZ E hE
  have hPnonneg (t : ℕ) (ω : Ω) : 0 ≤ P t ω := by
    by_cases he : ω ∈ E
    · simpa only [P, Set.indicator_of_mem he] using hnonneg t ω
    · simp only [P, Set.indicator_of_notMem he, le_refl]
  let σ : Ω → WithTop ℕ :=
    fun ω => (hittingBtwn P {z : ℝ | 1 ≤ z} 0 N ω : ℕ)
  have hσ : IsStoppingTime ℱ σ :=
    hP.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hσN : ∀ ω, σ ω ≤ (N : WithTop ℕ) := by
    intro ω
    exact WithTop.coe_le_coe.mpr (hittingBtwn_le (u := P) (s := {z : ℝ | 1 ≤ z}) (n := 0)
      (m := N) ω)
  have hstopint : Integrable (stoppedValue P σ) μ :=
    integrable_stoppedValue ℕ hσ (fun t => hP.integrable t) hσN
  have hstopnonneg : ∀ᵐ ω ∂μ, 0 ≤ stoppedValue P σ ω :=
    ae_of_all _ (fun ω => hPnonneg _ ω)
  have hstopmean : (∫ ω, stoppedValue P σ ω ∂μ) ≤ ∫ ω, P 0 ω ∂μ := by
    have hopt := hP.neg.expected_stoppedValue_mono
      (isStoppingTime_const ℱ 0) hσ
      (fun ω => show (0 : WithTop ℕ) ≤ σ ω from zero_le) hσN
    rw [stoppedValue_const] at hopt
    change (∫ ω, -P 0 ω ∂μ) ≤ ∫ ω, -(stoppedValue P σ ω) ∂μ at hopt
    rw [integral_neg, integral_neg] at hopt
    linarith
  have hsub : E ∩ {ω | ∃ t ≤ N, (1 : ℝ) ≤ Z t ω} ⊆
      {ω | (1 : ℝ) ≤ stoppedValue P σ ω} := by
    rintro ω ⟨he, t, ht, hz⟩
    have hhit : ∃ t ∈ Set.Icc 0 N, P t ω ∈ {z : ℝ | 1 ≤ z} :=
      ⟨t, ⟨zero_le, ht⟩, by simpa only [P, Set.indicator_of_mem he] using hz⟩
    exact stoppedValue_hittingBtwn_mem hhit
  have hEm : MeasurableSet E := (ℱ.le 0) _ hE
  have hinitial : (∫ ω, P 0 ω ∂μ) ≤ ε * μ.real E := by
    have hdom : P 0 ≤ᵐ[μ] E.indicator (fun _ : Ω => ε) := by
      refine ae_of_all _ (fun ω => ?_)
      by_cases he : ω ∈ E
      · simpa only [P, Set.indicator_of_mem he] using hzero ω he
      · simp only [P, Set.indicator_of_notMem he, le_refl]
    have hconst :
        E.indicator (fun _ : Ω => ε) =
          fun ω => ε * E.indicator (fun _ : Ω => (1 : ℝ)) ω := by
      funext ω
      by_cases he : ω ∈ E <;> simp [he]
    calc
      (∫ ω, P 0 ω ∂μ) ≤ ∫ ω, E.indicator (fun _ : Ω => ε) ω ∂μ :=
        integral_mono_ae (hP.integrable 0) ((integrable_const ε).indicator hEm) hdom
      _ = ε * μ.real E := by
        rw [hconst, integral_const_mul, integral_indicator_const _ hEm]
        simp
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hstopnonneg hstopint (1 : ℝ)
  calc
    μ.real (E ∩ {ω | ∃ t ≤ N, (1 : ℝ) ≤ Z t ω}) ≤
        μ.real {ω | (1 : ℝ) ≤ stoppedValue P σ ω} := measureReal_mono hsub
    _ ≤ ∫ ω, stoppedValue P σ ω ∂μ := by simpa only [one_mul] using hmarkov
    _ ≤ ∫ ω, P 0 ω ∂μ := hstopmean
    _ ≤ ε * μ.real E := hinitial

theorem prefix_maximal_finite {Z : ℕ → Ω → ℝ}
    (hZ : Supermartingale Z ℱ μ) (hnonneg : ∀ t ω, 0 ≤ Z t ω)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E)
    (ε : ℝ) (hε : 0 ≤ ε) (hzero : ∀ ω ∈ E, Z 0 ω ≤ ε)
    (N : ℕ) :
    μ (E ∩ {ω | ∃ t ≤ N, (1 : ℝ) ≤ Z t ω}) ≤ ENNReal.ofReal ε * μ E :=
  PhaseThreeClockThinning.measure_le_of_real_weighted_bound μ _ E ε hε
    (prefix_maximal_finite_real hZ hnonneg E hE ε hε hzero N)

/-- Infinite-horizon Ville bound, retaining the original prefix mass. -/
theorem prefix_maximal {Z : ℕ → Ω → ℝ}
    (hZ : Supermartingale Z ℱ μ) (hnonneg : ∀ t ω, 0 ≤ Z t ω)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E)
    (ε : ℝ) (hε : 0 ≤ ε) (hzero : ∀ ω ∈ E, Z 0 ω ≤ ε) :
    μ (E ∩ {ω | ∃ t, (1 : ℝ) ≤ Z t ω}) ≤ ENNReal.ofReal ε * μ E := by
  let B : ℕ → Set Ω := fun N => E ∩ {ω | ∃ t ≤ N, (1 : ℝ) ≤ Z t ω}
  have hmono : Monotone B := by
    intro N M hNM
    rintro ω ⟨he, t, ht, hz⟩
    exact ⟨he, t, ht.trans hNM, hz⟩
  have heq : E ∩ {ω | ∃ t, (1 : ℝ) ≤ Z t ω} = ⋃ N, B N := by
    ext ω
    constructor
    · rintro ⟨he, t, hz⟩
      exact Set.mem_iUnion.mpr ⟨t, he, t, le_rfl, hz⟩
    · intro hω
      obtain ⟨N, he, t, ht, hz⟩ := Set.mem_iUnion.mp hω
      exact ⟨he, t, hz⟩
  rw [heq, hmono.measure_iUnion]
  exact iSup_le (fun N => prefix_maximal_finite hZ hnonneg E hE ε hε hzero N)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockPrefixMaximal

end
