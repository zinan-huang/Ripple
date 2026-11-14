-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockTwoPeriodIndicators.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockPrefixMaximal
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockPotentialTail

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockTwoPeriodIndicators

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m₀}

open Classical in
def periodCharge (R L : Set Ω) (f : Ω → ℝ) : Ω → ℝ :=
  (R ∪ L).indicator f

open Classical in
def periodOpportunity (R L : Set Ω) (J : Ω → ℝ) : Ω → ℝ :=
  fun ω => R.indicator (fun _ => (1 : ℝ)) ω + L.indicator J ω

open Classical in
def periodRate (R : Set Ω) (r k : ℝ) : Ω → ℝ :=
  fun ω => if ω ∈ R then r else k

theorem periodCharge_zero_one (R L : Set Ω) (f : Ω → ℝ)
    (hf : ∀ ω, f ω = 0 ∨ f ω = 1) :
    ∀ ω, periodCharge R L f ω = 0 ∨ periodCharge R L f ω = 1 := by
  classical
  intro ω
  by_cases hω : ω ∈ R ∪ L
  · simpa only [periodCharge, Set.indicator_of_mem hω] using hf ω
  · simp only [periodCharge, Set.indicator_of_notMem hω, true_or]

theorem periodOpportunity_zero_one (R L : Set Ω) (J : Ω → ℝ)
    (hd : Disjoint R L) (hJ : ∀ ω, J ω = 0 ∨ J ω = 1) :
    ∀ ω, periodOpportunity R L J ω = 0 ∨ periodOpportunity R L J ω = 1 := by
  classical
  intro ω
  by_cases hR : ω ∈ R
  · have hL : ω ∉ L := fun hL => Set.disjoint_left.mp hd hR hL
    simp only [periodOpportunity, Set.indicator_of_mem hR,
      Set.indicator_of_notMem hL, add_zero, or_true]
  · by_cases hL : ω ∈ L
    · simpa only [periodOpportunity, Set.indicator_of_notMem hR,
        Set.indicator_of_mem hL, zero_add] using hJ ω
    · simp only [periodOpportunity, Set.indicator_of_notMem hR,
        Set.indicator_of_notMem hL, add_zero, true_or]

theorem periodCharge_le_opportunity (R L : Set Ω) (f J : Ω → ℝ)
    (hd : Disjoint R L) (hf : ∀ ω, f ω = 0 ∨ f ω = 1)
    (hfJ : ∀ ω, f ω ≤ J ω) :
    ∀ ω, periodCharge R L f ω ≤ periodOpportunity R L J ω := by
  classical
  intro ω
  by_cases hR : ω ∈ R
  · have hL : ω ∉ L := fun hL => Set.disjoint_left.mp hd hR hL
    have hU : ω ∈ R ∪ L := Or.inl hR
    simp only [periodCharge, periodOpportunity, Set.indicator_of_mem hU,
      Set.indicator_of_mem hR, Set.indicator_of_notMem hL, add_zero]
    rcases hf ω with h | h <;> simp [h]
  · by_cases hL : ω ∈ L
    · have hU : ω ∈ R ∪ L := Or.inr hL
      simpa only [periodCharge, periodOpportunity, Set.indicator_of_mem hU,
        Set.indicator_of_notMem hR, Set.indicator_of_mem hL, zero_add] using hfJ ω
    · have hU : ω ∉ R ∪ L := by simp only [Set.mem_union, hR, hL, false_or, not_false_eq_true]
      simp only [periodCharge, periodOpportunity, Set.indicator_of_notMem hU,
        Set.indicator_of_notMem hR, Set.indicator_of_notMem hL, add_zero, le_refl]

theorem periodCharge_stronglyMeasurable (t : ℕ) (R L : Set Ω)
    (hR : MeasurableSet[ℱ t] R) (hL : MeasurableSet[ℱ t] L)
    (f : Ω → ℝ) (hf : StronglyMeasurable[ℱ (t + 1)] f) :
    StronglyMeasurable[ℱ (t + 1)] (periodCharge R L f) :=
  hf.indicator ((ℱ.mono (Nat.le_succ t)) _ (hR.union hL))

theorem periodOpportunity_stronglyMeasurable (t : ℕ) (R L : Set Ω)
    (hR : MeasurableSet[ℱ t] R) (hL : MeasurableSet[ℱ t] L)
    (J : Ω → ℝ) (hJ : StronglyMeasurable[ℱ (t + 1)] J) :
    StronglyMeasurable[ℱ (t + 1)] (periodOpportunity R L J) :=
  (stronglyMeasurable_const.indicator ((ℱ.mono (Nat.le_succ t)) _ hR)).add
    (hJ.indicator ((ℱ.mono (Nat.le_succ t)) _ hL))

theorem periodRate_stronglyMeasurable (t : ℕ) (R : Set Ω)
    (hR : MeasurableSet[ℱ t] R) (r k : ℝ) :
    StronglyMeasurable[ℱ t] (periodRate R r k) := by
  classical
  exact StronglyMeasurable.ite hR stronglyMeasurable_const stronglyMeasurable_const

theorem periodRate_nonneg (R : Set Ω) (r k : ℝ) (hr : 0 ≤ r) (hk : 0 ≤ k) :
    ∀ ω, 0 ≤ periodRate R r k ω := by
  classical
  intro ω
  unfold periodRate
  split_ifs <;> assumption

theorem periodCharge_conditional (t : ℕ) (R L : Set Ω)
    (hR : MeasurableSet[ℱ t] R) (hL : MeasurableSet[ℱ t] L)
    (f : Ω → ℝ) (hf : Integrable f μ) :
    μ[periodCharge R L f | ℱ t] =ᵐ[μ] (R ∪ L).indicator (μ[f | ℱ t]) :=
  condExp_indicator hf (hR.union hL)

theorem periodOpportunity_conditional (t : ℕ) (R L : Set Ω)
    (hR : MeasurableSet[ℱ t] R) (hL : MeasurableSet[ℱ t] L)
    (J : Ω → ℝ) (hJ : Integrable J μ) :
    μ[periodOpportunity R L J | ℱ t] =ᵐ[μ]
      fun ω => R.indicator (fun _ => (1 : ℝ)) ω +
        L.indicator (μ[J | ℱ t]) ω := by
  have hRm : MeasurableSet R := (ℱ.le t) _ hR
  have hLm : MeasurableSet L := (ℱ.le t) _ hL
  have hc := condExp_add ((integrable_const (1 : ℝ)).indicator hRm)
    (hJ.indicator hLm) (ℱ t)
  have hconst :
      μ[R.indicator (fun _ : Ω => (1 : ℝ)) | ℱ t] =
        R.indicator (fun _ : Ω => (1 : ℝ)) :=
    condExp_of_stronglyMeasurable (ℱ.le t)
      (stronglyMeasurable_const.indicator hR)
      ((integrable_const (1 : ℝ)).indicator hRm)
  filter_upwards [hc, condExp_indicator hJ hL] with ω hcω hJω
  simpa only [periodOpportunity, Pi.add_apply, hconst, hJω] using hcω

theorem periodCharge_conditional_rate (t : ℕ) (R L : Set Ω)
    (hR : MeasurableSet[ℱ t] R) (hL : MeasurableSet[ℱ t] L)
    (hd : Disjoint R L) (f J M : Ω → ℝ) (r k : ℝ)
    (hf : Integrable f μ) (hJ : Integrable J μ)
    (hraw : μ[f | ℱ t] ≤ᵐ[μ] fun ω => r * M ω)
    (hclock : μ[f | ℱ t] ≤ᵐ[μ] fun ω => μ[J | ℱ t] ω * k * M ω) :
    μ[periodCharge R L f | ℱ t] ≤ᵐ[μ]
      fun ω => μ[periodOpportunity R L J | ℱ t] ω *
        periodRate R r k ω * M ω := by
  classical
  filter_upwards [periodCharge_conditional t R L hR hL f hf,
    periodOpportunity_conditional t R L hR hL J hJ, hraw, hclock]
    with ω hfω hJω hrω hkω
  rw [hfω, hJω]
  by_cases hRω : ω ∈ R
  · have hLω : ω ∉ L := fun hLω => Set.disjoint_left.mp hd hRω hLω
    have hU : ω ∈ R ∪ L := Or.inl hRω
    simpa only [Set.indicator_of_mem hU, Set.indicator_of_mem hRω,
      Set.indicator_of_notMem hLω, add_zero, periodRate, if_pos hRω, one_mul] using hrω
  · by_cases hLω : ω ∈ L
    · have hU : ω ∈ R ∪ L := Or.inr hLω
      simpa only [Set.indicator_of_mem hU, Set.indicator_of_notMem hRω,
        Set.indicator_of_mem hLω, zero_add, periodRate, if_neg hRω] using hkω
    · have hU : ω ∉ R ∪ L := by simp only [Set.mem_union, hRω, hLω, false_or, not_false_eq_true]
      simp only [Set.indicator_of_notMem hU, Set.indicator_of_notMem hRω,
        Set.indicator_of_notMem hLω, add_zero, zero_mul, le_refl]

theorem periodRate_mul_opportunity (R L : Set Ω) (J : Ω → ℝ)
    (r k : ℝ) (hd : Disjoint R L) (ω : Ω) :
    periodRate R r k ω * periodOpportunity R L J ω =
      r * R.indicator (fun _ => (1 : ℝ)) ω + k * L.indicator J ω := by
  classical
  by_cases hR : ω ∈ R
  · have hL : ω ∉ L := fun hL => Set.disjoint_left.mp hd hR hL
    simp [periodRate, periodOpportunity, hR, hL]
  · by_cases hL : ω ∈ L <;>
      simp [periodRate, periodOpportunity, hR, hL]

theorem period_compensator_split (R L : ℕ → Set Ω) (J : ℕ → Ω → ℝ)
    (r k : ℝ) (hd : ∀ t, Disjoint (R t) (L t)) (N : ℕ) (ω : Ω) :
    (∑ t ∈ Finset.range N, periodRate (R t) r k ω *
      periodOpportunity (R t) (L t) (J t) ω) =
      r * (∑ t ∈ Finset.range N, (R t).indicator (fun _ => (1 : ℝ)) ω) +
        k * (∑ t ∈ Finset.range N, (L t).indicator (J t) ω) := by
  calc
    _ = ∑ t ∈ Finset.range N,
        (r * (R t).indicator (fun _ => (1 : ℝ)) ω +
          k * (L t).indicator (J t) ω) := by
      apply Finset.sum_congr rfl
      intro t _
      exact periodRate_mul_opportunity (R t) (L t) (J t) r k (hd t) ω
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockTwoPeriodIndicators

end
