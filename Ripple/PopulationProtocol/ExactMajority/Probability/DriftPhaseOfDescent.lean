/-
# DriftPhase Constructor from Discrete Descent

Constructs a `DriftPhase` from a boolean descent condition:
if a potential `φ` is non-increasing, bounded by `M`, and decreases by at least 1
with probability at least `p`, then it contracts geometrically with rate `1 - p/M`.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.SupermartingaleHitting
import Ripple.PopulationProtocol.PopProtoCommon.Convergence.GeometricDrift

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- Convert a discrete probability of decrement into an expected value bound. -/
lemma lintegral_nat_le_of_descent {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (φ : α → ℕ)
    (v : ℕ)
    (hbound : ∀ᵐ a ∂μ, φ a ≤ v)
    (p : ℝ≥0)
    (hp_le : μ {a | φ a < v} ≥ p) :
    ∫⁻ a, (φ a : ℝ≥0∞) ∂μ ≤ (v : ℝ≥0∞) - p := by
  have h_pointwise : ∀ a, (φ a : ℝ≥0∞) + {a | φ a < v}.indicator (fun _ => 1) a ≤
      (v : ℝ≥0∞) + {a | v < φ a}.indicator (fun a => (φ a : ℝ≥0∞)) a := by
    intro a
    by_cases h1 : v < φ a
    · rw [Set.indicator_of_mem (show a ∈ {a | v < φ a} from h1) _,
          Set.indicator_of_notMem (show a ∉ {a | φ a < v} by simp; omega) _]
      simp
    · rw [Set.indicator_of_notMem (show a ∉ {a | v < φ a} from h1) _]
      by_cases h2 : φ a < v
      · rw [Set.indicator_of_mem (show a ∈ {a | φ a < v} from h2) _]
        have h_le : φ a + 1 ≤ v := by omega
        exact_mod_cast h_le
      · rw [Set.indicator_of_notMem (show a ∉ {a | φ a < v} from h2) _]
        have h_eq : φ a = v := by omega
        rw [h_eq]
  have h_int1 := lintegral_mono (μ := μ) h_pointwise
  rw [lintegral_add_left (Measurable.of_discrete (α := α))] at h_int1
  rw [lintegral_add_left measurable_const] at h_int1
  have h_ind1 : ∫⁻ a, {a | φ a < v}.indicator (fun _ => 1) a ∂μ = μ {a | φ a < v} := by
    rw [lintegral_indicator (DiscreteMeasurableSpace.forall_measurableSet _) _,
        lintegral_one, Measure.restrict_apply_univ]
  have h_ind2 : ∫⁻ a, {a | v < φ a}.indicator (fun a => (φ a : ℝ≥0∞)) a ∂μ = 0 := by
    have h_ae : ∀ᵐ a ∂μ, {a | v < φ a}.indicator (fun a => (φ a : ℝ≥0∞)) a = 0 := by
      filter_upwards [hbound] with a ha
      exact Set.indicator_of_notMem (show a ∉ {a | v < φ a} by simp; omega) _
    exact (lintegral_congr_ae h_ae).trans lintegral_zero
  rw [h_ind1, h_ind2, add_zero, lintegral_const, measure_univ, mul_one] at h_int1
  calc ∫⁻ a, (φ a : ℝ≥0∞) ∂μ
      = ∫⁻ a, (φ a : ℝ≥0∞) ∂μ + (p : ℝ≥0∞) - (p : ℝ≥0∞) :=
        (ENNReal.add_sub_cancel_right ENNReal.coe_ne_top).symm
    _ ≤ ∫⁻ a, (φ a : ℝ≥0∞) ∂μ + μ {a | φ a < v} - (p : ℝ≥0∞) := by gcongr
    _ ≤ (v : ℝ≥0∞) - (p : ℝ≥0∞) := by gcongr

/-- Build a `DriftPhase` from a discrete descent condition. -/
noncomputable def DriftPhase.ofDescent
    (P : Protocol Λ) [IsMarkovKernel P.transitionKernel]
    (Pre : Config Λ → Prop)
    (Post : Config Λ → Prop)
    (φ : Config Λ → ℕ)
    (p : ℝ≥0)
    (M : ℕ)
    (hpost : ∀ c, Post c ↔ φ c = 0)
    (hM : ∀ c, φ c ≤ M)
    (hnoninc : ∀ c, ¬Post c →
      ∀ᵐ c' ∂(P.transitionKernel c), φ c' ≤ φ c)
    (hdesc : ∀ c, ¬Post c →
      P.transitionKernel c {c' | φ c' < φ c} ≥ p)
    (hpost_abs : ∀ c, Post c → P.transitionKernel c {y | Post y} = 1) :
    DriftPhase P where
  Pre := Pre
  Post := Post
  Φ := fun c => (φ c : ℝ≥0∞)
  hΦ := Measurable.of_discrete
  r := 1 - (p : ℝ≥0∞) / (M : ℝ≥0∞)
  M := (M : ℝ≥0∞)
  post_iff := by
    intro c
    rw [hpost c]
    constructor
    · intro h
      rw [h]
      norm_num
    · intro h
      have h1 : (φ c : ℝ≥0∞) < 1 := h
      have hnat : φ c = 0 := by
        rcases Nat.eq_zero_or_pos (φ c) with h0 | hpos
        · exact h0
        · exfalso
          have : 1 ≤ (φ c : ℝ≥0∞) := by exact_mod_cast hpos
          exact not_lt.mpr this h1
      exact hnat
  hdrift := by
    intro c hc_not_post
    haveI : IsProbabilityMeasure (P.transitionKernel c) :=
      (inferInstance : IsMarkovKernel P.transitionKernel).isProbabilityMeasure c
    have h_bound :
        ∫⁻ c', (φ c' : ℝ≥0∞) ∂(P.transitionKernel c) ≤
          (φ c : ℝ≥0∞) - (p : ℝ≥0∞) := by
      exact lintegral_nat_le_of_descent (P.transitionKernel c) φ (φ c)
        (hnoninc c hc_not_post) p (hdesc c hc_not_post)
    by_cases hM0 : M = 0
    · have hφ0 : φ c = 0 := Nat.le_zero.mp (hM0 ▸ hM c)
      calc
        ∫⁻ c', (φ c' : ℝ≥0∞) ∂(P.transitionKernel c)
            ≤ (φ c : ℝ≥0∞) - (p : ℝ≥0∞) := h_bound
        _ = 0 := by simp [hφ0]
        _ = (1 - (p : ℝ≥0∞) / (M : ℝ≥0∞)) * (φ c : ℝ≥0∞) := by
          simp [hM0, hφ0]
    · have hv_le_M : (φ c : ℝ≥0∞) ≤ (M : ℝ≥0∞) := by
        exact_mod_cast hM c
      have hM_ne_zero : (M : ℝ≥0∞) ≠ 0 := by
        simp [hM0]
      have hM_ne_top : (M : ℝ≥0∞) ≠ ⊤ :=
        ENNReal.natCast_ne_top M
      have hmul_le :
          (p : ℝ≥0∞) / (M : ℝ≥0∞) * (φ c : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by
        calc
          (p : ℝ≥0∞) / (M : ℝ≥0∞) * (φ c : ℝ≥0∞)
              ≤ (p : ℝ≥0∞) / (M : ℝ≥0∞) * (M : ℝ≥0∞) := by
                exact mul_le_mul_left' hv_le_M ((p : ℝ≥0∞) / (M : ℝ≥0∞))
          _ = (p : ℝ≥0∞) := by
                exact ENNReal.div_mul_cancel hM_ne_zero hM_ne_top
      have hsub_le :
          (φ c : ℝ≥0∞) - (p : ℝ≥0∞) ≤
            (φ c : ℝ≥0∞) -
              ((p : ℝ≥0∞) / (M : ℝ≥0∞) * (φ c : ℝ≥0∞)) := by
        exact tsub_le_tsub_left hmul_le (φ c : ℝ≥0∞)
      have hmul_sub :
          (1 - (p : ℝ≥0∞) / (M : ℝ≥0∞)) * (φ c : ℝ≥0∞) =
            (φ c : ℝ≥0∞) -
              ((p : ℝ≥0∞) / (M : ℝ≥0∞) * (φ c : ℝ≥0∞)) := by
        simpa [one_mul] using
          (ENNReal.sub_mul (a := 1)
            (b := (p : ℝ≥0∞) / (M : ℝ≥0∞))
            (c := (φ c : ℝ≥0∞)))
      calc
        ∫⁻ c', (φ c' : ℝ≥0∞) ∂(P.transitionKernel c)
            ≤ (φ c : ℝ≥0∞) - (p : ℝ≥0∞) := h_bound
        _ ≤ (φ c : ℝ≥0∞) -
              ((p : ℝ≥0∞) / (M : ℝ≥0∞) * (φ c : ℝ≥0∞)) := hsub_le
        _ = (1 - (p : ℝ≥0∞) / (M : ℝ≥0∞)) * (φ c : ℝ≥0∞) :=
              hmul_sub.symm
  hM := by
    intro c hc_pre
    gcongr
    exact hM c
  post_absorbing := hpost_abs

end Ripple.PopulationProtocol.ExactMajority
