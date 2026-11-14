-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockWaitingProduct.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockWaitingProductAlgebra
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockPotentialTail

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockWaitingProduct

open PhaseThreeClockWaitingProductAlgebra PhaseThreeClockPotentialTail

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m₀}

theorem waiting_product_prefix_tail
    (A : ℕ → Ω → ℕ) (I : ℕ → Ω → ℝ) (p : ℕ → ℝ)
    (r K N : ℕ) (theta : ℝ) (hrK : r ≤ K) (htheta : 0 ≤ theta)
    (hp : ∀ j ∈ Finset.Ico r K, 0 < p j)
    (hsmall : ∀ j ∈ Finset.Ico r K, 1 - Real.exp (-theta) < p j)
    (hA : ∀ t, Measurable[ℱ t] (A t))
    (hmono : ∀ t ω, A t ω ≤ A (t + 1) ω)
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hinc : ∀ t, ∀ᵐ ω ∂μ, I t ω ≤ (A (t + 1) ω : ℝ) - (A t ω : ℝ))
    (hrate : ∀ t, ∀ᵐ ω ∂μ, r ≤ A t ω → A t ω < K →
      p (A t ω) ≤ (μ[I t | ℱ t]) ω)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E)
    (hstart : ∀ ω ∈ E, r ≤ A 0 ω) :
    μ (E ∩ {ω | A N ω < K}) ≤
      ENNReal.ofReal (Real.exp (-theta * (N : ℝ)) *
        waitingProduct p (1 - Real.exp (-theta)) r K) * μ E := by
  classical
  let delta : ℝ := 1 - Real.exp (-theta)
  let W : ℕ → ℝ := survivalWeight p delta r K
  let Z : ℕ → Ω → ℝ := fun t => E.indicator (fun ω => W (A t ω))
  let D : ℕ → Ω → ℝ := fun t ω => (delta / p (A t ω)) * Z t ω
  have hd : 0 ≤ delta := (exponential_delta_bounds theta htheta).1
  have hlt : ∀ j ∈ Finset.Ico r K, delta < p j := hsmall
  have hEt (t : ℕ) : MeasurableSet[ℱ t] E :=
    (ℱ.mono (show 0 ≤ t from zero_le)) _ hE
  have hAr (t : ℕ) (ω : Ω) (he : ω ∈ E) : r ≤ A t ω := by
    induction t with
    | zero => exact hstart ω he
    | succ t ih => exact ih.trans (hmono t ω)
  have hZ : ∀ t, StronglyMeasurable[ℱ t] (Z t) := by
    intro t
    exact (((measurable_of_countable W).comp (hA t)).stronglyMeasurable).indicator (hEt t)
  have hZbound : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ Z t ω ∧ Z t ω ≤ 1 := by
    intro t
    apply ae_of_all
    intro ω
    by_cases he : ω ∈ E
    · simpa only [Z, W, Set.indicator_of_mem he] using
        survivalWeight_bounds p delta r K (A t ω) hd hp hlt (hAr t ω he)
    · simp only [Z, Set.indicator_of_notMem he, le_refl, zero_le_one, and_self]
  have hD : ∀ t, StronglyMeasurable[ℱ t] (D t) := by
    intro t
    exact (((measurable_of_countable (fun a : ℕ => delta / p a)).comp
      (hA t)).stronglyMeasurable).mul (hZ t)
  have hDbound : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ D t ω ∧ D t ω ≤ 1 := by
    intro t
    apply ae_of_all
    intro ω
    by_cases he : ω ∈ E
    · simpa only [D, Z, W, Set.indicator_of_mem he] using
        survivalWeight_loss_bounds p delta r K (A t ω) hd hp hlt (hAr t ω he)
    · simp only [D, Z, Set.indicator_of_notMem he, mul_zero,
        le_refl, zero_le_one, and_self]
  have hstep : ∀ t, Z (t + 1) ≤ᵐ[μ] fun ω => Z t ω - D t ω * I t ω := by
    intro t
    filter_upwards [hzeroOne t, hinc t] with ω hi hmove
    by_cases he : ω ∈ E
    · simpa only [Z, D, W, Set.indicator_of_mem he] using
        survivalWeight_step p delta r K (A t ω) (A (t + 1) ω) (I t ω)
          hd hp hlt (hAr t ω he) (hmono t ω) hi hmove
    · simp only [Z, D, Set.indicator_of_notMem he, mul_zero,
        zero_mul, sub_zero, le_refl]
  have hrateZ : ∀ t, ∀ᵐ ω ∂μ,
      delta * Z t ω ≤ D t ω * (μ[I t | ℱ t]) ω := by
    intro t
    filter_upwards [hrate t] with ω hω
    by_cases he : ω ∈ E
    · have hra := hAr t ω he
      by_cases ha : A t ω < K
      · have haI : A t ω ∈ Finset.Ico r K := Finset.mem_Ico.mpr ⟨hra, ha⟩
        have hpn : p (A t ω) ≠ 0 := ne_of_gt (hp (A t ω) haI)
        have hcoef : 0 ≤ (delta / p (A t ω)) * W (A t ω) :=
          (survivalWeight_loss_bounds p delta r K (A t ω) hd hp hlt hra).1
        have hmul := mul_le_mul_of_nonneg_left (hω hra ha) hcoef
        have hid :
            ((delta / p (A t ω)) * W (A t ω)) * p (A t ω) =
              delta * W (A t ω) := by
          field_simp [hpn]
          <;> ring
        rw [hid] at hmul
        simpa only [D, Z, Set.indicator_of_mem he] using hmul
      · have hz : W (A t ω) = 0 := by simp only [W, survivalWeight, if_neg ha]
        simp only [D, Z, Set.indicator_of_mem he, hz, mul_zero, zero_mul, le_refl]
    · simp only [D, Z, Set.indicator_of_notMem he, mul_zero, zero_mul, le_refl]
  have hdrift := affine_conditional_drift hZ hZbound hD hDbound hI hzeroOne hstep hrateZ
  have hdriftExp : ∀ t, μ[Z (t + 1) | ℱ t] ≤ᵐ[μ]
      fun ω => Real.exp (-theta) * Z t ω := by
    intro t
    filter_upwards [hdrift t] with ω hω
    simpa only [delta, sub_sub_cancel] using hω
  let R : ℝ := waitingProduct p delta r K
  have hR : 0 ≤ R := zero_le_one.trans (waitingProduct_ge_one p delta r K hd hp hlt)
  let B : Set Ω := E ∩ {ω | A N ω < K}
  have hB : ∀ ω ∈ B, 1 ≤ R * Z N ω := by
    rintro ω ⟨he, hhit⟩
    simpa only [R, Z, W, Set.indicator_of_mem he] using
      survivalWeight_survival_lower p delta r K (A N ω) hd hp hlt (hAr N ω he) hhit
  have htail := prefix_potential_tail_ennreal hZ hZbound (Real.exp_nonneg (-theta))
    hdriftExp E hE N B R hR hB
  have hEB : E ∩ B = E ∩ {ω | A N ω < K} := by
    ext ω
    simp only [B, Set.mem_inter_iff, and_self_left]
  have hpow : Real.exp (-theta) ^ N = Real.exp (-theta * (N : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hEB, hpow] at htail
  simpa only [R, delta, mul_comm] using htail

theorem waiting_product_prefix_exponential_tail
    (A : ℕ → Ω → ℕ) (I : ℕ → Ω → ℝ) (p : ℕ → ℝ)
    (r K N : ℕ) (theta : ℝ) (hrK : r ≤ K) (htheta : 0 ≤ theta)
    (hp : ∀ j ∈ Finset.Ico r K, 0 < p j)
    (hsmall : ∀ j ∈ Finset.Ico r K, theta / p j ≤ 1 / 1000)
    (hA : ∀ t, Measurable[ℱ t] (A t))
    (hmono : ∀ t ω, A t ω ≤ A (t + 1) ω)
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hinc : ∀ t, ∀ᵐ ω ∂μ, I t ω ≤ (A (t + 1) ω : ℝ) - (A t ω : ℝ))
    (hrate : ∀ t, ∀ᵐ ω ∂μ, r ≤ A t ω → A t ω < K →
      p (A t ω) ≤ (μ[I t | ℱ t]) ω)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E)
    (hstart : ∀ ω ∈ E, r ≤ A 0 ω) :
    μ (E ∩ {ω | A N ω < K}) ≤
      ENNReal.ofReal (Real.exp ((1000 / 999 : ℝ) * theta *
        (∑ j ∈ Finset.Ico r K, 1 / p j) - theta * (N : ℝ))) * μ E := by
  have hlt (j : ℕ) (hj : j ∈ Finset.Ico r K) :
      1 - Real.exp (-theta) < p j :=
    exponential_delta_lt_rate theta (p j) htheta (hp j hj) (hsmall j hj)
  apply (waiting_product_prefix_tail A I p r K N theta hrK htheta hp hlt
    hA hmono hI hzeroOne hinc hrate E hE hstart).trans
  apply mul_le_mul_right'
  apply ENNReal.ofReal_le_ofReal
  calc
    Real.exp (-theta * (N : ℝ)) * waitingProduct p (1 - Real.exp (-theta)) r K ≤
        Real.exp (-theta * (N : ℝ)) *
          Real.exp ((1000 / 999 : ℝ) * theta * (∑ j ∈ Finset.Ico r K, 1 / p j)) :=
      mul_le_mul_of_nonneg_left (waitingProduct_le_exp p theta r K htheta hp hsmall)
        (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      ring

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockWaitingProduct

end
