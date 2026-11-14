-- Ripple/Kurtz/StrongApprox/PoissonDeterministicRenewal.lean
import Ripple.Kurtz.StrongApprox.PoissonTimeChangeGlobal
import Ripple.Kurtz.StrongApprox.ExponentialRaceResidual

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {N : ℕ → Ω → ℕ}
variable {ι : Type*} [Fintype ι]

/-- Increment of channel `l` over one deterministic internal-time window. -/
def familyIncrement (u h : ι → ℝ) (l : ι)
    (ω : ι → PathSpace Ω) : ℕ :=
  poisFamily ι N l (u l + h l) ω - poisFamily ι N l (u l) ω

theorem measurable_familyIncrement
    (hNm : ∀ i, Measurable (N i))
    (u h : ι → ℝ) (l : ι) :
    Measurable (familyIncrement (N := N) u h l) :=
  (measurable_poisPath hNm (u l + h l) |>.comp (measurable_pi_apply l)).sub
    (measurable_poisPath hNm (u l) |>.comp (measurable_pi_apply l))

/-- One deterministic channel increment has its exact Poisson law. -/
theorem familyIncrement_map_eq_poisMeasure
    (hNm : ∀ i, Measurable (N i))
    (hN : iIndepFun N P)
    (hNl : ∀ i k, P {ω | N i ω = k} =
      ENNReal.ofReal (poisTerm k 1))
    (u h : ι → ℝ) (hu : ∀ l, 0 ≤ u l) (hh : ∀ l, 0 ≤ h l)
    (l : ι) :
    (familyMeasure ι P).map (familyIncrement (N := N) u h l) =
      poisMeasure (h l) := by
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply (measurable_familyIncrement hNm u h l)
    (measurableSet_singleton k), poisMeasure_singleton]
  simpa [familyIncrement, add_sub_cancel_left] using
    familyMeasure_increment_eq (ι := ι) hNm hN hNl l
      (hu l) (le_add_of_nonneg_right (hh l)) k

/-- The whole deterministic increment vector is a product of Poisson laws. -/
theorem familyIncrementVector_map_eq
    (hNm : ∀ i, Measurable (N i))
    (hN : iIndepFun N P)
    (hNl : ∀ i k, P {ω | N i ω = k} =
      ENNReal.ofReal (poisTerm k 1))
    (u h : ι → ℝ) (hu : ∀ l, 0 ≤ u l) (hh : ∀ l, 0 ≤ h l) :
    (familyMeasure ι P).map
        (fun ω l => familyIncrement (N := N) u h l ω) =
      Measure.pi (fun l => poisMeasure (h l)) := by
  have hind : iIndepFun
      (fun l (ω : ι → PathSpace Ω) => familyIncrement (N := N) u h l ω)
      (familyMeasure ι P) := by
    exact (iIndepFun_poisFamily (ι := ι) hNm).comp
      (fun l (Y : ℝ → ℕ) => Y (u l + h l) - Y (u l))
      (fun l => (measurable_pi_apply (u l + h l)).sub
        (measurable_pi_apply (u l)))
  calc
    (familyMeasure ι P).map
        (fun ω l => familyIncrement (N := N) u h l ω) =
        Measure.pi (fun l =>
          (familyMeasure ι P).map
            (familyIncrement (N := N) u h l)) :=
      hind.map_fun_eq_pi_map
        (fun l => (measurable_familyIncrement hNm u h l).aemeasurable)
    _ = Measure.pi (fun l => poisMeasure (h l)) := by
      congr 1
      funext l
      exact familyIncrement_map_eq_poisMeasure hNm hN hNl u h hu hh l

/-- No channel has an arrival in its deterministic window. -/
def noArrivalOnWindow (u h : ι → ℝ) : Set (ι → PathSpace Ω) :=
  {ω | ∀ l, familyIncrement (N := N) u h l ω = 0}

theorem measurableSet_noArrivalOnWindow
    (hNm : ∀ i, Measurable (N i)) (u h : ι → ℝ) :
    MeasurableSet (noArrivalOnWindow (N := N) u h) := by
  have hset : noArrivalOnWindow (N := N) u h =
      ⋂ l, familyIncrement (N := N) u h l ⁻¹' {0} := by
    ext ω
    simp [noArrivalOnWindow]
  rw [hset]
  exact MeasurableSet.iInter fun l =>
    (measurable_familyIncrement hNm u h l) (measurableSet_singleton 0)

/-- Exact joint no-arrival probability for deterministic channel windows. -/
theorem familyMeasure_noArrivalOnWindow
    (hNm : ∀ i, Measurable (N i))
    (hN : iIndepFun N P)
    (hNl : ∀ i k, P {ω | N i ω = k} =
      ENNReal.ofReal (poisTerm k 1))
    (u h : ι → ℝ) (hu : ∀ l, 0 ≤ u l) (hh : ∀ l, 0 ≤ h l) :
    familyMeasure ι P (noArrivalOnWindow (N := N) u h) =
      ENNReal.ofReal (Real.exp (-(∑ l, h l))) := by
  letI (l : ι) : IsProbabilityMeasure (poisMeasure (h l)) :=
    poisMeasure_isProbabilityMeasure_of_nonneg (hh l)
  have hvec : Measurable
      (fun ω : ι → PathSpace Ω =>
        fun l => familyIncrement (N := N) u h l ω) :=
    measurable_pi_lambda _ fun l => measurable_familyIncrement hNm u h l
  have hpre : noArrivalOnWindow (N := N) u h =
      (fun ω l => familyIncrement (N := N) u h l ω) ⁻¹'
        ({fun _ : ι => 0} : Set (ι → ℕ)) := by
    ext ω
    simp [noArrivalOnWindow, funext_iff]
  rw [hpre, ← Measure.map_apply hvec (measurableSet_singleton _),
    familyIncrementVector_map_eq hNm hN hNl u h hu hh]
  have hsingleton : ({fun _ : ι => 0} : Set (ι → ℕ)) =
      Set.pi Set.univ (fun _ : ι => ({0} : Set ℕ)) := by
    ext z
    simp [funext_iff]
  rw [hsingleton, Measure.pi_pi]
  simp_rw [poisMeasure_singleton]
  simp only [poisTerm, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, mul_one]
  rw [← ENNReal.ofReal_prod_of_nonneg
      (fun l _ => Real.exp_nonneg (-(h l))),
    ← Real.exp_sum, Finset.sum_neg_distrib]

/-- Deterministic-time memoryless factorization. -/
theorem familyMeasure_noArrival_add
    (hNm : ∀ i, Measurable (N i))
    (hN : iIndepFun N P)
    (hNl : ∀ i k, P {ω | N i ω = k} =
      ENNReal.ofReal (poisTerm k 1))
    (u h g : ι → ℝ)
    (hu : ∀ l, 0 ≤ u l) (hh : ∀ l, 0 ≤ h l) (hg : ∀ l, 0 ≤ g l) :
    familyMeasure ι P
        (noArrivalOnWindow (N := N) u (fun l => h l + g l)) =
      familyMeasure ι P (noArrivalOnWindow (N := N) u h) *
        familyMeasure ι P
          (noArrivalOnWindow (N := N) (fun l => u l + h l) g) := by
  rw [familyMeasure_noArrivalOnWindow hNm hN hNl u
      (fun l => h l + g l) hu (fun l => add_nonneg (hh l) (hg l)),
    familyMeasure_noArrivalOnWindow hNm hN hNl u h hu hh,
    familyMeasure_noArrivalOnWindow hNm hN hNl
      (fun l => u l + h l) g (fun l => add_nonneg (hu l) (hh l)) hg,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2
  rw [Finset.sum_add_distrib]
  ring

/-- At a fixed state, deterministic internal windows generated for physical
time `t` have the survival function of an exponential clock with rate
`n * Σ_l β_l(x)`. -/
theorem familyMeasure_constantRate_noArrival
    (hNm : ∀ i, Measurable (N i))
    (hN : iIndepFun N P)
    (hNl : ∀ i k, P {ω | N i ω = k} =
      ENNReal.ofReal (poisTerm k 1))
    {d n : ℕ} (β : ι → (Fin d → ℝ) → ℝ)
    (hβ : ∀ l y, 0 ≤ β l y)
    (x : Fin d → ℝ) (u : ι → ℝ) (hu : ∀ l, 0 ≤ u l)
    {t : ℝ} (ht : 0 ≤ t) :
    familyMeasure ι P
        (noArrivalOnWindow (N := N) u
          (fun l => (n : ℝ) * β l x * t)) =
      ENNReal.ofReal
        (Real.exp (-((n : ℝ) * (∑ l, β l x) * t))) := by
  rw [familyMeasure_noArrivalOnWindow hNm hN hNl u
    (fun l => (n : ℝ) * β l x * t) hu
    (fun l => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hβ l x)) ht)]
  congr 2
  rw [← Finset.sum_mul, ← Finset.mul_sum]

end Ripple.Kurtz.StrongApprox

end
