-- Ripple/Kurtz/StrongApprox/PoissonTimeChangeExistence.lean
import Ripple.Kurtz.StrongApprox.FiniteBatchTimeChange

/-!
# Instantiating the finite-batch constructor with `poisFamily`

The arrival type may depend on `ω`; this is harmless for pointwise existence
and for the universal quantifier in `ae_chain_fluid_rate`. Joint measurability
in `ω` is deliberately not claimed here.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {N : ℕ → Ω → ℕ}
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For every driver sample, the finite-batch constructor supplies a genuine
solution of the Poisson random-time-change equation. -/
theorem exists_poisson_timeChangeWitness
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    {T : ℝ} (hT : 0 ≤ T) (x₀ : Fin d → ℝ)
    (ω : ι → PathSpace Ω) :
    ∃ X : ℝ → Fin d → ℝ,
      Measurable X ∧
      X 0 = x₀ ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        X t = x₀ +
          ∑ l, ((poisFamily ι N l
            ((n : ℝ) * clock β X l t) ω : ℝ) /
              (n : ℝ)) • v l) ∧
      (∀ t, ∀ᶠ s in 𝓝[≥] t, X s = X t) ∧
      (∃ S : Finset ℝ, ∀ ⦃s t : ℝ⦄, s ≤ t →
        Disjoint (Ioc s t : Set ℝ) (S : Set ℝ) → X s = X t) := by
  let D : BatchData d ι :=
    { scale := n
      horizon := T
      initial := x₀
      rate := β
      jump := v
      bound := b
      scale_pos := hn
      horizon_nonneg := hT
      rate_nonneg := hβ0
      rate_le := hβb
      rate_measurable := hβm }
  classical
  let U : ι → ℝ := fun l => (n : ℝ) * b l * T
  let arrival : ∀ l, HorizonArrival N (U l) (ω l) → ℝ :=
    fun l => horizonArrivalTime N (U l) (ω l)
  have harrival : ∀ l (a : HorizonArrival N (U l) (ω l)), 0 < arrival l a :=
    fun l a => horizonArrivalTime_pos N (U l) (ω l) a
  obtain ⟨W⟩ := D.finite_batch_timeChange_exists
    (κ := fun l => HorizonArrival N (U l) (ω l)) arrival harrival
  refine ⟨W.path, W.measurable_path, W.initial_eq, ?_,
    W.eventually_right, ⟨W.jumpSupport, W.eq_of_disjoint⟩⟩
  intro t ht
  rw [W.equation t ht]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  have hclock := W.scaledClock_mem l t ht
  have hcount := poisPath_eq_horizonArrivalCount N
    (U := U l) (t := (n : ℝ) * clock β W.path l t) hclock.2 (ω l)
  have hfinite :
      D.finiteCount arrival l
          ((n : ℝ) * clock β W.path l t) =
        poisFamily ι N l ((n : ℝ) * clock β W.path l t) ω := hcount.symm
  exact congrArg (fun m : ℕ => ((m : ℝ) / (n : ℝ)) • v l) hfinite

/-- **Non-vacuity of `ae_chain_fluid_rate`.** Almost surely, for all large
scales there exists a concrete finite-jump Poisson time-change solution, and
that solution satisfies the LIL-scale chain-to-fluid estimate. -/
theorem ae_exists_poisson_timeChange_rate
    (hNm : ∀ i, Measurable (N i))
    (hN : iIndepFun N P)
    (hNl : ∀ i k, P {ω | N i ω = k} =
      ENNReal.ofReal (poisTerm k 1))
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ y z,
      ‖tcDrift β v y - tcDrift β v z‖ ≤ L * ‖y - z‖)
    {T : ℝ} (hT : 0 ≤ T)
    {x : ℝ → Fin d → ℝ} {x₀ : Fin d → ℝ}
    (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Icc (0 : ℝ) T,
      x t = x₀ + ∫ s in (0 : ℝ)..t, tcDrift β v (x s)) :
    ∀ᵐ ω ∂familyMeasure ι P,
      ∀ᶠ n : ℕ in atTop,
        ∃ X : ℝ → Fin d → ℝ,
          Measurable X ∧
          X 0 = x₀ ∧
          (∀ t ∈ Icc (0 : ℝ) T,
            X t = x₀ +
              ∑ l, ((poisFamily ι N l
                ((n : ℝ) * clock β X l t) ω : ℝ) /
                  (n : ℝ)) • v l) ∧
          (∀ t, ∀ᶠ s in 𝓝[≥] t, X s = X t) ∧
          (∃ S : Finset ℝ, ∀ ⦃s t : ℝ⦄, s ≤ t →
            Disjoint (Ioc s t : Set ℝ) (S : Set ℝ) → X s = X t) ∧
          ∀ t ∈ Icc (0 : ℝ) T,
            ‖X t - x t‖ ≤
              ((n : ℝ)⁻¹ *
                ∑ l, ‖v l‖ * envelope ((n : ℝ) * (b l * T))) *
                  Real.exp (L * t) := by
  have hrate := ae_chain_fluid_rate hNm hN hNl
    hβ0 hβb hβm hL hF hT hxc hx
  filter_upwards [hrate] with ω hω
  filter_upwards [hω, Filter.eventually_gt_atTop 0] with n hnAll hn
  obtain ⟨X, hXm, hXzero, hXeq, hright, hsupport⟩ :=
    exists_poisson_timeChangeWitness
      (N := N) hn hβ0 hβb hβm hT x₀ ω
  have hEquationForRate : ∀ t ∈ Icc (0 : ℝ) T,
      X t = X 0 +
        ∑ l, ((poisFamily ι N l
          ((n : ℝ) * clock β X l t) ω : ℝ) /
            (n : ℝ)) • v l := by
    intro t ht
    simpa [hXzero] using hXeq t ht
  have hbound := hnAll X hXm hEquationForRate
  refine ⟨X, hXm, hXzero, hXeq, hright, hsupport, ?_⟩
  intro t ht
  have := hbound t ht
  simpa [hXzero] using this

end Ripple.Kurtz.StrongApprox

end
