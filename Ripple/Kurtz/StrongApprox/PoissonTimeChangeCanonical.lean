-- Ripple/Kurtz/StrongApprox/PoissonTimeChangeCanonical.lean
import Ripple.Kurtz.StrongApprox.FiniteBatchTimeChangeUniqueness
import Ripple.Kurtz.StrongApprox.PoissonTimeChangeExistence

/-!
# Canonical finite-horizon Poisson time change

The existential witness for the finite-horizon time change is now unique.  We may therefore name one
witness by classical choice without changing any pathwise statement, and
solutions chosen at two different horizons agree on the shorter horizon.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset Filter Topology
open scoped ENNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {N : ℕ → Ω → ℕ}
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Poisson random-time-change equation on one finite horizon. -/
structure IsPoissonTimeChangeSolution
    (n : ℕ)
    (β : ι → (Fin d → ℝ) → ℝ)
    (v : ι → Fin d → ℝ)
    (T : ℝ) (x₀ : Fin d → ℝ)
    (ω : ι → PathSpace Ω)
    (X : ℝ → Fin d → ℝ) : Prop where
  measurable_path : Measurable X
  initial_eq : X 0 = x₀
  equation : ∀ t ∈ Icc (0 : ℝ) T,
    X t = X 0 +
      ∑ l, ((poisFamily ι N l
        ((n : ℝ) * clock β X l t) ω : ℝ) /
          (n : ℝ)) • v l

/-- Two measurable Poisson time-change solutions agree on the finite horizon. -/
theorem poisson_timeChangeSolution_unique
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    {T : ℝ} (hT : 0 ≤ T) (x₀ : Fin d → ℝ)
    (ω : ι → PathSpace Ω)
    {X Z : ℝ → Fin d → ℝ}
    (hX : IsPoissonTimeChangeSolution (N := N)
      n β v T x₀ ω X)
    (hZ : IsPoissonTimeChangeSolution (N := N)
      n β v T x₀ ω Z) :
    Set.EqOn X Z (Icc (0 : ℝ) T) := by
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
  let arrival : ∀ l, HorizonArrival N (U l) (ω l) → ℝ := fun l =>
    horizonArrivalTime N (U l) (ω l)
  have harrival : ∀ l (a : HorizonArrival N (U l) (ω l)), 0 < arrival l a :=
    fun l a => horizonArrivalTime_pos N (U l) (ω l) a
  have toFinite : ∀ {Y : ℝ → Fin d → ℝ},
      IsPoissonTimeChangeSolution (N := N)
        n β v T x₀ ω Y →
      D.IsTimeChangeSolution arrival Y := by
    intro Y hY
    refine
      { measurable_path := hY.measurable_path
        initial_eq := hY.initial_eq
        equation := ?_ }
    intro t ht
    rw [hY.equation t ht]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    have hb0 : 0 ≤ b l :=
      (hβ0 l x₀).trans (hβb l x₀)
    have hclock := clock_le hβ0 hβb hβm
      hY.measurable_path l ht.1
    have hclockT : clock β Y l t ≤ b l * T :=
      hclock.trans
        (mul_le_mul_of_nonneg_left ht.2 hb0)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hscaled :
        (n : ℝ) * clock β Y l t ≤ U l := by
      dsimp [U]
      exact (mul_le_mul_of_nonneg_left hclockT hn0).trans_eq (mul_assoc _ _ _).symm
    have hcount := poisPath_eq_horizonArrivalCount N hscaled (ω l)
    have hfinite :
        D.finiteCount arrival l
            ((n : ℝ) * clock β Y l t) =
          poisFamily ι N l
            ((n : ℝ) * clock β Y l t) ω := hcount.symm
    exact congrArg (fun m : ℕ => ((m : ℝ) / (n : ℝ)) • v l) hfinite.symm
  exact D.timeChangeSolution_unique arrival
    (toFinite hX) (toFinite hZ) harrival

/-- A named finite-horizon path.  Uniqueness below makes the choice
extensional. -/
noncomputable def poissonHorizonPath
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    {T : ℝ} (hT : 0 ≤ T) (x₀ : Fin d → ℝ)
    (ω : ι → PathSpace Ω) : ℝ → Fin d → ℝ :=
  Classical.choose
    (exists_poisson_timeChangeWitness (N := N) (v := v)
      hn hβ0 hβb hβm hT x₀ ω)

private theorem poissonHorizonPath_spec
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    {T : ℝ} (hT : 0 ≤ T) (x₀ : Fin d → ℝ)
    (ω : ι → PathSpace Ω) :
    let X := poissonHorizonPath (N := N) (v := v)
      hn hβ0 hβb hβm hT x₀ ω
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
  exact Classical.choose_spec
    (exists_poisson_timeChangeWitness (N := N) (v := v)
      hn hβ0 hβb hβm hT x₀ ω)

theorem poissonHorizonPath_measurable
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    {T : ℝ} (hT : 0 ≤ T) (x₀ : Fin d → ℝ)
    (ω : ι → PathSpace Ω) :
    Measurable (poissonHorizonPath (N := N) (v := v)
      hn hβ0 hβb hβm hT x₀ ω) :=
  (poissonHorizonPath_spec (N := N) (v := v)
    hn hβ0 hβb hβm hT x₀ ω).1

theorem poissonHorizonPath_initial
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    {T : ℝ} (hT : 0 ≤ T) (x₀ : Fin d → ℝ)
    (ω : ι → PathSpace Ω) :
    poissonHorizonPath (N := N) (v := v)
      hn hβ0 hβb hβm hT x₀ ω 0 = x₀ :=
  (poissonHorizonPath_spec (N := N) (v := v)
    hn hβ0 hβb hβm hT x₀ ω).2.1

theorem poissonHorizonPath_equation
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    {T : ℝ} (hT : 0 ≤ T) (x₀ : Fin d → ℝ)
    (ω : ι → PathSpace Ω) :
    ∀ t ∈ Icc (0 : ℝ) T,
      let X := poissonHorizonPath (N := N) (v := v)
        hn hβ0 hβb hβm hT x₀ ω
      X t = x₀ +
        ∑ l, ((poisFamily ι N l
          ((n : ℝ) * clock β X l t) ω : ℝ) /
            (n : ℝ)) • v l :=
  (poissonHorizonPath_spec (N := N) (v := v)
    hn hβ0 hβb hβm hT x₀ ω).2.2.1

theorem poissonHorizonPath_eventually_right
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    {T : ℝ} (hT : 0 ≤ T) (x₀ : Fin d → ℝ)
    (ω : ι → PathSpace Ω) (t : ℝ) :
    ∀ᶠ s in 𝓝[≥] t,
      poissonHorizonPath (N := N) (v := v)
        hn hβ0 hβb hβm hT x₀ ω s =
      poissonHorizonPath (N := N) (v := v)
        hn hβ0 hβb hβm hT x₀ ω t :=
  (poissonHorizonPath_spec (N := N) (v := v)
    hn hβ0 hβb hβm hT x₀ ω).2.2.2.1 t

theorem poissonHorizonPath_finiteJumpSupport
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    {T : ℝ} (hT : 0 ≤ T) (x₀ : Fin d → ℝ)
    (ω : ι → PathSpace Ω) :
    ∃ S : Finset ℝ, ∀ ⦃s t : ℝ⦄, s ≤ t →
      Disjoint (Ioc s t : Set ℝ) (S : Set ℝ) →
      poissonHorizonPath (N := N) (v := v)
        hn hβ0 hβb hβm hT x₀ ω s =
      poissonHorizonPath (N := N) (v := v)
        hn hβ0 hβb hβm hT x₀ ω t :=
  (poissonHorizonPath_spec (N := N) (v := v)
    hn hβ0 hβb hβm hT x₀ ω).2.2.2.2

theorem poissonHorizonPath_isSolution
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    {T : ℝ} (hT : 0 ≤ T) (x₀ : Fin d → ℝ)
    (ω : ι → PathSpace Ω) :
    IsPoissonTimeChangeSolution (N := N)
      n β v T x₀ ω
      (poissonHorizonPath (N := N) (v := v)
        hn hβ0 hβb hβm hT x₀ ω) := by
  refine
    { measurable_path := poissonHorizonPath_measurable (N := N) (v := v)
        hn hβ0 hβb hβm hT x₀ ω
      initial_eq := poissonHorizonPath_initial (N := N) (v := v)
        hn hβ0 hβb hβm hT x₀ ω
      equation := ?_ }
  intro t ht
  rw [poissonHorizonPath_initial (N := N) (v := v)
    hn hβ0 hβb hβm hT x₀ ω]
  exact poissonHorizonPath_equation (N := N) (v := v)
    hn hβ0 hβb hβm hT x₀ ω t ht

/-- Every measurable Poisson solution is the named finite-horizon path. -/
theorem poissonHorizonPath_extensional_unique
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    {T : ℝ} (hT : 0 ≤ T) (x₀ : Fin d → ℝ)
    (ω : ι → PathSpace Ω)
    {X : ℝ → Fin d → ℝ}
    (hX : IsPoissonTimeChangeSolution (N := N)
      n β v T x₀ ω X) :
    Set.EqOn X
      (poissonHorizonPath (N := N) (v := v)
        hn hβ0 hβb hβm hT x₀ ω)
      (Icc (0 : ℝ) T) :=
  poisson_timeChangeSolution_unique (N := N)
    hn hβ0 hβb hβm hT x₀ ω hX
    (poissonHorizonPath_isSolution (N := N) (v := v)
      hn hβ0 hβb hβm hT x₀ ω)

/-- Constructors at two horizons agree on the shorter horizon. -/
theorem poissonHorizonPath_consistent
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    {T T' : ℝ} (hT : 0 ≤ T) (hTT' : T ≤ T')
    (x₀ : Fin d → ℝ) (ω : ι → PathSpace Ω) :
    Set.EqOn
      (poissonHorizonPath (N := N) (v := v)
        hn hβ0 hβb hβm hT x₀ ω)
      (poissonHorizonPath (N := N) (v := v)
        hn hβ0 hβb hβm (hT.trans hTT') x₀ ω)
      (Icc (0 : ℝ) T) := by
  let X := poissonHorizonPath (N := N) (v := v)
    hn hβ0 hβb hβm hT x₀ ω
  let Z := poissonHorizonPath (N := N) (v := v)
    hn hβ0 hβb hβm (hT.trans hTT') x₀ ω
  have hXS : IsPoissonTimeChangeSolution (N := N)
      n β v T x₀ ω X :=
    poissonHorizonPath_isSolution (N := N) (v := v)
      hn hβ0 hβb hβm hT x₀ ω
  have hZlarge : IsPoissonTimeChangeSolution (N := N)
      n β v T' x₀ ω Z :=
    poissonHorizonPath_isSolution (N := N) (v := v)
      hn hβ0 hβb hβm (hT.trans hTT') x₀ ω
  have hZS : IsPoissonTimeChangeSolution (N := N)
      n β v T x₀ ω Z :=
    { measurable_path := hZlarge.measurable_path
      initial_eq := hZlarge.initial_eq
      equation := fun t ht =>
        hZlarge.equation t ⟨ht.1, ht.2.trans hTT'⟩ }
  exact poisson_timeChangeSolution_unique (N := N)
    hn hβ0 hβb hβm hT x₀ ω hXS hZS

end Ripple.Kurtz.StrongApprox

end
