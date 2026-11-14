-- Ripple/Kurtz/StrongApprox/ComparisonPathRegularity.lean
import Ripple.Kurtz.StrongApprox.DiffusionTimeChangeExistence
import Ripple.Kurtz.StrongApprox.PoissonTimeChangeGlobal
import Ripple.Kurtz.StrongApprox.BrownianEntropyComparison

/-!
# Path-regularity premises of the B7 comparison, for the actual objects

`timeChange_diffusion_comparison_of_entropy` consumes four analytic premises on
the chain `X` and the diffusion `Z`:

* `hbetaX`, `hbetaZ`: interval integrability of the rates along each path;
* `huint`: `s ↦ ‖X s - Z s‖` is integrable on `[0,T]`;
* `hurc`: `s ↦ ‖X s - Z s‖` is right continuous at every `t ∈ [0,T)`.

For the chain `X = globalPoissonPath` of the Poisson time change (measurable,
locally constant to the right, finitely many jumps on every compact interval)
and any continuous `Z`, these are proved here for every sample; for the
diffusion `Z` produced by `exists_diffusionTimeChange_solution` they therefore
have a reachable producer.  No stochastic hypothesis is used: all statements
are pathwise.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset Filter Topology
open scoped ENNReal BigOperators

/-! ## Generic path facts -/

/-- A bounded measurable function of a measurable path is interval integrable. -/
theorem intervalIntegrable_comp_of_bounded
    {E : Type*} [MeasurableSpace E] {g : E → ℝ} (hg : Measurable g)
    {c : ℝ} (hc : ∀ y, |g y| ≤ c) {X : ℝ → E} (hX : Measurable X)
    (a b : ℝ) :
    IntervalIntegrable (fun s => g (X s)) volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := c) (by simp)
    (hg.comp hX).aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs]
  exact hc _

/-- A path that is constant on a right neighbourhood is right continuous
(within `Ioi`). -/
theorem continuousWithinAt_Ioi_of_eventually_right
    {E : Type*} [TopologicalSpace E] {X : ℝ → E} {t : ℝ}
    (h : ∀ᶠ s in 𝓝[≥] t, X s = X t) :
    ContinuousWithinAt X (Ioi t) t := by
  have h' : ∀ᶠ s in 𝓝[>] t, X s = X t :=
    Filter.Eventually.filter_mono (nhdsWithin_mono _ Set.Ioi_subset_Ici_self) h
  exact continuousWithinAt_const.congr_of_eventuallyEq h' rfl

/-- Finitely many jumps on `[0,T]` force boundedness there. -/
theorem bounded_of_finiteJumpSupport
    {E : Type*} [NormedAddCommGroup E] {X : ℝ → E} {T : ℝ}
    (S : Finset ℝ)
    (hS : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ T →
      Disjoint (Ioc s t : Set ℝ) (S : Set ℝ) → X s = X t) :
    ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ‖X t‖ ≤ C := by
  classical
  have hfin : (X '' (↑(insert (0 : ℝ) S) : Set ℝ)).Finite :=
    (Finset.finite_toSet _).image X
  obtain ⟨C, hC⟩ := hfin.isBounded.exists_norm_le
  refine ⟨C, fun t ht => ?_⟩
  by_cases hne : (S.filter fun x => x ∈ Ioc 0 t).Nonempty
  · set s := (S.filter fun x => x ∈ Ioc 0 t).max' hne with hs
    have hsmem := Finset.max'_mem _ hne
    rw [← hs, Finset.mem_filter] at hsmem
    have hdisj : Disjoint (Ioc s t : Set ℝ) (S : Set ℝ) := by
      rw [Set.disjoint_left]
      intro x hx hxS
      have hxf : x ∈ S.filter fun x => x ∈ Ioc 0 t :=
        Finset.mem_filter.mpr ⟨hxS, ⟨lt_trans hsmem.2.1 hx.1, hx.2⟩⟩
      have := Finset.le_max' _ x hxf
      rw [← hs] at this
      exact absurd hx.1 (not_lt.mpr this)
    have heq := hS hsmem.2.1.le hsmem.2.2 ht.2 hdisj
    rw [← heq]
    exact hC _ ⟨s, by simp [hsmem.1], rfl⟩
  · have hdisj : Disjoint (Ioc 0 t : Set ℝ) (S : Set ℝ) := by
      rw [Set.disjoint_left]
      intro x hx hxS
      exact hne ⟨x, Finset.mem_filter.mpr ⟨hxS, hx⟩⟩
    have heq := hS le_rfl ht.1 ht.2 hdisj
    rw [← heq]
    exact hC _ ⟨0, by simp, rfl⟩

/-- Integrability of the distance between a bounded measurable path and a
continuous path. -/
theorem integrableOn_norm_sub_of_bounded
    {d : ℕ} {X Z : ℝ → Fin d → ℝ} (hXm : Measurable X) (hZ : Continuous Z)
    {T C : ℝ} (hC : ∀ t ∈ Icc (0 : ℝ) T, ‖X t‖ ≤ C) :
    IntegrableOn (fun s => ‖X s - Z s‖) (Icc (0 : ℝ) T) := by
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := Z) (s := Icc (0 : ℝ) T) hZ.continuousOn
  refine Measure.integrableOn_of_bounded (M := C + D)
    (measure_Icc_lt_top.ne)
    ((hXm.sub hZ.measurable).norm.aestronglyMeasurable) ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  refine Filter.Eventually.of_forall fun t ht => ?_
  rw [norm_norm]
  calc ‖X t - Z t‖ ≤ ‖X t‖ + ‖Z t‖ := norm_sub_le _ _
    _ ≤ C + D := add_le_add (hC t ht) (hD t ht)


/-! ## The chain: regularity of `globalPoissonPath` -/

section Chain

variable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ → Ω → ℕ}
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The global chain is measurable, right continuous at every `t ≥ 0`, and
bounded on every `[0,T]`. -/
theorem globalPoissonPath_regularity
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (ω : ι → PathSpace Ω) {T : ℝ} (hT : 0 ≤ T) :
    Measurable (globalPoissonPath (N := N) (v := v) hn hβ0 hβb hβm x₀ ω) ∧
    (∀ t : ℝ, 0 ≤ t →
      ContinuousWithinAt
        (globalPoissonPath (N := N) (v := v) hn hβ0 hβb hβm x₀ ω)
        (Ioi t) t) ∧
    (∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) T,
      ‖globalPoissonPath (N := N) (v := v) hn hβ0 hβb hβm x₀ ω t‖ ≤ C) := by
  refine ⟨globalPoissonPath_measurable (N := N) (v := v) hn hβ0 hβb hβm x₀ ω,
    fun t ht => continuousWithinAt_Ioi_of_eventually_right
      (globalPoissonPath_eventually_right (N := N) (v := v)
        hn hβ0 hβb hβm x₀ ω ht), ?_⟩
  obtain ⟨S, hS⟩ := globalPoissonPath_locallyFinite (N := N) (v := v)
    hn hβ0 hβb hβm x₀ ω hT
  exact bounded_of_finiteJumpSupport S hS

/-- The chain satisfies its equation in the form consumed by the comparison
theorem, with the real-argument driver `Y l u = poisFamily ι N l u ω`. -/
theorem globalPoissonPath_hXeq
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (ω : ι → PathSpace Ω) {T : ℝ} :
    ∀ t ∈ Icc (0 : ℝ) T,
      globalPoissonPath (N := N) (v := v) hn hβ0 hβb hβm x₀ ω t =
        x₀ + ∑ l,
          (((poisFamily ι N l
            (scaledTcClock (n : ℝ) β
              (globalPoissonPath (N := N) (v := v) hn hβ0 hβb hβm x₀ ω)
              l t) ω : ℕ) : ℝ) / (n : ℝ)) • v l := by
  intro t ht
  have h := globalPoissonPath_equation (N := N) (v := v)
    hn hβ0 hβb hβm x₀ ω ht.1
  have h0 := globalPoissonPath_initial (N := N) (v := v)
    hn hβ0 hβb hβm x₀ ω
  simp only [h0] at h
  exact h

/-- Pathwise regularity of the pair (chain, continuous `Z`), in the form
consumed by `timeChange_diffusion_comparison_of_entropy`. -/
theorem comparison_pathRegularity
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (ω : ι → PathSpace Ω) {T : ℝ} (hT : 0 ≤ T)
    -- the rates of the diffusion
    {g : ι → (Fin d → ℝ) → ℝ} (hgm : ∀ l, Measurable (g l))
    {c : ι → ℝ} (hgc : ∀ l y, |g l y| ≤ c l)
    {Z : ℝ → Fin d → ℝ} (hZ : Continuous Z) :
    let X := globalPoissonPath (N := N) (v := v) hn hβ0 hβb hβm x₀ ω
    (∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => β l (X s)) volume 0 t) ∧
    (∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => g l (X s)) volume 0 t) ∧
    (∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => g l (Z s)) volume 0 t) ∧
    IntegrableOn (fun s => ‖X s - Z s‖) (Icc (0 : ℝ) T) ∧
    (∀ t ∈ Ico (0 : ℝ) T,
      ContinuousWithinAt (fun s => ‖X s - Z s‖) (Ioi t) t) := by
  intro X
  obtain ⟨hXm, hXrc, C, hC⟩ := globalPoissonPath_regularity (N := N) (v := v)
    hn hβ0 hβb hβm x₀ ω hT
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro l t _
    exact intervalIntegrable_rate hβ0 hβb hβm hXm l 0 t
  · intro l t _
    exact intervalIntegrable_comp_of_bounded (hgm l) (hgc l) hXm 0 t
  · intro l t _
    exact intervalIntegrable_comp_of_bounded (hgm l) (hgc l) hZ.measurable 0 t
  · exact integrableOn_norm_sub_of_bounded hXm hZ hC
  · intro t ht
    exact ((hXrc t ht.1).sub hZ.continuousWithinAt).norm


/-- **All premises of the B7 comparison have a producer on main.**  For the chain
`X = globalPoissonPath` (rates `β`, scale `n`) and the diffusion `Z` produced by
`exists_diffusionTimeChange_solution` (continuous rates `f`, continuous drivers
`W l`, same initial state, jumps and scale), the exact hypotheses
`hXeq`, `hZeq`, `hbetaX`, `hbetaZ`, `huint`, `hurc` of
`timeChange_diffusion_comparison_of_entropy` hold on `[0,T]` for every sample.
(`hbetaX` is given both for the chain rates `β` and for the diffusion rates
`f`, since the perturbed comparison uses both.) -/
theorem comparison_hPaths_actual
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (ω : ι → PathSpace Ω) {T : ℝ} (hT : 0 ≤ T)
    (W : ι → ℝ → ℝ) (hW : ∀ l, Continuous (W l))
    (f : ι → (Fin d → ℝ) → ℝ) (hf : ∀ l, Continuous (f l))
    (B : ι → ℝ) (hf0 : ∀ l y, 0 ≤ f l y) (hfB : ∀ l y, f l y ≤ B l) :
    let X := globalPoissonPath (N := N) (v := v) hn hβ0 hβb hβm x₀ ω
    (∀ t ∈ Icc (0 : ℝ) T,
      X t = x₀ + ∑ l,
        (((poisFamily ι N l (scaledTcClock (n : ℝ) β X l t) ω : ℕ) : ℝ) /
          (n : ℝ)) • v l) ∧
    ∃ Z : ℝ → Fin d → ℝ,
      Continuous Z ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        Z t = x₀ + (∫ s in (0 : ℝ)..t, tcDrift f v (Z s)) +
          ∑ l, (W l (scaledTcClock (n : ℝ) f Z l t) / (n : ℝ)) • v l) ∧
      (∀ l t, t ∈ Icc (0 : ℝ) T →
        IntervalIntegrable (fun s => β l (X s)) volume 0 t) ∧
      (∀ l t, t ∈ Icc (0 : ℝ) T →
        IntervalIntegrable (fun s => f l (X s)) volume 0 t) ∧
      (∀ l t, t ∈ Icc (0 : ℝ) T →
        IntervalIntegrable (fun s => f l (Z s)) volume 0 t) ∧
      IntegrableOn (fun s => ‖X s - Z s‖) (Icc (0 : ℝ) T) ∧
      (∀ t ∈ Ico (0 : ℝ) T,
        ContinuousWithinAt (fun s => ‖X s - Z s‖) (Ioi t) t) := by
  intro X
  refine ⟨globalPoissonPath_hXeq (N := N) (v := v) hn hβ0 hβb hβm x₀ ω, ?_⟩
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨Z, hZ, _hZint, hZeq⟩ := exists_diffusionTimeChange_solution
    W hW f hf B hf0 hfB v hnR hT x₀
  have hgc : ∀ l y, |f l y| ≤ B l := fun l y => by
    rw [abs_of_nonneg (hf0 l y)]
    exact hfB l y
  obtain ⟨h1, h2, h3, h4, h5⟩ := comparison_pathRegularity
    (N := N) (v := v) hn hβ0 hβb hβm x₀ ω hT
    (fun l => (hf l).measurable) hgc hZ
  exact ⟨Z, hZ, hZeq, h1, h2, h3, h4, h5⟩

end Chain

end Ripple.Kurtz.StrongApprox

end
