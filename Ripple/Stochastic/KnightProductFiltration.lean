import Ripple.Stochastic.KnightSplicePaths
import Mathlib.Probability.Process.Adapted

/-!
# Product filtration for the compactified splice

Before one only the first coordinate is visible.
At and after one the whole first-coordinate sigma-algebra is visible, together
with the auxiliary filtration at elapsed time `r - 1`.

The construction and adaptation results use no continuity, convergence,
independence, measure, or martingale premise. Measurability of a terminal
random variable must be supplied separately.
-/

open MeasureTheory
open scoped NNReal

namespace Ripple.ProbabilityTheory

variable {Ω Ω₀ : Type*} [mΩ : MeasurableSpace Ω] [mΩ₀ : MeasurableSpace Ω₀]

/-- Sigma-algebras for a splice with deterministic pre- and post-seam maps.
Only the values of `κ` before one and of `lam` from one onward are used. -/
noncomputable def spliceProductSigma
    (F : Filtration ℝ≥0 mΩ) (G : Filtration ℝ≥0 mΩ₀)
    (κ lam : ℝ≥0 → ℝ≥0) (r : ℝ≥0) : MeasurableSpace (Ω × Ω₀) :=
  if r < 1 then MeasurableSpace.comap Prod.fst (F (κ r))
  else MeasurableSpace.comap Prod.fst mΩ ⊔
    MeasurableSpace.comap Prod.snd (G (lam r))

/-- Each sigma-algebra in the splice lies in the ambient product sigma-algebra. -/
theorem spliceProductSigma_le
    (F : Filtration ℝ≥0 mΩ) (G : Filtration ℝ≥0 mΩ₀)
    (κ lam : ℝ≥0 → ℝ≥0) (r : ℝ≥0) :
    spliceProductSigma F G κ lam r ≤
      (inferInstance : MeasurableSpace (Ω × Ω₀)) := by
  have hfst : MeasurableSpace.comap (Prod.fst : Ω × Ω₀ → Ω) mΩ ≤
      (inferInstance : MeasurableSpace (Ω × Ω₀)) := measurable_fst.comap_le
  have hsnd : MeasurableSpace.comap (Prod.snd : Ω × Ω₀ → Ω₀) mΩ₀ ≤
      (inferInstance : MeasurableSpace (Ω × Ω₀)) := measurable_snd.comap_le
  unfold spliceProductSigma
  split_ifs
  · exact (MeasurableSpace.comap_mono (F.le _)).trans hfst
  · exact sup_le hfst ((MeasurableSpace.comap_mono (G.le _)).trans hsnd)

/-- Monotonicity needs each time map only on the side where it is used. -/
theorem spliceProductSigma_mono
    (F : Filtration ℝ≥0 mΩ) (G : Filtration ℝ≥0 mΩ₀)
    (κ lam : ℝ≥0 → ℝ≥0)
    (hκ : ∀ ⦃r s : ℝ≥0⦄, r ≤ s → s < 1 → κ r ≤ κ s)
    (hlam : ∀ ⦃r s : ℝ≥0⦄, r ≤ s → 1 ≤ r → lam r ≤ lam s) :
    Monotone (spliceProductSigma F G κ lam) := by
  intro r s hrs
  by_cases hs : s < 1
  · have hr : r < 1 := lt_of_le_of_lt hrs hs
    simp only [spliceProductSigma, if_pos hr, if_pos hs]
    exact MeasurableSpace.comap_mono (F.mono (hκ hrs hs))
  · by_cases hr : r < 1
    · simp only [spliceProductSigma, if_pos hr, if_neg hs]
      exact (MeasurableSpace.comap_mono (F.le _)).trans le_sup_left
    · simp only [spliceProductSigma, if_neg hr, if_neg hs]
      exact sup_le_sup le_rfl
        (MeasurableSpace.comap_mono (G.mono (hlam hrs (le_of_not_gt hr))))

/-- The product filtration associated with deterministic splice time maps. -/
noncomputable def spliceProductFiltration
    (F : Filtration ℝ≥0 mΩ) (G : Filtration ℝ≥0 mΩ₀)
    (κ lam : ℝ≥0 → ℝ≥0)
    (hκ : ∀ ⦃r s : ℝ≥0⦄, r ≤ s → s < 1 → κ r ≤ κ s)
    (hlam : ∀ ⦃r s : ℝ≥0⦄, r ≤ s → 1 ≤ r → lam r ≤ lam s) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω₀)) where
  seq := spliceProductSigma F G κ lam
  mono' := spliceProductSigma_mono F G κ lam hκ hlam
  le' := spliceProductSigma_le F G κ lam

/-- The compactification map is increasing on its relevant domain `[0,1)`. -/
theorem compactificationTime_mono_before_seam
    {r s : ℝ≥0} (hrs : r ≤ s) (hs : s < 1) :
    compactificationTime r ≤ compactificationTime s := by
  have hr : r < 1 := lt_of_le_of_lt hrs hs
  have hrreal : (r : ℝ) < 1 := by exact_mod_cast hr
  have hsreal : (s : ℝ) < 1 := by exact_mod_cast hs
  have hrsreal : (r : ℝ) ≤ (s : ℝ) := by exact_mod_cast hrs
  have hquot : (r : ℝ) / (1 - (r : ℝ)) ≤ (s : ℝ) / (1 - (s : ℝ)) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).2
    nlinarith
  have hrsub : ((1 - r : ℝ≥0) : ℝ) = 1 - (r : ℝ) := by
    simpa using NNReal.coe_sub hr.le
  have hssub : ((1 - s : ℝ≥0) : ℝ) = 1 - (s : ℝ) := by
    simpa using NNReal.coe_sub hs.le
  change r / (1 - r) ≤ s / (1 - s)
  exact_mod_cast (show ((r / (1 - r) : ℝ≥0) : ℝ) ≤
      ((s / (1 - s) : ℝ≥0) : ℝ) by
    simpa only [NNReal.coe_div, hrsub, hssub] using hquot)

/-- The concrete filtration for the compactified original path followed by an
auxiliary path. Its seam value includes the whole original sigma-algebra. -/
noncomputable def compactifiedProductFiltration
    (F : Filtration ℝ≥0 mΩ) (G : Filtration ℝ≥0 mΩ₀) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω₀)) :=
  spliceProductFiltration F G compactificationTime (fun r => r - 1)
    (fun _ _ hrs hs => compactificationTime_mono_before_seam hrs hs)
    (fun _ _ hrs _ => tsub_le_tsub_right hrs 1)

/-- The concrete splice is increasing across both branches and the seam. -/
theorem compactifiedProductFiltration_mono
    (F : Filtration ℝ≥0 mΩ) (G : Filtration ℝ≥0 mΩ₀) :
    Monotone (compactifiedProductFiltration F G) :=
  fun _ _ h => (compactifiedProductFiltration F G).mono h

/-- Each concrete splice sigma-algebra is bounded by the product ambient space. -/
theorem compactifiedProductFiltration_le
    (F : Filtration ℝ≥0 mΩ) (G : Filtration ℝ≥0 mΩ₀) (r : ℝ≥0) :
    compactifiedProductFiltration F G r ≤
      (inferInstance : MeasurableSpace (Ω × Ω₀)) :=
  (compactifiedProductFiltration F G).le r

theorem compactifiedProductFiltration_before_seam
    (F : Filtration ℝ≥0 mΩ) (G : Filtration ℝ≥0 mΩ₀)
    {r : ℝ≥0} (hr : r < 1) :
    compactifiedProductFiltration F G r =
      MeasurableSpace.comap Prod.fst (F (compactificationTime r)) := by
  simp [compactifiedProductFiltration, spliceProductFiltration, spliceProductSigma, hr]

theorem compactifiedProductFiltration_after_seam
    (F : Filtration ℝ≥0 mΩ) (G : Filtration ℝ≥0 mΩ₀)
    {r : ℝ≥0} (hr : 1 ≤ r) :
    compactifiedProductFiltration F G r =
      MeasurableSpace.comap Prod.fst mΩ ⊔
        MeasurableSpace.comap Prod.snd (G (r - 1)) := by
  simp [compactifiedProductFiltration, spliceProductFiltration, spliceProductSigma,
    not_lt_of_ge hr]

/-- Pre-seam adaptation is just original adaptation pulled back by the first
projection. The codomain can be any measurable space. -/
theorem measurable_compactified_original
    {E : Type*} [MeasurableSpace E]
    (F : Filtration ℝ≥0 mΩ) (G : Filtration ℝ≥0 mΩ₀)
    {M : ℝ≥0 → Ω → E} (hM : ∀ t, Measurable[F t] (M t))
    {r : ℝ≥0} (hr : r < 1) :
    Measurable[compactifiedProductFiltration F G r]
      (fun p : Ω × Ω₀ => M (compactificationTime r) p.1) := by
  rw [compactifiedProductFiltration_before_seam F G hr]
  exact (hM _).comp (comap_measurable Prod.fst)

/-- An ambient-measurable original terminal value becomes measurable from the
seam onward, since the whole original sigma-algebra has been revealed. -/
theorem measurable_terminal_after_seam
    {E : Type*} [MeasurableSpace E]
    (F : Filtration ℝ≥0 mΩ) (G : Filtration ℝ≥0 mΩ₀)
    {L : Ω → E} (hL : Measurable L) {r : ℝ≥0} (hr : 1 ≤ r) :
    Measurable[compactifiedProductFiltration F G r]
      (fun p : Ω × Ω₀ => L p.1) := by
  rw [compactifiedProductFiltration_after_seam F G hr]
  exact (hL.comp (comap_measurable Prod.fst)).mono le_sup_left le_rfl

/-- In particular, the terminal value is measurable at the seam itself. -/
theorem measurable_terminal_at_seam
    {E : Type*} [MeasurableSpace E]
    (F : Filtration ℝ≥0 mΩ) (G : Filtration ℝ≥0 mΩ₀)
    {L : Ω → E} (hL : Measurable L) :
    Measurable[compactifiedProductFiltration F G 1]
      (fun p : Ω × Ω₀ => L p.1) :=
  measurable_terminal_after_seam F G hL le_rfl

/-- The shifted auxiliary process is measurable at every post-seam time. -/
theorem measurable_shifted_auxiliary
    {E : Type*} [MeasurableSpace E]
    (F : Filtration ℝ≥0 mΩ) (G : Filtration ℝ≥0 mΩ₀)
    {W : ℝ≥0 → Ω₀ → E} (hW : ∀ t, Measurable[G t] (W t))
    {r : ℝ≥0} (hr : 1 ≤ r) :
    Measurable[compactifiedProductFiltration F G r]
      (fun p : Ω × Ω₀ => W (r - 1) p.2) := by
  rw [compactifiedProductFiltration_after_seam F G hr]
  exact ((hW _).comp (comap_measurable Prod.snd)).mono le_sup_right le_rfl

/-- The real-valued spliced path is adapted to the constructed product
filtration. Terminal measurability is an input, not a convergence claim. -/
theorem measurable_splicedPath
    (F : Filtration ℝ≥0 mΩ) (G : Filtration ℝ≥0 mΩ₀)
    {M : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ} {W : ℝ≥0 → Ω₀ → ℝ}
    (hM : ∀ t, Measurable[F t] (M t)) (hL : Measurable L)
    (hW : ∀ t, Measurable[G t] (W t)) :
    ∀ r, Measurable[compactifiedProductFiltration F G r]
      (fun p : Ω × Ω₀ => splicedPath (fun t => M t p.1) (L p.1)
        (fun t => W t p.2) r) := by
  intro r
  by_cases hr : r < 1
  · simpa only [splicedPath, if_pos hr] using
      measurable_compactified_original F G hM hr
  · simpa only [splicedPath, if_neg hr] using
      (measurable_terminal_after_seam F G hL (le_of_not_gt hr)).add
        (measurable_shifted_auxiliary F G hW (le_of_not_gt hr))

/-- For real-valued paths, the same hypotheses give the standard strong
adaptation interface used by the martingale library. -/
theorem stronglyAdapted_splicedPath
    (F : Filtration ℝ≥0 mΩ) (G : Filtration ℝ≥0 mΩ₀)
    {M : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ} {W : ℝ≥0 → Ω₀ → ℝ}
    (hM : ∀ t, Measurable[F t] (M t)) (hL : Measurable L)
    (hW : ∀ t, Measurable[G t] (W t)) :
    StronglyAdapted (compactifiedProductFiltration F G)
      (fun r p => splicedPath (fun t => M t p.1) (L p.1)
        (fun t => W t p.2) r) :=
  fun r => (measurable_splicedPath F G hM hL hW r).stronglyMeasurable

end Ripple.ProbabilityTheory
