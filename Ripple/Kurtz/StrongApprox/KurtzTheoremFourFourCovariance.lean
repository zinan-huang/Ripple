import Ripple.Kurtz.StrongApprox.KurtzTheoremFourFour
import Ripple.Kurtz.StrongApprox.SectionFourCovariance

/-!
# Kurtz's Theorem 4.4 with the covariance of the Gaussian limit

`kurtz_theorem_four_four_covariance` adds to `kurtz_theorem_four_four` the two-time covariance
of the Gaussian limit `V` of the conclusion, under the coupling measure:

`Cov(⟨a, V t⟩, ⟨b, V u⟩) = ∫_{(0, t ∧ u]} ⟨a, Φ(t,s) Σ(X s) Φ(u,s)ᵀ b⟩ ds`

for every horizon `T ≥ t, u`. Here `X` is the fluid limit, `Φ` is the fundamental matrix of the
linear equation `Φ' = DF(X) Φ` built from the Jacobian `DF` assembled from the paper's coordinate
partials, and `Σ(x) = Σ_l f_l(x) v_l v_lᵀ` is written with the original rates `f`. The
construction masks the rates of zero jump directions; masking does not change `Σ`
(`sectionFourSigma_maskZeroRate`).

The covariance is the channel-space formula `sectionFourVAll_covariance`, transported along the
measure-preserving projection of the coupling space onto the channel space
(`covariance_comp_measurePreserving`).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Kurtz.StrongApprox
open PaperSectionFourHypotheses VolterraGaussian

/-- The noise covariance matrix does not see the rates of zero jump directions. -/
theorem sectionFourSigma_maskZeroRate {m d : ℕ} (f : Fin m → (Fin d → ℝ) → ℝ)
    (v : Fin m → Fin d → ℝ) (x : Fin d → ℝ) :
    sectionFourSigma (maskZeroRate v f) v x = sectionFourSigma f v x := by
  classical
  ext i j
  simp only [sectionFourSigma]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : v l = 0
  · simp [hl]
  · simp [maskZeroRate, hl]

/-- Covariance is transported along a measure-preserving map. -/
theorem covariance_comp_measurePreserving {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'} {π : Ω' → Ω}
    (hπ : MeasurePreserving π P' P) {X Y : Ω → ℝ}
    (hX : AEStronglyMeasurable X P) (hY : AEStronglyMeasurable Y P) :
    cov[fun ω => X (π ω), fun ω => Y (π ω); P'] = cov[X, Y; P] := by
  have hint : ∀ g : Ω → ℝ, AEStronglyMeasurable g P →
      ∫ ω, g (π ω) ∂P' = ∫ x, g x ∂P := by
    intro g hg
    rw [← hπ.map_eq] at hg
    rw [← integral_map hπ.measurable.aemeasurable hg, hπ.map_eq]
  simp only [covariance]
  rw [hint X hX, hint Y hY]
  exact hint (fun x => (X x - ∫ ω, X ω ∂P) * (Y x - ∫ ω, Y ω ∂P))
    ((hX.sub aestronglyMeasurable_const).mul (hY.sub aestronglyMeasurable_const))

/-- **Kurtz's Theorem 4.4 with the covariance of the limit.** From the paper data, the
conclusion of `kurtz_theorem_four_four` holds, and the Gaussian limit `V` of that conclusion has,
under the coupling measure, the covariance
`Cov(⟨a, V t⟩, ⟨b, V u⟩) = ∫_{(0, t ∧ u]} ⟨a, Φ(t,s) Σ(X s) Φ(u,s)ᵀ b⟩ ds` for every horizon
`T ≥ t, u`, with `Φ` the fundamental matrix of `DF(X(·))` (the Jacobian from the coordinate
partials) on `[0, T]` and `Σ(x) = Σ_l f_l(x) v_l v_lᵀ` with the original rates. -/
theorem kurtz_theorem_four_four_covariance {m d : ℕ}
    {v : Fin m → Fin d → ℝ} {f : Fin m → (Fin d → ℝ) → ℝ}
    {fN : ℕ → Fin m → (Fin d → ℝ) → ℝ} {eps : Fin m → ℝ}
    {Gamma M firstBound secondBound : ℝ}
    (h : SectionFourPaperData v f fN eps Gamma M firstBound secondBound)
    (x0 : Fin d → ℝ) :
    h.Conclusion x0 ∧
    ∀ (T t u : ℝ≥0), t ≤ T → u ≤ T → ∀ a b : Fin d → ℝ,
      cov[fun z => dotProduct a (h.gaussian x0 z t),
        fun z => dotProduct b (h.gaussian x0 z u); h.couplingMeasure x0] =
        ∫ s in Ioc (0 : ℝ) (min (t : ℝ) (u : ℝ)),
          dotProduct a
            ((fundamentalMatrix (fun r => h.derivative (h.fluid x0 r.toNNReal)) T t s *
              sectionFourSigma f v (h.fluid x0 s.toNNReal) *
              (fundamentalMatrix (fun r => h.derivative (h.fluid x0 r.toNNReal))
                T u s).transpose).mulVec b) := by
  refine ⟨kurtz_theorem_four_four h x0, ?_⟩
  intro T t u ht hu a b
  have hmeas : ∀ (c : Fin d → ℝ) (r : ℝ≥0), r ≤ T →
      AEStronglyMeasurable
        (fun ω => dotProduct c (sectionFourVAll h.derivative h.rate v x0 ω r))
        (channelKMTMeasure (Fin m)) := by
    intro c r hr
    have hg := (sectionFourVAll_finiteDimensional_centeredGaussian (v := v) h.eps_nonneg
      h.rate_lipschitz.1 h.rate_bounds.1 h.rate_bounds.2 h.rate_lipschitz.2
      h.derivative_hypotheses.2.1 h.derivative_hypotheses.2.2.1
      h.derivative_hypotheses.2.2.2 h.sqrtConstant h.sqrt_lipschitz x0 T
      (fun _ : Fin 1 => (⟨r, r.coe_nonneg, by exact_mod_cast hr⟩ : Icc (0 : ℝ) T))).1.aemeasurable
    have hc : Continuous fun w : Fin 1 → Fin d → ℝ => dotProduct c (w 0) :=
      continuous_const.dotProduct (continuous_apply 0)
    exact (hc.measurable.comp_aemeasurable hg).aestronglyMeasurable
  have hcov := sectionFourVAll_covariance (F' := h.derivative) (v := v) h.eps_nonneg
    h.rate_lipschitz.1 h.rate_bounds.1 h.rate_bounds.2 h.rate_lipschitz.2
    h.derivative_hypotheses.2.1 h.derivative_hypotheses.2.2.1
    h.derivative_hypotheses.2.2.2 h.sqrtConstant h.sqrt_lipschitz x0 T ht hu a b
  have hs : ∀ x, sectionFourSigma h.rate v x = sectionFourSigma f v x :=
    sectionFourSigma_maskZeroRate f v
  simp only [hs] at hcov
  refine (covariance_comp_measurePreserving (h.projection_measurePreserving x0)
    (hmeas a t ht) (hmeas b u hu)).trans ?_
  exact hcov

end Ripple.Kurtz.StrongApprox
