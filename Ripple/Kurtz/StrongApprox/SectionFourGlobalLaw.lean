import Ripple.Kurtz.StrongApprox.SectionFourGaussianIdentification
import Ripple.Kurtz.StrongApprox.KurtzTheoremFourFourOfKnight

/-!
# Window laws for the all-time Section Four limit

On every bounded nonnegative window, the installed all-time process agrees
almost surely with the finite-horizon process. This identifies its continuous
paths, centered Gaussian observations, and deterministic linear equation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Kurtz.StrongApprox

variable {m d : ℕ} {v : Fin m → Fin d → ℝ}
  {f : Fin m → (Fin d → ℝ) → ℝ} {eps : Fin m → ℝ} {M : ℝ}
  {F' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {L1 L2 : ℝ}

/-- Almost surely the all-time process is continuous on each specified window. -/
theorem sectionFourVAll_ae_continuousOn
    (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hL1 : ∀ x, ‖F' x‖ ≤ L1)
    (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖)
    (x0 : Fin d → ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂channelKMTMeasure (Fin m),
      ContinuousOn (sectionFourVAll F' f v x0 ω) (Icc (0 : ℝ) T) := by
  filter_upwards [sectionFourVAll_eq (F' := F') (v := v)
    heps hM hf0 hfB h319 hL1 hL2n hL2 x0 T] with ω hω
  exact (continuous_sectionFourV heps hM hf0 hfB h319 hL2n hL2 x0 T ω).continuousOn.congr
    (fun t ht => hω t ht)

/-- Every finite vector of observations of the all-time process is centered Gaussian. -/
theorem sectionFourVAll_finiteDimensional_centeredGaussian {k : ℕ}
    (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hL1 : ∀ x, ‖F' x‖ ≤ L1)
    (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖)
    (Lg : Fin m → ℝ≥0)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)
    (x0 : Fin d → ℝ) (T : ℝ≥0) (t : Fin k → Icc (0 : ℝ) T) :
    HasGaussianLaw (fun ω q => sectionFourVAll F' f v x0 ω (t q))
      (channelKMTMeasure (Fin m)) ∧
    (∫ ω, (fun q => sectionFourVAll F' f v x0 ω (t q))
      ∂channelKMTMeasure (Fin m)) = 0 := by
  obtain ⟨hG, hmean⟩ := sectionFourV_finiteDimensional_centeredGaussian
    heps hM hf0 hfB h319 hL1 hL2n hL2 Lg hLg x0 T t
  have heq : (fun ω q => sectionFourVAll F' f v x0 ω (t q))
      =ᵐ[channelKMTMeasure (Fin m)]
      (fun ω q => sectionFourV F' f v x0 T ω (t q)) := by
    filter_upwards [sectionFourVAll_eq (F' := F') (v := v)
      heps hM hf0 hfB h319 hL1 hL2n hL2 x0 T] with ω hω
    funext q
    exact hω (t q) (t q).property
  exact ⟨hG.congr heq.symm, (integral_congr_ae heq).trans hmean⟩

/-- On one full-measure event for each window, the all-time process satisfies
the linear equation with the deterministic integration-by-parts forcing. -/
theorem sectionFourVAll_ae_equation_J
    (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hL1 : ∀ x, ‖F' x‖ ≤ L1)
    (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖)
    (Lg : Fin m → ℝ≥0)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)
    (x0 : Fin d → ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂channelKMTMeasure (Fin m), ∀ t ∈ Icc (0 : ℝ) T,
      sectionFourVAll F' f v x0 ω t =
        (∑ l, Ripple.Analysis.BVIntegrationByParts.J
          (fun s => Real.sqrt (f l (kurtzFluidLimit f v x0 s.toNNReal)))
          (fun s => channelBrownian l s.toNNReal ω) t • v l) +
        ∫ s in (0 : ℝ)..t,
          sectionFourCoeff F' f v x0 s (sectionFourVAll F' f v x0 ω s) := by
  filter_upwards [sectionFourVAll_eq (F' := F') (v := v)
      heps hM hf0 hfB h319 hL1 hL2n hL2 x0 T,
    sectionFourV_ae_equation_J heps hM hf0 hfB h319 hL2n hL2 Lg hLg x0 T]
    with ω heq hJ
  intro t ht
  rw [heq t ht, hJ t ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hst : s ∈ Icc (0 : ℝ) t := by
    simpa only [uIcc_of_le ht.1] using hs
  beta_reduce
  rw [heq s ⟨hst.1, hst.2.trans ht.2⟩]

/-- A measure-preserving projection transports centered Gaussian observation
vectors, including their vector-valued zero mean, to an extension space. -/
theorem centeredGaussian_comp_measurePreserving
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {k : ℕ}
    {π : Ω' → Ω} (hπ : MeasurePreserving π P' P)
    {X : Ω → Fin k → Fin d → ℝ}
    (hX : HasGaussianLaw X P) (hmean : (∫ ω, X ω ∂P) = 0) :
    HasGaussianLaw (fun ω => X (π ω)) P' ∧
      (∫ ω, X (π ω) ∂P') = 0 := by
  have hXm : AEMeasurable X (P'.map π) := by
    rw [hπ.map_eq]
    exact hX.aemeasurable
  have hmap : P'.map (fun ω => X (π ω)) = P.map X := by
    change P'.map (X ∘ π) = P.map X
    rw [← AEMeasurable.map_map_of_aemeasurable hXm hπ.measurable.aemeasurable,
      hπ.map_eq]
  have hG : HasGaussianLaw (fun ω => X (π ω)) P' := by
    refine ⟨?_⟩
    rw [hmap]
    exact hX.isGaussian_map
  refine ⟨hG, ?_⟩
  have hXs : AEStronglyMeasurable X (P'.map π) := by
    rw [hπ.map_eq]
    exact hX.integrable.aestronglyMeasurable
  calc
    (∫ ω, X (π ω) ∂P') = ∫ ω, X ω ∂P'.map π :=
      (integral_map hπ.measurable.aemeasurable hXs).symm
    _ = ∫ ω, X ω ∂P := by rw [hπ.map_eq]
    _ = 0 := hmean

end Ripple.Kurtz.StrongApprox
