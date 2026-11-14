import Ripple.Kurtz.StrongApprox.SectionFourCoordinateCovariance
import Ripple.Kurtz.StrongApprox.SectionFourCovarianceAlgebra
import Ripple.Kurtz.StrongApprox.SectionFourGlobalLaw

/-!
# Covariance of the actual Section Four Gaussian limit

The matrix is the columnwise fundamental evolution already used in the
construction. The noise covariance uses the original rates and jump vectors.
Euclidean pairings are explicit coordinate dot products.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal BigOperators

namespace Ripple.Kurtz.StrongApprox

open VolterraGaussian

variable {m d : ℕ} {v : Fin m → Fin d → ℝ}
  {f : Fin m → (Fin d → ℝ) → ℝ} {eps : Fin m → ℝ} {M : ℝ}
  {F' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {L1 L2 : ℝ}

/-- Each coordinate of the covariance integrand is integrable over the common
observation interval, by the starting-time continuity of the actual evolution. -/
theorem integrableOn_sectionFour_covariance_entry
    (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖)
    (x0 : Fin d → ℝ) (T : ℝ≥0) {t u : ℝ≥0} (ht : t ≤ T) (hu : u ≤ T)
    (i j : Fin d) :
    IntegrableOn (fun s => ∑ l,
      f l (kurtzFluidLimit f v x0 s.toNNReal) *
        (fundamentalCLM (sectionFourCoeff F' f v x0) T t s (v l)) i *
        (fundamentalCLM (sectionFourCoeff F' f v x0) T u s (v l)) j)
      (Ioc (0 : ℝ) (min (t : ℝ) (u : ℝ))) := by
  have hA := continuous_sectionFourCoeff (v := v) heps hM hf0 hfB h319 hL2n hL2 x0
  have hX := (continuous_kurtzFluidLimit (v := v) heps hM hf0 hfB h319 x0).comp
    continuous_real_toNNReal
  have htc := continuousOn_fundamentalCLM_start_of_continuous
    (T := (T : ℝ)) (t := (t : ℝ)) hA (by exact_mod_cast ht)
  have huc := continuousOn_fundamentalCLM_start_of_continuous
    (T := (T : ℝ)) (t := (u : ℝ)) hA (by exact_mod_cast hu)
  have ht' : Icc (0 : ℝ) (min (t : ℝ) (u : ℝ)) ⊆ Icc (0 : ℝ) (t : ℝ) :=
    Icc_subset_Icc le_rfl (min_le_left _ _)
  have hu' : Icc (0 : ℝ) (min (t : ℝ) (u : ℝ)) ⊆ Icc (0 : ℝ) (u : ℝ) :=
    Icc_subset_Icc le_rfl (min_le_right _ _)
  apply integrable_finsetSum
  intro l _
  have hterm : ContinuousOn (fun s =>
      f l (kurtzFluidLimit f v x0 s.toNNReal) *
        (fundamentalCLM (sectionFourCoeff F' f v x0) T t s (v l)) i *
        (fundamentalCLM (sectionFourCoeff F' f v x0) T u s (v l)) j)
        (Icc (0 : ℝ) (min (t : ℝ) (u : ℝ))) := by
    exact (((continuous_rate_of_lip heps hM h319 l).comp hX).continuousOn.mul
      ((continuous_apply i).comp_continuousOn
        ((htc.mono ht').clm_apply continuousOn_const))).mul
      ((continuous_apply j).comp_continuousOn
        ((huc.mono hu').clm_apply continuousOn_const))
  exact (hterm.integrableOn_compact isCompact_Icc).mono_set
    (fun s hs => ⟨hs.1.le, hs.2⟩)

/-- The requested two-time covariance for the actual finite-horizon V.
No kernel representation, independence, or covariance identity is a premise. -/
theorem sectionFourV_covariance
    (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hL1 : ∀ x, ‖F' x‖ ≤ L1)
    (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖)
    (Lg : Fin m → ℝ≥0)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)
    (x0 : Fin d → ℝ) (T : ℝ≥0) {t u : ℝ≥0} (ht : t ≤ T) (hu : u ≤ T)
    (a b : Fin d → ℝ) :
    cov[fun ω => dotProduct a (sectionFourV F' f v x0 T ω t),
      fun ω => dotProduct b (sectionFourV F' f v x0 T ω u); channelKMTMeasure (Fin m)] =
      ∫ s in Ioc (0 : ℝ) (min (t : ℝ) (u : ℝ)),
        dotProduct a
          ((fundamentalMatrix (sectionFourCoeff F' f v x0) T t s *
            sectionFourSigma f v (kurtzFluidLimit f v x0 s.toNNReal) *
            (fundamentalMatrix (sectionFourCoeff F' f v x0) T u s).transpose).mulVec b) := by
  classical
  let R : ℝ → Fin d → Fin d → ℝ := fun s i j => ∑ l,
    f l (kurtzFluidLimit f v x0 s.toNNReal) *
      (fundamentalCLM (sectionFourCoeff F' f v x0) T t s (v l)) i *
      (fundamentalCLM (sectionFourCoeff F' f v x0) T u s (v l)) j
  let ν := volume.restrict (Ioc (0 : ℝ) (min (t : ℝ) (u : ℝ)))
  have hint : ∀ i j, Integrable (fun s => R s i j) ν := fun i j =>
    integrableOn_sectionFour_covariance_entry heps hM hf0 hfB h319 hL2n hL2 x0 T ht hu i j
  rw [covariance_dotProduct
    (fun i => sectionFourV_coordinate_memLp heps hM hf0 hfB h319 hL1 hL2n hL2 Lg hLg x0 T ht i)
    (fun j => sectionFourV_coordinate_memLp heps hM hf0 hfB h319 hL1 hL2n hL2 Lg hLg x0 T hu j)]
  simp_rw [sectionFourV_coordinate_covariance heps hM hf0 hfB h319 hL1 hL2n hL2 Lg hLg x0 T ht hu]
  change (∑ i, ∑ j, a i * b j * ∫ s, R s i j ∂ν) = _
  simp_rw [← integral_const_mul]
  have hinner (i : Fin d) :
      (∑ j, ∫ s, (a i * b j) * R s i j ∂ν) =
        ∫ s, ∑ j, (a i * b j) * R s i j ∂ν :=
    (integral_finsetSum Finset.univ (fun j _ => (hint i j).const_mul (a i * b j))).symm
  simp_rw [hinner]
  -- The two finite sums now pass through the same scalar integral.
  rw [← integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum _ (fun j _ => (hint i j).const_mul (a i * b j)))]
  apply integral_congr_ae
  apply ae_of_all
  intro s
  have hentry (i j : Fin d) : R s i j =
      (fundamentalMatrix (sectionFourCoeff F' f v x0) T t s *
        sectionFourSigma f v (kurtzFluidLimit f v x0 s.toNNReal) *
        (fundamentalMatrix (sectionFourCoeff F' f v x0) T u s).transpose) i j := by
    rw [sectionFourSigma_propagated_entry]
    simp only [R, fundamentalCLM_eq_mulVec]
  simp_rw [hentry]
  exact weighted_entries_eq_pairing a b _

/-- Covariance is unaffected by replacing either variable on a null set. -/
theorem covariance_eq_of_ae
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  unfold covariance
  rw [integral_congr_ae hX, integral_congr_ae hY]
  apply integral_congr_ae
  filter_upwards [hX, hY] with ω hx hy
  rw [hx, hy]

/-- The same formula holds for the already installed horizon-independent V. -/
theorem sectionFourVAll_covariance
    (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hL1 : ∀ x, ‖F' x‖ ≤ L1)
    (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖)
    (Lg : Fin m → ℝ≥0)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)
    (x0 : Fin d → ℝ) (T : ℝ≥0) {t u : ℝ≥0} (ht : t ≤ T) (hu : u ≤ T)
    (a b : Fin d → ℝ) :
    cov[fun ω => dotProduct a (sectionFourVAll F' f v x0 ω t),
      fun ω => dotProduct b (sectionFourVAll F' f v x0 ω u); channelKMTMeasure (Fin m)] =
      ∫ s in Ioc (0 : ℝ) (min (t : ℝ) (u : ℝ)),
        dotProduct a
          ((fundamentalMatrix (sectionFourCoeff F' f v x0) T t s *
            sectionFourSigma f v (kurtzFluidLimit f v x0 s.toNNReal) *
            (fundamentalMatrix (sectionFourCoeff F' f v x0) T u s).transpose).mulVec b) := by
  have ht' : (t : ℝ) ∈ Icc (0 : ℝ) T := ⟨t.coe_nonneg, by exact_mod_cast ht⟩
  have hu' : (u : ℝ) ∈ Icc (0 : ℝ) T := ⟨u.coe_nonneg, by exact_mod_cast hu⟩
  have heq := sectionFourVAll_eq (F' := F') (v := v)
    heps hM hf0 hfB h319 hL1 hL2n hL2 x0 T
  have ha : (fun ω => dotProduct a (sectionFourVAll F' f v x0 ω t)) =ᵐ[_]
      fun ω => dotProduct a (sectionFourV F' f v x0 T ω t) :=
    heq.mono fun ω hω => congrArg (dotProduct a) (hω t ht')
  have hb : (fun ω => dotProduct b (sectionFourVAll F' f v x0 ω u)) =ᵐ[_]
      fun ω => dotProduct b (sectionFourV F' f v x0 T ω u) :=
    heq.mono fun ω hω => congrArg (dotProduct b) (hω u hu')
  rw [covariance_eq_of_ae ha hb]
  exact sectionFourV_covariance heps hM hf0 hfB h319 hL1 hL2n hL2 Lg hLg x0 T ht hu a b

end Ripple.Kurtz.StrongApprox
