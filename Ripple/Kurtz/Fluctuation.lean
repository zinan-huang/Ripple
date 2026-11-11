import Ripple.Kurtz.FluctuationMoments
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Finite-dimensional fluctuation laws and the Gaussian covariance


This file supplies the definitions and preliminary proof scripts listed
in the accompanying answer. The full CLT is recorded only as an outstanding
statement at the end; it is not an exported theorem.
-/

namespace Ripple.Kurtz

open MeasureTheory ProbabilityTheory Filter Topology Set Finset Matrix
open Ripple.CTMC
open scoped BigOperators ENNReal RealInnerProductSpace InnerProductSpace

noncomputable section

variable {d m : ℕ}

/-- The population sequence used in Section 4: N_n = n + 1. -/
def fluctuationModel (Γ : RateSpec d) (n : ℕ) : DensityDepCTMC d :=
  DensityDepCTMC.mk (n + 1) (Nat.succ_pos n) Γ

/-- The observation horizon, including the empty observation family. -/
def fluctuationHorizon (t : Fin m → ℝ) : ℝ := by
  classical
  exact max 1 ((insert 0 (Finset.univ.image t)).max' (by simp))

theorem one_le_fluctuationHorizon (t : Fin m → ℝ) :
    1 ≤ fluctuationHorizon t := by
  classical
  exact le_max_left _ _

theorem fluctuationHorizon_pos (t : Fin m → ℝ) :
    0 < fluctuationHorizon t :=
  zero_lt_one.trans_le (one_le_fluctuationHorizon t)

theorem time_le_fluctuationHorizon (t : Fin m → ℝ) (j : Fin m) :
    t j ≤ fluctuationHorizon t := by
  classical
  have hj : t j ∈ insert 0 (Finset.univ.image t) :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  exact (Finset.le_max' _ _ hj).trans (le_max_right _ _)

/-- The Euclidean random vector in equation (4.15). -/
def fluctuationVector (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (t : Fin m → ℝ) (n : ℕ) (ω : (fluctuationModel Γ n).canonicalRecordΩ) :
    EuclideanSpace ℝ (Fin m × Fin d) :=
  WithLp.toLp 2 fun ji =>
    Real.sqrt ((n + 1 : ℕ) : ℝ) *
      (((fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap (t ji.1) ω) ji.2 -
        mf.sol (t ji.1) ji.2)

theorem measurable_fluctuationVector (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ) (n : ℕ) :
    Measurable (fluctuationVector Γ mf t n) := by
  apply (WithLp.measurable_toLp 2 ((Fin m × Fin d) → ℝ)).comp
  apply measurable_pi_lambda
  intro ji
  exact measurable_const.mul
    (((measurable_pi_apply ji.2).comp
      ((fluctuationModel Γ n).measurable_canonicalFrozenDensityProcess (t ji.1))).sub
      measurable_const)

/-- The mapped canonical probability law in equation (4.16). -/
def fluctuationLaw (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (t : Fin m → ℝ) (z : ∀ n : ℕ, Fin d → Fin (n + 1 + 1)) (n : ℕ) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin m × Fin d)) :=
  ⟨((fluctuationModel Γ n).canonicalRecordMeasure (z n)).map
      (fluctuationVector Γ mf t n),
    Measure.isProbabilityMeasure_map
      (μ := (fluctuationModel Γ n).canonicalRecordMeasure (z n))
      (measurable_fluctuationVector Γ mf t n).aemeasurable⟩

theorem fluctuationLaw_toMeasure (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (t : Fin m → ℝ) (z : ∀ n : ℕ, Fin d → Fin (n + 1 + 1)) (n : ℕ) :
    (fluctuationLaw Γ mf t z n :
      Measure (EuclideanSpace ℝ (Fin m × Fin d))) =
      ((fluctuationModel Γ n).canonicalRecordMeasure (z n)).map
        (fluctuationVector Γ mf t n) := rfl

/-- The characteristic function of the mapped canonical law. -/
theorem fluctuationLaw_charFun (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (t : Fin m → ℝ) (z : ∀ n : ℕ, Fin d → Fin (n + 1 + 1))
    (n : ℕ) (a : EuclideanSpace ℝ (Fin m × Fin d)) :
    charFun (fluctuationLaw Γ mf t z n :
      Measure (EuclideanSpace ℝ (Fin m × Fin d))) a =
      ∫ ω, Complex.exp
        ((⟪fluctuationVector Γ mf t n ω, a⟫_ℝ : ℂ) * Complex.I)
        ∂(fluctuationModel Γ n).canonicalRecordMeasure (z n) := by
  rw [fluctuationLaw_toMeasure, charFun_apply,
    integral_map (measurable_fluctuationVector Γ mf t n).aemeasurable (by fun_prop)]

/-! ## Initial densities and Lemma 4.0 -/

/-- A lattice simplex state becomes a point of the closed real simplex after scaling. -/
theorem fluctuation_scaledState_mem_stdSimplex
    (M : DensityDepCTMC d) (z : Fin d → Fin (M.N + 1))
    (hz : M.InSimplex z) :
    M.scaledState z ∈ stdSimplex ℝ (Fin d) := by
  constructor
  · intro i
    change 0 ≤ (z i : ℝ) / (M.N : ℝ)
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · change (∑ i, (z i : ℝ) / (M.N : ℝ)) = 1
    have hz' : (∑ i, (z i : ℕ)) = M.N := hz
    rw [← Finset.sum_div, ← Nat.cast_sum, hz']
    exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt M.hN))

/-- The fluctuation initial condition implies ordinary density convergence. -/
theorem fluctuation_tendsto_of_sqrt_smul_tendsto
    (z : ℕ → Fin d → ℝ) (x v₀ : Fin d → ℝ)
    (h : Tendsto
      (fun n => Real.sqrt ((n + 1 : ℕ) : ℝ) • (z n - x))
      atTop (𝓝 v₀)) :
    Tendsto z atTop (𝓝 x) := by
  have hN : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hsqrt : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hN
  have hinv : Tendsto
      (fun n : ℕ => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹)
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have hsmall : Tendsto
      (fun n => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ •
        (Real.sqrt ((n + 1 : ℕ) : ℝ) • (z n - x)))
      atTop (𝓝 (0 : Fin d → ℝ)) := by
    simpa only [zero_smul] using hinv.smul h
  have hcancel (n : ℕ) :
      (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ •
        (Real.sqrt ((n + 1 : ℕ) : ℝ) • (z n - x)) = z n - x := by
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_pos n
    rw [smul_smul, inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hpos)), one_smul]
  have herr : Tendsto (fun n => z n - x) atTop (𝓝 (0 : Fin d → ℝ)) :=
    Tendsto.congr' (Eventually.of_forall hcancel) hsmall
  simpa only [sub_add_cancel, zero_add] using herr.add_const x

/-- Evaluation at a horizon time is below the bounded time supremum. -/
theorem fluctuation_le_timeSup {T B s : ℝ} {f : ℝ → ℝ}
    (hB : 0 ≤ B) (hf : ∀ u ∈ Icc 0 T, f u ≤ B)
    (hs : s ∈ Icc 0 T) :
    f s ≤ fluctuationTimeSup T f := by
  have hi : BddAbove (Set.range (fun _ : 0 ≤ s ∧ s ≤ T => f s)) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨h, rfl⟩
    exact hf s h
  have ho : BddAbove
      (Set.range (fun u : ℝ => ⨆ _ : 0 ≤ u ∧ u ≤ T, f u)) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨u, rfl⟩
    exact Real.iSup_le (fun hu => hf u hu) hB
  exact (le_ciSup hi hs).trans (le_ciSup ho s)

/-- Lemma 4.0 from convergence of deterministic initial densities. -/
theorem fluctuation_meanField_mem_stdSimplex_of_initial_tendsto [NeZero d]
    (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (hConservative : ∀ (N : ℕ) (hN : 0 < N),
      (DensityDepCTMC.mk N hN Γ).ConservativeJumps)
    (hBoundary : ∀ (N : ℕ) (hN : 0 < N),
      (DensityDepCTMC.mk N hN Γ).BoundaryCompatibleOnSimplex)
    (hSolBound : ∀ t : ℝ, 0 ≤ t → ‖mf.sol t‖ ≤ 1)
    (z : ∀ n : ℕ, Fin d → Fin (n + 1 + 1))
    (hz : ∀ n, (fluctuationModel Γ n).InSimplex (z n))
    (hinit : Tendsto
      (fun n => (fluctuationModel Γ n).scaledState (z n))
      atTop (𝓝 mf.x₀))
    {s : ℝ} (hs : 0 ≤ s) :
    mf.sol s ∈ stdSimplex ℝ (Fin d) := by
  classical
  rw [← (isClosed_stdSimplex ℝ (Fin d)).closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  by_contra hnear
  let T : ℝ := max 1 s
  have hT : 0 < T := zero_lt_one.trans_le (le_max_left 1 s)
  have hsT : s ∈ Icc 0 T := ⟨hs, le_max_right 1 s⟩
  obtain ⟨γ, hγ, N₀, hclose⟩ :=
    kurtz_finite_horizon_of_close Γ mf hConservative hBoundary
      hSolBound hT (ε / 2) (half_pos hε) (1 / 2) (by norm_num)
  obtain ⟨n₀, hn₀⟩ := Metric.tendsto_atTop.mp hinit γ hγ
  let n : ℕ := max N₀ n₀
  let M : DensityDepCTMC d := fluctuationModel Γ n
  have hNlarge : N₀ ≤ n + 1 := by
    dsimp [n]
    omega
  have hcloseinit :
      ‖(fun i => (z n i : ℝ) / ((n + 1 : ℕ) : ℝ)) - mf.x₀‖ ≤ γ := by
    have h := hn₀ n (le_max_right N₀ n₀)
    change dist (fun i => (z n i : ℝ) / ((n + 1 : ℕ) : ℝ)) mf.x₀ < γ at h
    rw [dist_eq_norm] at h
    exact h.le
  let E : Set M.canonicalRecordΩ :=
    {ω | ε / 2 < fluctuationTimeSup T
      (fun u => ‖M.frozenDensityProcess M.canonicalPathMap u ω - mf.sol u‖)}
  have hupper : M.canonicalRecordMeasure (z n) E ≤
      ENNReal.ofReal (1 / 2 : ℝ) := by
    exact hclose (n + 1) hNlarge (Nat.succ_pos n) (z n) (hz n) hcloseinit
  have hsimplex :
      ∀ᵐ ω ∂M.canonicalRecordMeasure (z n), ∀ u : ℝ,
        M.InSimplex ((M.canonicalPathMap ω).frozenStateAt u) :=
    M.canonicalPathMap_frozenStateAt_inSimplex_ae_of_conservative
      (z n) (hConservative (n + 1) (Nat.succ_pos n)) (hz n)
  have hlower : (1 : ℝ≥0∞) ≤ M.canonicalRecordMeasure (z n) E := by
    calc
      1 = M.canonicalRecordMeasure (z n) Set.univ := by simp
      _ ≤ M.canonicalRecordMeasure (z n) E := by
        apply measure_mono_ae
        filter_upwards [hsimplex] with ω hω
        intro _
        have hΔ :
            M.frozenDensityProcess M.canonicalPathMap s ω ∈
              stdSimplex ℝ (Fin d) := by
          change M.scaledState ((M.canonicalPathMap ω).frozenStateAt s) ∈
            stdSimplex ℝ (Fin d)
          exact fluctuation_scaledState_mem_stdSimplex M _ (hω s)
        have hdist :
            ε ≤ dist (mf.sol s) (M.frozenDensityProcess M.canonicalPathMap s ω) := by
          apply not_lt.mp
          intro hlt
          exact hnear ⟨M.frozenDensityProcess M.canonicalPathMap s ω, hΔ, hlt⟩
        rw [dist_comm, dist_eq_norm] at hdist
        have hbd : ∀ u ∈ Icc 0 T,
            ‖M.frozenDensityProcess M.canonicalPathMap u ω - mf.sol u‖ ≤ 2 := by
          intro u hu
          exact (norm_sub_le _ _).trans (by
            linarith [M.frozenDensityProcess_norm_le M.canonicalPathMap u ω,
              hSolBound u hu.1])
        change ε / 2 < fluctuationTimeSup T
          (fun u => ‖M.frozenDensityProcess M.canonicalPathMap u ω - mf.sol u‖)
        exact (half_lt_self hε).trans_le
          (hdist.trans (fluctuation_le_timeSup (by norm_num) hbd hsT))
  have hcontra : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 / 2 : ℝ) :=
    hlower.trans hupper
  norm_num at hcontra

/-- Lemma 4.0 with the fluctuation initial condition (4.2). -/
theorem fluctuation_meanField_mem_stdSimplex [NeZero d]
    (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (hConservative : ∀ (N : ℕ) (hN : 0 < N),
      (DensityDepCTMC.mk N hN Γ).ConservativeJumps)
    (hBoundary : ∀ (N : ℕ) (hN : 0 < N),
      (DensityDepCTMC.mk N hN Γ).BoundaryCompatibleOnSimplex)
    (hSolBound : ∀ t : ℝ, 0 ≤ t → ‖mf.sol t‖ ≤ 1)
    (z : ∀ n : ℕ, Fin d → Fin (n + 1 + 1))
    (hz : ∀ n, (fluctuationModel Γ n).InSimplex (z n))
    (v₀ : Fin d → ℝ)
    (hfluct : Tendsto
      (fun n => Real.sqrt ((n + 1 : ℕ) : ℝ) •
        ((fluctuationModel Γ n).scaledState (z n) - mf.sol 0))
      atTop (𝓝 v₀))
    {s : ℝ} (hs : 0 ≤ s) :
    mf.sol s ∈ stdSimplex ℝ (Fin d) := by
  apply fluctuation_meanField_mem_stdSimplex_of_initial_tendsto Γ mf
    hConservative hBoundary hSolBound z hz
  · have h := fluctuation_tendsto_of_sqrt_smul_tendsto
      (fun n => (fluctuationModel Γ n).scaledState (z n)) (mf.sol 0) v₀ hfluct
    simpa only [mf.sol_init] using h
  · exact hs

/-! ## Adjoint mean and covariance -/

noncomputable def fluctuationLinearization {d : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) : ℝ → Matrix (Fin d) (Fin d) ℝ :=
  fun s i j => (fderiv ℝ Γ.drift (mf.extendLeft.sol s) (Pi.single j 1)) i

theorem continuous_fluctuationLinearization {d : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (hF : ContDiff ℝ 1 Γ.drift) :
    Continuous (fluctuationLinearization Γ mf) := by
  have hD : Continuous (fun s => fderiv ℝ Γ.drift (mf.extendLeft.sol s)) :=
    (hF.continuous_fderiv (by simp)).comp mf.extendLeft_continuous
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply i).comp (hD.clm_apply continuous_const)

theorem fluctuationLinearization_mulVec {d : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (s : ℝ) (v : Fin d → ℝ) :
    fluctuationLinearization Γ mf s *ᵥ v =
      fderiv ℝ Γ.drift (mf.extendLeft.sol s) v := by
  classical
  have hv : (∑ j : Fin d, v j • Pi.single j (1 : ℝ)) = v := by
    ext i
    simp [Pi.single_apply]
  ext i
  change (∑ j, (fderiv ℝ Γ.drift (mf.extendLeft.sol s) (Pi.single j 1)) i * v j) =
    (fderiv ℝ Γ.drift (mf.extendLeft.sol s) v) i
  conv_rhs => rw [← hv]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

noncomputable def fluctuationBasisAdjoint {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (p : Fin m × Fin d) : ℝ → Fin d → ℝ :=
  adjointSol (fluctuationLinearization Γ mf) (t p.1) (Pi.single p.2 1)

theorem continuous_fluctuationBasisAdjoint {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (hF : ContDiff ℝ 1 Γ.drift) (p : Fin m × Fin d) :
    Continuous (fluctuationBasisAdjoint Γ mf t p) :=
  continuous_linSol _
    (continuous_neg_matCLM_transpose (continuous_fluctuationLinearization Γ mf hF)) _ _

theorem fluctuationBasisAdjoint_terminal {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (hF : ContDiff ℝ 1 Γ.drift) (p : Fin m × Fin d) :
    fluctuationBasisAdjoint Γ mf t p (t p.1) = Pi.single p.2 1 :=
  adjointSol_self (continuous_fluctuationLinearization Γ mf hF) _ _

theorem hasDerivAt_fluctuationBasisAdjoint {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (hF : ContDiff ℝ 1 Γ.drift) (p : Fin m × Fin d) (s : ℝ) :
    HasDerivAt (fluctuationBasisAdjoint Γ mf t p)
      (-((fluctuationLinearization Γ mf s)ᵀ *ᵥ
        fluctuationBasisAdjoint Γ mf t p s)) s :=
  hasDerivAt_adjointSol (continuous_fluctuationLinearization Γ mf hF) _ _ _

noncomputable def fluctuationBasisCutoff {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (p : Fin m × Fin d) (s : ℝ) : Fin d → ℝ :=
  if s ≤ t p.1 then fluctuationBasisAdjoint Γ mf t p (max s 0) else 0

noncomputable def fluctuationCombinedTest {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (a : EuclideanSpace ℝ (Fin m × Fin d)) (s : ℝ) : Fin d → ℝ :=
  ∑ p : Fin m × Fin d, a p • fluctuationBasisCutoff Γ mf t p s

noncomputable def fluctuationMean {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (v0 : Fin d → ℝ) : EuclideanSpace ℝ (Fin m × Fin d) :=
  WithLp.toLp 2 (fun p => fluctuationBasisAdjoint Γ mf t p 0 ⬝ᵥ v0)

theorem fluctuationMean_eq_fundamentalSol {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ) (v0 : Fin d → ℝ)
    (hF : ContDiff ℝ 1 Γ.drift) (p : Fin m × Fin d) :
    fluctuationMean Γ mf t v0 p =
      fundamentalSol (fluctuationLinearization Γ mf) 0 v0 (t p.1) p.2 := by
  change adjointSol (fluctuationLinearization Γ mf) (t p.1)
    (Pi.single p.2 1) 0 ⬝ᵥ v0 = _
  exact (fundamentalSol_apply_eq_adjointSol_dotProduct
    (continuous_fluctuationLinearization Γ mf hF) 0 (t p.1) v0 p.2).symm

noncomputable def fluctuationCovarianceKernel {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (p q : Fin m × Fin d) (s : ℝ) : ℝ :=
  ∑ ℓ ∈ Γ.jumps, Γ.rate ℓ (mf.sol s) *
    fluctuationPairing (fluctuationBasisAdjoint Γ mf t p) ℓ s *
    fluctuationPairing (fluctuationBasisAdjoint Γ mf t q) ℓ s

noncomputable def fluctuationCovariance {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ) :
    Matrix (Fin m × Fin d) (Fin m × Fin d) ℝ :=
  fun p q => ∫ s in Icc 0 (min (t p.1) (t q.1)),
    fluctuationCovarianceKernel Γ mf t p q s

noncomputable def fluctuationCovarianceCutoffKernel {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (s : ℝ) : Matrix (Fin m × Fin d) (Fin m × Fin d) ℝ :=
  fun p q => ∑ ℓ ∈ Γ.jumps, Γ.rate ℓ (mf.sol s) *
    fluctuationPairing (fluctuationBasisCutoff Γ mf t p) ℓ s *
    fluctuationPairing (fluctuationBasisCutoff Γ mf t q) ℓ s

theorem fluctuationCovarianceKernel_symm {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (p q : Fin m × Fin d) (s : ℝ) :
    fluctuationCovarianceKernel Γ mf t p q s =
      fluctuationCovarianceKernel Γ mf t q p s := by
  unfold fluctuationCovarianceKernel
  apply Finset.sum_congr rfl
  intro ℓ _
  ring

theorem fluctuationCovariance_isHermitian {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ) :
    (fluctuationCovariance Γ mf t).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro p q
  simp only [star_trivial]
  change (∫ s in Icc 0 (min (t q.1) (t p.1)),
    fluctuationCovarianceKernel Γ mf t q p s) =
      ∫ s in Icc 0 (min (t p.1) (t q.1)),
        fluctuationCovarianceKernel Γ mf t p q s
  rw [min_comm (t q.1) (t p.1)]
  exact integral_congr_ae (Eventually.of_forall fun s =>
    fluctuationCovarianceKernel_symm Γ mf t q p s)

theorem fluctuation_rate_continuous {d : ℕ} (Γ : RateSpec d)
    (ℓ : Fin d → ℤ) (hℓ : ℓ ∈ Γ.jumps) : Continuous (Γ.rate ℓ) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  let R : ℝ := ‖x‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨L, hL, hLip⟩ := Γ.rate_lipschitz ℓ hℓ R hR
  refine ⟨min 1 (ε / L), lt_min one_pos (div_pos hε hL), ?_⟩
  intro y hy
  have hy1 : dist y x < 1 := hy.trans_le (min_le_left _ _)
  have hyε : dist y x < ε / L := hy.trans_le (min_le_right _ _)
  have hxR : ‖x‖ ≤ R := by dsimp [R]; linarith
  have hyR : ‖y‖ ≤ R := by
    have htri : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
      calc
        ‖y‖ = ‖x + (y - x)‖ := by congr 1; abel
        _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
    rw [dist_eq_norm] at hy1
    dsimp [R]
    linarith
  rw [dist_eq_norm]
  calc
    ‖Γ.rate ℓ y - Γ.rate ℓ x‖ ≤ L * ‖y - x‖ := hLip y x hyR hxR
    _ < L * (ε / L) :=
      mul_lt_mul_of_pos_left (by simpa only [dist_eq_norm] using hyε) hL
    _ = ε := by field_simp

private theorem ff_pairing_continuous {d : ℕ} {ψ : ℝ → Fin d → ℝ}
    (hψ : Continuous ψ) (ℓ : Fin d → ℤ) :
    Continuous (fluctuationPairing ψ ℓ) := by
  unfold fluctuationPairing dotProduct
  exact continuous_finset_sum _ fun i _ =>
    ((continuous_apply i).comp hψ).mul continuous_const

theorem continuousOn_fluctuationCovarianceKernel {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (hF : ContDiff ℝ 1 Γ.drift) (p q : Fin m × Fin d) (T : ℝ) :
    ContinuousOn (fluctuationCovarianceKernel Γ mf t p q) (Icc 0 T) := by
  let k : ℝ → ℝ := fun s => ∑ ℓ ∈ Γ.jumps,
    Γ.rate ℓ (mf.extendLeft.sol s) *
      fluctuationPairing (fluctuationBasisAdjoint Γ mf t p) ℓ s *
      fluctuationPairing (fluctuationBasisAdjoint Γ mf t q) ℓ s
  have hk : Continuous k :=
    continuous_finset_sum _ fun ℓ hℓ =>
      (((fluctuation_rate_continuous Γ ℓ hℓ).comp mf.extendLeft_continuous).mul
        (ff_pairing_continuous (continuous_fluctuationBasisAdjoint Γ mf t hF p) ℓ)).mul
          (ff_pairing_continuous (continuous_fluctuationBasisAdjoint Γ mf t hF q) ℓ)
  apply hk.continuousOn.congr
  intro s hs
  simp only [k, fluctuationCovarianceKernel, mf.extendLeft_sol_of_nonneg hs.1]

theorem fluctuationCovarianceCutoffKernel_eq_indicator {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (p q : Fin m × Fin d) {s : ℝ} (hs : 0 ≤ s) :
    fluctuationCovarianceCutoffKernel Γ mf t s p q =
      (Iic (min (t p.1) (t q.1))).indicator
        (fluctuationCovarianceKernel Γ mf t p q) s := by
  classical
  by_cases hp : s ≤ t p.1 <;> by_cases hq : s ≤ t q.1 <;>
    simp [fluctuationCovarianceCutoffKernel, fluctuationCovarianceKernel,
      fluctuationPairing, fluctuationBasisCutoff, max_eq_left hs,
      Set.indicator, Set.mem_Iic, le_min_iff, hp, hq]

theorem integrableOn_fluctuationCovarianceCutoffKernel {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (hF : ContDiff ℝ 1 Γ.drift) (p q : Fin m × Fin d) (T : ℝ) :
    IntegrableOn (fun s => fluctuationCovarianceCutoffKernel Γ mf t s p q)
      (Icc 0 T) volume := by
  have h : IntegrableOn (fluctuationCovarianceKernel Γ mf t p q)
      (Icc 0 T) volume :=
    (continuousOn_fluctuationCovarianceKernel Γ mf t hF p q T).integrableOn_Icc
      (μ := volume)
  have hi : IntegrableOn
      ((Iic (min (t p.1) (t q.1))).indicator
        (fluctuationCovarianceKernel Γ mf t p q)) (Icc 0 T) volume :=
    h.indicator measurableSet_Iic
  apply hi.congr
  filter_upwards [self_mem_ae_restrict measurableSet_Icc] with s hs
  exact (fluctuationCovarianceCutoffKernel_eq_indicator Γ mf t p q hs.1).symm

theorem fluctuationCovariance_eq_integral_cutoff {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (T : ℝ) (hT : ∀ j, t j ≤ T) (p q : Fin m × Fin d) :
    fluctuationCovariance Γ mf t p q =
      ∫ s in Icc 0 T, fluctuationCovarianceCutoffKernel Γ mf t s p q := by
  have hset : Icc 0 T ∩ Iic (min (t p.1) (t q.1)) =
      Icc 0 (min (t p.1) (t q.1)) := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
    constructor
    · rintro ⟨⟨hs0, _⟩, hsmin⟩
      exact ⟨hs0, hsmin⟩
    · rintro ⟨hs0, hsmin⟩
      exact ⟨⟨hs0, hsmin.trans ((min_le_left _ _).trans (hT p.1))⟩, hsmin⟩
  symm
  calc
    (∫ s in Icc 0 T, fluctuationCovarianceCutoffKernel Γ mf t s p q) =
        ∫ s in Icc 0 T, (Iic (min (t p.1) (t q.1))).indicator
          (fluctuationCovarianceKernel Γ mf t p q) s := by
      apply integral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Icc] with s hs
      exact fluctuationCovarianceCutoffKernel_eq_indicator Γ mf t p q hs.1
    _ = _ := by
      rw [setIntegral_indicator measurableSet_Iic, hset]
      rfl

theorem fluctuation_integral_quadratic {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (K : Ω → Matrix ι ι ℝ)
    (hK : ∀ i j, Integrable (fun s => K s i j) μ) (a : ι → ℝ) :
    a ⬝ᵥ ((fun i j => ∫ s, K s i j ∂μ) *ᵥ a) =
      ∫ s, a ⬝ᵥ (K s *ᵥ a) ∂μ := by
  classical
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  symm
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ =>
      ((hK i j).mul_const (a j)).const_mul (a i)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ =>
    ((hK i j).mul_const (a j)).const_mul (a i))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, integral_mul_const]

theorem fluctuation_posSemidef_integral {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (K : Ω → Matrix ι ι ℝ)
    (hK : ∀ i j, Integrable (fun s => K s i j) μ)
    (hpos : ∀ᵐ s ∂μ, (K s).PosSemidef) :
    (Matrix.of (fun i j => ∫ s, K s i j ∂μ)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial]
    change (∫ s, K s j i ∂μ) = ∫ s, K s i j ∂μ
    exact integral_congr_ae (hpos.mono fun s hs => by
      simpa only [star_trivial] using hs.isHermitian.apply i j)
  · intro a
    simp only [star_trivial]
    change 0 ≤ a ⬝ᵥ ((fun i j => ∫ s, K s i j ∂μ) *ᵥ a)
    rw [fluctuation_integral_quadratic μ K hK a]
    exact integral_nonneg_of_ae (hpos.mono fun s hs => by
      simpa only [star_trivial] using hs.dotProduct_mulVec_nonneg a)

theorem fluctuationCovarianceCutoffKernel_posSemidef {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ) (s : ℝ)
    (hs : ∀ i, 0 ≤ mf.sol s i) :
    (fluctuationCovarianceCutoffKernel Γ mf t s).PosSemidef := by
  classical
  let b : (Fin d → ℤ) → (Fin m × Fin d) → ℝ :=
    fun ℓ p => fluctuationPairing (fluctuationBasisCutoff Γ mf t p) ℓ s
  have houter (ℓ : Fin d → ℤ) :
      (Matrix.vecMulVec (b ℓ) (b ℓ)).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (b ℓ)
  have heq : fluctuationCovarianceCutoffKernel Γ mf t s =
      ∑ ℓ ∈ Γ.jumps, Γ.rate ℓ (mf.sol s) • Matrix.vecMulVec (b ℓ) (b ℓ) := by
    ext p q
    simp only [fluctuationCovarianceCutoffKernel, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, b]
    apply Finset.sum_congr rfl
    intro ℓ _
    ring
  rw [heq]
  exact Matrix.posSemidef_sum _ fun ℓ hℓ =>
    (houter ℓ).smul (Γ.rate_nonneg ℓ hℓ (mf.sol s) hs)

theorem fluctuationCovariance_posSemidef {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (hF : ContDiff ℝ 1 Γ.drift)
    (hNonneg : ∀ s ≥ 0, ∀ i, 0 ≤ mf.sol s i) :
    (fluctuationCovariance Γ mf t).PosSemidef := by
  classical
  let T : ℝ := ∑ j, |t j|
  have hT : ∀ j, t j ≤ T := fun j =>
    (le_abs_self (t j)).trans (Finset.single_le_sum
      (fun k _ => abs_nonneg (t k)) (Finset.mem_univ j))
  have heq : fluctuationCovariance Γ mf t =
      fun p q => ∫ s in Icc 0 T, fluctuationCovarianceCutoffKernel Γ mf t s p q := by
    ext p q
    exact fluctuationCovariance_eq_integral_cutoff Γ mf t T hT p q
  rw [heq]
  refine fluctuation_posSemidef_integral (volume.restrict (Icc 0 T))
    (fluctuationCovarianceCutoffKernel Γ mf t) ?_ ?_
  · intro p q
    exact integrableOn_fluctuationCovarianceCutoffKernel Γ mf t hF p q T
  · filter_upwards [self_mem_ae_restrict measurableSet_Icc] with s hs
    exact fluctuationCovarianceCutoffKernel_posSemidef Γ mf t s (hNonneg s hs.1)


private theorem ff_gram_quadratic {ι κ : Type*} [Fintype ι]
    (J : Finset κ) (w : κ → ℝ) (b : κ → ι → ℝ) (a : ι → ℝ) :
    a ⬝ᵥ ((fun i j => ∑ ℓ ∈ J, w ℓ * b ℓ i * b ℓ j) *ᵥ a) =
      ∑ ℓ ∈ J, w ℓ * (∑ i, a i * b ℓ i) ^ 2 := by
  classical
  calc
    a ⬝ᵥ ((fun i j => ∑ ℓ ∈ J, w ℓ * b ℓ i * b ℓ j) *ᵥ a) =
        ∑ i, ∑ j, ∑ ℓ ∈ J,
          w ℓ * (a i * b ℓ i) * (a j * b ℓ j) := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro ℓ _
      ring
    _ = ∑ i, ∑ ℓ ∈ J, ∑ j,
          w ℓ * (a i * b ℓ i) * (a j * b ℓ j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ ℓ ∈ J, ∑ i, ∑ j,
          w ℓ * (a i * b ℓ i) * (a j * b ℓ j) := Finset.sum_comm
    _ = ∑ ℓ ∈ J, w ℓ * (∑ i, a i * b ℓ i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro ℓ _
      simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem fluctuationCovarianceCutoffKernel_quadratic {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (a : EuclideanSpace ℝ (Fin m × Fin d)) (s : ℝ) :
    (fun p => a p) ⬝ᵥ
      (fluctuationCovarianceCutoffKernel Γ mf t s *ᵥ (fun p => a p)) =
        ∑ ℓ ∈ Γ.jumps, Γ.rate ℓ (mf.sol s) *
          (fluctuationPairing (fluctuationCombinedTest Γ mf t a) ℓ s) ^ 2 := by
  simpa only [fluctuationCovarianceCutoffKernel, fluctuationPairing,
    fluctuationCombinedTest, sum_dotProduct, smul_dotProduct, smul_eq_mul] using
    (ff_gram_quadratic Γ.jumps (fun ℓ => Γ.rate ℓ (mf.sol s))
      (fun ℓ p => fluctuationPairing (fluctuationBasisCutoff Γ mf t p) ℓ s)
      (fun p => a p))

theorem fluctuationCovariance_quadratic_eq {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (hF : ContDiff ℝ 1 Γ.drift) (T : ℝ) (hT : ∀ j, t j ≤ T)
    (a : EuclideanSpace ℝ (Fin m × Fin d)) :
    (fun p => a p) ⬝ᵥ (fluctuationCovariance Γ mf t *ᵥ (fun p => a p)) =
      fluctuationQuadraticCompensator Γ
        (fluctuationPairing (fluctuationCombinedTest Γ mf t a)) mf.sol T := by
  have heq : fluctuationCovariance Γ mf t =
      fun p q => ∫ s in Icc 0 T, fluctuationCovarianceCutoffKernel Γ mf t s p q := by
    ext p q
    exact fluctuationCovariance_eq_integral_cutoff Γ mf t T hT p q
  rw [heq, fluctuation_integral_quadratic (volume.restrict (Icc 0 T))
    (fluctuationCovarianceCutoffKernel Γ mf t)
    (fun p q => integrableOn_fluctuationCovarianceCutoffKernel Γ mf t hF p q T)
    (fun p => a p)]
  unfold fluctuationQuadraticCompensator
  exact integral_congr_ae (Eventually.of_forall fun s =>
    fluctuationCovarianceCutoffKernel_quadratic Γ mf t a s)

/-! ## Equivalent forward-flow formulas -/

/-- The forward-flow matrix, represented by its adjoint rows. -/
noncomputable def fluctuationFundamentalMatrix (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (r s : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i k => adjointSol (fluctuationLinearization Γ mf) r
    (Pi.single i 1) s k

/-- This matrix acts as the forward fundamental solution from Lemma 4.1. -/
theorem fluctuationFundamentalMatrix_mulVec (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (hF : ContDiff ℝ 1 Γ.drift)
    (r s : ℝ) (v : Fin d → ℝ) :
    fluctuationFundamentalMatrix Γ mf r s *ᵥ v =
      fundamentalSol (fluctuationLinearization Γ mf) s v r := by
  ext i
  change adjointSol (fluctuationLinearization Γ mf) r
    (Pi.single i 1) s ⬝ᵥ v = _
  exact (fundamentalSol_apply_eq_adjointSol_dotProduct
    (continuous_fluctuationLinearization Γ mf hF) s r v i).symm

/-- The instantaneous noise matrix G(x) from Section 4.3. -/
noncomputable def fluctuationNoiseMatrix (Γ : RateSpec d) (x : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i k => ∑ ℓ ∈ Γ.jumps, Γ.rate ℓ x * (ℓ i : ℝ) * (ℓ k : ℝ)

private theorem fluctuation_mul_gram
    {ι κ ρ τ : Type*} [Fintype κ]
    (J : Finset τ) (w : τ → ℝ) (b : τ → κ → ℝ) (G : Matrix κ κ ℝ)
    (hG : ∀ k l, G k l = ∑ ℓ ∈ J, w ℓ * b ℓ k * b ℓ l)
    (A : Matrix ι κ ℝ) (B : Matrix ρ κ ℝ) (i : ι) (j : ρ) :
    (A * G * Bᵀ) i j =
      ∑ ℓ ∈ J, w ℓ *
        (∑ l, A i l * b ℓ l) * (∑ k, B j k * b ℓ k) := by
  classical
  calc
    (A * G * Bᵀ) i j =
        ∑ k, ∑ l, ∑ ℓ ∈ J,
          w ℓ * (A i l * b ℓ l) * (B j k * b ℓ k) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, hG,
        Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro ℓ _
      ring
    _ = ∑ k, ∑ ℓ ∈ J, ∑ l,
          w ℓ * (A i l * b ℓ l) * (B j k * b ℓ k) := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm
    _ = ∑ ℓ ∈ J, ∑ k, ∑ l,
          w ℓ * (A i l * b ℓ l) * (B j k * b ℓ k) := Finset.sum_comm
    _ = ∑ ℓ ∈ J, w ℓ *
          (∑ l, A i l * b ℓ l) * (∑ k, B j k * b ℓ k) := by
      apply Finset.sum_congr rfl
      intro ℓ _
      simp only [Finset.mul_sum, Finset.sum_mul]
      try (refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_; ring)

/-- The kernel in (4.18) is the corresponding entry of Φ G Φᵀ. -/
theorem fluctuationCovarianceKernel_eq_flow (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (p q : Fin m × Fin d) (s : ℝ) :
    fluctuationCovarianceKernel Γ mf t p q s =
      (fluctuationFundamentalMatrix Γ mf (t p.1) s *
        fluctuationNoiseMatrix Γ (mf.sol s) *
        (fluctuationFundamentalMatrix Γ mf (t q.1) s)ᵀ) p.2 q.2 := by
  symm
  simpa only [fluctuationNoiseMatrix, fluctuationFundamentalMatrix,
    fluctuationCovarianceKernel, fluctuationPairing,
    fluctuationBasisAdjoint, dotProduct] using
    (fluctuation_mul_gram Γ.jumps (fun ℓ => Γ.rate ℓ (mf.sol s))
      (fun ℓ i => (ℓ i : ℝ)) (fluctuationNoiseMatrix Γ (mf.sol s)) (fun _ _ => rfl)
      (fluctuationFundamentalMatrix Γ mf (t p.1) s)
      (fluctuationFundamentalMatrix Γ mf (t q.1) s) p.2 q.2)

/-- The entrywise linearized-flow covariance formula from Section 4.3. -/
theorem fluctuationCovariance_eq_flow (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (p q : Fin m × Fin d) :
    fluctuationCovariance Γ mf t p q =
      ∫ s in Icc 0 (min (t p.1) (t q.1)),
        (fluctuationFundamentalMatrix Γ mf (t p.1) s *
          fluctuationNoiseMatrix Γ (mf.sol s) *
          (fluctuationFundamentalMatrix Γ mf (t q.1) s)ᵀ) p.2 q.2 := by
  unfold fluctuationCovariance
  exact integral_congr_ae (Eventually.of_forall fun s =>
    fluctuationCovarianceKernel_eq_flow Γ mf t p q s)

/-! ## Bounded cutoff tests -/

theorem measurable_fluctuationBasisCutoff {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (hF : ContDiff ℝ 1 Γ.drift) (p : Fin m × Fin d) :
    Measurable (fluctuationBasisCutoff Γ mf t p) := by
  have hbranch : Measurable (fun s : ℝ =>
      fluctuationBasisAdjoint Γ mf t p (max s 0)) :=
    ((continuous_fluctuationBasisAdjoint Γ mf t hF p).comp
      (continuous_id.max continuous_const)).measurable
  unfold fluctuationBasisCutoff
  exact Measurable.ite (measurableSet_le measurable_id measurable_const)
    hbranch measurable_const

theorem exists_fluctuationBasisCutoff_bound {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (hF : ContDiff ℝ 1 Γ.drift) (ht : ∀ j, 0 ≤ t j)
    (p : Fin m × Fin d) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s, ‖fluctuationBasisCutoff Γ mf t p s‖ ≤ B := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := t p.1)).exists_bound_of_continuousOn
      (continuous_fluctuationBasisAdjoint Γ mf t hF p).continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro s
  by_cases hst : s ≤ t p.1
  · simp only [fluctuationBasisCutoff, if_pos hst]
    exact (hC (max s 0) ⟨le_max_right _ _, max_le hst (ht p.1)⟩).trans
      (le_max_left _ _)
  · simp only [fluctuationBasisCutoff, if_neg hst, norm_zero]
    exact le_max_right _ _

theorem measurable_fluctuationCombinedTest {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (hF : ContDiff ℝ 1 Γ.drift) (a : EuclideanSpace ℝ (Fin m × Fin d)) :
    Measurable (fluctuationCombinedTest Γ mf t a) := by
  classical
  unfold fluctuationCombinedTest
  exact Finset.measurable_sum Finset.univ fun p _ =>
    measurable_const.smul (measurable_fluctuationBasisCutoff Γ mf t hF p)

theorem norm_fluctuationCombinedTest_le {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (a : EuclideanSpace ℝ (Fin m × Fin d)) (B : Fin m × Fin d → ℝ)
    (hB : ∀ p s, ‖fluctuationBasisCutoff Γ mf t p s‖ ≤ B p) (s : ℝ) :
    ‖fluctuationCombinedTest Γ mf t a s‖ ≤ ∑ p, |a p| * B p := by
  classical
  change ‖∑ p : Fin m × Fin d, a p • fluctuationBasisCutoff Γ mf t p s‖ ≤ _
  calc
    ‖∑ p : Fin m × Fin d, a p • fluctuationBasisCutoff Γ mf t p s‖ ≤
        ∑ p : Fin m × Fin d, ‖a p • fluctuationBasisCutoff Γ mf t p s‖ :=
      norm_sum_le Finset.univ _
    _ ≤ ∑ p, |a p| * B p := by
      apply Finset.sum_le_sum
      intro p _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hB p s) (abs_nonneg (a p))

theorem exists_fluctuationCombinedTest_bound {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (hF : ContDiff ℝ 1 Γ.drift) (ht : ∀ j, 0 ≤ t j)
    (a : EuclideanSpace ℝ (Fin m × Fin d)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s, ‖fluctuationCombinedTest Γ mf t a s‖ ≤ B := by
  classical
  have hb : ∀ p : Fin m × Fin d, ∃ B : ℝ,
      0 ≤ B ∧ ∀ s, ‖fluctuationBasisCutoff Γ mf t p s‖ ≤ B :=
    fun p => exists_fluctuationBasisCutoff_bound Γ mf t hF ht p
  choose B hB0 hB using hb
  refine ⟨∑ p, |a p| * B p, ?_, ?_⟩
  · exact Finset.sum_nonneg fun p _ => mul_nonneg (abs_nonneg (a p)) (hB0 p)
  · exact norm_fluctuationCombinedTest_le Γ mf t a B hB

theorem continuousAt_fluctuationBasisCutoff {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (hF : ContDiff ℝ 1 Γ.drift) (p : Fin m × Fin d)
    {s : ℝ} (hs : s ≠ t p.1) :
    ContinuousAt (fluctuationBasisCutoff Γ mf t p) s := by
  rcases lt_or_gt_of_ne hs with hst | hts
  · have hbranch : ContinuousAt (fun u : ℝ =>
        fluctuationBasisAdjoint Γ mf t p (max u 0)) s :=
      ((continuous_fluctuationBasisAdjoint Γ mf t hF p).comp
        (continuous_id.max continuous_const)).continuousAt
    apply hbranch.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hst] with u hu
    have hut : u < t p.1 := Set.mem_Iio.mp hu
    simp only [fluctuationBasisCutoff, if_pos hut.le]
  · apply (continuousAt_const :
        ContinuousAt (fun _ : ℝ => (0 : Fin d → ℝ)) s).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hts] with u hu
    have htu : t p.1 < u := Set.mem_Ioi.mp hu
    simp only [fluctuationBasisCutoff, if_neg (not_le.mpr htu)]

theorem continuousAt_fluctuationCombinedTest {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (hF : ContDiff ℝ 1 Γ.drift) (a : EuclideanSpace ℝ (Fin m × Fin d))
    {s : ℝ} (hs : s ∉ Set.range t) :
    ContinuousAt (fluctuationCombinedTest Γ mf t a) s := by
  classical
  change Tendsto (fun u => ∑ p : Fin m × Fin d,
      a p • fluctuationBasisCutoff Γ mf t p u) (𝓝 s)
    (𝓝 (∑ p : Fin m × Fin d, a p • fluctuationBasisCutoff Γ mf t p s))
  apply tendsto_finsetSum Finset.univ
  intro p _
  have hp : s ≠ t p.1 := fun h => hs ⟨p.1, h.symm⟩
  exact (continuousAt_const : ContinuousAt (fun _ : ℝ => a p) s).smul
    (continuousAt_fluctuationBasisCutoff Γ mf t hF p hp)

theorem continuousOn_fluctuationCombinedTest {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (hF : ContDiff ℝ 1 Γ.drift) (a : EuclideanSpace ℝ (Fin m × Fin d)) :
    ContinuousOn (fluctuationCombinedTest Γ mf t a) (Set.range t)ᶜ := by
  intro s hs
  exact (continuousAt_fluctuationCombinedTest Γ mf t hF a hs).continuousWithinAt

/-! ## The bounded purely imaginary tilt -/

noncomputable def fluctuationTilt {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (a : EuclideanSpace ℝ (Fin m × Fin d)) (n : ℕ) (s : ℝ)
    (x y : Fin d → Fin (n + 1 + 1)) : ℂ :=
  Complex.I *
    (((fluctuationCombinedTest Γ mf t a s ⬝ᵥ
      (fun i => (y i : ℝ) - (x i : ℝ))) /
      Real.sqrt ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ)

theorem fluctuationTilt_re {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (a : EuclideanSpace ℝ (Fin m × Fin d)) (n : ℕ) (s : ℝ)
    (x y : Fin d → Fin (n + 1 + 1)) :
    (fluctuationTilt Γ mf t a n s x y).re = 0 := by
  simp [fluctuationTilt]

theorem norm_fluctuationTilt {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (a : EuclideanSpace ℝ (Fin m × Fin d)) (n : ℕ) (s : ℝ)
    (x y : Fin d → Fin (n + 1 + 1)) :
    ‖fluctuationTilt Γ mf t a n s x y‖ =
      |fluctuationCombinedTest Γ mf t a s ⬝ᵥ
        (fun i => (y i : ℝ) - (x i : ℝ))| /
          |Real.sqrt ((n + 1 : ℕ) : ℝ)| := by
  simp only [fluctuationTilt, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_div]

theorem fluctuationTilt_isExpTilt {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (hF : ContDiff ℝ 1 Γ.drift) (ht : ∀ j, 0 ≤ t j)
    (a : EuclideanSpace ℝ (Fin m × Fin d)) (n : ℕ) :
    Ripple.CTMC.IsExpTilt (fluctuationTilt Γ mf t a n) (Set.range t) := by
  classical
  refine {
    diag := ?_
    meas := ?_
    bdd := ?_
    countable := (Set.finite_range t).countable
    cont := ?_ }
  · intro s x
    simp only [fluctuationTilt, dotProduct, sub_self, mul_zero,
      Finset.sum_const_zero, zero_div, Complex.ofReal_zero]
  · intro x y
    have hψ : Measurable (fluctuationCombinedTest Γ mf t a) :=
      measurable_fluctuationCombinedTest Γ mf t hF a
    have hdot : Measurable (fun s =>
        fluctuationCombinedTest Γ mf t a s ⬝ᵥ
          (fun i => (y i : ℝ) - (x i : ℝ))) := by
      unfold dotProduct
      exact Finset.measurable_sum Finset.univ fun i _ =>
        ((measurable_pi_apply i).comp hψ).mul measurable_const
    unfold fluctuationTilt
    exact measurable_const.mul
      (Complex.measurable_ofReal.comp
        (hdot.div_const (Real.sqrt ((n + 1 : ℕ) : ℝ))))
  · obtain ⟨C, hC0, hC⟩ :=
      exists_fluctuationCombinedTest_bound Γ mf t hF ht a
    have hstate (x y : Fin d → Fin (n + 1 + 1)) :
        ‖(fun i => (y i : ℝ) - (x i : ℝ))‖ ≤ ((n + 1 : ℕ) : ℝ) := by
      apply (pi_norm_le_iff_of_nonneg
        (Nat.cast_nonneg (n + 1) : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))).mpr
      intro i
      rw [Real.norm_eq_abs]
      have hx0 : (0 : ℝ) ≤ (x i : ℝ) := Nat.cast_nonneg _
      have hy0 : (0 : ℝ) ≤ (y i : ℝ) := Nat.cast_nonneg _
      have hxNnat : (x i).val ≤ n + 1 :=
        Nat.le_of_lt_succ (x i).isLt
      have hyNnat : (y i).val ≤ n + 1 :=
        Nat.le_of_lt_succ (y i).isLt
      have hxN : (x i : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast hxNnat
      have hyN : (y i : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast hyNnat
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    refine ⟨((d : ℝ) * C * ((n + 1 : ℕ) : ℝ)) /
      |Real.sqrt ((n + 1 : ℕ) : ℝ)|, ?_⟩
    intro s x y
    rw [norm_fluctuationTilt]
    have hdot :
        |fluctuationCombinedTest Γ mf t a s ⬝ᵥ
          (fun i => (y i : ℝ) - (x i : ℝ))| ≤
        (d : ℝ) * ‖fluctuationCombinedTest Γ mf t a s‖ *
          ‖(fun i => (y i : ℝ) - (x i : ℝ))‖ :=
      fluctuation_abs_dot_le _ _
    have hcoeff :
        (d : ℝ) * ‖fluctuationCombinedTest Γ mf t a s‖ ≤
          (d : ℝ) * C :=
      mul_le_mul_of_nonneg_left (hC s) (Nat.cast_nonneg d)
    have hproduct :
        (d : ℝ) * ‖fluctuationCombinedTest Γ mf t a s‖ *
            ‖(fun i => (y i : ℝ) - (x i : ℝ))‖ ≤
          (d : ℝ) * C * ((n + 1 : ℕ) : ℝ) :=
      mul_le_mul hcoeff (hstate x y) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg d) hC0)
    exact div_le_div_of_nonneg_right (hdot.trans hproduct) (abs_nonneg _)
  · intro x y s hs
    have hψ : ContinuousAt (fluctuationCombinedTest Γ mf t a) s :=
      continuousAt_fluctuationCombinedTest Γ mf t hF a hs
    have hdot : ContinuousAt (fun u =>
        fluctuationCombinedTest Γ mf t a u ⬝ᵥ
          (fun i => (y i : ℝ) - (x i : ℝ))) s := by
      unfold dotProduct
      refine Ripple.CTMC.continuousAt_finset_sum' Finset.univ fun i _ => ?_
      exact ((continuous_apply i).continuousAt.comp hψ).mul continuousAt_const
    unfold fluctuationTilt
    exact continuousAt_const.mul
      (Complex.continuous_ofReal.continuousAt.comp
        (hdot.div_const (Real.sqrt ((n + 1 : ℕ) : ℝ))))

/-! ## The initial deterministic mean term -/

/-- The deterministic mean depends continuously on the initial fluctuation. -/
theorem continuous_fluctuationMean {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ) :
    Continuous (fluctuationMean Γ mf t) := by
  unfold fluctuationMean
  apply (PiLp.continuous_toLp 2 (fun _ : Fin m × Fin d => ℝ)).comp
  apply continuous_pi
  intro p
  unfold dotProduct
  exact continuous_finsetSum Finset.univ fun i _ =>
    continuous_const.mul (continuous_apply i)

/-- At time zero the combined adjoint gives the scalar pairing with the mean. -/
theorem fluctuationCombinedTest_zero_dotProduct {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (ht : ∀ j, 0 ≤ t j) (a : EuclideanSpace ℝ (Fin m × Fin d))
    (v : Fin d → ℝ) :
    fluctuationCombinedTest Γ mf t a 0 ⬝ᵥ v =
      inner ℝ a (fluctuationMean Γ mf t v) := by
  classical
  rw [fluctuationCombinedTest, sum_dotProduct]
  simp only [smul_dotProduct, smul_eq_mul]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [fluctuationMean, WithLp.ofLp_toLp, star_trivial, dotProduct]
  apply Finset.sum_congr rfl
  intro p _
  simp [fluctuationBasisCutoff, ht p.1, mul_comm]

/-- The deterministic initial term in the scalar fluctuation decomposition. -/
noncomputable def fluctuationInitialTerm {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (z : ∀ n : ℕ, Fin d → Fin (n + 1 + 1))
    (a : EuclideanSpace ℝ (Fin m × Fin d)) (n : ℕ) : ℝ :=
  inner ℝ a (fluctuationMean Γ mf t
    (Real.sqrt ((n + 1 : ℕ) : ℝ) •
      ((fluctuationModel Γ n).scaledState (z n) - mf.sol 0)))

theorem fluctuationInitialTerm_eq {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (ht : ∀ j, 0 ≤ t j)
    (z : ∀ n : ℕ, Fin d → Fin (n + 1 + 1))
    (a : EuclideanSpace ℝ (Fin m × Fin d)) (n : ℕ) :
    fluctuationInitialTerm Γ mf t z a n =
      Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (fluctuationCombinedTest Γ mf t a 0 ⬝ᵥ
          ((fluctuationModel Γ n).scaledState (z n) - mf.sol 0)) := by
  unfold fluctuationInitialTerm
  rw [← fluctuationCombinedTest_zero_dotProduct Γ mf t ht a]
  simp only [dotProduct_smul, smul_eq_mul]

theorem tendsto_fluctuationInitialTerm {d m : ℕ} (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (z : ∀ n : ℕ, Fin d → Fin (n + 1 + 1))
    (a : EuclideanSpace ℝ (Fin m × Fin d)) (v0 : Fin d → ℝ)
    (hinit : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) •
        ((fluctuationModel Γ n).scaledState (z n) - mf.sol 0))
      atTop (𝓝 v0)) :
    Tendsto (fluctuationInitialTerm Γ mf t z a) atTop
      (𝓝 (inner ℝ a (fluctuationMean Γ mf t v0))) := by
  have hmean : Continuous (fun v : Fin d → ℝ =>
      inner ℝ a (fluctuationMean Γ mf t v)) :=
    continuous_const.inner (continuous_fluctuationMean Γ mf t)
  simpa only [fluctuationInitialTerm, Function.comp_apply] using
    (hmean.tendsto v0).comp hinit

/-! ## Gaussian parameters under the model hypotheses -/

/-- Equation (4.28), with nonnegativity of the ODE path derived from the
document's model hypotheses rather than assumed. -/
theorem fluctuationCovariance_posSemidef_of_model [NeZero d]
    (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (hConservative : ∀ (N : ℕ) (hN : 0 < N),
      (DensityDepCTMC.mk N hN Γ).ConservativeJumps)
    (hBoundary : ∀ (N : ℕ) (hN : 0 < N),
      (DensityDepCTMC.mk N hN Γ).BoundaryCompatibleOnSimplex)
    (hSolBound : ∀ s : ℝ, 0 ≤ s → ‖mf.sol s‖ ≤ 1)
    (hF : ContDiff ℝ 1 Γ.drift) (t : Fin m → ℝ)
    (z : ∀ n : ℕ, Fin d → Fin (n + 1 + 1))
    (hz : ∀ n, (fluctuationModel Γ n).InSimplex (z n))
    (v₀ : Fin d → ℝ)
    (hinit : Tendsto
      (fun n => Real.sqrt ((n + 1 : ℕ) : ℝ) •
        ((fluctuationModel Γ n).scaledState (z n) - mf.sol 0))
      atTop (𝓝 v₀)) :
    (fluctuationCovariance Γ mf t).PosSemidef := by
  apply fluctuationCovariance_posSemidef Γ mf t hF
  intro s hs i
  exact (fluctuation_meanField_mem_stdSimplex Γ mf hConservative hBoundary
    hSolBound z hz v₀ hinit hs).1 i

/-- The Gaussian measure in Theorem 4.2 has the displayed mean vector. -/
theorem fluctuation_gaussian_mean (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (t : Fin m → ℝ) (v₀ : Fin d → ℝ) :
    (∫ x, x ∂ProbabilityTheory.multivariateGaussian
      (fluctuationMean Γ mf t v₀) (fluctuationCovariance Γ mf t)) =
        fluctuationMean Γ mf t v₀ :=
  ProbabilityTheory.integral_id_multivariateGaussian

/-- Its coordinate covariances are exactly the entries in equation (4.18). -/
theorem fluctuation_gaussian_covariance (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ) (v₀ : Fin d → ℝ)
    (hS : (fluctuationCovariance Γ mf t).PosSemidef)
    (p q : Fin m × Fin d) :
    ProbabilityTheory.covariance
      (fun x : EuclideanSpace ℝ (Fin m × Fin d) => x p)
      (fun x : EuclideanSpace ℝ (Fin m × Fin d) => x q)
      (ProbabilityTheory.multivariateGaussian
        (fluctuationMean Γ mf t v₀) (fluctuationCovariance Γ mf t)) =
          fluctuationCovariance Γ mf t p q :=
  ProbabilityTheory.covariance_eval_multivariateGaussian hS p q

/-! ## Quadratic-compensator convergence -/

/-- L4 along the canonical population sequence. -/
theorem fluctuation_quadratic_tendsto [NeZero d]
    (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (hConservative : ∀ (N : ℕ) (hN : 0 < N),
      (DensityDepCTMC.mk N hN Γ).ConservativeJumps)
    (hBoundary : ∀ (N : ℕ) (hN : 0 < N),
      (DensityDepCTMC.mk N hN Γ).BoundaryCompatibleOnSimplex)
    (hSolBound : ∀ s : ℝ, 0 ≤ s → ‖mf.sol s‖ ≤ 1)
    (z : ∀ n : ℕ, Fin d → Fin (n + 1 + 1))
    (hz : ∀ n, (fluctuationModel Γ n).InSimplex (z n))
    (hinit : Tendsto
      (fun n => (fluctuationModel Γ n).scaledState (z n))
      atTop (𝓝 mf.x₀))
    (p : (Fin d → ℤ) → ℝ → ℝ)
    (L P : (Fin d → ℤ) → ℝ)
    {T : ℝ} (hT : 0 < T)
    (hp : ∀ ℓ ∈ Γ.jumps, Measurable (p ℓ))
    (hP : ∀ ℓ ∈ Γ.jumps, ∀ s ∈ Icc 0 T, |p ℓ s| ≤ P ℓ)
    (hL : ∀ ℓ ∈ Γ.jumps, 0 ≤ L ℓ)
    (hLip : ∀ ℓ ∈ Γ.jumps, ∀ x y : Fin d → ℝ,
      ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |Γ.rate ℓ x - Γ.rate ℓ y| ≤ L ℓ * ‖x - y‖)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto
      (fun n =>
        (fluctuationModel Γ n).canonicalRecordMeasure (z n)
          {ω | ε <
            |fluctuationQuadraticCompensator Γ p
                (fun s =>
                  (fluctuationModel Γ n).frozenDensityProcess
                    (fluctuationModel Γ n).canonicalPathMap s ω) T -
              fluctuationQuadraticCompensator Γ p mf.sol T|})
      atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  by_cases hetop : e = ⊤
  · exact Eventually.of_forall fun _ => hetop ▸ le_top
  let η : ℝ := e.toReal
  have hη : 0 < η := ENNReal.toReal_pos he.ne' hetop
  have hofη : ENNReal.ofReal η = e := ENNReal.ofReal_toReal hetop
  obtain ⟨δ, hδ, N₀, hclose⟩ :=
    fluctuation_quadratic_compensator_probability_of_close Γ mf
      hConservative hBoundary hSolBound p L P hT hp hP hL hLip
      ε η hε hη
  have hnear :
      ∀ᶠ n in atTop,
        ‖(fluctuationModel Γ n).scaledState (z n) - mf.x₀‖ ≤ δ := by
    filter_upwards [Metric.tendsto_nhds.mp hinit δ hδ] with n hn
    exact (show
      ‖(fluctuationModel Γ n).scaledState (z n) - mf.x₀‖ < δ
      from by simpa only [dist_eq_norm] using hn).le
  filter_upwards [eventually_ge_atTop N₀, hnear] with n hn hnear_n
  have hNlarge : N₀ ≤ n + 1 := hn.trans (Nat.le_succ n)
  have hcloseinit :
      ‖(fun i => (z n i : ℝ) / ((n + 1 : ℕ) : ℝ)) - mf.x₀‖ ≤ δ := by
    change ‖(fluctuationModel Γ n).scaledState (z n) - mf.x₀‖ ≤ δ
    exact hnear_n
  exact
    (hclose (n + 1) hNlarge (Nat.succ_pos n) (z n)
      (hz n) hcloseinit).trans_eq hofη

/-! ## Model-specific scalar quantities for the remaining CLT steps -/

/-- The adjoint with terminal coordinate vector (a(j,i))_i. -/
def fluctuationObservationTest (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (t : Fin m → ℝ) (a : EuclideanSpace ℝ (Fin m × Fin d))
    (j : Fin m) (s : ℝ) : Fin d → ℝ :=
  ∑ i : Fin d, a (j, i) • fluctuationBasisAdjoint Γ mf t (j, i) s

/-- Its inclusive cutoff extension; the value at t_j is retained. -/
def fluctuationObservationCutoffTest (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (a : EuclideanSpace ℝ (Fin m × Fin d)) (j : Fin m) (s : ℝ) :
    Fin d → ℝ :=
  ∑ i : Fin d, a (j, i) • fluctuationBasisCutoff Γ mf t (j, i) s

theorem measurable_fluctuationObservationCutoffTest (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (hF : ContDiff ℝ 1 Γ.drift) (a : EuclideanSpace ℝ (Fin m × Fin d))
    (j : Fin m) :
    Measurable (fluctuationObservationCutoffTest Γ mf t a j) := by
  unfold fluctuationObservationCutoffTest
  exact Finset.measurable_sum Finset.univ fun i _ =>
    measurable_const.smul (measurable_fluctuationBasisCutoff Γ mf t hF (j, i))

/-- The real martingale term ξ_n in Theorem 4.2. -/
def fluctuationNoise (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (t : Fin m → ℝ) (a : EuclideanSpace ℝ (Fin m × Fin d))
    (n : ℕ) (ω : (fluctuationModel Γ n).canonicalRecordΩ) : ℝ :=
  Real.sqrt ((n + 1 : ℕ) : ℝ) *
    fluctuationCompensatedJump (fluctuationModel Γ n)
      (fluctuationCombinedTest Γ mf t a) (fluctuationHorizon t) ω

/-- The real Taylor error ρ_n in Theorem 4.2. -/
def fluctuationError (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (t : Fin m → ℝ) (a : EuclideanSpace ℝ (Fin m × Fin d))
    (n : ℕ) (ω : (fluctuationModel Γ n).canonicalRecordΩ) : ℝ :=
  Real.sqrt ((n + 1 : ℕ) : ℝ) *
    ∑ j : Fin m, fluctuationRemainder (fluctuationModel Γ n)
      (fluctuationObservationCutoffTest Γ mf t a j)
      mf.extendLeft.sol (t j) ω

theorem measurable_fluctuationNoise (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (hF : ContDiff ℝ 1 Γ.drift) (a : EuclideanSpace ℝ (Fin m × Fin d))
    (n : ℕ) : Measurable (fluctuationNoise Γ mf t a n) := by
  unfold fluctuationNoise
  exact measurable_const.mul
    (measurable_fluctuationCompensatedJump (fluctuationModel Γ n)
      (measurable_fluctuationCombinedTest Γ mf t hF a) (fluctuationHorizon t))

theorem measurable_fluctuationError (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (hF : ContDiff ℝ 1 Γ.drift) (a : EuclideanSpace ℝ (Fin m × Fin d))
    (n : ℕ) : Measurable (fluctuationError Γ mf t a n) := by
  unfold fluctuationError
  apply measurable_const.mul
  exact Finset.measurable_sum Finset.univ fun j _ =>
    measurable_fluctuationRemainder (fluctuationModel Γ n)
      (measurable_fluctuationObservationCutoffTest Γ mf t hF a j)
      mf.extendLeft_continuous.measurable hF (t j)

/-- The random quadratic compensator Q_n. -/
def fluctuationPathQuadratic (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (t : Fin m → ℝ) (a : EuclideanSpace ℝ (Fin m × Fin d))
    (n : ℕ) (ω : (fluctuationModel Γ n).canonicalRecordΩ) : ℝ :=
  fluctuationQuadraticCompensator Γ
    (fluctuationPairing (fluctuationCombinedTest Γ mf t a))
    (fun s => (fluctuationModel Γ n).frozenDensityProcess
      (fluctuationModel Γ n).canonicalPathMap s ω) (fluctuationHorizon t)

/-- The deterministic quadratic form Q(a) = aᵀ S a. -/
def fluctuationLimitQuadratic (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (t : Fin m → ℝ) (a : EuclideanSpace ℝ (Fin m × Fin d)) : ℝ :=
  (fun p => a p) ⬝ᵥ (fluctuationCovariance Γ mf t *ᵥ (fun p => a p))

theorem fluctuationLimitQuadratic_eq_compensator (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (hF : ContDiff ℝ 1 Γ.drift) (a : EuclideanSpace ℝ (Fin m × Fin d)) :
    fluctuationLimitQuadratic Γ mf t a =
      fluctuationQuadraticCompensator Γ
        (fluctuationPairing (fluctuationCombinedTest Γ mf t a))
        mf.sol (fluctuationHorizon t) :=
  fluctuationCovariance_quadratic_eq Γ mf t hF (fluctuationHorizon t)
    (time_le_fluctuationHorizon t) a

/-- The scalar exponential remainder ζ(r). -/
def fluctuationZeta (r : ℝ) : ℂ :=
  Complex.exp (Complex.I * (r : ℂ)) - 1 - Complex.I * (r : ℂ)

/-- The listed-jump form of the nonlinear compensator D_n. -/
def fluctuationNonlinearCompensator (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (a : EuclideanSpace ℝ (Fin m × Fin d))
    (n : ℕ) (ω : (fluctuationModel Γ n).canonicalRecordΩ) : ℂ :=
  ∫ s in Icc 0 (fluctuationHorizon t),
    ((n + 1 : ℕ) : ℂ) *
      ∑ ℓ ∈ Γ.jumps,
        (Γ.rate ℓ ((fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap s ω) : ℂ) *
        fluctuationZeta
          (fluctuationPairing (fluctuationCombinedTest Γ mf t a) ℓ s /
            Real.sqrt ((n + 1 : ℕ) : ℝ))

/-- The scaled supremum U_n used in the tightness argument. -/
def fluctuationScaledErrorSup (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (t : Fin m → ℝ) (n : ℕ)
    (ω : (fluctuationModel Γ n).canonicalRecordΩ) : ℝ :=
  Real.sqrt ((n + 1 : ℕ) : ℝ) * fluctuationTimeSup (fluctuationHorizon t)
    (fun s => ‖(fluctuationModel Γ n).frozenDensityProcess
      (fluctuationModel Γ n).canonicalPathMap s ω - mf.sol s‖)

/-- Pairing a Borel vector test with a fixed jump is Borel. -/
theorem measurable_fluctuationPairing {d : ℕ} {ψ : ℝ → Fin d → ℝ}
    (hψ : Measurable ψ) (ℓ : Fin d → ℤ) :
    Measurable (fluctuationPairing ψ ℓ) := by
  unfold fluctuationPairing dotProduct
  exact Finset.measurable_sum Finset.univ fun i _ =>
    ((measurable_pi_apply i).comp hψ).mul measurable_const

/-- L4 for the actual combined adjoint and the covariance quadratic form.
The Lipschitz constants and test bounds are obtained from the model. -/
theorem fluctuationPathQuadratic_tendsto {d m : ℕ} [NeZero d]
    (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (hConservative : ∀ (N : ℕ) (hN : 0 < N),
      (DensityDepCTMC.mk N hN Γ).ConservativeJumps)
    (hBoundary : ∀ (N : ℕ) (hN : 0 < N),
      (DensityDepCTMC.mk N hN Γ).BoundaryCompatibleOnSimplex)
    (hSolBound : ∀ s : ℝ, 0 ≤ s → ‖mf.sol s‖ ≤ 1)
    (hF : ContDiff ℝ 1 Γ.drift)
    (t : Fin m → ℝ) (ht : ∀ j, 0 ≤ t j)
    (z : ∀ n : ℕ, Fin d → Fin (n + 1 + 1))
    (hz : ∀ n, (fluctuationModel Γ n).InSimplex (z n))
    (v0 : Fin d → ℝ)
    (hinit : Tendsto
      (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) •
        ((fluctuationModel Γ n).scaledState (z n) - mf.sol 0))
      atTop (𝓝 v0))
    (a : EuclideanSpace ℝ (Fin m × Fin d))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto
      (fun n => (fluctuationModel Γ n).canonicalRecordMeasure (z n)
        {ω | ε < |fluctuationPathQuadratic Γ mf t a n ω -
          fluctuationLimitQuadratic Γ mf t a|})
      atTop (𝓝 0) := by
  classical
  obtain ⟨C, _hC, hCbound⟩ :=
    exists_fluctuationCombinedTest_bound Γ mf t hF ht a
  let P : (Fin d → ℤ) → ℝ :=
    fun ℓ => (d : ℝ) * C * ‖(fun i => (ℓ i : ℝ))‖
  have hp : ∀ ℓ ∈ Γ.jumps,
      Measurable (fluctuationPairing (fluctuationCombinedTest Γ mf t a) ℓ) := by
    intro ℓ _
    exact measurable_fluctuationPairing
      (measurable_fluctuationCombinedTest Γ mf t hF a) ℓ
  have hP : ∀ ℓ ∈ Γ.jumps, ∀ s ∈ Icc 0 (fluctuationHorizon t),
      |fluctuationPairing (fluctuationCombinedTest Γ mf t a) ℓ s| ≤ P ℓ := by
    intro ℓ _ s _
    change |fluctuationCombinedTest Γ mf t a s ⬝ᵥ
      (fun i => (ℓ i : ℝ))| ≤ (d : ℝ) * C * ‖(fun i => (ℓ i : ℝ))‖
    exact (fluctuation_abs_dot_le _ _).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hCbound s) (Nat.cast_nonneg d))
        (norm_nonneg _))
  have hLip_exists : ∀ ℓ : Fin d → ℤ, ∃ L : ℝ, 0 ≤ L ∧
      (ℓ ∈ Γ.jumps → ∀ x y : Fin d → ℝ,
        ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |Γ.rate ℓ x - Γ.rate ℓ y| ≤ L * ‖x - y‖) := by
    intro ℓ
    by_cases hℓ : ℓ ∈ Γ.jumps
    · obtain ⟨L, hL, hLip⟩ := Γ.rate_lipschitz ℓ hℓ 1 zero_lt_one
      refine ⟨L, hL.le, ?_⟩
      intro _ x y hx hy
      simpa only [Real.norm_eq_abs] using hLip x y hx hy
    · exact ⟨0, le_rfl, fun h => (hℓ h).elim⟩
  choose L hL hLip using hLip_exists
  have hT : 0 < fluctuationHorizon t := by
    unfold fluctuationHorizon
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hinitial : Tendsto
      (fun n => (fluctuationModel Γ n).scaledState (z n))
      atTop (𝓝 mf.x₀) := by
    simpa only [mf.sol_init] using
      fluctuation_tendsto_of_sqrt_smul_tendsto
        (fun n => (fluctuationModel Γ n).scaledState (z n))
        (mf.sol 0) v0 hinit
  have h := fluctuation_quadratic_tendsto Γ mf
    hConservative hBoundary hSolBound z hz hinitial
    (fluctuationPairing (fluctuationCombinedTest Γ mf t a))
    L P hT hp hP (fun ℓ _ => hL ℓ) hLip ε hε
  simpa only [fluctuationPathQuadratic,
    fluctuationLimitQuadratic_eq_compensator Γ mf t hF a] using h

/-! ## Remainder integrability and characteristic-function assembly -/

private theorem fluctuation_remainder_abs_integral_le
    {τ C : ℝ} (hτ : 0 ≤ τ)
    (f : ℝ → ℝ) (hb : ∀ s ∈ Icc 0 τ, |f s| ≤ C) :
    |∫ s in Icc 0 τ, f s| ≤ τ * C := by
  haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) τ)) :=
    ⟨by simpa using
      (measure_Icc_lt_top : volume (Icc (0 : ℝ) τ) < ⊤)⟩
  have hbound : (fun s => |f s|) ≤ᵐ[volume.restrict (Icc 0 τ)]
      (fun _ => C) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with s hs
    exact hb s hs
  calc
    |∫ s in Icc 0 τ, f s| ≤ ∫ s in Icc 0 τ, |f s| := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm
          (f := f) (μ := volume.restrict (Icc 0 τ)))
    _ ≤ ∫ _s in Icc (0 : ℝ) τ, C :=
      integral_mono_of_nonneg
        (Eventually.of_forall fun s => abs_nonneg (f s))
        (integrable_const C) hbound
    _ = τ * C := by
      simp [Real.volume_Icc, hτ, smul_eq_mul]

/-- A deterministic bound for the total remainder functional. -/
theorem fluctuation_abs_remainder_le
    (M : DensityDepCTMC d) {ψ x : ℝ → Fin d → ℝ}
    {τ C B D : ℝ} (hτ : 0 ≤ τ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hψC : ∀ s ∈ Icc 0 τ, ‖ψ s‖ ≤ C)
    (hx : ∀ s ∈ Icc 0 τ, ‖x s‖ ≤ 1)
    (hB : ∀ y : Fin d → ℝ, ‖y‖ ≤ 1 →
      ‖M.rateSpec.drift y‖ ≤ B)
    (hDF : ∀ y : Fin d → ℝ, ‖y‖ ≤ 1 →
      ‖fderiv ℝ M.rateSpec.drift y‖ ≤ D)
    (ω : M.canonicalRecordΩ) :
    |fluctuationRemainder M ψ x τ ω| ≤
      τ * ((d : ℝ) * C * (2 * B + 2 * D)) := by
  have hX (s : ℝ) :
      ‖M.frozenDensityProcess M.canonicalPathMap s ω‖ ≤ 1 :=
    M.frozenDensityProcess_norm_le M.canonicalPathMap s ω
  have hrem (s : ℝ) (hs : s ∈ Icc 0 τ) :
      ‖M.rateSpec.drift (M.frozenDensityProcess M.canonicalPathMap s ω) -
          M.rateSpec.drift (x s) -
          (fderiv ℝ M.rateSpec.drift (x s))
            (M.frozenDensityProcess M.canonicalPathMap s ω - x s)‖ ≤
        2 * B + 2 * D := by
    have hdiff :
        ‖M.frozenDensityProcess M.canonicalPathMap s ω - x s‖ ≤ 2 := by
      calc
        _ ≤ ‖M.frozenDensityProcess M.canonicalPathMap s ω‖ + ‖x s‖ :=
          norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (hX s) (hx s hs)
        _ = 2 := by norm_num
    have hlin :
        ‖(fderiv ℝ M.rateSpec.drift (x s))
          (M.frozenDensityProcess M.canonicalPathMap s ω - x s)‖ ≤
          D * 2 :=
      ((fderiv ℝ M.rateSpec.drift (x s)).le_opNorm _).trans
        (mul_le_mul (hDF (x s) (hx s hs)) hdiff (norm_nonneg _) hD)
    calc
      _ ≤
          ‖M.rateSpec.drift
            (M.frozenDensityProcess M.canonicalPathMap s ω) -
            M.rateSpec.drift (x s)‖ +
          ‖(fderiv ℝ M.rateSpec.drift (x s))
            (M.frozenDensityProcess M.canonicalPathMap s ω - x s)‖ :=
        norm_sub_le _ _
      _ ≤
          (‖M.rateSpec.drift
              (M.frozenDensityProcess M.canonicalPathMap s ω)‖ +
            ‖M.rateSpec.drift (x s)‖) +
          ‖(fderiv ℝ M.rateSpec.drift (x s))
            (M.frozenDensityProcess M.canonicalPathMap s ω - x s)‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (B + B) + D * 2 :=
        add_le_add
          (add_le_add (hB _ (hX s)) (hB _ (hx s hs))) hlin
      _ = 2 * B + 2 * D := by ring
  change |∫ s in Icc 0 τ, ψ s ⬝ᵥ
    (M.rateSpec.drift (M.frozenDensityProcess M.canonicalPathMap s ω) -
      M.rateSpec.drift (x s) -
      (fderiv ℝ M.rateSpec.drift (x s))
        (M.frozenDensityProcess M.canonicalPathMap s ω - x s))| ≤ _
  apply fluctuation_remainder_abs_integral_le hτ
  intro s hs
  exact (fluctuation_abs_dot_le _ _).trans
    (mul_le_mul
      (mul_le_mul_of_nonneg_left (hψC s hs) (Nat.cast_nonneg _))
      (hrem s hs) (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) hC))

/-- The remaining integrability clause for the total L6 remainder. -/
theorem integrable_fluctuationRemainder
    (M : DensityDepCTMC d)
    (z : Fin d → Fin (M.N + 1)) {ψ x : ℝ → Fin d → ℝ}
    (hψ : Measurable ψ) (hψb : ∃ C : ℝ, ∀ s, ‖ψ s‖ ≤ C)
    (hxm : Measurable x) (hF : ContDiff ℝ 1 M.rateSpec.drift)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (hx : ∀ s ∈ Icc 0 τ, ‖x s‖ ≤ 1) :
    Integrable (fluctuationRemainder M ψ x τ)
      (M.canonicalRecordMeasure z) := by
  obtain ⟨C, hψC⟩ := hψb
  have hC : 0 ≤ C := (norm_nonneg (ψ 0)).trans (hψC 0)
  obtain ⟨B₀, hB₀⟩ :=
    (isCompact_closedBall (0 : Fin d → ℝ) 1).exists_bound_of_continuousOn
      M.rateSpec.drift_continuous.continuousOn
  have hDcont : Continuous (fderiv ℝ M.rateSpec.drift) :=
    hF.continuous_fderiv (by simp)
  obtain ⟨D₀, hD₀⟩ :=
    (isCompact_closedBall (0 : Fin d → ℝ) 1).exists_bound_of_continuousOn
      hDcont.continuousOn
  let B : ℝ := max B₀ 0
  let D : ℝ := max D₀ 0
  have hB : ∀ y : Fin d → ℝ, ‖y‖ ≤ 1 →
      ‖M.rateSpec.drift y‖ ≤ B := by
    intro y hy
    exact (hB₀ y (by simpa using hy)).trans (le_max_left _ _)
  have hDF : ∀ y : Fin d → ℝ, ‖y‖ ≤ 1 →
      ‖fderiv ℝ M.rateSpec.drift y‖ ≤ D := by
    intro y hy
    exact (hD₀ y (by simpa using hy)).trans (le_max_left _ _)
  have hbound (ω : M.canonicalRecordΩ) :
      |fluctuationRemainder M ψ x τ ω| ≤
        τ * ((d : ℝ) * C * (2 * B + 2 * D)) :=
    fluctuation_abs_remainder_le M hτ hC (le_max_right _ _)
      (fun s _ => hψC s) hx hB hDF ω
  refine (integrable_const
    (τ * ((d : ℝ) * C * (2 * B + 2 * D)))).mono'
      (measurable_fluctuationRemainder M hψ hxm hF τ).aestronglyMeasurable ?_
  exact Eventually.of_forall fun ω => by
    simpa only [Real.norm_eq_abs] using hbound ω

/-- The elementary phase estimate used in Step 3 of Theorem 4.2. -/
theorem fluctuation_norm_cexp_add_sub_le (u v : ℝ) :
    ‖Complex.exp (Complex.I * ((u + v : ℝ) : ℂ)) -
        Complex.exp (Complex.I * (u : ℂ))‖ ≤ min |v| 2 := by
  apply le_min
  · have heq :
        Complex.exp (Complex.I * ((u + v : ℝ) : ℂ)) -
            Complex.exp (Complex.I * (u : ℂ)) =
          Complex.exp (Complex.I * (u : ℂ)) *
            (Complex.exp (Complex.I * (v : ℂ)) - 1) := by
      simp only [Complex.ofReal_add, mul_add, Complex.exp_add,
        mul_sub, mul_one]
    rw [heq, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
    simpa only [Real.norm_eq_abs] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := v))
  · calc
      _ ≤ ‖Complex.exp (Complex.I * ((u + v : ℝ) : ℂ))‖ +
          ‖Complex.exp (Complex.I * (u : ℂ))‖ :=
        norm_sub_le _ _
      _ = 2 := by
        rw [Complex.norm_exp_I_mul_ofReal, Complex.norm_exp_I_mul_ofReal]
        norm_num

private theorem fluctuation_integrable_cexp
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] {f : Ω → ℝ} (hf : Measurable f) :
    Integrable (fun ω => Complex.exp (Complex.I * (f ω : ℂ))) P := by
  refine (integrable_const (1 : ℝ)).mono' ?_ ?_
  · exact (Complex.measurable_exp.comp
      (measurable_const.mul (Complex.measurable_ofReal.comp hf))).aestronglyMeasurable
  · exact Eventually.of_forall fun ω =>
      (Complex.norm_exp_I_mul_ofReal (f ω)).le

/-- A negligible real remainder changes the scalar characteristic function
by a quantity tending to zero. No independence hypothesis is needed. -/
theorem fluctuation_tendsto_integral_cexp_add_sub
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (ξ ρ : ∀ n, Ω n → ℝ)
    (hξ : ∀ n, Measurable (ξ n)) (hρm : ∀ n, Measurable (ρ n))
    (hρ : ∀ η > (0 : ℝ),
      Tendsto (fun n => P n {ω | η < |ρ n ω|}) atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        (∫ ω, Complex.exp (Complex.I * ((ξ n ω + ρ n ω : ℝ) : ℂ)) ∂P n) -
        (∫ ω, Complex.exp (Complex.I * (ξ n ω : ℂ)) ∂P n))
      atTop (𝓝 0) := by
  let W : ∀ n, Ω n → ℂ := fun n ω =>
    Complex.exp (Complex.I * ((ξ n ω + ρ n ω : ℝ) : ℂ)) -
      Complex.exp (Complex.I * (ξ n ω : ℂ))
  have hWle (n : ℕ) (ω : Ω n) : ‖W n ω‖ ≤ |ρ n ω| :=
    (fluctuation_norm_cexp_add_sub_le (ξ n ω) (ρ n ω)).trans
      (min_le_left _ _)
  have hWbdd : ∀ n, ∀ᵐ ω ∂P n, ‖W n ω‖ ≤ 2 := fun n =>
    Eventually.of_forall fun ω =>
      (fluctuation_norm_cexp_add_sub_le (ξ n ω) (ρ n ω)).trans
        (min_le_right _ _)
  have hWprob : ∀ η > (0 : ℝ),
      Tendsto (fun n => P n {ω | η < ‖W n ω‖}) atTop (𝓝 0) := by
    intro η hη
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    filter_upwards
      [(ENNReal.tendsto_nhds_zero.mp (hρ η hη)) ε hε] with n hn
    have hsub : {ω : Ω n | η < ‖W n ω‖} ⊆
        {ω : Ω n | η < |ρ n ω|} := by
      intro ω hω
      change η < ‖W n ω‖ at hω
      change η < |ρ n ω|
      exact hω.trans_le (hWle n ω)
    exact (measure_mono hsub).trans hn
  have hW0 :=
    tendsto_integral_complex_of_bounded_of_tendsto_measure P W
      (M := 2) (by norm_num) hWbdd hWprob
  have heq (n : ℕ) :
      (∫ ω, W n ω ∂P n) =
        (∫ ω, Complex.exp (Complex.I * ((ξ n ω + ρ n ω : ℝ) : ℂ)) ∂P n) -
        (∫ ω, Complex.exp (Complex.I * (ξ n ω : ℂ)) ∂P n) := by
    dsimp [W]
    exact integral_sub
      (fluctuation_integrable_cexp (P n) ((hξ n).add (hρm n)))
      (fluctuation_integrable_cexp (P n) (hξ n))
  simpa only [heq] using hW0

/-- Scalar characteristic-function assembly corresponding to (4.44).
The stochastic hypotheses here are intermediate conclusions, not additional
hypotheses of the model CLT. -/
theorem fluctuation_scalar_charFun_assembly
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (c : ℕ → ℝ) (ξ ρ : ∀ n, Ω n → ℝ) (c₀ q : ℝ)
    (hξ : ∀ n, Measurable (ξ n)) (hρm : ∀ n, Measurable (ρ n))
    (hc : Tendsto c atTop (𝓝 c₀))
    (hρ : ∀ η > (0 : ℝ),
      Tendsto (fun n => P n {ω | η < |ρ n ω|}) atTop (𝓝 0))
    (hξlim :
      Tendsto
        (fun n => ∫ ω, Complex.exp (Complex.I * (ξ n ω : ℂ)) ∂P n)
        atTop (𝓝 (Complex.exp (-(q : ℂ) / 2)))) :
    Tendsto
      (fun n => ∫ ω,
        Complex.exp (Complex.I * ((c n + ξ n ω + ρ n ω : ℝ) : ℂ)) ∂P n)
      atTop (𝓝 (Complex.exp ((c₀ : ℂ) * Complex.I - (q : ℂ) / 2))) := by
  have hnoise :=
    fluctuation_tendsto_integral_cexp_add_sub P ξ ρ hξ hρm hρ
  have hmiddle :
      Tendsto
        (fun n => ∫ ω,
          Complex.exp (Complex.I * ((ξ n ω + ρ n ω : ℝ) : ℂ)) ∂P n)
        atTop (𝓝 (Complex.exp (-(q : ℂ) / 2))) := by
    simpa only [sub_add_cancel, zero_add] using hnoise.add hξlim
  have hcc : Tendsto (fun n => (c n : ℂ)) atTop (𝓝 (c₀ : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hc
  have hphase :
      Tendsto (fun n => Complex.exp (Complex.I * (c n : ℂ))) atTop
        (𝓝 (Complex.exp (Complex.I * (c₀ : ℂ)))) :=
    Complex.continuous_exp.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul hcc)
  have hfactor (n : ℕ) :
      (∫ ω,
        Complex.exp (Complex.I * ((c n + ξ n ω + ρ n ω : ℝ) : ℂ)) ∂P n) =
        Complex.exp (Complex.I * (c n : ℂ)) *
          (∫ ω,
            Complex.exp (Complex.I * ((ξ n ω + ρ n ω : ℝ) : ℂ)) ∂P n) := by
    calc
      _ = ∫ ω, Complex.exp (Complex.I * (c n : ℂ)) *
          Complex.exp (Complex.I * ((ξ n ω + ρ n ω : ℝ) : ℂ)) ∂P n := by
        apply integral_congr_ae
        exact Eventually.of_forall fun ω => by
          simp only [Complex.ofReal_add, mul_add, Complex.exp_add, mul_assoc]
      _ = _ := integral_const_mul _ _
  have hvalue :
      Complex.exp (Complex.I * (c₀ : ℂ)) *
          Complex.exp (-(q : ℂ) / 2) =
        Complex.exp ((c₀ : ℂ) * Complex.I - (q : ℂ) / 2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hlim := hphase.mul hmiddle
  rw [hvalue] at hlim
  simpa only [hfactor] using hlim

/-- The final Lévy transfer after the pointwise characteristic-function
limit has been proved from the model hypotheses. -/
theorem fluctuation_tendsto_gaussian_of_charFun
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ℕ → ProbabilityMeasure (EuclideanSpace ℝ ι))
    (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (hS : S.PosSemidef)
    (hchar : ∀ a : EuclideanSpace ℝ ι,
      Tendsto
        (fun n => charFun (L n : Measure (EuclideanSpace ℝ ι)) a)
        atTop
        (𝓝 (Complex.exp ((⟪a, μ⟫_ℝ : ℂ) * Complex.I -
          ((a ⬝ᵥ S *ᵥ a : ℝ) : ℂ) / 2)))) :
    Tendsto L atTop
      (𝓝 (⟨ProbabilityTheory.multivariateGaussian μ S, inferInstance⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ ι))) := by
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
  intro a
  change Tendsto
    (fun n => charFun (L n : Measure (EuclideanSpace ℝ ι)) a) atTop
    (𝓝 (charFun (ProbabilityTheory.multivariateGaussian μ S) a))
  rw [ProbabilityTheory.charFun_multivariateGaussian hS]
  exact hchar a

/-- The model-specific characteristic-function assembly, once the three
stochastic steps below have been supplied. This is an intermediate implication,
not Theorem 4.2. -/
theorem fluctuation_charFun_limit_of_scalar_steps
    (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (t : Fin m → ℝ) (hF : ContDiff ℝ 1 Γ.drift)
    (z : ∀ n : ℕ, Fin d → Fin (n + 1 + 1))
    (v₀ : Fin d → ℝ)
    (hinit : Tendsto
      (fun n => Real.sqrt ((n + 1 : ℕ) : ℝ) •
        ((fluctuationModel Γ n).scaledState (z n) - mf.sol 0))
      atTop (𝓝 v₀))
    (a : EuclideanSpace ℝ (Fin m × Fin d))
    (hdecomp : ∀ n, ∀ᵐ ω ∂(fluctuationModel Γ n).canonicalRecordMeasure (z n),
      ⟪a, fluctuationVector Γ mf t n ω⟫_ℝ =
        fluctuationInitialTerm Γ mf t z a n +
          fluctuationNoise Γ mf t a n ω + fluctuationError Γ mf t a n ω)
    (hnoise : Tendsto
      (fun n => ∫ ω, Complex.exp (Complex.I * (fluctuationNoise Γ mf t a n ω : ℂ))
        ∂(fluctuationModel Γ n).canonicalRecordMeasure (z n))
      atTop (𝓝 (Complex.exp (-(fluctuationLimitQuadratic Γ mf t a : ℂ) / 2))))
    (herror : ∀ ε > (0 : ℝ),
      Tendsto (fun n => (fluctuationModel Γ n).canonicalRecordMeasure (z n)
        {ω | ε < |fluctuationError Γ mf t a n ω|}) atTop (𝓝 0)) :
    Tendsto
      (fun n => charFun (fluctuationLaw Γ mf t z n :
        Measure (EuclideanSpace ℝ (Fin m × Fin d))) a)
      atTop
      (𝓝 (Complex.exp ((⟪a, fluctuationMean Γ mf t v₀⟫_ℝ : ℂ) * Complex.I -
        (fluctuationLimitQuadratic Γ mf t a : ℂ) / 2))) := by
  have hsum :=
    fluctuation_scalar_charFun_assembly
      (fun n => (fluctuationModel Γ n).canonicalRecordMeasure (z n))
      (fluctuationInitialTerm Γ mf t z a)
      (fluctuationNoise Γ mf t a) (fluctuationError Γ mf t a)
      (⟪a, fluctuationMean Γ mf t v₀⟫_ℝ) (fluctuationLimitQuadratic Γ mf t a)
      (fun n => measurable_fluctuationNoise Γ mf t hF a n)
      (fun n => measurable_fluctuationError Γ mf t hF a n)
      (tendsto_fluctuationInitialTerm Γ mf t z a v₀ hinit)
      herror hnoise
  have heq (n : ℕ) :
      charFun (fluctuationLaw Γ mf t z n :
        Measure (EuclideanSpace ℝ (Fin m × Fin d))) a =
      ∫ ω, Complex.exp (Complex.I *
        ((fluctuationInitialTerm Γ mf t z a n +
          fluctuationNoise Γ mf t a n ω + fluctuationError Γ mf t a n ω : ℝ) : ℂ))
        ∂(fluctuationModel Γ n).canonicalRecordMeasure (z n) := by
    rw [fluctuationLaw_charFun]
    apply integral_congr_ae
    filter_upwards [hdecomp n] with ω hω
    rw [real_inner_comm, hω]
    congr 1
    ring
  simpa only [heq] using hsum

/-!
## Unfinished statement register

The following block comment records exact specifications only. None of its
theorem signatures is an exported Lean declaration. Every theorem declaration
outside this comment includes a complete proof script.
-/

/-
-- T1: the two sharp scalar Taylor estimates in (4.33).
theorem fluctuationZeta_bound (r : ℝ) :
    ‖fluctuationZeta r‖ ≤ r ^ 2 / 2

theorem fluctuationZeta_cubic_bound (r : ℝ) :
    ‖fluctuationZeta r + ((r : ℂ) ^ 2) / 2‖ ≤ |r| ^ 3 / 6

-- E1: the record-index uniform bound needed for the complex limit.
theorem fluctuation_uniform_imaginary_expSum_bound
    {S : Type*} [Fintype S] [DecidableEq S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (Q : QMatrix S) {g : ℝ → S → S → ℂ} {D : Set ℝ}
    (hg : IsExpTilt g D) (hRe : ∀ s x y, (g s x y).re = 0)
    (T Λ : ℝ) (hT : 0 ≤ T) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ x, Q.exitRate x ≤ Λ) (x₀ : S) :
    ∀ᵐ ω ∂Q.canonicalRecordMeasure x₀, ∀ r : ℕ,
      ‖Complex.exp (Q.expSum g T r ω)‖ ≤ Real.exp (2 * Λ * T)

section RemainingModelStatements

variable [NeZero d]
variable (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
variable
  (hConservative : ∀ (N : ℕ) (hN : 0 < N),
    (DensityDepCTMC.mk N hN Γ).ConservativeJumps)
  (hBoundary : ∀ (N : ℕ) (hN : 0 < N),
    (DensityDepCTMC.mk N hN Γ).BoundaryCompatibleOnSimplex)
  (hSolBound : ∀ s : ℝ, 0 ≤ s → ‖mf.sol s‖ ≤ 1)
  (hF : ContDiff ℝ 1 Γ.drift)
  (t : Fin m → ℝ) (ht : ∀ j, 0 ≤ t j)
  (z : ∀ n : ℕ, Fin d → Fin (n + 1 + 1))
  (hz : ∀ n, (fluctuationModel Γ n).InSimplex (z n))
  (v₀ : Fin d → ℝ)
  (hinit : Tendsto
    (fun n => Real.sqrt ((n + 1 : ℕ) : ℝ) •
      ((fluctuationModel Γ n).scaledState (z n) - mf.sol 0))
    atTop (𝓝 v₀))
  (a : EuclideanSpace ℝ (Fin m × Fin d))

-- Every signature in this section includes precisely these model hypotheses.
include hConservative hBoundary hSolBound hF ht hz hinit

local notation "H" => fluctuationHorizon t
local notation "P" =>
  (fun n : ℕ => (fluctuationModel Γ n).canonicalRecordMeasure (z n))
local notation "X" =>
  (fun (n : ℕ) (s : ℝ) (ω : (fluctuationModel Γ n).canonicalRecordΩ) =>
    (fluctuationModel Γ n).frozenDensityProcess
      (fluctuationModel Γ n).canonicalPathMap s ω)
local notation "Ysup" =>
  (fun (n : ℕ) (ω : (fluctuationModel Γ n).canonicalRecordΩ) =>
    fluctuationTimeSup H (fun s => ‖X n s ω - mf.sol s‖))

-- W1: adjoint integration by parts, (4.25), on one event for every j.
theorem fluctuation_adjoint_integration_by_parts (n : ℕ) :
    ∀ᵐ ω ∂P n, ∀ j : Fin m,
      (fun i => a (j, i)) ⬝ᵥ (X n (t j) ω - mf.sol (t j)) =
        fluctuationObservationTest Γ mf t a j 0 ⬝ᵥ
          ((fluctuationModel Γ n).scaledState (z n) - mf.sol 0) +
        fluctuationCompensatedJump (fluctuationModel Γ n)
          (fluctuationObservationCutoffTest Γ mf t a j) (t j) ω +
        fluctuationRemainder (fluctuationModel Γ n)
          (fluctuationObservationCutoffTest Γ mf t a j)
          mf.extendLeft.sol (t j) ω

-- W2: inclusive-cutoff additivity, (4.26).
theorem fluctuation_compensated_cutoff_sum (n : ℕ) :
    ∀ᵐ ω ∂P n,
      fluctuationCompensatedJump (fluctuationModel Γ n)
        (fluctuationCombinedTest Γ mf t a) H ω =
      ∑ j : Fin m, fluctuationCompensatedJump (fluctuationModel Γ n)
        (fluctuationObservationCutoffTest Γ mf t a j) (t j) ω

-- W3: the scalar decomposition consumed by the proved assembly helper.
theorem fluctuation_scalar_decomposition (n : ℕ) :
    ∀ᵐ ω ∂P n,
      ⟪a, fluctuationVector Γ mf t n ω⟫_ℝ =
        fluctuationInitialTerm Γ mf t z a n +
          fluctuationNoise Γ mf t a n ω + fluctuationError Γ mf t a n ω

-- E2: identify the record-index limit with i ξ_n - D_n.
theorem fluctuation_expSum_tendsto (n : ℕ) :
    ∀ᵐ ω ∂P n,
      Tendsto
        (fun r => (fluctuationModel Γ n).toQMatrix.expSum
          (fluctuationTilt Γ mf t a n) H r ω)
        atTop
        (𝓝 (Complex.I * (fluctuationNoise Γ mf t a n ω : ℂ) -
          fluctuationNonlinearCompensator Γ mf t a n ω))

-- E3: the total expectation identity (4.37).
theorem fluctuation_exponential_identity (n : ℕ) :
    (∫ ω, Complex.exp
      (Complex.I * (fluctuationNoise Γ mf t a n ω : ℂ) -
        fluctuationNonlinearCompensator Γ mf t a n ω) ∂P n) = 1

-- T2: choose the deterministic bounds from the model; they are not final
-- CLT assumptions.
theorem fluctuation_compensator_constants :
    ∃ J Λ C : ℝ, 1 ≤ J ∧ 1 ≤ Λ ∧ 0 ≤ C ∧
      (∀ ℓ ∈ Γ.jumps, ‖(fun i => (ℓ i : ℝ))‖ ≤ J) ∧
      (∀ x : Fin d → ℝ, (∀ i, 0 ≤ x i) → ‖x‖ ≤ 1 →
        (∑ ℓ ∈ Γ.jumps, Γ.rate ℓ x) ≤ Λ) ∧
      (∀ s, ‖fluctuationCombinedTest Γ mf t a s‖ ≤ C)

-- T3: the explicit constants in (4.34)-(4.35), with P = d J C.
theorem fluctuation_compensator_uniform_bounds
    (J Λ C : ℝ) (hJ0 : 1 ≤ J) (hΛ0 : 0 ≤ Λ) (hC0 : 0 ≤ C)
    (hJ : ∀ ℓ ∈ Γ.jumps, ‖(fun i => (ℓ i : ℝ))‖ ≤ J)
    (hΛ : ∀ x : Fin d → ℝ, (∀ i, 0 ≤ x i) → ‖x‖ ≤ 1 →
      (∑ ℓ ∈ Γ.jumps, Γ.rate ℓ x) ≤ Λ)
    (hC : ∀ s, ‖fluctuationCombinedTest Γ mf t a s‖ ≤ C)
    (n : ℕ) (ω : (fluctuationModel Γ n).canonicalRecordΩ) :
    ‖fluctuationNonlinearCompensator Γ mf t a n ω‖ ≤
        H * Λ * ((d : ℝ) * J * C) ^ 2 / 2 ∧
      ‖fluctuationNonlinearCompensator Γ mf t a n ω +
          (fluctuationPathQuadratic Γ mf t a n ω : ℂ) / 2‖ ≤
        H * Λ * ((d : ℝ) * J * C) ^ 3 /
          (6 * Real.sqrt ((n + 1 : ℕ) : ℝ))

-- T4: measurability and convergence of D_n to -Q(a)/2, (4.36).
theorem fluctuationNonlinearCompensator_tendsto :
    (∀ n, Measurable (fluctuationNonlinearCompensator Γ mf t a n)) ∧
      ∀ ε > (0 : ℝ),
        Tendsto
          (fun n => P n {ω | ε <
            ‖fluctuationNonlinearCompensator Γ mf t a n ω +
              (fluctuationLimitQuadratic Γ mf t a : ℂ) / 2‖})
          atTop (𝓝 0)

-- N: Step 1's scalar Gaussian-noise characteristic-function limit.
theorem fluctuationNoise_charFun_tendsto :
    Tendsto
      (fun n => ∫ ω,
        Complex.exp (Complex.I * (fluctuationNoise Γ mf t a n ω : ℂ)) ∂P n)
      atTop
      (𝓝 (Complex.exp (-(fluctuationLimitQuadratic Γ mf t a : ℂ) / 2)))

-- R1: the uniform tightness conclusion of (4.40)-(4.41).
theorem fluctuationScaledErrorSup_tight :
    ∀ ε > (0 : ℝ), ∃ R > (0 : ℝ), ∀ n,
      P n {ω | R < fluctuationScaledErrorSup Γ mf t n ω} ≤ ENNReal.ofReal ε

-- R2: the localized remainder estimate, with the essential factor d.
theorem fluctuation_remainder_local_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ (n : ℕ)
      (ω : (fluctuationModel Γ n).canonicalRecordΩ) (j : Fin m) (C : ℝ),
      0 ≤ C →
      (∀ s ∈ Icc 0 (t j),
        ‖fluctuationObservationCutoffTest Γ mf t a j s‖ ≤ C) →
      Ysup n ω ≤ δ →
      Real.sqrt ((n + 1 : ℕ) : ℝ) *
          |fluctuationRemainder (fluctuationModel Γ n)
            (fluctuationObservationCutoffTest Γ mf t a j)
            mf.extendLeft.sol (t j) ω| ≤
        ((d : ℝ) * t j * C * ε) * fluctuationScaledErrorSup Γ mf t n ω

-- R3: the finite sum of scaled remainders vanishes in probability, (4.42).
theorem fluctuationError_tendsto :
    ∀ ε > (0 : ℝ),
      Tendsto
        (fun n => P n {ω | ε < |fluctuationError Γ mf t a n ω|})
        atTop (𝓝 0)

end RemainingModelStatements

-- The full model-only target. Its second conjunct is the literal Mathlib
-- target from Section 4.2; the first is the PSD assertion in Theorem 4.2.
-- The first conjunct is already proved by
-- fluctuationCovariance_posSemidef_of_model.
theorem kurtz_finite_dimensional_clt
    {d m : ℕ} [NeZero d] (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ)
    (hConservative : ∀ (N : ℕ) (hN : 0 < N),
      (DensityDepCTMC.mk N hN Γ).ConservativeJumps)
    (hBoundary : ∀ (N : ℕ) (hN : 0 < N),
      (DensityDepCTMC.mk N hN Γ).BoundaryCompatibleOnSimplex)
    (hSolBound : ∀ s : ℝ, 0 ≤ s → ‖mf.sol s‖ ≤ 1)
    (hF : ContDiff ℝ 1 Γ.drift)
    (t : Fin m → ℝ) (ht : ∀ j, 0 ≤ t j)
    (z : ∀ n : ℕ, Fin d → Fin (n + 1 + 1))
    (hz : ∀ n, (fluctuationModel Γ n).InSimplex (z n))
    (v₀ : Fin d → ℝ)
    (hinit : Tendsto
      (fun n => Real.sqrt ((n + 1 : ℕ) : ℝ) •
        ((fluctuationModel Γ n).scaledState (z n) - mf.sol 0))
      atTop (𝓝 v₀)) :
    (fluctuationCovariance Γ mf t).PosSemidef ∧
      Tendsto (fun n => fluctuationLaw Γ mf t z n) atTop
        (𝓝 (⟨ProbabilityTheory.multivariateGaussian
          (fluctuationMean Γ mf t v₀)
          (fluctuationCovariance Γ mf t), inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin m × Fin d))))
-/

end

end Ripple.Kurtz
