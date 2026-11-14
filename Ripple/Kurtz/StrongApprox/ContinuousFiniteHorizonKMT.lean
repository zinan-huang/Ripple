-- Ripple/Kurtz/StrongApprox/ContinuousFiniteHorizonKMT.lean
import Ripple.Kurtz.StrongApprox.BrownianFineDyadicCompletion
import Ripple.Kurtz.StrongApprox.DyadicInterpolationOvershoot
import Ripple.Kurtz.StrongApprox.ClockModulusGronwall

/-!
# Continuous finite-horizon KMT on one probability space

From `BrownianFineDyadicCompletion` this file uses:
* `brownianPath`, `measurable_brownianPath`, `continuous_brownianPath`;
* `brownianPath_eq_candidate_of_mem`;
* `brownianPath_dyadicBrownianOn`.

From `BrownianFinePath`, through that import, it uses
`brownianCandidate_natCast` and `brownianFineMeasure_map_fst`.

From `DyadicConditionalPoissonPath` it uses `committedContinuousPoisson`, its integer agreement,
monotonicity, measurability, and finite increment-vector law.

The fixed two-factor K20 corollary cannot accept the extra fine-Gaussian
coordinate.  We therefore instantiate its underlying theorem
`continuousInterpolation_tail` on the common three-factor source.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal NNReal BigOperators Nat Topology

namespace Ripple.Kurtz.StrongApprox.ContinuousFiniteHorizonKMT

open BrownianFinePath BrownianFineDyadicCompletion
open DyadicGaussianTree DyadicSpatialSkeleton
open DyadicConditionalPoissonPath DyadicInterpolationOvershoot
open DyadicFiniteHorizonUnion

/-! ## The common source and its two marginals -/

/-- Association chosen to make the Brownian projection literally `Prod.fst`. -/
abbrev ContinuousKMTSpace (K : ℕ) :=
  BrownianFineSpace K × DyadicPositionArray K

noncomputable def continuousKMTMeasure (K : ℕ) :
    Measure (ContinuousKMTSpace K) :=
  (brownianFineMeasure K).prod (dyadicPositionMeasure K)

instance continuousKMTMeasure_isProbabilityMeasure (K : ℕ) :
    IsProbabilityMeasure (continuousKMTMeasure K) := by
  unfold continuousKMTMeasure
  infer_instance

/-- Forget the position rows. -/
def continuousKMTToBrownian (K : ℕ) :
    ContinuousKMTSpace K → BrownianFineSpace K :=
  Prod.fst

/-- Forget the fine Gaussian family, retaining the common tree and positions. -/
def continuousKMTToContinuous (K : ℕ) :
    ContinuousKMTSpace K → DyadicContinuousSpace K :=
  fun omega => (omega.1.1, omega.2)

@[fun_prop]
theorem measurable_continuousKMTToBrownian (K : ℕ) :
    Measurable (continuousKMTToBrownian K) :=
  measurable_fst

@[fun_prop]
theorem measurable_continuousKMTToContinuous (K : ℕ) :
    Measurable (continuousKMTToContinuous K) :=
  (measurable_fst.comp measurable_fst).prodMk measurable_snd

/-- The Brownian projection preserves its complete two-factor law. -/
theorem continuousKMTMeasure_toBrownian (K : ℕ) :
    MeasurePreserving (continuousKMTToBrownian K)
      (continuousKMTMeasure K) (brownianFineMeasure K) := by
  simpa [continuousKMTMeasure, continuousKMTToBrownian] using
    (measurePreserving_fst :
      MeasurePreserving
        (fun z : BrownianFineSpace K × DyadicPositionArray K => z.1)
        ((brownianFineMeasure K).prod (dyadicPositionMeasure K))
        (brownianFineMeasure K))

/-- The Poisson projection preserves `tree × positions`. -/
theorem continuousKMTMeasure_toContinuous (K : ℕ) :
    MeasurePreserving (continuousKMTToContinuous K)
      (continuousKMTMeasure K) (dyadicContinuousMeasure K) := by
  have htree :
      MeasurePreserving
        (fun z : BrownianFineSpace K => z.1)
        (brownianFineMeasure K) (dyadicNoiseMeasure K) :=
    ⟨measurable_fst, brownianFineMeasure_map_fst K⟩
  have hprod := MeasurePreserving.prod htree
    (MeasurePreserving.id (dyadicPositionMeasure K))
  simpa [continuousKMTMeasure, continuousKMTToContinuous,
    dyadicContinuousMeasure] using hprod

/-- The tree coordinate on the common source has the committed tree law. -/
theorem continuousKMTMeasure_map_tree (K : ℕ) :
    (continuousKMTMeasure K).map
        (fun omega : ContinuousKMTSpace K => omega.1.1) =
      dyadicNoiseMeasure K := by
  have htree :
      MeasurePreserving
        (fun z : DyadicContinuousSpace K => z.1)
        (dyadicContinuousMeasure K) (dyadicNoiseMeasure K) :=
    ⟨measurable_fst, dyadicContinuousMeasure_map_fst K⟩
  have h := htree.comp (continuousKMTMeasure_toContinuous K)
  simpa [continuousKMTToContinuous, Function.comp_def] using h.map_eq

/-! ## Transported paths and their laws -/

noncomputable def continuousKMTPoisson
    (K : ℕ) (t : ℝ) (omega : ContinuousKMTSpace K) : ℕ :=
  committedContinuousPoisson K t
    (continuousKMTToContinuous K omega)

noncomputable def continuousKMTBrownian
    (K : ℕ) (t : ℝ) (omega : ContinuousKMTSpace K) : ℝ :=
  brownianPath K t (continuousKMTToBrownian K omega)

@[fun_prop]
theorem measurable_continuousKMTPoisson (K : ℕ) (t : ℝ) :
    Measurable (continuousKMTPoisson K t) :=
  (measurable_committedContinuousPoisson K t).comp
    (measurable_continuousKMTToContinuous K)

@[fun_prop]
theorem measurable_continuousKMTBrownian (K : ℕ) (t : ℝ) :
    Measurable (continuousKMTBrownian K t) :=
  (measurable_brownianPath K t).comp
    (measurable_continuousKMTToBrownian K)

/-- The transported counting path is nondecreasing samplewise. -/
theorem continuousKMTPoisson_mono
    (K : ℕ) (omega : ContinuousKMTSpace K) {s t : ℝ}
    (hst : s ≤ t) :
    continuousKMTPoisson K s omega ≤
      continuousKMTPoisson K t omega :=
  committedContinuousPoisson_mono K
    (continuousKMTToContinuous K omega) hst

/-- Integer agreement with the committed Poisson skeleton, pointwise. -/
theorem continuousKMTPoisson_natCast
    (K j : ℕ) (omega : ContinuousKMTSpace K) :
    continuousKMTPoisson K (j : ℝ) omega =
      DyadicSpatialSkeleton.spatialPoissonSkeleton K omega.1.1 j := by
  simpa [continuousKMTPoisson, continuousKMTToContinuous] using
    committedContinuousPoisson_natCast K j
      (continuousKMTToContinuous K omega)

/-- Integer agreement with the committed Gaussian skeleton, pointwise. -/
theorem continuousKMTBrownian_natCast
    (K j : ℕ) (hj : j ≤ dyadicHorizon K)
    (omega : ContinuousKMTSpace K) :
    continuousKMTBrownian K (j : ℝ) omega =
      DyadicSpatialSkeleton.spatialGaussianSkeleton K omega.1.1 j := by
  have hj' : j ≤ 2 ^ K := by
    simpa [dyadicHorizon] using hj
  have hjmem :
      (j : ℝ) ∈ Icc (0 : ℝ) ((2 : ℝ) ^ K) := by
    constructor
    · positivity
    · exact_mod_cast hj'
  unfold continuousKMTBrownian continuousKMTToBrownian
  rw [brownianPath_eq_candidate_of_mem K hjmem,
    brownianCandidate_natCast K j hj']

/-- The complete Brownian interface survives pullback to the common source. -/
theorem continuousKMTBrownian_dyadicBrownianOn (K : ℕ) :
    DyadicBrownianOn (continuousKMTMeasure K)
      (continuousKMTBrownian K) ((2 : ℝ) ^ K) := by
  let hbase := brownianPath_dyadicBrownianOn K
  refine
    { eval_measurable := measurable_continuousKMTBrownian K
      continuous_ae :=
        Filter.Eventually.of_forall fun omega =>
          continuous_brownianPath K omega.1
      cell_law := ?_
      cell_independent := ?_ }
  · intro m k
    let X : BrownianFineSpace K → ℝ := fun z =>
      brownianPath K
          (brownianDyadicPoint ((2 : ℝ) ^ K) m (k.val + 1)) z -
        brownianPath K
          (brownianDyadicPoint ((2 : ℝ) ^ K) m k.val) z
    have hX : Measurable X :=
      (measurable_brownianPath K
        (brownianDyadicPoint ((2 : ℝ) ^ K) m (k.val + 1))).sub
      (measurable_brownianPath K
        (brownianDyadicPoint ((2 : ℝ) ^ K) m k.val))
    calc
      (continuousKMTMeasure K).map
          (fun omega =>
            continuousKMTBrownian K
                (brownianDyadicPoint ((2 : ℝ) ^ K) m
                  (k.val + 1)) omega -
              continuousKMTBrownian K
                (brownianDyadicPoint ((2 : ℝ) ^ K) m
                  k.val) omega) =
        (continuousKMTMeasure K).map
          (fun omega => X (continuousKMTToBrownian K omega)) := rfl
      _ = ((continuousKMTMeasure K).map
          (continuousKMTToBrownian K)).map X := by
        exact (Measure.map_map hX
          (continuousKMTMeasure_toBrownian K).measurable).symm
      _ = (brownianFineMeasure K).map X := by
        rw [(continuousKMTMeasure_toBrownian K).map_eq]
      _ = gaussianReal 0
          (Real.toNNReal
            (brownianDyadicMesh ((2 : ℝ) ^ K) m)) := by
        simpa [X] using hbase.cell_law m k
  · intro m
    have h := iIndepFun_comp_fst
      (dyadicPositionMeasure K) (hbase.cell_independent m)
    simpa [continuousKMTMeasure, continuousKMTBrownian,
      continuousKMTToBrownian] using h

/-- The exact K20 data on the common source. -/
noncomputable def continuousKMTData (K : ℕ) :
    InterpolationData K (ContinuousKMTSpace K) where
  tree := fun omega => omega.1.1
  tree_measurable := measurable_fst.comp measurable_fst
  poissonPath := fun omega t => continuousKMTPoisson K t omega
  poisson_mono := fun omega _ _ hst =>
    continuousKMTPoisson_mono K omega hst
  poisson_integer := fun omega j =>
    continuousKMTPoisson_natCast K j omega
  gaussianPath := fun omega t => continuousKMTBrownian K t omega
  gaussian_integer := fun omega j hj =>
    continuousKMTBrownian_natCast K j hj omega

/-! ## Independent Poisson increments after transport -/

noncomputable def continuousKMTPoissonIncrementVector
    (K : ℕ) {r : ℕ} (t : Fin (r + 1) → ℝ)
    (omega : ContinuousKMTSpace K) : Fin r → ℕ :=
  fun i =>
    continuousKMTPoisson K (t i.succ) omega -
      continuousKMTPoisson K (t i.castSucc) omega

@[fun_prop]
theorem measurable_continuousKMTPoissonIncrementVector
    (K : ℕ) {r : ℕ} (t : Fin (r + 1) → ℝ) :
    Measurable (continuousKMTPoissonIncrementVector K t) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_continuousKMTPoisson K (t i.succ)).sub
    (measurable_continuousKMTPoisson K (t i.castSucc))

/-- The transported path retains the full product Poisson increment law. -/
theorem continuousKMTPoisson_incrementVector_law
    (K : ℕ) {r : ℕ} (t : Fin (r + 1) → ℝ)
    (hzero : t 0 = 0) (hstrict : StrictMono t)
    (hlast : t (Fin.last r) ≤ (2 ^ K : ℕ)) :
    (continuousKMTMeasure K).map
        (continuousKMTPoissonIncrementVector K t) =
      poissonIncrementProduct t := by
  let F : DyadicContinuousSpace K → Fin r → ℕ := fun z =>
    finiteIncrementVector (2 ^ K) t (dyadicCellBlock K z)
  have hF : Measurable F :=
    (measurable_finiteIncrementVector (2 ^ K) t).comp
      (measurable_dyadicCellBlock K)
  have hfun :
      continuousKMTPoissonIncrementVector K t =
        F ∘ continuousKMTToContinuous K := by
    funext omega i
    rfl
  calc
    (continuousKMTMeasure K).map
        (continuousKMTPoissonIncrementVector K t) =
      (continuousKMTMeasure K).map
        (F ∘ continuousKMTToContinuous K) := by rw [hfun]
    _ = ((continuousKMTMeasure K).map
          (continuousKMTToContinuous K)).map F := by
      exact (Measure.map_map hF
        (continuousKMTMeasure_toContinuous K).measurable).symm
    _ = (dyadicContinuousMeasure K).map F := by
      rw [(continuousKMTMeasure_toContinuous K).map_eq]
    _ = poissonIncrementProduct t :=
      committedContinuousPoisson_incrementVector_law
        K t hzero hstrict hlast

/-- Every transported increment has its requested Poisson marginal. -/
theorem continuousKMTPoisson_increment_map
    (K : ℕ) {r : ℕ} (t : Fin (r + 1) → ℝ)
    (hzero : t 0 = 0) (hstrict : StrictMono t)
    (hlast : t (Fin.last r) ≤ (2 ^ K : ℕ))
    (i : Fin r) :
    (continuousKMTMeasure K).map
        (fun omega => continuousKMTPoissonIncrementVector K t omega i) =
      poisMeasure (t i.succ - t i.castSucc) := by
  have hX := measurable_continuousKMTPoissonIncrementVector K t
  calc
    (continuousKMTMeasure K).map
        (fun omega => continuousKMTPoissonIncrementVector K t omega i) =
      ((continuousKMTMeasure K).map
        (continuousKMTPoissonIncrementVector K t)).map
          (fun v => v i) :=
      (Measure.map_map (measurable_pi_apply i) hX).symm
    _ = (poissonIncrementProduct t).map (fun v => v i) := by
      rw [continuousKMTPoisson_incrementVector_law
        K t hzero hstrict hlast]
    _ = poisMeasure (t i.succ - t i.castSucc) := by
      unfold poissonIncrementProduct
      haveI : ∀ q : Fin r,
          IsProbabilityMeasure (poisMeasure (t q.succ - t q.castSucc)) :=
        fun q => poisMeasure_isProbabilityMeasure_of_nonneg
          (sub_nonneg.mpr
            (hstrict.monotone (Fin.castSucc_le_succ q)))
      exact Measure.infinitePi_map_eval
        (fun q : Fin r =>
          poisMeasure (t q.succ - t q.castSucc)) i

/-- Hence every finite increasing grid has independent Poisson increments. -/
theorem continuousKMTPoisson_increment_iIndep
    (K : ℕ) {r : ℕ} (t : Fin (r + 1) → ℝ)
    (hzero : t 0 = 0) (hstrict : StrictMono t)
    (hlast : t (Fin.last r) ≤ (2 ^ K : ℕ)) :
    iIndepFun
      (fun i omega => continuousKMTPoissonIncrementVector K t omega i)
      (continuousKMTMeasure K) := by
  classical
  let X := continuousKMTPoissonIncrementVector K t
  have hX : Measurable X :=
    measurable_continuousKMTPoissonIncrementVector K t
  have hm : ∀ i, Measurable (fun omega => X omega i) := fun i =>
    (measurable_pi_apply i).comp hX
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map hm]
  change
    (continuousKMTMeasure K).map
        (continuousKMTPoissonIncrementVector K t) =
      Measure.infinitePi fun i : Fin r =>
        (continuousKMTMeasure K).map
          (fun omega => continuousKMTPoissonIncrementVector K t omega i)
  rw [continuousKMTPoisson_incrementVector_law
    K t hzero hstrict hlast]
  unfold poissonIncrementProduct
  congr 1
  funext i
  exact (continuousKMTPoisson_increment_map
    K t hzero hstrict hlast i).symm

/-! ## Brownian unit-cell oscillation -/

def brownianOscillationA : ℝ := 512

def brownianOscillationB : ℝ := 256

def brownianOscillationPrefactor : ℝ :=
  brownianEntropyTailConstant

/-- On a unit interval, the `BrownianEntropyModulus` modulus is below K20's threshold. -/
theorem brownianEntropyBound_unit_le_oscillationThreshold
    (K : ℕ) {a h : ℝ} (ha : 0 ≤ a)
    (hh : h ∈ Icc (0 : ℝ) 1) :
    brownianEntropyBound ((2 : ℝ) ^ K) a h ≤
      oscillationThreshold K
        brownianOscillationA brownianOscillationB a := by
  by_cases hhzero : h = 0
  · subst h
    have h0 : brownianEntropyCore ((2 : ℝ) ^ K) a 0 = 0 := by
      simp [brownianEntropyCore]
    unfold brownianEntropyBound oscillationThreshold
      brownianOscillationA brownianOscillationB
    rw [h0]
    unfold brownianEntropyConstant
    nlinarith [Real.sqrt_nonneg (kmtHorizonLog K + a)]
  have hhpos : 0 < h :=
    lt_of_le_of_ne hh.1 (Ne.symm hhzero)
  have hHpos : 0 < (2 : ℝ) ^ K := by positivity
  have hHone : (1 : ℝ) ≤ (2 : ℝ) ^ K :=
    one_le_pow₀ (by norm_num)
  have hlogH0 : 0 ≤ Real.log ((2 : ℝ) ^ K) :=
    Real.log_nonneg hHone
  have hmain :
      h * Real.log ((2 : ℝ) ^ K) ≤
        Real.log ((2 : ℝ) ^ K) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hh.2) hlogH0]
  have hsmall := neg_mul_log_le_one hhpos
  have hlogDiv :
      h * Real.log (((2 : ℝ) ^ K) / h) ≤
        Real.log ((2 : ℝ) ^ K) + 1 := by
    rw [Real.log_div hHpos.ne' hhpos.ne']
    nlinarith
  have htail : h * a ≤ a := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hh.2) ha]
  have hlogTwo : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlogCompare :
      Real.log ((2 : ℝ) ^ K) + 1 ≤
        2 * kmtHorizonLog K := by
    unfold kmtHorizonLog
    rw [Real.log_pow, Real.log_pow]
    push_cast
    have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith
  have hL0 : 0 ≤ kmtHorizonLog K := by
    unfold kmtHorizonLog
    exact Real.log_nonneg (one_le_pow₀ (by norm_num))
  have hinsideTwo :
      h * (Real.log (((2 : ℝ) ^ K) / h) + a) ≤
        2 * (kmtHorizonLog K + a) := by
    calc
      h * (Real.log (((2 : ℝ) ^ K) / h) + a) =
          h * Real.log (((2 : ℝ) ^ K) / h) + h * a := by ring
      _ ≤ (Real.log ((2 : ℝ) ^ K) + 1) + a :=
        add_le_add hlogDiv htail
      _ ≤ 2 * (kmtHorizonLog K + a) := by
        nlinarith
  have hinsideFour :
      h * (Real.log (((2 : ℝ) ^ K) / h) + a) ≤
        4 * (kmtHorizonLog K + a) := by
    nlinarith
  have hsqrt :
      Real.sqrt
          (h * (Real.log (((2 : ℝ) ^ K) / h) + a)) ≤
        2 * Real.sqrt (kmtHorizonLog K + a) := by
    calc
      Real.sqrt
          (h * (Real.log (((2 : ℝ) ^ K) / h) + a)) ≤
        Real.sqrt (4 * (kmtHorizonLog K + a)) :=
          Real.sqrt_le_sqrt hinsideFour
      _ = 2 * Real.sqrt (kmtHorizonLog K + a) := by
        rw [Real.sqrt_mul (by norm_num),
          show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]
  unfold brownianEntropyBound brownianEntropyCore
    brownianEntropyConstant oscillationThreshold
    brownianOscillationA brownianOscillationB
  rw [if_neg hhzero]
  nlinarith

/-- K20's unit-cell event is contained in the all-pairs event of `BrownianEntropyModulus`. -/
theorem continuousKMTOscillationFailure_subset
    (K : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    oscillationFailure (continuousKMTData K)
        (oscillationThreshold K
          brownianOscillationA brownianOscillationB y) ⊆
      brownianEntropyFailure (continuousKMTBrownian K)
        ((2 : ℝ) ^ K) y := by
  rintro omega ⟨j, u, hu, hbad⟩
  have hjTopNat : j.1 + 1 ≤ 2 ^ K := by
    have h := Nat.succ_le_iff.mpr j.isLt
    simpa [dyadicHorizon] using h
  have hjTopReal : (j.1 : ℝ) + 1 ≤ (2 : ℝ) ^ K := by
    exact_mod_cast hjTopNat
  have hbad' :
      oscillationThreshold K
          brownianOscillationA brownianOscillationB y <
        |continuousKMTBrownian K ((j.1 : ℝ) + u) omega -
          continuousKMTBrownian K (j.1 : ℝ) omega| := by
    simpa [continuousKMTData] using hbad
  refine ⟨(j.1 : ℝ) + u,
    ⟨by linarith [hu.1, (Nat.cast_nonneg j.1 : (0 : ℝ) ≤ j.1)],
      by linarith [hu.2]⟩,
    (j.1 : ℝ), ⟨by positivity, by linarith⟩, ?_⟩
  have hbound :=
    brownianEntropyBound_unit_le_oscillationThreshold K hy hu
  have hdist :
      |((j.1 : ℝ) + u) - (j.1 : ℝ)| = u := by
    rw [show ((j.1 : ℝ) + u) - (j.1 : ℝ) = u by ring,
      abs_of_nonneg hu.1]
  rw [hdist]
  exact hbound.trans_lt hbad'

/-- Exact `(H_osc)` for the common-space K20 theorem. -/
theorem continuousKMTOscillation_tail
    (K : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    (continuousKMTMeasure K).real
        (oscillationFailure (continuousKMTData K)
          (oscillationThreshold K
            brownianOscillationA brownianOscillationB y)) ≤
      brownianOscillationPrefactor * Real.exp (-y) := by
  calc
    (continuousKMTMeasure K).real
        (oscillationFailure (continuousKMTData K)
          (oscillationThreshold K
            brownianOscillationA brownianOscillationB y)) ≤
      (continuousKMTMeasure K).real
        (brownianEntropyFailure (continuousKMTBrownian K)
          ((2 : ℝ) ^ K) y) :=
      measureReal_mono
        (continuousKMTOscillationFailure_subset K hy)
    _ ≤ brownianOscillationPrefactor * Real.exp (-y) := by
      have htail := law_brownianEntropyFailure_le
        (P := continuousKMTMeasure K)
        (W := continuousKMTBrownian K)
        (H := (2 : ℝ) ^ K) (a := y)
        (one_le_pow₀ (by norm_num)) hy
        (continuousKMTBrownian_dyadicBrownianOn K)
      change
        ((continuousKMTMeasure K)
          (brownianEntropyFailure (continuousKMTBrownian K)
            ((2 : ℝ) ^ K) y)).toReal ≤ _
      calc
        ((continuousKMTMeasure K)
            (brownianEntropyFailure (continuousKMTBrownian K)
              ((2 : ℝ) ^ K) y)).toReal ≤
          (ENNReal.ofReal
            (brownianEntropyTailConstant * Real.exp (-y))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top htail
        _ = brownianOscillationPrefactor * Real.exp (-y) := by
          rw [ENNReal.toReal_ofReal (by
            unfold brownianEntropyTailConstant
            positivity)]
          rfl

/-! ## Explicit final constants and headline -/

def continuousKMTConstant : ℝ :=
  3375 + 2 * Real.exp 1

def continuousKMTPrefactor : ℝ :=
  7 + Real.exp 2

def continuousKMTRate : ℝ :=
  9 / 65536

private theorem interpolationConstant_concrete :
    interpolationConstant
        brownianOscillationA brownianOscillationB =
      continuousKMTConstant := by
  unfold interpolationConstant brownianOscillationA
    brownianOscillationB continuousKMTConstant
  ring

private theorem interpolationPrefactor_concrete :
    interpolationPrefactor brownianOscillationPrefactor =
      continuousKMTPrefactor := by
  unfold interpolationPrefactor brownianOscillationPrefactor
    brownianEntropyTailConstant continuousKMTPrefactor
  first | rfl | norm_num

private theorem interpolationRate_concrete :
    interpolationRate brownianOscillationA brownianOscillationB =
      continuousKMTRate := by
  unfold interpolationRate brownianOscillationA brownianOscillationB
    continuousKMTRate
  apply min_eq_left
  apply le_min
  · norm_num
  · unfold interpolationOscillationRate
    norm_num

/-- **Continuous finite-horizon KMT theorem, with no remaining hypothesis.** -/
theorem continuousTime_finiteHorizonKMT
    (K : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (continuousKMTMeasure K).real
        {omega | ∃ t : ℝ,
          t ∈ Icc (0 : ℝ) ((2 : ℝ) ^ K) ∧
            continuousKMTConstant *
                  Real.log ((2 : ℝ) ^ (K + 1)) + x <
              |(continuousKMTPoisson K t omega : ℝ) - t -
                continuousKMTBrownian K t omega|} ≤
      continuousKMTPrefactor *
        Real.exp (-(continuousKMTRate * x)) := by
  have htail := continuousInterpolation_tail
    (K := K) (mu := continuousKMTMeasure K)
    (D := continuousKMTData K)
    (hTreeLaw := by simpa [continuousKMTData] using continuousKMTMeasure_map_tree K)
    (A := brownianOscillationA)
    (B := brownianOscillationB)
    (c := brownianOscillationPrefactor)
    (hA := by norm_num [brownianOscillationA])
    (hB := by norm_num [brownianOscillationB])
    (hc := by
      unfold brownianOscillationPrefactor brownianEntropyTailConstant
      positivity)
    (hOsc := continuousKMTOscillation_tail K)
    (x := x) hx
  rw [interpolationConstant_concrete,
    interpolationPrefactor_concrete,
    interpolationRate_concrete] at htail
  simpa [continuousDeviationFailure, continuousKMTData,
    continuousKMTPoisson, continuousKMTBrownian,
    dyadicHorizon, kmtHorizonLog] using htail

/-!
THEOREM LIST
* `continuousKMTMeasure_toBrownian`
* `continuousKMTMeasure_toContinuous`
* `continuousKMTMeasure_map_tree`
* `continuousKMTPoisson_natCast`
* `continuousKMTBrownian_natCast`
* `continuousKMTBrownian_dyadicBrownianOn`
* `continuousKMTPoisson_incrementVector_law`
* `continuousKMTPoisson_increment_map`
* `continuousKMTPoisson_increment_iIndep`
* `brownianEntropyBound_unit_le_oscillationThreshold`
* `continuousKMTOscillationFailure_subset`
* `continuousKMTOscillation_tail`
* `continuousTime_finiteHorizonKMT`

CLOSES
* Item 1: the common three-factor source and both measure-preserving
  projections; the two paths share the original tree coordinate.
* Item 2: exact K20 oscillation hypothesis with
  `A = 512`, `B = 256`, `c = exp 2`, and pointwise integer agreement.
* Item 3: the no-premise continuous-time finite-horizon KMT tail with
  `C = 3375 + 2 exp 1`, `a = 7 + exp 2`, `b = 9/65536`, together with the
  transported product Poisson increment law, increment independence, and
  `DyadicBrownianOn`.

UNFINISHED
* No mathematical hypothesis remains in this item.
END
-/

end Ripple.Kurtz.StrongApprox.ContinuousFiniteHorizonKMT

end
